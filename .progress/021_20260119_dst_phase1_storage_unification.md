# Task: DST Phase 1 - Storage Unification (The "Split Brain" Fix)

**Created:** 2026-01-19
**State:** IN PROGRESS
**Priority:** CRITICAL - Current "DST" bypasses real DST infrastructure
**Plan Number:** 021
**Parent Plan:** 020_dst_remediation_plan.md

## Problem Statement

The current `kelpie-server` implements its own `SimStorage` (a `HashMap` wrapper) which bypasses the actual `kelpie-dst` infrastructure that has sophisticated fault injection and transaction support.

**Current Architecture:**
```
kelpie-server/src/storage/sim.rs
├── SimStorage (separate implementation)
├── RwLock<HashMap<String, AgentMetadata>>
├── RwLock<HashMap<String, Vec<Block>>>
├── Basic fault injection
└── Implements AgentStorage trait

kelpie-dst/src/storage.rs
├── SimStorage (proper DST infrastructure)
├── Arc<RwLock<HashMap<Vec<u8>, Vec<u8>>>>
├── Sophisticated fault injection
├── Transaction support (CrashDuringTransaction, etc.)
└── Implements ActorKV trait
```

**The Split Brain Problem:**
- Two separate storage implementations
- Server's SimStorage has NO transaction support
- DST tests don't test the actual production storage patterns
- Fault injection is incomplete in server's version

## Solution: Create KvAdapter

Create a structural adapter that maps `AgentStorage` (high-level) onto `ActorKV` (byte-level).

**Target Architecture:**
```
kelpie-server uses:
└── KvAdapter (NEW)
    ├── Wraps Arc<dyn ActorKV>
    ├── Implements AgentStorage trait
    ├── Serializes/deserializes structs to/from bytes
    └── Uses proper DST infrastructure

    Can wrap any ActorKV:
    ├── SimStorage (kelpie-dst) - for DST
    ├── MemoryKV - for unit tests
    └── FdbKV - for production (future)
```

## Options & Decisions

### Option 1: JSON Serialization (CHOSEN)
**Pros:**
- Human-readable keys and values
- Easy debugging in tests
- Flexible schema evolution
- Matches Letta's approach

**Cons:**
- Slightly larger storage footprint
- Not as compact as bincode

**Decision:** Use JSON for serialization. Reasoning: Debugging and schema flexibility are more important than storage density at this stage. We can optimize later if needed.

### Option 2: Bincode Serialization
**Pros:**
- Very compact
- Fast serialization

**Cons:**
- Binary format (harder to debug)
- Less flexible for schema changes

**Decision:** NOT chosen - optimization can come later.

### Key Mapping Strategy (CHOSEN)

```rust
// Agents: agents/{id}
fn agent_key(id: &str) -> Vec<u8> {
    format!("agents/{}", id).into_bytes()
}

// Sessions: sessions/{agent_id}/{session_id}
fn session_key(agent_id: &str, session_id: &str) -> Vec<u8> {
    format!("sessions/{}/{}", agent_id, session_id).into_bytes()
}

// Messages: messages/{agent_id}/{message_id}
fn message_key(agent_id: &str, message_id: &str) -> Vec<u8> {
    format!("messages/{}/{}", agent_id, message_id).into_bytes()
}

// Blocks: blocks/{agent_id}
fn blocks_key(agent_id: &str) -> Vec<u8> {
    format!("blocks/{}", agent_id).into_bytes()
}

// Tools: tools/{name}
fn tool_key(name: &str) -> Vec<u8> {
    format!("tools/{}", name).into_bytes()
}
```

**Rationale:**
- Hierarchical keys support prefix scanning
- Clear namespacing prevents collisions
- Compatible with FDB's range scans

## Implementation Phases

### Phase 1.1: Create KvAdapter ✅ COMPLETE
- [x] Create `crates/kelpie-server/src/storage/adapter.rs`
- [x] Define KvAdapter struct wrapping `Arc<dyn ActorKV>`
- [x] Implement key mapping functions
- [x] Implement AgentMetadata operations (save/load/delete/list)
- [x] Implement Block operations
- [x] Implement Session operations
- [x] Implement Message operations
- [x] Implement CustomTool operations
- [x] Implement checkpoint (use ActorKV transactions!)
- [x] Add comprehensive unit tests (7 tests, all passing)

**Key Implementation Details:**
```rust
pub struct KvAdapter {
    kv: Arc<dyn ActorKV>,
    actor_id: ActorId, // Scoped to "kelpie-server" namespace
}

impl KvAdapter {
    pub fn new(kv: Arc<dyn ActorKV>) -> Self {
        // Use a well-known ActorId for the server's storage namespace
        let actor_id = ActorId::new("kelpie", "server").unwrap();
        Self { kv, actor_id }
    }
}
```

### Phase 1.2: Replace SimStorage
- [ ] Update `crates/kelpie-server/src/storage/mod.rs` exports
- [ ] Delete `crates/kelpie-server/src/storage/sim.rs`
- [ ] Update `AppState` to use KvAdapter
- [ ] Add factory function for creating SimStorage-backed adapter
- [ ] Add factory function for creating MemoryKV-backed adapter

### Phase 1.3: Update DST Tests
- [ ] Find all `*_dst.rs` tests in kelpie-server
- [ ] Update to use `kelpie_dst::SimStorage` via KvAdapter
- [ ] Add proper FaultInjector setup
- [ ] Verify determinism (same seed = same behavior)

### Phase 1.4: Verification
- [ ] Run `cargo test -p kelpie-server`
- [ ] Run `cargo test -p kelpie-dst`
- [ ] Run `scripts/check_dst.sh` to verify determinism
- [ ] Verify no stubs or TODOs left

## Instance Log

| Instance | Phase | Status | Notes |
|----------|-------|--------|-------|
| Claude-1 | 1.1   | IN_PROGRESS | Creating plan, implementing KvAdapter |

## Findings

### Key Discoveries
- Server's SimStorage has 5 main data stores: agents, blocks, sessions, messages, custom_tools
- DST's SimStorage already implements ActorKV perfectly
- ActorTransaction exists and supports CrashDuringTransaction fault
- AgentStorage trait already has checkpoint() method for atomic session+message saves
- CustomToolRecord has additional fields (runtime, requirements, created_at, updated_at) not used in old SimStorage tests

### Technical Insights
- ActorKV uses scoped keys: `actor_id.to_key_bytes() + "/" + key`
- We'll use ActorId("kelpie", "server") as the namespace for all server storage
- JSON serialization is ~2x larger than bincode but much easier to debug
- Borrow checker requires cloning blocks before calling save_blocks in update/append operations
- Need `?Sized` on serialize() to handle `&[Block]` slices

### Implementation Stats
- **Lines of code**: 854 lines in adapter.rs
- **Tests**: 7 comprehensive tests, all passing ✅
- **Total server tests**: 154 tests passing
- **Key mapping functions**: 7 functions for different entity types
- **AgentStorage methods implemented**: 19 methods (all required)

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-19 14:00 | Use JSON for serialization | Human-readable, flexible schema | Larger storage footprint |
| 2026-01-19 14:05 | Hierarchical key mapping | Supports prefix scans, clear namespacing | Slightly longer keys |
| 2026-01-19 14:10 | Use ActorId("kelpie", "server") | Scopes all server storage under one namespace | All server data in one logical space |
| 2026-01-19 14:15 | Implement checkpoint with transactions | Leverage ActorKV transaction support | More complex but correct |

## What to Try

### Works Now ✅
- **Create KvAdapter with MemoryKV** (for unit tests):
  ```rust
  let adapter = KvAdapter::with_memory();
  ```
- **Create KvAdapter with DST infrastructure** (for DST tests):
  ```rust
  let rng = DeterministicRng::new(42);
  let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
  let adapter = KvAdapter::with_dst_storage(rng, faults);
  ```
- **Use adapter as AgentStorage**:
  ```rust
  let storage: Arc<dyn AgentStorage> = Arc::new(adapter);
  storage.save_agent(&agent).await?;
  ```
- **Atomic checkpoints with transactions**:
  ```rust
  adapter.checkpoint(&session, Some(&message)).await?;
  // Uses ActorKV transactions under the hood!
  ```

### Doesn't Work Yet
- Server integration (Phase 1.2 pending - need to replace old SimStorage)
- DST test updates (Phase 1.3 pending - need to use new adapter)
- Old SimStorage still exists (Phase 1.2 will delete it)

### Known Limitations
- Will need to migrate existing in-memory data to new format (not covered in this phase)
- FDB integration deferred to later phase

## Success Criteria

1. **No Split Brain**: Server uses `kelpie-dst::SimStorage` for DST tests
2. **Transaction Support**: checkpoint() uses ActorKV transactions
3. **Fault Injection Works**: Can inject CrashDuringTransaction and see proper behavior
4. **All Tests Pass**: Both kelpie-server and kelpie-dst test suites pass
5. **Determinism Verified**: `scripts/check_dst.sh` passes
6. **No Placeholders**: No TODOs, no stubs, no commented code

## Verification Checklist

Before marking Phase 1 complete:
- [ ] `cargo test -p kelpie-server` passes
- [ ] `cargo test -p kelpie-dst` passes
- [ ] `cargo clippy` has no warnings
- [ ] `cargo fmt --check` passes
- [ ] `scripts/check_dst.sh` passes (determinism verified)
- [ ] No TODOs in new code
- [ ] No stubs or placeholder implementations
- [ ] All AgentStorage methods implemented
- [ ] Checkpoint uses transactions
- [ ] Comprehensive unit tests added

## References

- Parent Plan: `.progress/020_dst_remediation_plan.md`
- Proper DST Architecture: `.progress/012_20260114_proper_dst_architecture.md`
- ActorKV Trait: `crates/kelpie-storage/src/kv.rs`
- DST SimStorage: `crates/kelpie-dst/src/storage.rs`
- Server SimStorage (to be deleted): `crates/kelpie-server/src/storage/sim.rs`
- AgentStorage Trait: `crates/kelpie-server/src/storage/traits.rs`

## Commit Message Template

```
feat(dst): Unify storage with KvAdapter for true DST

Phase 1 of DST remediation:
- Create KvAdapter wrapping ActorKV trait
- Replace server's SimStorage with adapter
- Enable proper fault injection and transactions
- Fixes "split brain" issue where DST tests bypassed real infrastructure

Resolves: #020 Phase 1
```

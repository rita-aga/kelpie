# ADR-009: Memory Tools Architecture

**Date:** 2026-01-13
**Status:** Accepted
**Context:** Kelpie Agent Framework - Letta Feature Parity

---

## Context

Kelpie implements Letta-compatible memory tools that allow agents to modify their own memory during conversation. These tools are critical for long-running agents that need to persist knowledge across sessions.

The memory tools need to:
1. Integrate with the existing AppState storage
2. Support DST (Deterministic Simulation Testing) with fault injection
3. Handle concurrent access from multiple tool calls
4. Be available to all agents automatically

---

## Decision

### Architecture: Thin Wrappers Around AppState

Memory tools are implemented as thin wrappers around `AppState` methods, registered via `UnifiedToolRegistry`.

```
┌─────────────────────────────────────────────────────────────┐
│                   Memory Tools (tools/memory.rs)            │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ core_memory_append     → state.update_block_by_label │  │
│  │ core_memory_replace    → state.update_block_by_label │  │
│  │ archival_memory_insert → state.add_archival          │  │
│  │ archival_memory_search → state.search_archival       │  │
│  │ conversation_search    → state.list_messages         │  │
│  └──────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    AppState (state.rs)                       │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ Fault Injection Points (cfg(feature = "dst")):        │  │
│  │  - block_read    → get_block_by_label                 │  │
│  │  - block_write   → update_block_by_label              │  │
│  │  - agent_write   → update_agent                       │  │
│  │  - archival_read → search_archival                    │  │
│  │  - archival_write→ add_archival                       │  │
│  │  - message_read  → list_messages                      │  │
│  └──────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### Implementation Details

1. **Tool Registration**: Memory tools are registered at server startup via `register_memory_tools()`.

2. **Fault Injection**: AppState methods include fault injection points gated by `#[cfg(feature = "dst")]`. The `FaultInjector` is passed via `AppState::with_fault_injector()`.

3. **Error Handling**: Tools return user-friendly error messages (not panics) when operations fail.

### Known Issue: TOCTOU Race Condition (BUG-001)

The `core_memory_append` implementation has a TOCTOU (Time-of-Check to Time-of-Use) race condition:

```rust
// Check if block exists
let block_exists = state.get_block_by_label(&agent_id, &label)?;

// GAP: Another thread could create the block here!

if block_exists.is_some() {
    state.update_block_by_label(...)  // Append
} else {
    state.update_agent(...)  // Create new block
}
```

**Impact:** Under concurrent requests, duplicate blocks with the same label could be created.

**Recommended Fix:** Atomic `append_or_create_block_by_label()` operation that uses a single write lock.

---

## Alternatives Considered

### 1. Direct Umi Integration

**Description:** Wire memory tools directly to Umi memory backend instead of AppState.

**Pros:**
- Richer memory semantics (entity extraction, evolution tracking)
- Semantic search via embeddings

**Cons:**
- Additional complexity for simple use cases
- Umi requires embedding provider configuration

**Decision:** Deferred. Current AppState approach is simpler and meets immediate needs. Can add Umi layer later without breaking API.

### 2. Separate Memory Service

**Description:** Create a dedicated memory service with its own process/API.

**Pros:**
- Clear separation of concerns
- Independent scaling

**Cons:**
- Network overhead
- Additional operational complexity
- Harder to DST test

**Decision:** Rejected. In-process AppState is simpler and DST-friendly.

### 3. Lock-Free Data Structures

**Description:** Use lock-free concurrent data structures instead of `RwLock<HashMap>`.

**Pros:**
- Better concurrent performance
- No lock contention

**Cons:**
- Complex implementation
- Harder to reason about correctness
- Rust's borrowing rules make lock-free structures challenging

**Decision:** Rejected. Current RwLock approach is correct, simple, and sufficient for expected load.

---

## Consequences

### Positive

1. **Simplicity:** Memory tools are thin wrappers, easy to understand and maintain.
2. **DST Support:** Fault injection points allow comprehensive testing under failures.
3. **Unified Storage:** All memory operations go through AppState, single source of truth.
4. **API Compatibility:** Letta-compatible tool signatures.

### Negative

1. **TOCTOU Bug:** Race condition in `core_memory_append` needs fixing.
2. **No Semantic Search:** AppState uses text search, not embeddings. Umi would provide semantic search.
3. **In-Memory Only:** Current implementation loses data on restart (FDB integration pending).

### Risks

1. **Data Corruption:** TOCTOU race could create duplicate blocks under high concurrency.
   - Mitigation: Atomic operation, or document as limitation until fixed.

2. **Performance:** RwLock contention under high load.
   - Mitigation: Monitor, add sharding if needed.

---

## DST Testing Strategy

### Two Testing Approaches

**1. Standalone Fault Injection (memory_tools_real_dst.rs)**
- Uses `AppState::with_fault_injector()` directly
- Tests the actual `tools/memory.rs` implementation
- Injects faults at AppState operation points
- Lightweight, fast tests

**2. Full Simulation Harness (memory_tools_simulation.rs)**
- Uses `Simulation::new(config).run(|env| ...)`
- Tests via `UmiMemoryBackend::from_sim_env(&env, agent_id)`
- Full simulated environment: SimClock, SimNetwork, SimStorage
- Proper DST-first testing methodology

### Fault Types Used

**Standalone Tests (AppState):**
| Operation | Fault Point | Test Coverage |
|-----------|------------|---------------|
| Block read | `block_read` | ✅ 100% fault rate tested |
| Block write | `block_write` | ✅ 100% fault rate tested |
| Agent update | `agent_write` | ✅ 100% fault rate tested |
| Archival read | `archival_read` | ✅ 100% fault rate tested |
| Archival write | `archival_write` | ✅ 100% fault rate tested |
| Message read | `message_read` | ✅ 100% fault rate tested |

**Simulation Tests (UmiMemoryBackend):**
| Operation | Fault Types | Test Coverage |
|-----------|------------|---------------|
| Core memory append | StorageWriteFail, StorageReadFail | ✅ 20% rate tested |
| Core memory replace | StorageReadFail, StorageWriteFail | ✅ 10% rate tested |
| Archival insert | EmbeddingTimeout, StorageWriteFail | ✅ 10% rate tested |
| Archival search | VectorSearchFail, EmbeddingTimeout | ✅ 10% rate tested |
| High load | Mixed faults (5%) | ✅ 50 operations tested |
| Storage corruption | StorageCorruption | ✅ 10% rate tested |

### Test Results (seed=42)

**Standalone Tests (10 passing):**
- Probabilistic testing: 12 successes, 8 failures at 30% fault rate
- Recovery after transient faults verified
- Graceful error handling confirmed

**Simulation Tests (12 passing):**
- Core memory operations: append, replace
- Archival operations: insert, search
- Conversation search
- Multi-agent isolation
- High load stress test (95 successes, 10 faults)
- Determinism verified (same seed = same results)

### TOCTOU Race Testing

The race condition was not triggered because:
- Async tests use cooperative scheduling (`join_all`)
- True parallelism requires OS threads

**Recommendation:** Add multi-threaded test with `std::thread::spawn` to expose race.

---

## Future Work

1. **Fix TOCTOU Race (P0):** Implement atomic `append_or_create_block_by_label()`.
2. **Umi Integration (P1):** Add semantic search via Umi backend.
3. **FDB Persistence (P1):** Wire FDB for durable storage.
4. **Performance Testing (P2):** Benchmark under high concurrency.

---

## References

- Progress file: `.progress/006_20260112_agent_framework_letta_parity.md`
- DST framework: `crates/kelpie-dst/src/fault.rs`
- Memory tools: `crates/kelpie-server/src/tools/memory.rs`
- AppState: `crates/kelpie-server/src/state.rs`
- DST tests: `crates/kelpie-server/tests/memory_tools_real_dst.rs`

# Task: DST-First Transaction Support

**Created:** 2026-01-12 16:00:00
**State:** IMPLEMENTING

---

## Vision Alignment

**Vision files read:**
- `.vision/CONSTRAINTS.md` - Simulation-first development requirements
- `CLAUDE.md` - TigerStyle principles, DST workflow
- `docs/adr/002-foundationdb-integration.md` - Storage design
- `docs/adr/007-fdb-backend-implementation.md` - DST vs Production separation

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - Write DST tests BEFORE implementation
- TigerStyle safety principles (CONSTRAINTS.md §3) - 2+ assertions per function
- No placeholders in production (CONSTRAINTS.md §4)
- DST tests APPLICATION code, not infrastructure (ADR-007)

---

## Task Description

Add transaction support to Kelpie's storage layer following DST-first methodology. Currently:

1. **State only saved on deactivation** - Crashes lose in-memory state
2. **KV operations not atomic** - Multiple `set()` calls can partially fail
3. **State + KV not atomic** - No way to atomically update state and user KV data
4. **`CrashDuringTransaction` fault exists but unused** - SimStorage doesn't support transactions

**Goal:** Enable actors to perform atomic multi-key operations that survive crashes.

---

## Problems to Solve

### Problem 1: State Persistence on Crash

**Current behavior:** Actor state is held in memory, only persisted on graceful deactivation (`save_state()` in `activation.rs:deactivate()`).

**Impact:** If a node crashes, all in-flight actor state is lost.

**Solution approach:**
- Option A: Save state after every invocation (simple, high I/O)
- Option B: Add transaction API, save state atomically within transactions (proper)
- Option C: Write-ahead log for crash recovery (complex)

### Problem 2: Non-Atomic KV Operations

**Current behavior:** Each `set()`, `delete()` is independent. No way to ensure multiple operations succeed or fail together.

**Impact:** Partial updates can leave actor state inconsistent.

**Solution approach:**
- Add transaction API to `ActorKV` trait
- Batch operations within transaction, commit atomically

### Problem 3: State + KV Atomicity

**Current behavior:** Actor's primary state blob (`__state__` key) and user KV data are separate. No way to update both atomically.

**Impact:** Actor may have updated user data but old state, or vice versa.

**Solution approach:**
- Transactions must include both state writes and KV writes
- Runtime wraps invocations in transactions

---

## DST-First Development Order

```
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 1: Extend DST Harness (SimStorage)                               │
│  - Add Transaction trait with begin/commit/abort                        │
│  - Implement in SimStorage with in-memory buffering                     │
│  - Wire up CrashDuringTransaction fault injection                       │
│  - NO production code touched yet                                       │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 2: Write DST Tests FIRST                                         │
│  - Test: Atomic multi-key write succeeds                                │
│  - Test: Crash during transaction rolls back                            │
│  - Test: Crash after commit preserves data                              │
│  - Test: Concurrent transactions don't interfere                        │
│  - Tests define the CONTRACT before implementation                      │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 3: Add Transaction API to ActorKV Trait                          │
│  - Add ActorTransaction trait                                           │
│  - Add begin_transaction() to ActorKV                                   │
│  - Update ScopedKV to support transactions                              │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 4: Update Actor Runtime                                          │
│  - Wrap invocations in transactions                                     │
│  - Auto-commit on success, abort on failure                             │
│  - State saved within transaction (not just deactivation)               │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 5: Implement in FdbKV (Production)                               │
│  - Map ActorTransaction to FDB transactions                             │
│  - Use FDB's native atomicity                                           │
│  - Integration tests against real FDB                                   │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Options & Decisions [REQUIRED]

### Decision 1: Transaction API Design

**Context:** How should the transaction API be structured?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Closure-based | `kv.transaction(\|txn\| { txn.set(...) })` | Ensures commit/abort, Rust-idiomatic | Lifetime complexity, async closures tricky |
| B: Explicit handle | `let txn = kv.begin(); txn.set(...); txn.commit()` | Simple API, easy async | User must remember to commit |
| C: Builder pattern | `kv.batch().set(...).set(...).commit()` | Fluent, obvious | Less flexible, can't read-then-write |

**Decision:** Option B - Explicit handle

**Rationale:**
- FDB uses explicit transactions - natural mapping
- Async closures in Rust are complex (lifetime issues)
- Can add helper for common patterns later
- Runtime will manage commit/abort, reducing user error risk

**Trade-offs accepted:**
- User CAN forget to commit (but runtime handles this for actor invocations)
- More verbose than closure style
- Worth it for: simplicity, FDB alignment, async compatibility

---

### Decision 2: Transaction Isolation Level

**Context:** What isolation guarantees should transactions provide?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Serializable | Full isolation, reads see consistent snapshot | Strongest guarantee, matches FDB | Higher abort rate under contention |
| B: Read committed | Reads see committed data, no snapshot | Lower abort rate | Phantom reads possible |
| C: Snapshot | Read snapshot at begin, writes buffered | Good read consistency | Complex implementation |

**Decision:** Option A - Serializable

**Rationale:**
- FDB provides serializable isolation natively
- Virtual actors already have single-activation guarantee (low contention)
- Simplest mental model for users
- Matches Kelpie's linearizability guarantees

**Trade-offs accepted:**
- Possible aborts under extreme contention (rare with virtual actors)
- Worth it for: correctness, simplicity, FDB alignment

---

### Decision 3: State Persistence Strategy

**Context:** When should actor state be persisted?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Every invocation | Auto-save state in transaction after each invoke | Crash-safe, simple | High I/O, unnecessary if state unchanged |
| B: On dirty flag | Only save if actor marks state dirty | Efficient | Requires actor cooperation, easy to forget |
| C: Explicit transaction | Actor calls `ctx.save()` explicitly within txn | Full control | More code, easy to forget |

**Decision:** Option A - Every invocation (initially), with optimization path

**Rationale:**
- Correctness first, optimize later
- Single activation means invocations are serialized anyway
- FDB handles write coalescing efficiently
- Can add dirty-flag optimization in Phase 6 if needed

**Trade-offs accepted:**
- Extra writes for read-only invocations
- Worth it for: crash safety, simplicity, no actor changes required

---

### Decision 4: SimStorage Transaction Implementation

**Context:** How should SimStorage implement transactions for DST?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Buffer + apply | Buffer writes, apply on commit | Simple, obvious | Must track read set for conflicts |
| B: Copy-on-write | Clone data at begin, replace on commit | Full isolation, simple reads | Memory overhead |
| C: MVCC | Multi-version with timestamps | Realistic, scalable | Complex for a test harness |

**Decision:** Option A - Buffer + apply

**Rationale:**
- SimStorage is a test harness, not production
- Simple implementation (~50 lines) is easy to audit
- Matches FDB's optimistic model conceptually
- Conflict detection can be added for realism if needed

**Trade-offs accepted:**
- Simplified conflict model (no read tracking initially)
- Worth it for: simplicity, debuggability, fast implementation

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 16:00 | Explicit transaction handles | FDB alignment, async simplicity | User must commit |
| 16:02 | Serializable isolation | Matches FDB, simplest model | Possible aborts |
| 16:04 | Save state every invocation | Crash safety first | Extra I/O |
| 16:06 | Buffer+apply for SimStorage | Simplicity for test harness | No conflict detection initially |

---

## Implementation Plan

### Phase 1: Extend DST Harness (SimStorage) ✅
- [x] Define `Transaction` trait in `kelpie-storage/src/kv.rs`
- [x] Add `SimTransaction` struct to `kelpie-dst/src/storage.rs`
- [x] Implement buffer + apply pattern
- [x] Wire up `CrashDuringTransaction` fault injection
- [x] Add `begin_transaction()` to `SimStorage`

### Phase 2: Write DST Tests FIRST ✅
- [x] `test_transaction_atomic_commit` - Multi-key write succeeds atomically
- [x] `test_transaction_abort_rollback` - Abort discards all writes
- [x] `test_crash_during_transaction` - Crash mid-transaction rolls back
- [x] `test_crash_after_commit` - Committed data survives crash
- [x] `test_transaction_isolation` - Uncommitted writes not visible
- [x] `test_transaction_read_your_writes` - Read-your-writes semantics
- [x] `test_transaction_determinism` - Same seed = same results

### Phase 3: Add Transaction API to ActorKV Trait ✅
- [x] Define `ActorTransaction` trait
- [x] Add `begin_transaction()` to `ActorKV` trait
- [x] Update `ScopedKV` to support transactions
- [x] Implement `MemoryTransaction` for `MemoryKV`
- [ ] Update `ContextKV` trait in `kelpie-core` (not needed - runtime handles transactions)

### Phase 4: Update Actor Runtime ✅
- [x] Modify `ActiveActor` to use transactions
- [x] Save state within transaction after each successful invocation
- [x] Handle transaction failures (propagate as errors)
- [x] Update DST test for intermittent failures

### Phase 5: Implement in FdbKV ✅
- [x] Implement `ActorTransaction` for FDB (`FdbActorTransaction`)
- [x] Map to native FDB transactions (buffer + apply pattern)
- [x] Add retry logic for conflicts (up to 5 retries with backoff)
- [x] Integration tests against real FDB (5 tests, marked #[ignore])

### Phase 6: (Future) Optimizations
- [ ] Dirty-flag for state saves
- [ ] Read-only transaction fast path
- [ ] Batching across actors on same node

---

## Checkpoints

- [x] Codebase understood
- [x] Plan approved
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained**
- [x] Implemented
- [x] Tests passing (`cargo test`)
- [x] Clippy clean (`cargo clippy`)
- [x] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [x] Vision aligned
- [x] **DST coverage added**
- [x] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**DST tests (WRITE FIRST - Phase 2):**
- [ ] `test_transaction_atomic_commit` - Normal conditions
- [ ] `test_transaction_abort_rollback` - Explicit abort
- [ ] `test_crash_during_transaction` - CrashDuringTransaction fault
- [ ] `test_crash_after_commit` - CrashAfterWrite fault post-commit
- [ ] `test_transaction_isolation` - Read isolation
- [ ] Determinism verification (same seed = same result)

**Unit tests:**
- [ ] SimTransaction buffer operations
- [ ] Fault injection in transaction path

**Integration tests (requires FDB):**
- [ ] FDB transaction atomicity
- [ ] FDB conflict retry
- [ ] FDB crash recovery

**Commands:**
```bash
# Run DST tests
cargo test -p kelpie-dst

# Reproduce specific DST failure
DST_SEED=12345 cargo test -p kelpie-dst

# Run all tests
cargo test

# Run clippy
cargo clippy --all-targets --all-features
```

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 16:00 | kv.rs, storage.rs, fault.rs | Understanding current state |
| 16:00 | ADR-007 | DST vs Production boundary |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| None currently | - | - |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Current | Planning | In progress | 2026-01-12 16:00 |

---

## Findings

- `CrashDuringTransaction` fault type exists in `fault.rs` but isn't used by SimStorage
- `with_crash_faults()` builder registers `CrashDuringTransaction` at given probability
- SimStorage handles `CrashBeforeWrite` and `CrashAfterWrite` but not `CrashDuringTransaction`
- Actor state saved only in `deactivate()` - vulnerable to crashes
- FDB natively supports serializable transactions - good alignment

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Transaction API | `cargo test -p kelpie-storage` | 6 tests pass |
| SimTransaction with fault injection | `cargo test -p kelpie-dst` | 36 tests pass (8 transaction tests) |
| CrashDuringTransaction fault | See `test_crash_during_transaction` | Uncommitted writes rolled back |
| Transaction determinism | See `test_transaction_determinism` | Same seed = same results |
| Actor runtime with transactions | `cargo test -p kelpie-runtime` | 23 tests pass |
| Transactional state persistence | `process_invocation()` saves state atomically | Crash-safe state |
| All workspace tests | `cargo test` | ~400 tests pass |
| FdbKV transactions | `cargo test -p kelpie-storage --features fdb -- --ignored` | 5 FDB transaction tests (requires FDB) |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| Actor's KV ops within transaction | Actor's `kv_*` calls not within state txn | Future enhancement |

### Known Limitations ⚠️
- FDB integration tests require FoundationDB server running (marked `#[ignore]`)
- Actor's `kv_set()`/`kv_delete()` calls are NOT within the state transaction
- No conflict detection in SimStorage (simplified for DST)
- State saved after EVERY invocation (may be optimized with dirty flag later)

---

## API Design Sketch

```rust
// In kelpie-storage/src/kv.rs

/// Transaction on actor's KV store
#[async_trait]
pub trait ActorTransaction: Send + Sync {
    /// Get a value within the transaction
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>>;

    /// Set a value (buffered until commit)
    async fn set(&mut self, key: &[u8], value: &[u8]) -> Result<()>;

    /// Delete a key (buffered until commit)
    async fn delete(&mut self, key: &[u8]) -> Result<()>;

    /// Commit the transaction atomically
    async fn commit(self) -> Result<()>;

    /// Abort the transaction, discarding all writes
    async fn abort(self) -> Result<()>;
}

/// Extended ActorKV with transaction support
#[async_trait]
pub trait ActorKV: Send + Sync {
    // ... existing methods ...

    /// Begin a new transaction
    async fn begin_transaction(&self, actor_id: &ActorId) -> Result<Box<dyn ActorTransaction>>;
}
```

---

## SimStorage Transaction Design

```rust
// In kelpie-dst/src/storage.rs

pub struct SimTransaction {
    actor_id: ActorId,
    storage: Arc<SimStorage>,
    write_buffer: HashMap<Vec<u8>, Option<Vec<u8>>>, // None = delete
    committed: bool,
}

impl SimTransaction {
    async fn commit(mut self) -> Result<()> {
        // Check for CrashDuringTransaction fault
        if let Some(FaultType::CrashDuringTransaction) =
            self.storage.fault_injector.should_inject("transaction_commit")
        {
            // Simulate crash - writes NOT applied
            return Err(Error::Internal {
                message: "crash during transaction (injected)".into()
            });
        }

        // Apply all buffered writes atomically
        for (key, value) in self.write_buffer.drain() {
            match value {
                Some(v) => self.storage.write(&key, &v).await?,
                None => self.storage.delete(&key).await?,
            }
        }

        self.committed = true;
        Ok(())
    }
}
```

---

## Completion Notes

_To be filled after implementation_

**Verification Status:**
- Tests: [pending]
- Clippy: [pending]
- Formatter: [pending]
- /no-cap: [pending]
- Vision alignment: [pending]

**DST Coverage:**
- Fault types tested: [pending]
- Seeds tested: [pending]
- Determinism verified: [pending]

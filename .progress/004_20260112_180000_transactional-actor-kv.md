# Task: Transactional Actor KV Operations

**Created:** 2026-01-12 18:00:00
**State:** COMPLETE

---

## Vision Alignment

**Vision files read:**
- `.vision/CONSTRAINTS.md` - Simulation-first development requirements
- `CLAUDE.md` - TigerStyle principles, DST workflow
- `docs/adr/008-transaction-api.md` - Existing transaction API

**Relevant constraints/guidance:**
- Simulation-first development - Write DST tests BEFORE implementation
- TigerStyle safety principles - 2+ assertions per function
- DST tests APPLICATION code, not infrastructure

---

## Task Description

**Problem:** Actor's `kv_set()`/`kv_delete()` calls are NOT atomic with state persistence.

Currently:
```rust
// Inside actor's invoke():
ctx.kv_set(b"balance", &new_balance).await?;  // IMMEDIATE write
ctx.state.last_txn = txn_id;                   // In-memory change

// After invoke() returns, in process_invocation():
save_state_transactional().await?;             // SEPARATE transaction
```

**Failure scenario:**
1. Actor calls `ctx.kv_set(b"balance", b"100")`
2. Actor updates `ctx.state.last_txn = "txn-1"`
3. `save_state_transactional()` fails (crash, network issue)
4. Result: KV has `balance=100` but state doesn't have `last_txn="txn-1"`
5. **Data is inconsistent!**

**Goal:** All KV operations within an invocation should be atomic with state persistence.

---

## DST-First Development Order

```
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 1: Write Failing DST Test FIRST                                  │
│  - Test demonstrating atomicity gap                                     │
│  - Crash after KV write but before state commit                         │
│  - Verify inconsistency occurs (test should FAIL initially)             │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 2: Design API Solution                                           │
│  - Option A: Pass transaction to actor context                          │
│  - Option B: Buffer all KV ops, apply on commit                         │
│  - Option C: Transactional context wrapper                              │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 3: Implement in SimStorage/Runtime                               │
│  - Extend ActorContext with transaction                                 │
│  - Buffer KV ops within invocation                                      │
│  - Commit all (state + KV) atomically                                   │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 4: DST Test Should Now Pass                                      │
│  - Same test from Phase 1                                               │
│  - Crash after KV write → both KV and state rolled back                 │
│  - Data remains consistent                                              │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Options & Decisions [REQUIRED]

### Decision 1: How to make KV ops transactional

**Context:** How should actor's KV operations be included in the state transaction?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Pass transaction to context | `ActorContext` holds active transaction | Simple, explicit | Requires context API changes |
| B: Buffer in context | Buffer all KV ops, apply on commit | No API change for actors | Higher memory usage |
| C: Transactional wrapper | Wrap ContextKV with transaction-aware impl | Clean separation | More abstraction layers |

**Decision:** [To be decided after Phase 1]

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 18:00 | Write failing test first | True DST-first | Test will fail initially |
| 19:30 | Use filter on fault injection | CrashDuringTransaction without filter blocks ALL storage writes | More explicit test setup |
| 19:35 | Don't call deactivate() after crash | deactivate() does direct write that "heals" inconsistency | Simulates real crash better |

---

## Implementation Plan

### Phase 1: Write Failing DST Test FIRST ✅ COMPLETE
- [x] Create test actor that writes KV + updates state (`BankAccountActor`)
- [x] Inject crash between KV write and state commit (CrashDuringTransaction)
- [x] Verify inconsistency (KV changed but state didn't)
- [x] Test FAILS with current implementation (as expected for DST-first)

### Phase 2: Design API Solution ✅ COMPLETE
- [x] Chose Option B: Buffer all KV ops, apply on commit
- [x] Created `BufferingContextKV` wrapper in kelpie-core
- [x] Created `ArcContextKV` wrapper for Arc sharing

### Phase 3: Implement Solution ✅ COMPLETE
- [x] Added `BufferingContextKV` to buffer KV operations
- [x] Added `swap_kv()` method to ActorContext
- [x] Updated `process_invocation()` to use buffering
- [x] Created `save_all_transactional()` for atomic state+KV commit

### Phase 4: Verify DST Test Passes ✅ COMPLETE
- [x] Phase 1 test now PASSES (was failing before)
- [x] All other DST tests still pass (no regressions)
- [x] Storm tested with 50+ random seeds - all pass

---

## Checkpoints

- [x] Codebase understood
- [x] **Failing DST test written (Phase 1)**
- [x] Options & Decisions filled in
- [x] Quick Decision Log maintained
- [x] Implemented
- [x] Tests passing (`cargo test`)
- [x] Clippy clean (`cargo clippy`) - 1 dead_code warning (acceptable)
- [x] Code formatted (`cargo fmt`)
- [x] Vision aligned
- [x] DST coverage added
- [x] What to Try section updated
- [ ] Committed

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| State saved transactionally | See ADR-008 tests | State survives crashes |
| **KV + State atomic** | `cargo test -p kelpie-dst test_dst_kv_state_atomicity_gap` | Test PASSES (both rolled back on crash) |
| Storm testing | Run 50+ iterations with random seeds | All pass |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| (None - all features working) | | |

### Known Limitations ⚠️
- `deactivate()` still uses direct write, not transaction (separate issue, not invocation path)
- `save_state_transactional()` is now dead code (superseded by `save_all_transactional()`)

---

## Findings

### Phase 1 Findings

1. **FaultConfig requires explicit filter for transaction-only faults**
   - `CrashDuringTransaction` without filter matches ALL storage operations
   - Must use `.with_filter("transaction_commit")` to only crash during commits
   - Without filter, `handle_write_fault()` returns early without writing data

2. **Two paths for state persistence**
   - `save_state_transactional()` - used in `process_invocation()`, uses transactions
   - `save_state()` - used in `deactivate()`, direct write (no transaction)
   - This means `deactivate()` can "heal" inconsistency after failed invocation

3. **Test must simulate real crash**
   - Drop actor without calling `deactivate()` to prevent healing
   - In production crash, process dies without cleanup

4. **Atomicity gap confirmed**
   - `ctx.kv_set()` writes immediately via `ScopedKV` → `SimStorage::set()` → direct write
   - `ctx.state` changes are only persisted via transaction in `save_state_transactional()`
   - Crash during commit leaves KV persisted but state not

---

## Completion Notes

### Summary

Successfully implemented transactional actor KV operations following DST-first methodology:

1. **Wrote failing test first** - `test_dst_kv_state_atomicity_gap` demonstrated the atomicity gap
2. **Designed buffering solution** - `BufferingContextKV` captures KV ops during invoke()
3. **Implemented fix** - `process_invocation()` now buffers KV ops and commits them with state
4. **Verified with DST** - Test passes, storm tested with 50+ random seeds

### Files Changed

- `kelpie-core/src/actor.rs` - Added `BufferingContextKV`, `ArcContextKV`, `BufferedKVOp`, `swap_kv()`
- `kelpie-core/src/lib.rs` - Exported new types
- `kelpie-storage/src/kv.rs` - Added `underlying_kv()` getter to `ScopedKV`
- `kelpie-runtime/src/activation.rs` - Updated `process_invocation()`, added `save_all_transactional()`
- `kelpie-dst/tests/actor_lifecycle_dst.rs` - Added `BankAccountActor` and atomicity test

### Key Design Decision

Chose **Option B: Buffer in context** because:
- No API change for actors (ctx.kv_set still works same way)
- Clean separation between buffering and transaction commit
- Simpler than passing transaction through context
- Read-your-writes supported via local cache

---

## Phase 5: Exploratory DST Bug Hunting

### Initial Findings

After initial fix, ran exploratory DST with 100 iterations. Found **52 bugs**:
- `KV balance X != state expected_balance Y`
- Pattern: Some had KV but no state, others had state but no KV

### Root Cause Analysis

**Bug 1: State not rolled back on transaction failure**
- When transaction fails, `process_invocation()` returned Err but left `ctx.state` modified
- On deactivation, `save_state()` persisted this corrupted in-memory state
- Fix: Added state snapshot before invoke, restore on any failure path

**Bug 2: SimStorage handle_read_fault returning Ok(None) for unhandled faults**
- `StorageLatency` fault was being passed to `handle_read_fault()`
- The catch-all `_ => Ok(None)` returned "key not found" instead of actual error
- This caused invariant check to see "empty" state when data existed
- Fix: Changed `read()` to handle `StorageLatency` inline (add delay then read)
- Fix: Changed `handle_read_fault()` to return errors for unexpected faults

### Additional Changes

- `kelpie-runtime/src/activation.rs`:
  - Added state snapshot before invoke
  - Restore state on transaction failure, actor error, or timeout
  - Added `Clone` bound to `S` type parameter throughout runtime

- `kelpie-runtime/src/dispatcher.rs`:
  - Added `Clone` bound to `S` type parameter

- `kelpie-runtime/src/runtime.rs`:
  - Added `Clone` bound to `S` type parameter on all impls and struct

- `kelpie-dst/src/storage.rs`:
  - Fixed `read()` to handle `StorageLatency` inline (not in handle_read_fault)
  - Fixed `handle_read_fault()` to not silently return Ok(None) for unknown faults

- `kelpie-dst/tests/actor_lifecycle_dst.rs`:
  - Added `LedgerActor` for exploratory testing
  - Added `test_dst_exploratory_bug_hunting` with 100 iterations
  - Added detailed debug output controllable via DST_DEBUG env var

### Final Result

After fixes: **100/100 iterations pass with 0 bugs found**

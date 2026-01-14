# Task: AppState Actor Integration (Plan 007 Phase 5)

**Created:** 2026-01-14 21:15:00
**State:** PLANNING
**Parent Plan:** 007_20260113_actor_based_agent_server.md (Phase 5)

---

## Aggressive DST-First Approach (CRITICAL)

**Lesson from BUG-001:** Standard 30% fault rates miss real bugs. We MUST use:
- **50%+ fault rates** for critical paths
- **CrashDuringTransaction** not just StorageWriteFail
- **Targeted timing tests** for multi-step operations
- **Create → immediate read patterns** to catch data loss

**This plan will follow the PROVEN approach that found BUG-001.**

---

## Vision Alignment

**Constraints Applied:**
- Aggressive DST-first (50%+ fault rates)
- No placeholders - real implementation only
- TigerStyle assertions and explicit errors
- Test timing windows explicitly

**Prior Work:**
- Phase 3: AgentActor implemented (10/10 tests passing)
- Phase 4: AgentService implemented (6/6 tests passing + BUG-001 found/fixed)
- BUG-001 found via 50% CrashDuringTransaction aggressive testing

---

## Task Description

**Current State:**
AppState uses HashMap for agent storage. HTTP handlers call AppState methods directly.

```rust
// Current (Phase 4 complete)
struct AppStateInner {
    agents: RwLock<HashMap<String, AgentState>>,  // ← HashMap
    messages: RwLock<HashMap<String, Vec<Message>>>,
    // ... other HashMaps
}

// HTTP handlers
async fn create_agent_handler(State(app): State<AppState>, ...) {
    let agent = app.create_agent(agent_state)?;  // ← Direct HashMap operation
}
```

**Target State (Phase 5):**
AppState wraps AgentService + DispatcherHandle. HTTP handlers use service.

```rust
// Target
struct AppStateInner {
    agent_service: AgentService,  // ← Service layer (Phase 4)
    dispatcher: DispatcherHandle,  // ← Actor runtime
    // Legacy fields kept for backward compat during migration
}

// HTTP handlers (Phase 6)
async fn create_agent_handler(State(app): State<AppState>, ...) {
    let agent = app.agent_service().create_agent(request).await?;
}
```

---

## Options & Decisions

### Decision 1: Migration Strategy

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Big Bang | Replace all HashMap operations in one PR | Fastest, clean cut | High risk, long PR review |
| B: Dual Write | Write to both HashMap and actors, read from HashMap | Gradual, low risk | Complexity, temporary duplication |
| C: Service Wrapper | Add AgentService to AppState, keep HashMap temporarily | Incremental, testable | Longer timeline |

**Decision:** **Option C - Service Wrapper**

**Reasoning:**
- Proven safe with DST tests
- Can test service integration independently
- HTTP handlers migrated one-by-one (Phase 6)
- Can remove HashMap after full migration
- BUG-001 experience shows incremental + aggressive testing works

### Decision 2: Shutdown Semantics

**Question:** How to handle in-flight requests during shutdown?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Immediate | Shutdown dispatcher immediately, fail in-flight requests | Fast shutdown | User-visible errors |
| B: Graceful Drain | Wait for in-flight requests (timeout 30s) | Clean shutdown | Slower |
| C: No Explicit Shutdown | Let Rust Drop handle cleanup | Simple | No guarantees |

**Decision:** **Option B - Graceful Drain (30s timeout)**

**Reasoning:**
- User-facing service should complete requests
- 30s timeout prevents hang
- Can test with aggressive fault injection
- Aligns with TigerStyle (explicit lifecycle)

---

## Implementation Phases

### Phase 5.1: Aggressive DST Tests FIRST (MANDATORY)

Write tests with **50%+ fault rates** targeting specific bugs:

#### Test 1: AppState Initialization Race
**Target Bug:** Dispatcher fails during AppState::new()
**Fault:** 50% CrashDuringTransaction during dispatcher creation
**Assertion:** Either AppState creation succeeds fully OR fails cleanly (no partial state)

#### Test 2: Concurrent Agent Creation
**Target Bug:** Race condition - two requests create same agent simultaneously
**Fault:** 40% CrashAfterWrite during actor activation
**Assertion:** Exactly one agent created, second request fails with AlreadyExists

#### Test 3: Shutdown with In-Flight Requests
**Target Bug:** Shutdown drops in-flight requests silently
**Fault:** 50% NetworkDelay + immediate shutdown
**Assertion:** In-flight requests either complete OR fail with clear error

#### Test 4: Service Invoke During Shutdown
**Target Bug:** Service call after shutdown starts
**Fault:** 40% CrashDuringTransaction
**Assertion:** Returns ShuttingDown error, doesn't panic

#### Test 5: First Invoke After Creation
**Target Bug:** Similar to BUG-001 - state exists but not readable
**Fault:** 50% CrashDuringTransaction
**Assertion:** create → immediate get works OR both fail

**File:** `crates/kelpie-server/tests/appstate_integration_dst.rs` (NEW)

**Verification:**
```bash
$ cargo test -p kelpie-server --test appstate_integration_dst
test test_appstate_init_crash ... FAILED (expected)
test test_concurrent_agent_creation_race ... FAILED
test test_shutdown_with_inflight_requests ... FAILED
test test_service_invoke_during_shutdown ... FAILED
test test_first_invoke_after_creation ... FAILED
```

**DO NOT PROCEED until these 5 tests are written and FAILING.**

### Phase 5.2: Implement AppState with AgentService

**Files:**
- `crates/kelpie-server/src/state.rs`

**Changes:**
```rust
struct AppStateInner {
    // NEW: Actor-based
    agent_service: AgentService,
    dispatcher: DispatcherHandle,

    // KEEP temporarily for backward compat
    agents: RwLock<HashMap<String, AgentState>>,
    messages: RwLock<HashMap<String, Vec<Message>>>,
    // ... other fields

    // NEW: Shutdown coordination
    shutdown_tx: Option<tokio::sync::broadcast::Sender<()>>,
}

impl AppState {
    pub fn new() -> Self {
        // Create LLM client
        let llm = Arc::new(LlmClient::from_env());

        // Create AgentActor
        let actor = AgentActor::new(llm);

        // Create dispatcher
        let factory = Arc::new(CloneFactory::new(actor));
        let kv = Arc::new(SimStorage::new()); // or FDB in production
        let mut dispatcher = Dispatcher::new(factory, kv, DispatcherConfig::default());
        let handle = dispatcher.handle();

        // Spawn dispatcher
        tokio::spawn(async move { dispatcher.run().await });

        // Create service
        let agent_service = AgentService::new(handle.clone());

        Self {
            inner: Arc::new(AppStateInner {
                agent_service,
                dispatcher: handle,
                agents: RwLock::new(HashMap::new()),
                // ... rest
                shutdown_tx: None,
            }),
        }
    }

    pub fn agent_service(&self) -> &AgentService {
        &self.inner.agent_service
    }

    pub async fn shutdown(&self, timeout: Duration) -> Result<()> {
        // Signal shutdown
        if let Some(tx) = &self.inner.shutdown_tx {
            let _ = tx.send(());
        }

        // Wait for in-flight requests (up to timeout)
        tokio::time::sleep(timeout).await;

        // Shutdown dispatcher
        self.inner.dispatcher.shutdown().await
    }
}
```

**Iteration Loop:**
1. Run test_appstate_init_crash → Fix until PASSES
2. Run test_concurrent_agent_creation_race → Fix until PASSES
3. Run test_shutdown_with_inflight_requests → Fix until PASSES
4. Run test_service_invoke_during_shutdown → Fix until PASSES
5. Run test_first_invoke_after_creation → Fix until PASSES

**DO NOT PROCEED until all 5 tests PASS.**

### Phase 5.3: Integration Tests (Existing Tests Must Still Pass)

Run existing AppState tests to ensure backward compat:
```bash
$ cargo test -p kelpie-server state::tests
```

All existing tests must pass. If any fail, the HashMap → Actor migration has a bug.

### Phase 5.4: Aggressive Fault Injection on Full Stack

Run ALL previous tests with AppState integration:
```bash
$ cargo test -p kelpie-server --test agent_actor_dst
$ cargo test -p kelpie-server --test agent_service_dst
$ cargo test -p kelpie-server --test agent_deactivation_timing
$ cargo test -p kelpie-server --test agent_service_fault_injection
```

All 26 tests must still pass. If any fail, AppState broke something.

---

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Shutdown doesn't wait for in-flight | Medium | High (data loss) | Test with aggressive delays + immediate shutdown |
| Dispatcher fails during init | Low | High (server won't start) | Test with 50% crash rate during creation |
| Memory leak (HashMap not cleaned) | Medium | Medium (slow leak) | Add memory tracking test |
| Race in concurrent creates | Low | Medium (duplicate agents) | Test with high concurrency + faults |

---

## Success Criteria

**Phase 5 is complete when:**
1. ✅ 5 aggressive DST tests written (50%+ fault rates)
2. ✅ All 5 tests PASS
3. ✅ All existing AppState unit tests PASS
4. ✅ All 26 previous DST tests STILL PASS
5. ✅ No clippy warnings
6. ✅ Code formatted
7. ✅ Shutdown gracefully handles in-flight requests

**Verification:**
```bash
$ cargo test -p kelpie-server --test appstate_integration_dst
# 5/5 tests passing

$ cargo test -p kelpie-server state::tests
# All existing tests passing

$ cargo test -p kelpie-server --test agent_actor_dst --test agent_service_dst \
  --test agent_deactivation_timing --test agent_service_fault_injection
# 26/26 tests still passing
```

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-14 21:15 | Use 50%+ fault rates | BUG-001 found with 50%, not 30% | Slower tests |
| 2026-01-14 21:15 | Service wrapper (Option C) | Incremental, proven with Phase 4 | Longer timeline |
| 2026-01-14 21:15 | Graceful shutdown (30s) | User-facing service | Slower shutdown |

---

## What to Try (UPDATED AFTER EACH PHASE)

**Phase 5.1 (Tests Written):**
- Works Now: N/A (tests not implemented yet)
- Doesn't Work Yet: Everything (tests MUST fail)
- Known Limitations: Tests define contract only

**Phase 5.2 (After Implementation):**
- Works Now: [Will update after implementation]
- Doesn't Work Yet: [Will update after implementation]
- Known Limitations: [Will update after implementation]

---

## Notes

**Remember BUG-001 Lesson:**
- 30% fault rate missed the bug
- 50% CrashDuringTransaction found it
- Targeted timing tests (create → immediate read) essential
- General fault injection not enough - need specific scenarios

**This plan applies those lessons to Phase 5.**

---

## References

- Parent Plan: `.progress/007_20260113_actor_based_agent_server.md`
- BUG-001: `docs/bugs/001-create-agent-data-loss.md`
- Fault Injection Findings: `docs/fault-injection-findings.md`
- Phase 3 Tests: `crates/kelpie-server/tests/agent_actor_dst.rs`
- Phase 4 Tests: `crates/kelpie-server/tests/agent_service_dst.rs`

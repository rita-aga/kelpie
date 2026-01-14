# Handoff Prompt: Actor-Based Agent Server Implementation

**Plan:** `.progress/007_20260113_actor_based_agent_server.md`
**Prerequisite:** Plan 006 is ~97% complete (204+ DST tests passing)

---

## Context

You are implementing an actor-based architecture for the Kelpie agent server. This builds on top of existing Letta-compatible agent functionality (plan 006) to add:

1. **Virtual actors** - Single activation guarantee, location transparency
2. **FDB persistence** - Agent state survives restarts (currently in-memory only)
3. **Session handoff** - Crash recovery and session transfer between agents
4. **DST coverage** - All features tested under fault injection

**Read these files FIRST:**
```
.vision/CONSTRAINTS.md          # DST-first workflow (MANDATORY)
.progress/007_20260113_actor_based_agent_server.md  # The plan
.progress/006_20260112_agent_framework_letta_parity.md  # What's already done
```

---

## Architecture Summary

```
┌─────────────────────────────────────────────────────────────┐
│                    FDB (Hot Path - CRUD)                     │
│  • Agent metadata    • Core blocks    • Messages            │
│  • Session checkpoints (crash recovery, handoff)            │
└─────────────────────────────────────────────────────────────┘
              │
              │ Async sync on write
              ↓
┌─────────────────────────────────────────────────────────────┐
│                    UMI (Search Layer)                        │
│  • archival_memory_search    • conversation_search          │
│  • Working memory promotion based on usage                  │
└─────────────────────────────────────────────────────────────┘
              │
              │ Actor wraps both
              ↓
┌─────────────────────────────────────────────────────────────┐
│                    AgentActor                                │
│  • Single activation guarantee                              │
│  • Checkpoint every iteration to FDB                        │
│  • Session handoff (crash recovery, transfer)               │
└─────────────────────────────────────────────────────────────┘
```

---

## Key Decisions (from plan)

| # | Decision | Summary |
|---|----------|---------|
| 1 | Single AgentActor type | Agent types differ in config, not behavior |
| 2 | FDB hot + UMI search | FDB for CRUD/ACID, UMI for semantic search |
| 3 | Service layer abstraction | REST → AgentService → Dispatcher → AgentActor |
| 4 | Big bang replacement | Clean slate, DST coverage, pre-production |
| 5 | Use ActorKV via FDB | Proven design, 1000+ LOC exists |
| 6 | Checkpoint every iteration | Crash recovery, session handoff |

---

## DST-First Workflow (MANDATORY)

**Per CONSTRAINTS.md, you MUST follow this order:**

```
1. HARNESS CHECK → Extend kelpie-dst if needed
2. WRITE TEST → Tests will FAIL (no implementation yet)
3. IMPLEMENT → Make tests pass
4. RUN SIMULATION → Multiple seeds, find bugs
5. FIX & ITERATE → Until tests pass
6. VERIFY DETERMINISM → Same seed = same result
```

**Phase 1 is critical:** You must extend the DST harness BEFORE writing any actor code:
- Add `SimLlmClient` (deterministic LLM responses)
- Add fault types: `LlmTimeout`, `LlmFailure`, `LlmRateLimited`
- Add `SimAgentEnv` (high-level test harness)

---

## What Already Exists

**kelpie-runtime (actor runtime):**
- Dispatcher with command channel ✅
- ActorFactory trait ✅
- Single activation guarantee ✅
- ActorKV integration ✅
- 23 passing tests ✅

**kelpie-server (agent server):**
- REST API handlers ✅ (will need minor changes)
- Data models ✅ (no changes needed)
- Tool registry ✅ (no changes needed)
- Memory tools ✅ (will need wiring to UMI)
- Heartbeat/pause ✅ (no changes needed)
- FdbStorage ✅ (1000+ LOC, NOT WIRED to server)
- UmiMemoryBackend ✅ (613 LOC, NOT WIRED to server)
- 204+ DST tests ✅

**What's NOT wired:**
- FDB storage backend (exists but not connected to server startup)
- UMI for search (exists but using SimStorageBackend)
- Session checkpointing (SessionState exists, agent loop doesn't use it)

---

## Implementation Order

1. **Phase 1: DST Harness Extension** (MUST DO FIRST)
   - Add SimLlmClient
   - Add LLM fault types
   - Add SimAgentEnv
   - Verify harness works before continuing

2. **Phase 2: Write DST Tests** (before implementation)
   - ~25 tests across 4 files
   - All tests will FAIL (expected)

3. **Phase 3: Implement AgentActor**
   - Run tests iteratively until passing

4. **Phase 4-7: Service layer, API refactor, streaming**

5. **Phase 8: FDB + UMI wiring**
   - Finally wire FDB to server startup
   - Wire UMI for search

6. **Phase 9-11: Stress testing, cleanup, docs**

---

## Session Handoff Requirements

**What gets checkpointed (every iteration):**
```rust
struct SessionCheckpoint {
    session_id: String,
    agent_id: String,
    iteration: u32,
    is_paused: bool,
    pause_until_ms: Option<u64>,
    pending_tool_calls: Vec<PendingToolCall>,
    last_tool_result: Option<String>,
    stop_reason: Option<StopReason>,
}
```

**Crash recovery flow:**
```
Agent crashes at iteration 3
  → FDB has checkpoint: iteration=2 (last completed)
  → New actor loads checkpoint
  → Resume at iteration 3 (re-execute)
```

**Session transfer flow:**
```
POST /v1/agents/{source}/sessions/{id}/transfer
  → Source agent checkpoints and deactivates
  → Target agent loads checkpoint + messages + blocks
  → Resume from last iteration
```

---

## Verification Commands

```bash
# Phase 1: Verify harness extensions
cargo test -p kelpie-dst test_sim_llm_client
cargo test -p kelpie-dst test_new_fault_types

# Phase 2: Confirm tests fail (expected)
cargo test -p kelpie-server test_dst_agent -- --nocapture

# Phase 3+: Iteration loop
cargo test -p kelpie-server test_dst_agent_actor_activation_basic
# Fix, re-run, repeat

# Final verification
cargo test --workspace
cargo clippy --all-targets --all-features
cargo fmt --check

# Determinism verification
DST_SEED=12345 cargo test -p kelpie-server test_dst_determinism
DST_SEED=12345 cargo test -p kelpie-server test_dst_determinism  # Must match!
```

---

## Files to Create

```
crates/kelpie-dst/src/llm.rs           # SimLlmClient
crates/kelpie-dst/src/agent.rs         # SimAgentEnv
crates/kelpie-server/src/actor/mod.rs  # AgentActor
crates/kelpie-server/src/service/mod.rs # AgentService
crates/kelpie-server/tests/agent_actor_dst.rs
crates/kelpie-server/tests/agent_service_dst.rs
crates/kelpie-server/tests/agent_streaming_dst.rs
crates/kelpie-server/tests/agent_stress_dst.rs
```

## Files to Modify

```
crates/kelpie-dst/src/fault.rs         # Add LLM fault types
crates/kelpie-server/src/state.rs      # Replace HashMap with Dispatcher
crates/kelpie-server/src/lib.rs        # Add actor, service modules
crates/kelpie-server/src/api/*.rs      # Update handlers to use service
crates/kelpie-server/src/main.rs       # Initialize dispatcher
```

## Files to Delete (Phase 10)

```
crates/kelpie-server/src/storage/      # Replaced by ActorKV
```

---

## Success Criteria

- [ ] All 204+ existing DST tests still pass
- [ ] ~30 new actor-related DST tests pass
- [ ] Agents persist across server restarts (FDB)
- [ ] Session handoff works (crash recovery + transfer)
- [ ] Determinism verified (same seed = same result)
- [ ] `/no-cap` passes (no placeholders)
- [ ] `cargo clippy` clean
- [ ] Letta API compatibility maintained

---

## Questions to Ask Before Starting

1. Is FDB running locally? (needed for integration tests)
2. Is UMI available as a dependency? (check Cargo.toml)
3. Should streaming work during Phase 7, or is non-streaming OK initially?

---

## Start Here

1. Read the full plan: `.progress/007_20260113_actor_based_agent_server.md`
2. Read CONSTRAINTS.md for DST-first workflow
3. Start Phase 1: Extend DST harness
4. Do NOT write any AgentActor code until harness is verified

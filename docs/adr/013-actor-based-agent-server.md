# ADR 013: Actor-Based Agent Server Architecture

**Status:** In Progress
**Date:** 2026-01-13
**Deciders:** Claude (AI Assistant)
**Related:** ADR-001 (Virtual Actor Model), ADR-005 (DST Framework), ADR-011 (Agent Types)

## Context

The current agent server (`kelpie-server`) directly manages agent state via in-memory HashMap. It does NOT use the virtual actor runtime (`kelpie-runtime`) that has been fully implemented. This creates several issues:

1. **Not aligned with vision** - Virtual actors were always the intended design (see VISION.md, ADR-001)
2. **Limited scaling** - HashMap approach limited to single server
3. **No fault tolerance** - Actor runtime handles failures automatically
4. **Race conditions** - No single activation guarantee
5. **Code duplication** - 1000+ LOC of actor runtime unused

## Decision

Transform the agent server to use the virtual actor runtime, with each agent as a virtual actor.

### Key Architectural Decisions

#### 1. Agent-to-Actor Mapping: Single AgentActor Type

**Options Considered:**
- A: Single `AgentActor` type, agent_type in state
- B: Actor per agent type (`MemgptActor`, `ReactActor`, etc.)
- C: Trait-based behavior with pluggable traits

**Chosen:** Option A - Single AgentActor Type

**Rationale:**
- Agent types differ in configuration (tools, max_iterations), not fundamental behavior
- The agent loop is identical across types - only tool filtering varies
- We already have `AgentCapabilities` for type-specific logic (ADR-011)
- Simpler to reason about and test with DST

#### 2. State Schema: FDB Hot Path + UMI Search

**Options Considered:**
- A: Everything in ActorKV
- B: UMI as primary storage
- C: FDB for CRUD, UMI for semantic search

**Chosen:** Option C - FDB Hot + UMI Search

**Rationale:**
- FDB designed for ACID transactions and hot path operations
- UMI is a search layer (needs backend like LanceDB/PostgreSQL)
- Session handoff requires reliable persistence (FDB)
- Clear separation of concerns

**Storage Responsibilities:**

```
┌─────────────────────────────────────────────────────────────┐
│                 FDB (Hot Path - CRUD)                        │
│  • Agent metadata    • Core blocks    • Messages            │
│  • Session checkpoints (crash recovery, handoff)            │
└─────────────────────────────────────────────────────────────┘
              │ Async sync on write
              ↓
┌─────────────────────────────────────────────────────────────┐
│                 UMI (Search Layer)                           │
│  • Archival memory search    • Conversation search          │
│  • Working memory promotion based on usage                  │
└─────────────────────────────────────────────────────────────┘
```

#### 3. REST API Integration: Service Layer Abstraction

**Options Considered:**
- A: API handlers call `dispatcher.invoke()` directly
- B: Service layer wraps dispatcher
- C: Actor-native REST API (1:1 mapping)

**Chosen:** Option B - Service Layer Abstraction

**Rationale:**
- Clean separation: REST API → AgentService → Dispatcher → AgentActor
- Service layer handles cross-cutting concerns (auth, rate limiting)
- Testable: Mock service for API tests, mock dispatcher for service tests
- Future-proof: Can swap dispatcher without changing API

#### 4. Migration Strategy: Big Bang Replacement

**Options Considered:**
- A: Big bang replacement
- B: Feature flag dual mode
- C: Phased replacement (endpoint by endpoint)

**Chosen:** Option A - Big Bang Replacement

**Rationale:**
- Early enough that breaking changes acceptable
- DST coverage will catch issues before production
- No production users yet (in-memory data lost on restart anyway)
- Cleaner codebase without hybrid complexity
- Faster timeline (2-3 weeks vs months)

#### 5. Session Handoff: Checkpoint Every Iteration

**Options Considered:**
- A: No handoff (session dies with agent)
- B: Checkpoint on deactivate only
- C: Checkpoint every iteration
- D: Checkpoint + WAL

**Chosen:** Option C - Checkpoint Every Iteration

**Rationale:**
- Agent loop iterations are natural checkpoint boundaries
- FDB writes are fast (single transaction)
- Crash recovery can resume from last completed iteration
- Session handoff gets consistent state
- Simpler than WAL, good enough for agent workloads

**Checkpoint Structure:**
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
    started_at: DateTime<Utc>,
    checkpointed_at: DateTime<Utc>,
}
```

## Consequences

### Positive

1. **Alignment with vision** - Finally using the actor runtime as intended
2. **Distributed scaling** - Can scale across cluster nodes
3. **Fault tolerance** - Actor runtime handles failures automatically
4. **Single activation guarantee** - No race conditions
5. **Session handoff** - Crash recovery and transfer between agents
6. **Code reuse** - Leverage 1000+ LOC of complete actor runtime

### Negative

1. **All-or-nothing transition** - Need comprehensive testing before merge
2. **Two storage systems** - FDB + UMI (but proper separation of concerns)
3. **Sync lag** - Between FDB write and UMI indexing (acceptable for search)
4. **Re-execute on resume** - Last iteration re-executed on crash recovery (requires idempotency)

### Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Breaking changes affect users | Pre-production, no users yet |
| Integration bugs | DST coverage with fault injection (Phase 1 complete) |
| Performance regression | FDB is fast, actor overhead is minimal |
| Session state loss | Checkpoint every iteration to FDB |
| UMI sync failures | Fire-and-forget, doesn't block hot path |

## Implementation Plan

**DST-First Workflow (per CONSTRAINTS.md):**

1. **Phase 1:** Extend DST Harness ✅ COMPLETE
   - Added SimLlmClient for deterministic LLM testing
   - Added SimAgentEnv for agent-level testing
   - Added LLM fault types (LlmTimeout, LlmFailure, LlmRateLimited)
   - **Bugs found:** 2 critical bugs caught by integration tests

2. **Phase 2:** Write DST Tests FIRST (tests will fail) - IN PROGRESS
   - ~25 tests for AgentActor lifecycle and message handling
   - Tests define the contract before implementation

3. **Phase 3:** Implement AgentActor (iterate until tests pass)
4. **Phase 4:** Implement AgentService (iterate until tests pass)
5. **Phase 5-7:** Wire dispatcher, refactor API, add streaming
6. **Phase 8:** FDB + UMI storage integration
7. **Phase 9:** Stress testing + determinism verification
8. **Phase 10:** Remove deprecated code
9. **Phase 11:** Integration tests + documentation

## References

- [VISION.md](../../VISION.md) - Virtual actor model, distributed runtime
- [ADR-001](001-virtual-actor-model.md) - Virtual actor design decisions
- [ADR-005](005-dst-framework.md) - Deterministic simulation testing
- [ADR-011](011-agent-types-abstraction.md) - Agent types and capabilities
- [Plan 007](.progress/007_20260113_actor_based_agent_server.md) - Detailed implementation plan

## Status Log

- **2026-01-13:** ADR created, Phase 1 complete with DST harness extensions
- **2026-01-13:** Phase 1.4 found 2 critical bugs via integration testing
- **2026-01-13:** Phase 2.1 complete - 11 DST tests written defining AgentActor contract
  - Tests use full Simulation harness with fault injection
  - Tests marked `#[ignore]` - will fail until Phase 3 implements AgentActor
  - Blocked by external umi-memory compilation error (not related to test contract)

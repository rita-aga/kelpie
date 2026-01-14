# Task: Actor-Based Agent Server Architecture

**Created:** 2026-01-13 21:00:00
**State:** GROUNDING

---

## Vision Alignment

**Vision files read:**
- `VISION.md` - Virtual actor model, distributed runtime
- `.vision/CONSTRAINTS.md` - Simulation-first development, TigerStyle
- `CLAUDE.md` - Vision-aligned planning, DST-first workflow
- `docs/adr/001-virtual-actor-model.md` - Actor design decisions

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - MANDATORY DST coverage
- TigerStyle safety principles (CONSTRAINTS.md §3) - Assertions, explicit errors
- No placeholders in production (CONSTRAINTS.md §4)
- Virtual actor properties: single activation, location transparency, automatic lifecycle
- Actor runtime complete (23 tests passing, `kelpie-runtime`)
- FDB backend complete (1000 LOC, `kelpie-storage/src/fdb.rs`)

---

## Dependencies

**Prerequisite:** Plan 006 (~97% complete, 204+ DST tests passing)
- Agent loop ✅
- Tool execution ✅
- Memory tools ✅
- Heartbeat/pause ✅
- Agent types ✅
- AgentStorage trait ✅

**This plan builds on 006** to add actor-based architecture, FDB persistence, and session handoff.

---

## Task Description

**Current State:**
The agent server (`kelpie-server`) directly manages agent state via in-memory HashMap. It does NOT use the virtual actor runtime that has been fully implemented.

```rust
// Current architecture (simplified, no actors)
AppState {
    agents: Arc<RwLock<HashMap<String, Agent>>>,  // Direct HashMap
    blocks: Arc<RwLock<HashMap<String, Block>>>,
    messages: Arc<RwLock<HashMap<String, Vec<Message>>>>,
}
```

**Target State:**
Each agent should be a virtual actor with:
- Single activation guarantee (one instance per agent_id at a time)
- Automatic lifecycle (activate on-demand, deactivate when idle)
- Location transparency (call via dispatcher, no knowledge of location)
- Distributed placement (can scale across cluster nodes)
- State persistence via `ActorKV` → FoundationDB

```rust
// Target architecture (actor-based)
AppState {
    dispatcher: DispatcherHandle<AgentActor, AgentState>,
}

// Invoke agent
dispatcher.invoke(&agent_id, "handle_message", payload).await?
```

**Why This Matters:**
1. **Alignment with vision** - This was always the intended design (see VISION.md, ADR-001)
2. **Distributed scaling** - Current approach limited to single server
3. **Fault tolerance** - Actor runtime handles failures automatically
4. **Consistency** - Single activation prevents race conditions
5. **Code reuse** - Leverage the 1000+ LOC of complete actor runtime

---

## Options & Decisions

### Decision 1: Agent-to-Actor Mapping Strategy

**Context:** How should agents map to actors? What is the actor's identity and state?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: One Actor Type | Single `AgentActor` type, agent_type in state | Simple, single code path | Less type safety, all agents share same logic |
| B: Actor Per Agent Type | `MemgptActor`, `ReactActor`, `LettaV1Actor` | Type-safe, specialized logic per type | More code, dispatch complexity |
| C: Trait-Based Behavior | `AgentActor` with pluggable behavior traits | Flexible, reusable behaviors | Abstraction complexity, trait objects |

**Decision:** **Option A - Single AgentActor Type**

**Reasoning:**
- Agent types differ in **configuration** (allowed tools, max_iterations), not fundamental behavior
- The agent loop is identical across types - only tool filtering varies
- We already have `AgentCapabilities` for this (Phase 5 complete)
- Simpler to reason about and test with DST
- Can evolve to B or C later if needed

**Trade-offs accepted:**
- Less type-level enforcement of agent type differences
- Single actor implementation must handle all agent type variations
- **Acceptable because:** Agent type logic is already centralized in `AgentCapabilities`

---

### Decision 2: State Schema Design

**Context:** What state does the AgentActor store? What role do FDB and UMI play?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Everything in ActorKV | Metadata, blocks, messages, sessions all in ActorKV | Single source | Large state, slow serialization |
| B: UMI as Primary | UMI handles all memory, actor minimal | Leverages UMI | UMI is search layer, not database |
| C: FDB Hot + UMI Search | FDB for CRUD, UMI for semantic search | Proper separation | Two systems to sync |

**Decision:** **Option C - FDB for Hot Path, UMI for Search**

**Reasoning:**
- **FDB was designed for this** - FdbStorage already has agent/block/message/session storage (1000+ LOC, just not wired)
- **UMI is a search layer, not a database** - UMI needs a backend (LanceDB/PostgreSQL), it's not persistence itself
- **ACID guarantees** - FDB provides transactions, UMI doesn't guarantee consistency
- **Session handoff requires FDB** - Need reliable persistence for crash recovery and transfer

**Storage Responsibilities:**

```
┌─────────────────────────────────────────────────────────────┐
│                 FDB (Hot Path - CRUD)                        │
│                                                              │
│  • Agent metadata (id, name, type, model, system)           │
│  • Core memory blocks (persona, human, facts, goals)        │
│  • Messages (full conversation history)                     │
│  • Session state (iteration, pause, pending_tools)          │
│                                                              │
│  ACID, fast reads, crash recovery, session handoff          │
└─────────────────────────────────────────────────────────────┘
              │
              │ Async sync on write (fire-and-forget)
              ↓
┌─────────────────────────────────────────────────────────────┐
│                 UMI (Search Layer)                           │
│                                                              │
│  • Archival memory (semantic vector search)                 │
│  • Conversation search (semantic recall)                    │
│  • Working memory promotion (usage-based)                   │
│                                                              │
│  Embeddings, recall, promotion logic                        │
└─────────────────────────────────────────────────────────────┘
```

**Actor State (in ActorKV via FDB):**
```rust
struct AgentActorState {
    // Session state for crash recovery / handoff
    session_id: String,
    iteration: u32,
    is_paused: bool,
    pause_until_ms: Option<u64>,
    pending_tool_calls: Vec<PendingToolCall>,
    last_tool_result: Option<String>,

    // Cached for fast access (source of truth is FDB)
    agent_id: String,
}
```

**How It Works:**
```
AgentActor::on_activate()
  1. Load session state from FDB (or create new)
  2. Load agent metadata from FDB
  3. Load core blocks from FDB
  4. Initialize UmiMemoryBackend for search

AgentActor::handle_message(msg)
  1. Store message in FDB
  2. Async: Sync message to UMI for search indexing
  3. Build prompt from FDB blocks
  4. Call LLM
  5. Tool calls → update FDB + sync to UMI
  6. Checkpoint session state to FDB (every iteration)

AgentActor::on_deactivate()
  1. Final checkpoint to FDB
  2. Actor can be resumed on any node
```

**Session Handoff:**
```
Agent A (source)              FDB                 Agent B (target)
     │                         │                        │
     ├─ checkpoint() ─────────►│                        │
     │   (session, messages,   │                        │
     │    blocks, metadata)    │                        │
     │                         │                        │
     └─ [deactivate]           │◄─────── load() ───────┤
                               │   (session, messages,  │
                               │    blocks, metadata)   │
                               │                        │
                               │         Resume from iteration N
```

**Trade-offs accepted:**
- Two storage systems (FDB + UMI)
- Sync lag between FDB write and UMI indexing
- **Acceptable because:** Each system does what it's designed for

---

### Decision 3: REST API to Actor Integration Point

**Context:** Where does the REST API hand off to the actor runtime?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: API Layer Invokes Dispatcher | Axum handlers call `dispatcher.invoke()` directly | Simple, direct path | API coupled to actor protocol |
| B: Service Layer Abstraction | `AgentService` wraps dispatcher, provides high-level API | Clean separation, testable | Extra layer, indirection |
| C: Actor-Native API | REST endpoints map 1:1 to actor operations | Minimal translation, efficient | Tight coupling, less flexible |

**Decision:** **Option B - Service Layer Abstraction**

**Reasoning:**
- Clean separation: REST API → AgentService → Dispatcher → AgentActor
- Service layer can handle cross-cutting concerns (auth, rate limiting, caching)
- Testable: Mock service for API tests, mock dispatcher for service tests
- Future-proof: Can swap dispatcher implementation without changing API

**Trade-offs accepted:**
- Slight indirection overhead
- More files and abstractions
- **Acceptable because:** Better architecture, easier to test and maintain

---

### Decision 4: Migration Strategy

**Context:** How do we transition from HashMap-based to actor-based without breaking everything?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Big Bang Replacement | Delete HashMap code, implement actors, cut over | Clean slate, no hybrid state | Risky, long development gap |
| B: Feature Flag Dual Mode | Support both HashMap and actors, toggle via config | Safe rollback, gradual migration | Complex, technical debt |
| C: Phased Replacement | Implement actors alongside HashMap, migrate endpoints one-by-one | Lower risk, incremental progress | Temporary duplication, longer timeline |

**Decision:** **Option A - Big Bang Replacement**

**Reasoning:**
- We're early enough that breaking changes are acceptable
- DST coverage will catch issues before production
- No production users yet (server uses in-memory, data lost on restart anyway)
- Cleaner codebase without hybrid complexity
- Can complete in 2-3 weeks vs months of gradual migration

**Trade-offs accepted:**
- All-or-nothing transition
- Need comprehensive testing before merge
- **Acceptable because:** Pre-production, DST harness will validate, cleaner result

---

### Decision 5: FDB Storage Layer

**Context:** Which FDB implementation should AgentActor use?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Use kelpie-storage/fdb.rs (ActorKV) | Existing 1000 LOC, battle-tested | Already complete, proven design | Generic key-value, no agent schema |
| B: Use kelpie-server/storage/fdb.rs (AgentStorage) | Purpose-built for agents, explicit schema | Type-safe, agent-specific operations | Not designed for actors, different layer |
| C: Hybrid - ActorKV for hot, AgentStorage for cold | Best of both worlds | Optimized for access patterns | Two FDB connections, more complexity |

**Decision:** **Option A - Use ActorKV (kelpie-storage/fdb.rs)**

**Reasoning:**
- Actor runtime already expects `ActorKV` trait
- Proven design with 23 passing tests
- Generic key-value is flexible enough for agent state
- Can serialize `AgentMetadata`, `Block`, `SessionState` as values
- `AgentStorage` was a temporary layer for non-actor approach

**Trade-offs accepted:**
- Need to serialize agent-specific types to bytes
- Less type-safe than `AgentStorage` trait
- **Acceptable because:** Serialization is standard pattern, ActorKV is the proper layer

---

### Decision 6: Session Handoff Strategy

**Context:** How do we enable crash recovery and session transfer between agents?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: No Handoff | Session dies with agent, start fresh | Simple | Poor UX, lost context |
| B: Checkpoint on Deactivate | Save state only when actor deactivates | Low overhead | Loses in-flight work on crash |
| C: Checkpoint Every Iteration | Save after each agent loop iteration | Full recovery | Higher write load |
| D: Checkpoint + WAL | Write-ahead log for in-flight, checkpoint for stable | Best recovery | Complex implementation |

**Decision:** **Option C - Checkpoint Every Iteration**

**Reasoning:**
- Agent loop iterations are natural checkpoint boundaries
- FDB writes are fast (single transaction)
- Crash recovery can resume from last completed iteration
- Session handoff gets consistent state
- Simpler than WAL, good enough for agent workloads

**What Gets Checkpointed:**

```rust
struct SessionCheckpoint {
    // Session identity
    session_id: String,
    agent_id: String,

    // Loop state
    iteration: u32,
    max_iterations: u32,

    // Pause state
    is_paused: bool,
    pause_until_ms: Option<u64>,

    // Tool execution state
    pending_tool_calls: Vec<PendingToolCall>,
    last_tool_result: Option<String>,

    // Stop reason (if stopped)
    stop_reason: Option<StopReason>,

    // Timestamps
    started_at: DateTime<Utc>,
    checkpointed_at: DateTime<Utc>,
}

struct PendingToolCall {
    tool_call_id: String,
    tool_name: String,
    arguments: serde_json::Value,
    status: ToolCallStatus,  // Pending, Executing, Completed, Failed
    result: Option<String>,
}
```

**Checkpoint Flow:**
```
┌─────────────────────────────────────────────────────────────┐
│                    Agent Loop Iteration                      │
│                                                              │
│  1. [Start iteration N]                                      │
│  2. Build prompt (from FDB blocks)                          │
│  3. Call LLM                                                 │
│  4. Process tool calls                                       │
│  5. ──► CHECKPOINT to FDB ◄──                               │
│         • iteration = N                                      │
│         • pending_tool_calls (if any)                       │
│         • last_tool_result                                   │
│  6. Check stop conditions                                    │
│  7. [Loop or exit]                                          │
└─────────────────────────────────────────────────────────────┘
```

**Crash Recovery Flow:**
```
Agent crashes at iteration 3, tool "shell" executing
                    │
                    ↓
FDB has checkpoint: iteration=2, pending_tool_calls=[], last_result="..."
                    │
                    ↓
New actor activates:
  1. Load checkpoint from FDB
  2. iteration = 2 (last completed)
  3. Resume at iteration 3 (re-execute)
  4. Continue loop
```

**Session Transfer Flow:**
```
Agent A (iteration 5, paused)     Agent B (receiving)
         │                              │
         ├─ checkpoint(session)         │
         │  iteration=5                 │
         │  is_paused=true              │
         │  pause_until=X               │
         │                              │
         └─ [deactivate]                │
                                        │
         transfer_session(A→B) ─────────┤
                                        │
                                  1. Load A's checkpoint
                                  2. Load A's messages
                                  3. Load A's blocks
                                  4. Resume at iteration 5
                                  5. Wait until pause_until
                                  6. Continue
```

**API for Session Handoff:**
```rust
// Transfer session to another agent
POST /v1/agents/{source_id}/sessions/{session_id}/transfer
{
    "target_agent_id": "agent-456"
}

// Resume agent from latest checkpoint
POST /v1/agents/{id}/resume
{
    "session_id": "optional-specific-session"  // or latest
}
```

**Trade-offs accepted:**
- Write to FDB every iteration (but FDB is fast)
- Resume re-executes last iteration (idempotency required)
- **Acceptable because:** Agent iterations are expensive (LLM calls), checkpoint overhead is negligible

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-13 21:00 | Single `AgentActor` type | Agent types are config differences, not behavior | Less type-level safety |
| 2026-01-13 21:05 | ~~Hybrid~~ → ~~UMI primary~~ → **FDB hot + UMI search** | FDB for CRUD/ACID, UMI for semantic search | Two systems to sync |
| 2026-01-13 21:10 | Service layer abstraction | Clean separation, testable, future-proof | Slight indirection |
| 2026-01-13 21:15 | Big bang replacement | Clean slate, DST coverage, pre-production | All-or-nothing transition |
| 2026-01-13 21:20 | Use ActorKV (kelpie-storage/fdb.rs) | Proper actor layer, proven design | Need serialization layer |
| 2026-01-13 22:30 | Restructure plan to DST-first | Per CONSTRAINTS.md §1, tests must precede implementation | Must extend DST harness first |
| 2026-01-13 23:00 | Checkpoint every iteration | Natural boundaries, FDB fast, full crash recovery | Re-execute last iteration on resume |
| 2026-01-13 23:00 | FDB hot path + UMI search | FDB for CRUD/ACID, UMI for semantic search | Corrects earlier "UMI primary" mistake |
| 2026-01-13 (Phase 1) | Used wrapping arithmetic in SimLlmClient | Prevent overflow in modulo operations | Slightly less obvious than checked operations |
| 2026-01-13 (Phase 1) | SimAgentEnv as test-only harness | Placeholder until AgentActor exists (Phase 3) | Not production-ready yet |

---

## Implementation Plan (DST-First)

> **Critical:** This plan follows the Simulation-First Workflow from CONSTRAINTS.md:
> 1. HARNESS CHECK → 2. WRITE TEST → 3. IMPLEMENT → 4. RUN SIMULATION → 5. FIX & ITERATE → 6. VERIFY DETERMINISM

---

### Phase 0: Understand Current Actor Runtime
- [x] Read `kelpie-runtime` crate code
- [ ] Read all actor runtime tests (23 tests)
- [ ] Understand `Dispatcher`, `ActorFactory`, `ActorHandle` APIs
- [ ] Review `ActorKV` trait and FDB implementation
- [ ] Identify gaps between runtime capabilities and agent needs

**Deliverable:** Understanding documented in Findings section

---

### Phase 1: DST Harness Extension (MUST DO FIRST)

**Per CONSTRAINTS.md §1:** "If the feature requires fault types the harness doesn't support: STOP implementation work, extend the harness FIRST"

**1.1 - Add Missing Fault Types**

Add to `kelpie-dst/src/fault.rs`:
```rust
// New fault types for agent-level testing
LlmTimeout,        // LLM provider takes too long
LlmFailure,        // LLM provider returns error
LlmRateLimited,    // LLM provider rate limits
AgentLoopPanic,    // Agent loop crashes mid-execution
```

- [x] Add `LlmTimeout` fault type
- [x] Add `LlmFailure` fault type
- [x] Add `LlmRateLimited` fault type
- [x] Add `AgentLoopPanic` fault type
- [x] Update `FaultInjector` to handle new types (added `with_llm_faults` builder)
- [x] Write unit tests for new fault types

**File:** `crates/kelpie-dst/src/fault.rs` ✅

**1.2 - Create SimLlmClient**

Deterministic LLM client for testing (similar to existing `SimMcpClient`):
```rust
pub struct SimLlmClient {
    rng: DeterministicRng,
    faults: Arc<FaultInjector>,
    responses: HashMap<String, String>,  // Canned responses by prompt hash
}

impl SimLlmClient {
    pub async fn complete(&self, messages: &[Message]) -> Result<String> {
        // Check for faults first
        if self.faults.should_inject(FaultType::LlmTimeout) {
            return Err(Error::Timeout);
        }
        if self.faults.should_inject(FaultType::LlmFailure) {
            return Err(Error::LlmUnavailable);
        }
        // Return deterministic response based on message hash + rng
        Ok(self.generate_response(messages))
    }
}
```

- [x] Create `SimLlmClient` struct
- [x] Implement deterministic response generation (hash-based + RNG)
- [x] Integrate with `FaultInjector` for fault injection
- [x] Add canned responses for common test scenarios
- [x] Write unit tests for `SimLlmClient` (6 tests, all passing)

**File:** `crates/kelpie-dst/src/llm.rs` (new) ✅

**1.3 - Create Agent Test Harness**

High-level harness for agent-level DST tests:
```rust
pub struct SimAgentEnv {
    pub storage: Arc<SimStorage>,
    pub llm: Arc<SimLlmClient>,
    pub clock: Arc<SimClock>,
    pub faults: Arc<FaultInjector>,
    pub rng: DeterministicRng,
}

impl SimAgentEnv {
    /// Create agent through dispatcher (returns AgentId)
    pub async fn create_agent(&self, config: AgentConfig) -> Result<AgentId>;

    /// Send message and get response
    pub async fn send_message(&self, id: &AgentId, msg: &str) -> Result<String>;

    /// Get agent state for assertions
    pub async fn get_agent(&self, id: &AgentId) -> Result<AgentState>;
}
```

- [x] Create `SimAgentEnv` struct
- [x] Implement `create_agent()` wrapper
- [x] Implement `send_message()` wrapper
- [x] Implement `get_agent()` wrapper
- [x] Add helper methods: `update_agent()`, `delete_agent()`, `list_agents()`
- [x] Write unit tests (8 tests, all passing)

**File:** `crates/kelpie-dst/src/agent.rs` (new) ✅

**1.4 - Verify Harness Works**

Before ANY implementation:
```bash
# Must pass before continuing
cargo test -p kelpie-dst test_sim_llm_client
cargo test -p kelpie-dst test_sim_agent_env
cargo test -p kelpie-dst test_new_fault_types
```

- [x] All harness extension tests pass (50 unit tests total, all passing)
- [x] Can run `Simulation::new(config).run_async(|env| { ... })` with agent env
- [x] Fault injection works for new fault types (verified in SimLlmClient tests)

**Deliverable:** Harness ready for agent-level testing ✅

---

### Phase 2: Write DST Tests FIRST (Before Implementation)

**Per CONSTRAINTS.md:** "WRITE SIMULATION TEST - Test will FAIL initially (feature doesn't exist)"

These tests define the contract. Write them now, they WILL fail, then implement in Phase 3.

**2.1 - AgentActor Lifecycle Tests**

**File:** `crates/kelpie-server/tests/agent_actor_dst.rs`

```rust
#[tokio::test]
async fn test_dst_agent_actor_activation_basic() {
    // Create agent → actor activates → state loads
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_actor_activation_with_storage_fail() {
    // 20% StorageReadFail → graceful error
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_actor_deactivation_persists_state() {
    // Deactivate → reactivate → state recovered
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_actor_deactivation_with_storage_fail() {
    // 20% StorageWriteFail → retry logic works
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_actor_crash_recovery() {
    // CrashAfterWrite → state consistent after recovery
    // WILL FAIL: AgentActor doesn't exist yet
}
```

- [x] Write `test_dst_agent_actor_activation_basic`
- [x] Write `test_dst_agent_actor_activation_with_storage_fail`
- [x] Write `test_dst_agent_actor_deactivation_persists_state`
- [x] Write `test_dst_agent_actor_deactivation_with_storage_fail`
- [x] Write `test_dst_agent_actor_crash_recovery`
- [x] **Tests written** - marked `#[ignore]` until Phase 3 implements AgentActor
- ⚠️ **Cannot run yet** - blocked by external umi-memory compilation error

**2.2 - AgentActor Message Handling Tests**

**File:** `crates/kelpie-server/tests/agent_actor_dst.rs` (continued)

```rust
#[tokio::test]
async fn test_dst_agent_handle_message_basic() {
    // Send message → LLM called → response returned
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_handle_message_with_llm_timeout() {
    // LlmTimeout fault → graceful timeout error
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_handle_message_with_llm_failure() {
    // LlmFailure fault → error propagated correctly
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_tool_execution() {
    // LLM requests tool → tool executes → result returned
    // WILL FAIL: AgentActor doesn't exist yet
}

#[tokio::test]
async fn test_dst_agent_memory_tools() {
    // core_memory_append → state updated → persisted
    // WILL FAIL: AgentActor doesn't exist yet
}
```

- [x] Write `test_dst_agent_handle_message_basic`
- [x] Write `test_dst_agent_handle_message_with_llm_timeout`
- [x] Write `test_dst_agent_handle_message_with_llm_failure`
- [x] Write `test_dst_agent_tool_execution`
- [x] Write `test_dst_agent_memory_tools`
- [x] **Tests written** - define contract for AgentActor message handling
- ⚠️ **Cannot run yet** - blocked by external umi-memory compilation error

**2.3 - AgentService Tests**

**File:** `crates/kelpie-server/tests/agent_service_dst.rs` (new)

- [ ] Write `test_dst_service_create_agent`
- [ ] Write `test_dst_service_send_message`
- [ ] Write `test_dst_service_get_agent`
- [ ] Write `test_dst_service_delete_agent`
- [ ] Write `test_dst_service_dispatcher_failure`
- [ ] Write `test_dst_service_timeout_handling`
- [ ] **Run tests, confirm they FAIL**

**2.4 - Full Lifecycle Stress Tests**

**File:** `crates/kelpie-server/tests/agent_stress_dst.rs` (new)

- [ ] Write `test_dst_stress_100_concurrent_agents`
- [ ] Write `test_dst_stress_rapid_create_delete`
- [ ] Write `test_dst_stress_many_messages_per_agent`
- [ ] Write `test_dst_determinism_same_seed_same_result`
- [ ] **Run tests, confirm they FAIL**

**Deliverable:** Complete DST test suite (all failing, ~25 tests)

---

### Phase 3: Implement AgentActor (Iterate Until Tests Pass)

Now implement to make Phase 2 tests pass.

**3.1 - AgentActor Core**

- [ ] Create `AgentActor` struct implementing `Actor` trait
- [ ] Define `AgentState` (metadata, blocks, session state)
- [ ] Implement `on_activate()` - Load state from ActorKV
- [ ] Implement `on_deactivate()` - Persist state to ActorKV
- [ ] Add TigerStyle assertions (2+ per method)

**File:** `crates/kelpie-server/src/actor/mod.rs` (new)

**3.2 - Iteration Loop**

```bash
# Run repeatedly until passing
cargo test -p kelpie-server test_dst_agent_actor_activation
# Fix issues
cargo test -p kelpie-server test_dst_agent_actor_activation
# Repeat until pass
```

- [ ] `test_dst_agent_actor_activation_basic` → PASSES
- [ ] `test_dst_agent_actor_activation_with_storage_fail` → PASSES
- [ ] `test_dst_agent_actor_deactivation_persists_state` → PASSES
- [ ] `test_dst_agent_actor_deactivation_with_storage_fail` → PASSES
- [ ] `test_dst_agent_actor_crash_recovery` → PASSES

**3.3 - AgentActor Operations**

- [ ] Implement `invoke()` routing to operations
- [ ] Implement `handle_message` operation (LLM loop)
- [ ] Implement `get_metadata` operation
- [ ] Implement `update_metadata` operation
- [ ] Implement `get_blocks` / `update_block` operations

**Iteration Loop:**
- [ ] `test_dst_agent_handle_message_basic` → PASSES
- [ ] `test_dst_agent_handle_message_with_llm_timeout` → PASSES
- [ ] `test_dst_agent_handle_message_with_llm_failure` → PASSES
- [ ] `test_dst_agent_tool_execution` → PASSES
- [ ] `test_dst_agent_memory_tools` → PASSES

**Deliverable:** AgentActor complete, all lifecycle tests pass

---

### Phase 4: Implement AgentService (Iterate Until Tests Pass)

**4.1 - Service Layer**

- [ ] Create `AgentService` struct wrapping `DispatcherHandle`
- [ ] Implement `create_agent()`
- [ ] Implement `send_message()`
- [ ] Implement `get_agent()` / `update_agent()` / `delete_agent()`
- [ ] Error mapping: Actor errors → Service errors

**File:** `crates/kelpie-server/src/service/mod.rs` (new)

**Iteration Loop:**
- [ ] `test_dst_service_create_agent` → PASSES
- [ ] `test_dst_service_send_message` → PASSES
- [ ] `test_dst_service_get_agent` → PASSES
- [ ] `test_dst_service_delete_agent` → PASSES
- [ ] `test_dst_service_dispatcher_failure` → PASSES
- [ ] `test_dst_service_timeout_handling` → PASSES

**Deliverable:** AgentService complete, all service tests pass

---

### Phase 5: Wire Dispatcher to AppState

- [ ] Replace HashMap fields with `DispatcherHandle` in `AppState`
- [ ] Add `AgentService` to `AppState`
- [ ] Update `AppState::new()` to initialize dispatcher
- [ ] Add `AppState::shutdown()` to cleanup dispatcher

**File:** `crates/kelpie-server/src/state.rs`

---

### Phase 6: Refactor REST API Handlers

- [ ] `POST /v1/agents` → service.create_agent()
- [ ] `GET /v1/agents/{id}` → service.get_agent()
- [ ] `PATCH /v1/agents/{id}` → service.update_agent()
- [ ] `DELETE /v1/agents/{id}` → service.delete_agent()
- [ ] `GET /v1/agents/{id}/blocks` → actor invoke
- [ ] `PATCH /v1/agents/{id}/blocks/{bid}` → actor invoke
- [ ] `POST /v1/agents/{id}/messages` → service.send_message()
- [ ] `POST /v1/agents/{id}/messages/stream` → streaming (Phase 7)

**Files:** `crates/kelpie-server/src/api/*.rs`

---

### Phase 7: Message Streaming Architecture

**7.1 - Write Streaming DST Tests First**

**File:** `crates/kelpie-server/tests/agent_streaming_dst.rs` (new)

- [ ] Write `test_dst_streaming_basic`
- [ ] Write `test_dst_streaming_with_network_delay`
- [ ] Write `test_dst_streaming_cancellation`
- [ ] **Run tests, confirm they FAIL**

**7.2 - Implement Streaming**

- [ ] Design streaming protocol (channel-based)
- [ ] Implement `StreamingHandle` for actor → service communication
- [ ] Update `AgentActor::handle_message` to support streaming
- [ ] Wire SSE endpoint to streaming service

**Iteration Loop:**
- [ ] `test_dst_streaming_basic` → PASSES
- [ ] `test_dst_streaming_with_network_delay` → PASSES
- [ ] `test_dst_streaming_cancellation` → PASSES

---

### Phase 8: FDB + UMI Storage Integration

**FDB is the hot path (CRUD), UMI is the search layer.**

**8.1 - Wire FDB to AgentActor**

FDB stores all agent data with ACID guarantees:
- [ ] Wire `FdbStorage` to server startup (currently NOT connected)
- [ ] Actor loads agent metadata from FDB on activate
- [ ] Actor loads core blocks from FDB on activate
- [ ] Actor loads/creates session checkpoint from FDB
- [ ] Messages stored to FDB on each send
- [ ] Blocks updated in FDB on tool calls

**8.2 - Wire UMI for Search**

UMI provides semantic search over FDB data:
- [ ] Initialize `UmiMemoryBackend` per agent on activate
- [ ] Async sync: FDB write → UMI indexing (fire-and-forget)
- [ ] `archival_memory_search` → `backend.search_archival()`
- [ ] `conversation_search` → `backend.search_conversations()`
- [ ] `archival_memory_insert` → FDB write + UMI sync

**8.3 - Session Checkpointing**

Per Decision 6, checkpoint every iteration:
- [ ] After each agent loop iteration → `fdb.save_session(checkpoint)`
- [ ] Checkpoint includes: iteration, pending_tools, pause_state
- [ ] On actor activate → `fdb.load_latest_session(agent_id)`
- [ ] Resume from last completed iteration

**DST Requirements:**
- [ ] Write `test_dst_fdb_agent_crud` (metadata, blocks, messages)
- [ ] Write `test_dst_session_checkpoint_every_iteration`
- [ ] Write `test_dst_crash_recovery_resume_from_checkpoint`
- [ ] Write `test_dst_session_handoff_between_agents`
- [ ] Write `test_dst_umi_search_after_fdb_write`

---

### Phase 9: Stress Testing & Determinism Verification

**Final DST validation:**

```bash
# Run all stress tests
cargo test -p kelpie-server test_dst_stress --release

# Verify determinism (same seed = same result)
DST_SEED=12345 cargo test -p kelpie-server test_dst_determinism
DST_SEED=12345 cargo test -p kelpie-server test_dst_determinism  # Must match!

# Run with 10 different seeds
for seed in $(seq 1 10); do
    DST_SEED=$seed cargo test -p kelpie-server
done
```

- [ ] `test_dst_stress_100_concurrent_agents` → PASSES
- [ ] `test_dst_stress_rapid_create_delete` → PASSES
- [ ] `test_dst_stress_many_messages_per_agent` → PASSES
- [ ] `test_dst_determinism_same_seed_same_result` → PASSES
- [ ] 10 different seeds all pass

---

### Phase 10: Remove Deprecated Code

- [ ] Delete `kelpie-server/src/storage/` module
- [ ] Delete HashMap-based state management
- [ ] Clean up unused imports and types
- [ ] Run `cargo clippy --all-targets`

---

### Phase 11: Integration Testing & Documentation

- [ ] Update existing integration tests
- [ ] Test Letta API compatibility
- [ ] Manual testing: Create agent, chat, verify persistence
- [ ] Update VISION.md implementation status
- [ ] Update README.md with actor-based architecture
- [ ] Add ADR: Actor-Based Agent Server

---

## Checkpoints

**Phase Gates (must pass before proceeding):**

- [ ] Phase 0: Actor runtime understood
- [ ] Plan approved (handoff prompt provided)
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained** (ongoing) ✅
- [x] Phase 1: DST harness extensions complete + verified ✅
- [ ] Phase 2: All DST tests written + confirmed failing
- [ ] Phase 3: AgentActor implemented + tests passing
- [ ] Phase 4: AgentService implemented + tests passing
- [ ] Phase 5: Dispatcher wired to AppState
- [ ] Phase 6: API handlers refactored
- [ ] Phase 7: Streaming implemented + tests passing
- [ ] Phase 8: Cold storage integrated
- [ ] Phase 9: Stress tests passing + determinism verified
- [ ] Phase 10: Deprecated code removed
- [ ] Phase 11: Integration tests + documentation

**Final Verification:**
- [ ] `cargo test --workspace` passes
- [ ] `cargo clippy --all-targets` clean
- [ ] `cargo fmt --check` passes
- [ ] `/no-cap` passes
- [ ] Vision/CONSTRAINTS.md aligned
- [ ] **What to Try section updated** (after each phase)
- [ ] Committed and pushed

---

## Test Requirements

### DST Test Files (Phase 2)

| File | Tests | Purpose |
|------|-------|---------|
| `agent_actor_dst.rs` | ~10 tests | Actor lifecycle, fault handling |
| `agent_service_dst.rs` | ~6 tests | Service layer, dispatcher integration |
| `agent_streaming_dst.rs` | ~3 tests | Streaming responses |
| `agent_stress_dst.rs` | ~4 tests | Concurrent load, determinism |
| **Total** | **~25 DST tests** | |

### Fault Injection Matrix

| Test Category | Faults | Rate |
|---------------|--------|------|
| Activation | `StorageReadFail` | 20% |
| Deactivation | `StorageWriteFail` | 20% |
| Crash Recovery | `CrashAfterWrite` | 10% |
| LLM Handling | `LlmTimeout`, `LlmFailure` | 30% |
| Tool Execution | `McpToolFail`, `McpToolTimeout` | 20% |
| Streaming | `NetworkDelay` | 50ms base |

### Commands

```bash
# Phase 1: Verify harness extensions
cargo test -p kelpie-dst test_sim_llm_client
cargo test -p kelpie-dst test_new_fault_types

# Phase 2: Confirm tests fail (expected)
cargo test -p kelpie-server test_dst_agent -- --nocapture
# Expected: all tests FAIL (no implementation yet)

# Phase 3+: Iteration loop
cargo test -p kelpie-server test_dst_agent_actor_activation_basic
# Fix, re-run, repeat until pass

# Phase 9: Full stress + determinism
cargo test -p kelpie-server test_dst_stress --release
DST_SEED=12345 cargo test -p kelpie-server test_dst_determinism
DST_SEED=12345 cargo test -p kelpie-server test_dst_determinism  # Must match!

# Final verification
cargo test --workspace
cargo clippy --all-targets --all-features
cargo fmt --check
```

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 2026-01-13 21:00 | kelpie-runtime/src/lib.rs | Understand exported API |
| 2026-01-13 21:05 | kelpie-runtime/src/dispatcher.rs | Dispatcher API, command protocol |
| | | |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| None yet | - | - |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Claude-1 | Phase 0-10 | Grounding | 2026-01-13 21:00 |

---

## Findings

### Actor Runtime Capabilities (from kelpie-runtime)
- ✅ Dispatcher with command channel
- ✅ ActorFactory trait for creating actors
- ✅ Single activation guarantee
- ✅ Automatic lifecycle (activate/deactivate)
- ✅ Mailbox management
- ✅ ActorKV integration for state persistence
- ✅ 23 passing tests

### DST Harness Analysis (2026-01-13 22:30)

**Current DST Capabilities (✅ Complete):**
| Component | Status | LOC | Notes |
|-----------|--------|-----|-------|
| SimClock | ✅ | ~400 | Deterministic time control |
| DeterministicRng | ✅ | ~200 | ChaCha20-based, seeded |
| SimStorage | ✅ | ~750 | In-memory KV, transactions, fault injection |
| SimNetwork | ✅ | ~200 | Latency, packet loss, partitions |
| FaultInjector | ✅ | ~300 | 16+ fault types |
| Simulation Runner | ✅ | ~350 | `run()` and `run_async()` patterns |

**~~Missing for Agent-Level DST~~ (✅ Phase 1 COMPLETE):**
| Component | Status | LOC | Notes |
|-----------|--------|-----|-------|
| `SimLlmClient` | ✅ Complete | ~270 LOC | Deterministic LLM with fault injection, 6 tests passing |
| `LlmTimeout` fault | ✅ Complete | ~5 LOC | Added to FaultType enum |
| `LlmFailure` fault | ✅ Complete | ~5 LOC | Added to FaultType enum |
| `LlmRateLimited` fault | ✅ Complete | ~5 LOC | Added to FaultType enum (bonus) |
| `AgentLoopPanic` fault | ✅ Complete | ~5 LOC | Added to FaultType enum (bonus) |
| `SimAgentEnv` | ✅ Complete | ~380 LOC | High-level agent harness, 8 tests passing |
| `with_llm_faults` | ✅ Complete | ~10 LOC | Builder method for LLM fault configs |

**Existing Agent DST (partial coverage):**
- `agent_loop_dst.rs` - Tool registry tests with SimMcpClient
- `heartbeat_dst.rs` - Pause mechanism with SimClock
- `memory_tools_dst.rs` - Memory tools with fault injection
- ~~**Gap:** No end-to-end agent invoke simulation (LLM → tools → response)~~ ✅ **FIXED**
- `agent_integration_dst.rs` (NEW) - 9 comprehensive integration tests with full Simulation harness

### Integration Testing Results (Phase 1.4)

**Bugs Found by Full Simulation Testing:**

1. **Bug #1: SimStorage Not Clone-able**
   - **Symptom:** `no method named 'clone' found for struct 'SimStorage'`
   - **Root Cause:** SimStorage wraps Arc<RwLock<HashMap>> but didn't derive Clone
   - **Impact:** Cannot share storage across SimEnvironment components
   - **Fix:** Added `#[derive(Clone)]` to SimStorage (Arc cloning is cheap)
   - **Severity:** Critical - blocked all integration testing

2. **Bug #2: Error Type Mismatch**
   - **Symptom:** `the trait 'From<String>' is not implemented for 'kelpie_core::error::Error'`
   - **Root Cause:** SimAgentEnv returned `Result<_, String>`, Simulation expects `Result<_, kelpie_core::Error>`
   - **Impact:** Cannot use `?` operator in simulation closures
   - **Fix:** Changed all SimAgentEnv methods to return `Result<_, kelpie_core::Error>`
   - **Severity:** Critical - blocked integration with Simulation framework

**Integration Test Coverage:**
- ✅ `test_agent_env_with_simulation_basic` - Basic agent creation and messaging
- ✅ `test_agent_env_with_llm_faults` - 30%+20% fault rate, verifies failures occur
- ✅ `test_agent_env_with_storage_faults` - Storage operations under 10%+10% fault injection
- ✅ `test_agent_env_with_time_advancement` - Simulated time progression
- ✅ `test_agent_env_determinism` - Same seed produces same results
- ✅ `test_agent_env_multiple_agents_concurrent` - 10 agents, all accessible
- ✅ `test_agent_env_with_tools` - Tool call generation works
- ✅ `test_agent_env_stress_with_faults` - 20 agents, 100 messages, 35% combined fault rate
- ✅ `test_llm_client_direct_with_simulation` - Direct LLM testing with 25% failure rate

**Fault Injection Verification:**
- LLM faults (timeout, failure, rate limit) properly injected and handled
- Storage faults (read fail, write fail) tested under load
- Determinism maintained under fault conditions
- Success/failure ratio matches expected probability

**Test Result Summary:**
- 59 total tests passing (50 unit + 9 integration)
- All tests use seeded RNG for reproducibility
- Multiple fault scenarios validated
- No flaky tests observed

### Gaps Identified
- ❓ Streaming support: Need to investigate if actors can yield intermediate results
- ❓ List operations: How to query all active agents? (Need registry query)
- ❓ Cluster support: Is multi-node placement ready? (Out of scope for this task)

### Key Files to Create (Phase 1-2)
- `kelpie-dst/src/llm.rs` - SimLlmClient
- `kelpie-dst/src/agent.rs` - SimAgentEnv
- `kelpie-server/tests/agent_actor_dst.rs` - Actor lifecycle tests
- `kelpie-server/tests/agent_service_dst.rs` - Service layer tests
- `kelpie-server/tests/agent_streaming_dst.rs` - Streaming tests
- `kelpie-server/tests/agent_stress_dst.rs` - Stress/determinism tests

### Key Files to Modify (Phase 3+)
- `kelpie-server/src/lib.rs` - Add AgentActor, AgentService
- `kelpie-server/src/state.rs` - Replace HashMap with Dispatcher
- `kelpie-server/src/main.rs` - Initialize dispatcher
- `kelpie-server/src/api/*.rs` - Update all handlers
- `kelpie-dst/src/fault.rs` - Add LLM fault types

### Key Files to Delete (Phase 10)
- `kelpie-server/src/storage/` - Entire module (replaced by ActorKV)

---

## What to Try

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Current API (HashMap-based) | `cargo run -p kelpie-server` then `curl POST /v1/agents` | Agent created, stored in memory |
| Actor runtime standalone | `cargo test -p kelpie-runtime` | 23 tests pass |
| **Phase 1: DST Harness** | `cargo test -p kelpie-dst` | **59 tests pass** (23 new: 14 unit + 9 integration) |
| SimLlmClient | `cargo test -p kelpie-dst test_sim_llm` | 6 tests pass, deterministic LLM responses |
| SimAgentEnv | `cargo test -p kelpie-dst test_sim_agent_env` | 8 tests pass, agent-level test harness |
| **Integration Tests** | `cargo test -p kelpie-dst agent_integration_dst` | **9 tests pass with full Simulation harness** |
| LLM fault types | See fault tests | LlmTimeout, LlmFailure, LlmRateLimited work |
| Fault injection | Integration tests | 35% combined fault rate, proper failures observed |
| Storage Clone bug | Fixed | SimStorage now Clone-able for SimEnvironment |
| Error type bug | Fixed | SimAgentEnv uses kelpie_core::Error |
| **Phase 2: Test Contracts** | `cargo test -p kelpie-server agent_actor_dst` | **11 tests written, all `#[ignore]` until Phase 3** |
| AgentActor DST tests | See agent_actor_dst.rs | Lifecycle, faults, LLM integration, tool execution tests |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| Actor-based agents | Not implemented | After Phase 4 |
| Persistent agents (FDB) | Not wired | After Phase 4 |
| Distributed placement | Cluster not wired | Out of scope |

### Known Limitations ⚠️
- Current server: Data lost on restart (in-memory HashMap) → **Fixed by FDB integration (Phase 8)**
- Actor runtime: Single-node only (cluster coordination not integrated)
- Streaming: Design TBD (Phase 7)
- FDB not wired: FdbStorage exists (1000+ LOC) but not connected to server startup

### Architecture Clarification ⚠️
**FDB is the hot path, UMI is the search layer:**
```
FDB (ACID, persistence):
  • Agent metadata
  • Core memory blocks
  • Messages (conversation history)
  • Session checkpoints (crash recovery, handoff)

UMI (semantic search):
  • Archival memory search
  • Conversation search
  • Working memory promotion

Actor provides:
  • Single activation guarantee
  • Checkpoint every iteration to FDB
  • Session handoff between agents
```

---

## Completion Notes

**Status:** GROUNDING - Plan created, awaiting approval

**Next Steps:**
1. User reviews and approves plan
2. Begin Phase 0: Deep dive into actor runtime
3. Phase 1: Extend DST harness (MUST complete before implementation)
4. Phase 2: Write all DST tests (confirm they fail)
5. Phase 3+: Implement until tests pass

**Workflow Per Phase:**
```
┌─────────────────────────────────────────────────────────────┐
│  1. HARNESS CHECK - Do we need new SimXxx or fault types?  │
│     YES → Add to kelpie-dst first                          │
├─────────────────────────────────────────────────────────────┤
│  2. WRITE DST TESTS - Define the contract                  │
│     Tests WILL fail (no implementation yet)                │
├─────────────────────────────────────────────────────────────┤
│  3. IMPLEMENT - Make tests pass                            │
│     cargo test <specific_test>                             │
│     Fix issues                                             │
│     Repeat until pass                                      │
├─────────────────────────────────────────────────────────────┤
│  4. VERIFY DETERMINISM - Same seed = same result           │
│     DST_SEED=X cargo test (run twice, compare)             │
└─────────────────────────────────────────────────────────────┘
```

**Verification Status:** N/A (not implemented yet)

**Commit:** N/A
**PR:** N/A

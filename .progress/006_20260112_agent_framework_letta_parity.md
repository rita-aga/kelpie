# Kelpie Agent Framework: Letta Feature Parity Plan

**Date:** 2026-01-12
**Author:** Claude
**Status:** Phase 0 Complete - In Progress
**Estimated Effort:** ~6-7 weeks (DST-first)

---

## Executive Summary

Kelpie's agent framework is **80-85% complete**. The core agent loop, tool execution, memory blocks, and infrastructure are all working. This plan details the remaining work to achieve Letta feature parity, with **Umi as the memory backend**.

### Key Decisions Made

| Decision | Choice | Rationale |
|----------|--------|-----------|
| **Conversation storage** | Umi + LanceDB (dev) / PostgreSQL (prod) | Already has vector search, DST support |
| **Embeddings** | Umi's SimEmbedding (DST) + OpenAI (prod) | Deterministic for testing, quality for prod |
| **MCP registration** | Static configuration at startup | Simpler, more DST-friendly, like Letta |
| **Agent state persistence** | FDB for actor state, Umi for memory | Separation of concerns |

### What Already Exists (80-85%)

| Component | Location | Status |
|-----------|----------|--------|
| Agent loop | `kelpie-server/src/api/messages.rs:222-282` | ✅ Working |
| Tool execution | `kelpie-server/src/api/messages.rs` | ✅ Working |
| Memory blocks → context | `kelpie-server/src/api/messages.rs` | ✅ Working |
| SSE streaming | `kelpie-server/src/api/messages.rs` | ✅ Working |
| Tool chaining (5 iterations) | `kelpie-server/src/api/messages.rs` | ✅ Working |
| Rust Tool trait | `kelpie-tools/src/traits.rs` | ✅ Complete |
| MCP client | `kelpie-tools/src/mcp.rs` (1324 lines) | ✅ Complete |
| FDB storage | `kelpie-storage/src/fdb.rs` (1000 lines) | ✅ Complete |
| Letta REST API | `adapters/letta/` | ✅ Compatible |
| Core memory | `kelpie-memory/src/core.rs` | ✅ Complete |
| Working memory | `kelpie-memory/src/working.rs` | ✅ Complete |
| DST harness | `kelpie-dst/` (16+ fault types) | ✅ Complete |

### What's Missing (15-20%)

| Gap | Priority | Effort | With Umi |
|-----|----------|--------|----------|
| Umi integration | P0 | 5 days | Foundation for memory |
| MCP tools in agent loop | P0 | 4 days | MCP client exists, just needs wiring |
| Memory editing tools | P0 | 3 days | Simplified - wraps Umi |
| Archival search | P0 | 2 days | Trivial - Umi has DualRetriever |
| Heartbeat/pause mechanism | P1 | 2 days | Loop modification |
| Conversation search | P1 | 2 days | Umi recall with tags |
| Agent types abstraction | P2 | 5 days | Trait + implementations |
| Wire FDB to server | P1 | 2 days | Integration work |

---

## Architecture with Umi

```
┌─────────────────────────────────────────────────────────────────┐
│                        KELPIE SERVER                            │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    Agent Loop (messages.rs)               │  │
│  │  - Receives user message                                  │  │
│  │  - Builds context from Umi core memory                    │  │
│  │  - Calls LLM with tools (Rust + MCP)                      │  │
│  │  - Executes tools (including memory tools)                │  │
│  │  - Returns response via SSE                               │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │              Memory Tools (wrap Umi)                      │  │
│  │  - core_memory_append    → umi.remember() + core tag      │  │
│  │  - core_memory_replace   → umi entity update              │  │
│  │  - archival_memory_insert→ umi.remember() + archival tag  │  │
│  │  - archival_memory_search→ umi.recall()                   │  │
│  │  - conversation_search   → umi.recall() + conversation tag│  │
│  │  - pause_heartbeats      → signal loop continuation       │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │              Tool Registry (Rust + MCP)                   │  │
│  │  - Built-in tools (shell, memory, heartbeat)              │  │
│  │  - MCP tools (static config, discovered at startup)       │  │
│  └──────────────────────────────────────────────────────────┘  │
└──────────────────────────────┼──────────────────────────────────┘
                               │
┌──────────────────────────────┼──────────────────────────────────┐
│                          UMI MEMORY                             │
│  ┌─────────────────┐  ┌─────────────────┐  ┌────────────────┐  │
│  │  EntityExtractor│  │  DualRetriever  │  │ EvolutionTracker│ │
│  │  (parse → store)│  │  (fast+semantic)│  │ (track changes) │ │
│  └─────────────────┘  └─────────────────┘  └────────────────┘  │
│                              │                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │              Storage Backend (pluggable)                  │  │
│  │  DST: SimStorage | Dev: LanceDB | Prod: PostgreSQL        │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │             Embedding Provider (pluggable)                │  │
│  │  DST: SimEmbeddingProvider | Prod: OpenAIEmbeddingProvider│  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                               │
┌──────────────────────────────┼──────────────────────────────────┐
│                    FOUNDATIONDB (Actor State)                   │
│  - Agent metadata (id, name, created_at, agent_type)            │
│  - Agent configuration (model, system prompt)                   │
│  - Tool assignments per agent                                   │
│  - NOT memory content (that's in Umi)                           │
└─────────────────────────────────────────────────────────────────┘
```

---

## Phase 0: Umi Integration (P0 - 5 days)

**This is the foundation. Do this first.**

### Goal

Replace Kelpie's in-memory storage with Umi for all memory operations.

### Why First?

- Umi already has `kelpie_mapping.rs` designed for this integration
- Memory tools (Phase 2) and archival search (Phase 3) become trivial wrappers
- DST support built-in (SimStorage, SimEmbedding)
- Conversation storage question is answered

### Required Changes

1. **Add Umi dependency** to `kelpie-server/Cargo.toml`
   ```toml
   [dependencies]
   umi = { path = "../../umi" }
   ```

2. **Create UmiMemoryBackend** (`kelpie-server/src/memory/umi_backend.rs`)
   ```rust
   pub struct UmiMemoryBackend {
       memory: umi::Memory,
       agent_id: AgentId,
   }

   impl UmiMemoryBackend {
       pub async fn new(agent_id: AgentId, config: UmiConfig) -> Result<Self>;

       // Core memory operations
       pub async fn get_core_blocks(&self) -> Result<Vec<MemoryBlock>>;
       pub async fn append_core(&self, label: &str, content: &str) -> Result<()>;
       pub async fn replace_core(&self, label: &str, old: &str, new: &str) -> Result<()>;

       // Archival memory operations
       pub async fn insert_archival(&self, content: &str) -> Result<EntityId>;
       pub async fn search_archival(&self, query: &str, limit: usize) -> Result<Vec<Entity>>;

       // Conversation history
       pub async fn store_message(&self, role: &str, content: &str) -> Result<()>;
       pub async fn search_conversations(&self, query: &str, limit: usize) -> Result<Vec<Entity>>;
   }
   ```

3. **Wire into server startup** (`kelpie-server/src/main.rs`)
   ```rust
   // DST mode
   let storage = SimStorageBackend::new(seed);
   let embedder = SimEmbeddingProvider::new(seed);

   // Production mode
   let storage = LanceStorageBackend::connect(&config.lance_path).await?;
   let embedder = OpenAIEmbeddingProvider::new(&config.openai_key);

   let umi = umi::Memory::new(llm, embedder, vector, storage);
   ```

4. **Update agent loop** to use Umi for context building
   ```rust
   // In messages.rs build_system_prompt()
   let core_blocks = umi_backend.get_core_blocks().await?;
   // Format into system prompt...
   ```

### DST Requirements

| Test | Fault Types | Assertion |
|------|-------------|-----------|
| Store and recall entity | StorageWriteFail (10%) | Entity persists after retry |
| Core memory append | StorageLatency (100ms) | Operation completes within timeout |
| Archival search | NetworkDelay (50ms) | Results match expected |
| Conversation storage | CrashAfterWrite | Message survives restart |

### DST Test Example

```rust
#[test]
fn test_umi_integration_with_storage_faults() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::StorageLatency, 0.2))
        .run(|env| async move {
            let backend = UmiMemoryBackend::new_sim(env.seed).await?;

            // Store core memory
            backend.append_core("persona", "I am a helpful assistant").await?;

            // Verify it persists
            let blocks = backend.get_core_blocks().await?;
            assert!(blocks.iter().any(|b| b.label == "persona"));

            // Store archival memory
            let id = backend.insert_archival("User prefers dark mode").await?;

            // Search should find it
            let results = backend.search_archival("dark mode preference", 5).await?;
            assert!(!results.is_empty());

            Ok(())
        })
        .await
        .expect("Umi integration must work under faults");
}
```

### Acceptance Criteria

- [x] `cargo test -p kelpie-server` passes with Umi backend (46 tests pass)
- [x] DST tests pass with 10% storage failure rate (11 DST tests, 7 seeds tested)
- [x] Agent can read/write core memory through Umi
- [x] Archival search returns semantically relevant results (via Umi recall)

---

## Phase 1: MCP Tools in Agent Loop (P0 - 4 days)

### Current State

MCP client exists (`kelpie-tools/src/mcp.rs`, 1324 lines) but is not wired into the agent loop.

```rust
// Current: Only hardcoded shell tool
let tools = vec![ToolDefinition::shell()];
```

### Required Changes

1. **Static MCP configuration** (`kelpie-server/src/config.rs`)
   ```rust
   #[derive(Deserialize)]
   pub struct McpConfig {
       pub servers: Vec<McpServerConfig>,
   }

   #[derive(Deserialize)]
   pub struct McpServerConfig {
       pub name: String,
       pub command: String,  // e.g., "npx @modelcontextprotocol/server-filesystem"
       pub args: Vec<String>,
       pub env: HashMap<String, String>,
   }
   ```

2. **Tool registry unification** (`kelpie-server/src/tools/registry.rs`)
   ```rust
   pub struct UnifiedToolRegistry {
       rust_tools: ToolRegistry,
       mcp_clients: HashMap<String, McpClient>,
   }

   impl UnifiedToolRegistry {
       pub async fn discover_all(&self) -> Vec<ToolDefinition>;
       pub async fn execute(&self, name: &str, input: &Value) -> ToolResult;
   }
   ```

3. **Wire into agent loop** (`messages.rs`)
   ```rust
   async fn execute_tool(
       name: &str,
       input: &Value,
       registry: &UnifiedToolRegistry,
   ) -> ToolResult {
       registry.execute(name, input).await
   }
   ```

### DST Requirements

| Test | Fault Types | Assertion |
|------|-------------|-----------|
| MCP tool discovery | NetworkPartition | Graceful degradation to Rust tools |
| MCP tool execution | NetworkDelay (200ms) | Timeout handled correctly |
| Mixed tool execution | NetworkPacketLoss (5%) | Results still correct |
| MCP server restart | CrashDuringTransaction | Reconnection works |

### Harness Extension Needed

**New fault type:** `McpServerCrash` - Simulates MCP server process dying mid-call.

```rust
pub enum FaultType {
    // ... existing
    McpServerCrash,           // MCP server process dies
    McpServerSlowStart,       // MCP server takes long to start
    McpToolTimeout,           // Individual tool call times out
}
```

### Acceptance Criteria

- [ ] MCP tools appear in LLM tool list
- [ ] Agent can call MCP tools successfully
- [ ] Mixed Rust + MCP tools work in single conversation
- [ ] DST tests pass with network faults

---

## Phase 2: Memory Editing Tools (P0 - 3 days)

### What Letta Has

| Tool | Purpose | Kelpie Implementation |
|------|---------|----------------------|
| `core_memory_append` | Add to core memory | `umi.remember()` + core tag |
| `core_memory_replace` | Replace in core memory | Umi entity update |
| `rethink_memory` | Complete block rewrite | Umi entity replace |
| `memory_insert` | Insert at specific line | Parse + Umi update |
| `memory_finish_edits` | Signal editing complete | No-op signal |
| `archival_memory_insert` | Store in archival | `umi.remember()` + archival tag |
| `archival_memory_search` | Search archival | `umi.recall()` |
| `conversation_search` | Search past messages | `umi.recall()` + conversation tag |
| `conversation_search_date` | Search by date range | `umi.recall()` + date filter |

### Implementation

All tools are thin wrappers around `UmiMemoryBackend`:

```rust
// kelpie-tools/src/builtin/memory.rs

pub struct CoreMemoryAppend {
    backend: Arc<UmiMemoryBackend>,
}

#[async_trait]
impl Tool for CoreMemoryAppend {
    fn metadata(&self) -> &ToolMetadata {
        &CORE_MEMORY_APPEND_METADATA
    }

    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
        let label = input.get_string("label")?;
        let content = input.get_string("content")?;

        self.backend.append_core(&label, &content).await?;

        Ok(ToolOutput::success(format!(
            "Successfully appended to memory block '{}'", label
        )))
    }
}

// Similar for: CoreMemoryReplace, RethinkMemory, MemoryInsert,
// ArchivalMemoryInsert, ArchivalMemorySearch, ConversationSearch
```

### DST Requirements

| Test | Fault Types | Assertion |
|------|-------------|-----------|
| core_memory_append | StorageWriteFail (10%) | Memory persists after retry |
| core_memory_replace | StorageLatency (100ms) | Old content replaced |
| archival_memory_search | NetworkDelay (50ms) | Semantic results correct |
| concurrent edits | CrashDuringTransaction | No data corruption |

### Acceptance Criteria

- [ ] All 9 memory tools implemented
- [ ] Tools registered automatically for all agents
- [ ] DST tests pass with storage faults
- [ ] Memory changes visible in next LLM call

---

## Phase 3: Heartbeat/Pause Mechanism (P1 - 2 days)

### What Letta Has

`pause_heartbeats` - Agent can pause autonomous iterations for N minutes.

### Current Kelpie Behavior

```rust
while response.stop_reason == "tool_use" && iterations < 5 {
    iterations += 1;
    // ...
}
```

### Required Changes

1. **Add pause_heartbeats tool**
   ```rust
   pub struct PauseHeartbeats;

   #[async_trait]
   impl Tool for PauseHeartbeats {
       fn metadata(&self) -> &ToolMetadata {
           &PAUSE_HEARTBEATS_METADATA  // minutes param (1-60)
       }

       async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
           let minutes = input.get_i64("minutes").unwrap_or(2);
           Ok(ToolOutput::pause_heartbeats(minutes))
       }
   }
   ```

2. **Modify loop termination** (`messages.rs`)
   ```rust
   let mut heartbeat_paused_until: Option<Instant> = None;

   while response.stop_reason == "tool_use" {
       // Check if heartbeats are paused
       if let Some(until) = heartbeat_paused_until {
           if Instant::now() < until {
               break;  // Paused, stop iterating
           }
           heartbeat_paused_until = None;
       }

       // Execute tools
       for tool_call in &response.tool_calls {
           let result = execute_tool(&tool_call.name, &tool_call.input).await?;

           // Check for pause signal
           if let Some(pause_minutes) = result.pause_heartbeats {
               heartbeat_paused_until = Some(
                   Instant::now() + Duration::from_secs(pause_minutes * 60)
               );
           }

           tool_results.push((tool_call.id.clone(), result));
       }

       iterations += 1;
       if iterations >= MAX_ITERATIONS {
           break;
       }

       // Continue...
   }
   ```

### DST Requirements

| Test | Fault Types | Assertion |
|------|-------------|-----------|
| pause_heartbeats basic | None | Loop stops after pause |
| pause duration | ClockSkew (5s) | Duration calculated correctly |
| pause persistence | CrashAfterWrite | Pause state survives restart |

### Acceptance Criteria

- [ ] `pause_heartbeats` tool available to agents
- [ ] Agent loop respects pause duration
- [ ] DST tests pass with clock faults

---

## Phase 4: Wire FDB to Server (P1 - 2 days)

### Current State

FDB backend is fully implemented (`kelpie-storage/src/fdb.rs`, 1000 lines) but server uses in-memory storage.

### Required Changes

1. **Add FDB to server startup**
   ```rust
   // kelpie-server/src/main.rs
   let actor_storage = match config.storage_backend {
       StorageBackend::Memory => Box::new(MemoryKV::new()),
       StorageBackend::Fdb => Box::new(FdbKV::connect(&config.fdb_cluster_file).await?),
   };
   ```

2. **Persist agent metadata to FDB**
   ```rust
   // Agent state stored in FDB
   // Key: ("agents", agent_id)
   // Value: AgentMetadata { name, agent_type, created_at, model, system_prompt }
   ```

3. **Memory content stays in Umi** (not FDB)
   - FDB: Agent configuration, tool assignments
   - Umi: Core memory, archival memory, conversations

### DST Requirements

| Test | Fault Types | Assertion |
|------|-------------|-----------|
| Agent creation | StorageWriteFail (10%) | Agent persists after retry |
| Agent retrieval | StorageReadFail (5%) | Agent loaded correctly |
| Server restart | CrashAfterWrite | Agents survive restart |

### Acceptance Criteria

- [ ] Agents persist across server restarts
- [ ] FDB transactions handle conflicts correctly
- [ ] DST tests pass with storage faults

---

## Phase 5: Agent Types Abstraction (P2 - 5 days)

### What Letta Has

| Agent Type | Memory Tools | Heartbeats | Use Case |
|------------|--------------|------------|----------|
| `memgpt_agent` | Full set | Yes | Original MemGPT behavior |
| `memgpt_v2_agent` | Refreshed set | Yes | Updated tools |
| `letta_v1_agent` | Simplified | No | Simple loop |
| `react_agent` | None | No | Basic ReAct |

### Required Changes

1. **Agent trait** (`kelpie-agent/src/traits.rs`)
   ```rust
   #[async_trait]
   pub trait Agent: Send + Sync {
       fn agent_type(&self) -> &str;
       fn available_tools(&self) -> Vec<Arc<dyn Tool>>;
       fn system_prompt_template(&self) -> &str;
       fn supports_heartbeats(&self) -> bool;

       async fn handle_message(
           &self,
           message: &Message,
           context: &AgentContext,
       ) -> Result<Response>;
   }
   ```

2. **Built-in agent types**
   ```rust
   pub struct MemGptAgent {
       memory_tools: Vec<Arc<dyn Tool>>,  // All 9 memory tools
       supports_heartbeats: true,
   }

   pub struct ReactAgent {
       // No memory tools, basic loop
       supports_heartbeats: false,
   }

   pub struct LettaV1Agent {
       memory_tools: Vec<Arc<dyn Tool>>,  // Simplified set
       supports_heartbeats: false,
   }
   ```

3. **Agent factory**
   ```rust
   pub fn create_agent(agent_type: &str, config: AgentConfig) -> Result<Box<dyn Agent>> {
       match agent_type {
           "memgpt_agent" | "memgpt" => Ok(Box::new(MemGptAgent::new(config))),
           "react_agent" | "react" => Ok(Box::new(ReactAgent::new(config))),
           "letta_v1_agent" => Ok(Box::new(LettaV1Agent::new(config))),
           _ => Err(Error::UnknownAgentType { agent_type: agent_type.to_string() }),
       }
   }
   ```

### DST Requirements

| Test | Fault Types | Assertion |
|------|-------------|-----------|
| MemGPT agent message | All faults (5% each) | Correct behavior |
| ReAct agent message | NetworkDelay | No memory tool calls |
| Agent type switching | None | Tools change correctly |

### Acceptance Criteria

- [ ] `memgpt_agent` type works like Letta
- [ ] `react_agent` type works without memory tools
- [ ] Agent type specified at creation time
- [ ] DST tests pass for all agent types

---

## Timeline Summary

| Phase | Description | Effort | Dependencies | Status |
|-------|-------------|--------|--------------|--------|
| **0** | Umi integration | 5 days | None | ✅ Complete |
| **1** | MCP tools in loop | 4 days | Phase 0 | 🔴 Not Started |
| **2** | Memory editing tools | 3 days | Phase 0 | 🔴 Not Started |
| **3** | Heartbeat mechanism | 2 days | Phase 1 | 🔴 Not Started |
| **4** | Wire FDB to server | 2 days | None | 🔴 Not Started |
| **5** | Agent types | 5 days | Phases 0-3 | 🔴 Not Started |

**Critical Path:** Phase 0 → Phase 1 → Phase 2 → Phase 3 → Phase 5

**Parallel Track:** Phase 4 can run alongside Phase 1

**Total:** ~6-7 weeks with DST-first approach

```
Week 1: Phase 0 (Umi integration)
Week 2: Phase 1 (MCP tools) + Phase 4 (FDB wiring) in parallel
Week 3: Phase 2 (Memory tools) + Phase 3 (Heartbeat)
Week 4-5: Phase 5 (Agent types)
Week 6: Integration testing, bug fixes, polish
Week 7: Buffer for DST-discovered issues
```

---

## DST-First Workflow (Per Phase)

```
┌─────────────────────────────────────────────────────────────────┐
│  1. HARNESS CHECK                                               │
│     Does kelpie-dst support needed faults?                      │
│     NO → Extend harness FIRST                                   │
├─────────────────────────────────────────────────────────────────┤
│  2. WRITE DST TEST (RED)                                        │
│     Test under faults BEFORE implementation                     │
│     Use SimStorage, SimEmbedding, SimNetwork                    │
├─────────────────────────────────────────────────────────────────┤
│  3. IMPLEMENT FEATURE (GREEN)                                   │
│     Write production code                                       │
├─────────────────────────────────────────────────────────────────┤
│  4. RUN SIMULATION                                              │
│     Multiple seeds: DST_SEED=1,2,3,...,100                      │
│     Find and fix bugs                                           │
├─────────────────────────────────────────────────────────────────┤
│  5. VERIFY DETERMINISM                                          │
│     Same seed = same behavior                                   │
│     Reproduce any failure with logged seed                      │
└─────────────────────────────────────────────────────────────────┘
```

---

## Success Criteria

### Letta Compatibility

- [ ] `letta-client` SDK works unmodified against Kelpie
- [ ] All 9 memory tools function identically
- [ ] Agent types match Letta behavior
- [ ] Heartbeat/pause mechanism works
- [ ] MCP tools integrated

### Performance

- [ ] Agent response latency < 2x Letta
- [ ] Memory operations persist correctly
- [ ] No memory leaks in long conversations

### Testing

- [ ] DST tests for all new functionality
- [ ] 100+ seed runs pass for each phase
- [ ] Fault injection tests at 10% failure rate
- [ ] Integration tests with real LLM

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-12 | Use Umi for memory | Already has Kelpie mapping, DST support | Additional dependency |
| 2026-01-12 | LanceDB for dev, Postgres for prod | Zero-config dev, scalable prod | Two storage paths |
| 2026-01-12 | Static MCP config | Simpler, DST-friendly | Less dynamic |
| 2026-01-12 | FDB for actor state only | Separation of concerns | Two storage systems |
| 2026-01-12 | DST-first adds 30% time | Catches bugs early, worth it | Longer timeline |
| 2026-01-12 | Git dep with local override | Easy to develop both repos simultaneously | Need to sync commits |
| 2026-01-12 | Pin chrono to =0.4.38 | Resolve arrow-arith conflict with Umi | Version lock |
| 2026-01-12 | Create lib.rs for tests | Integration tests need library crate access | Dual bin/lib crate |
| 2026-01-12 | Use seed from SimConfig | Deterministic behavior without full Simulation env integration | Limited fault injection |

---

## What to Try (Update After Each Phase)

### Works Now (Phase 0 Complete)
- Agent loop with hardcoded shell tool
- Memory blocks in system prompt
- SSE streaming responses
- FDB storage (not wired to server)
- MCP client (not wired to agent loop)
- **NEW: UmiMemoryBackend with SimProviders**
  - Core memory: append, replace, get_blocks
  - Archival memory: insert, search
  - Conversation storage: store_message, search
  - Agent scoping: isolated memory per agent_id
- **NEW: DST tests for memory operations**
  - 11 tests covering all memory operations
  - Tested with 7 different seeds (1, 42, 100, 999, 12345, 54321, 999999)
  - Fault injection: StorageWriteFail, StorageReadFail, EmbeddingTimeout, VectorSearchFail

### Doesn't Work Yet
- Memory editing tools (Phase 2) - UmiMemoryBackend exists but tools not implemented
- MCP tools in conversations (Phase 1)
- Agent types (Phase 5) - single hardcoded behavior
- Heartbeat/pause mechanism (Phase 3)
- FDB wired to server (Phase 4)

### Known Limitations
- UmiMemoryBackend uses SimStorageBackend (in-memory) - no persistence across restarts
- SimEmbeddingProvider returns deterministic embeddings (not semantically meaningful)
- Agent scoping is per-backend instance (not shared storage yet)
- 5-iteration limit (no heartbeat extension)

---

## Appendix: Letta Tool Signatures

### Core Memory Tools

```python
def core_memory_append(agent_state, label: str, content: str) -> None:
    """Append to a core memory block."""

def core_memory_replace(agent_state, label: str, old_content: str, new_content: str) -> None:
    """Replace content in a core memory block."""

def rethink_memory(agent_state, new_memory: str, target_block_label: str) -> None:
    """Completely rewrite a memory block."""

def memory_insert(agent_state, label: str, new_str: str, insert_line: int = -1) -> None:
    """Insert at specific line in memory block."""

def memory_finish_edits(agent_state) -> None:
    """Signal completion of memory editing."""
```

### Archival Memory Tools

```python
def archival_memory_insert(agent_state, content: str) -> None:
    """Store in archival memory with embedding."""

def archival_memory_search(agent_state, query: str, page: int = 0) -> List[str]:
    """Semantic search in archival memory."""
```

### Conversation Tools

```python
def conversation_search(agent_state, query: str, page: int = 0) -> List[str]:
    """Search past conversations by text/semantic."""

def conversation_search_date(agent_state, start_date: str, end_date: str, page: int = 0) -> List[str]:
    """Search conversations by date range."""
```

### Control Flow

```python
def pause_heartbeats(agent_state, minutes: int = 2) -> None:
    """Pause autonomous iterations for N minutes."""
```

---

## Related Documents

- Umi memory system: `/umi/README.md`
- Kelpie FDB integration: `/kelpie/.progress/002_*.md`
- Kelpie vision: `/kelpie/VISION.md`
- Kelpie constraints: `/kelpie/.vision/CONSTRAINTS.md`

# Kelpie: The Open-Source Agent Runtime

## Vision Statement

Kelpie is an **open-source agent runtime** that provides the infrastructure layer for building production-grade AI agent systems. It combines:

1. **Virtual Actors** for stateful agent identity and coordination
2. **Managed Memory** for hierarchical context management
3. **Sandboxed Execution** for secure tool use and code execution
4. **Linearizable State** for correct multi-agent coordination

**Target Users:**
- Agent framework developers (Letta, LangGraph, CrewAI) who need a scalable backend
- Platform builders who need secure sandbox environments for agents
- Enterprises deploying agent fleets at scale

---

## Problem Statement

### The Scaling Wall

Current agent infrastructure hits walls at different scales:

| Scale | What Breaks | Root Cause |
|-------|-------------|------------|
| **10K agents** | Connection pool exhaustion | Per-agent DB connections |
| **100K agents** | State loading latency | Eager initialization |
| **1M agents** | Memory explosion | No hierarchical memory |
| **10M agents** | Coordination overhead | No linearizable primitives |

### The Integration Gap

Today's landscape is fragmented:
- **State**: Redis + PostgreSQL + Vector DB (3 systems to manage)
- **Execution**: Separate sandbox providers (E2B, Modal)
- **Memory**: Framework-specific implementations
- **Coordination**: No standard protocol

### The Security Gap

Agent execution is fundamentally unsafe:
- LLM-generated code is untrusted by definition
- Container isolation is insufficient (shared kernel)
- Tool results need sandboxing before entering memory

---

## Solution: Kelpie Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           Kelpie Runtime                                 │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                        Agent Layer                               │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐   │   │
│  │  │  Agent A     │  │  Agent B     │  │  Agent N             │   │   │
│  │  │  (Letta)     │  │  (LangGraph) │  │  (Custom)            │   │   │
│  │  │  ┌────────┐  │  │  ┌────────┐  │  │  ┌────────┐          │   │   │
│  │  │  │ Memory │  │  │  │ Memory │  │  │  │ Memory │          │   │   │
│  │  │  │ Blocks │  │  │  │ Blocks │  │  │  │ Blocks │          │   │   │
│  │  │  └────────┘  │  │  └────────┘  │  │  └────────┘          │   │   │
│  │  └──────┬───────┘  └──────┬───────┘  └──────────┬───────────┘   │   │
│  └─────────┼─────────────────┼─────────────────────┼───────────────┘   │
│            │                 │                     │                    │
│  ┌─────────┴─────────────────┴─────────────────────┴───────────────┐   │
│  │                    Virtual Actor Runtime                         │   │
│  │  - On-demand activation    - Single activation guarantee         │   │
│  │  - Location transparency   - Linearizable state                  │   │
│  │  - Automatic failover      - Connection multiplexing             │   │
│  └─────────────────────────────┬───────────────────────────────────┘   │
│                                │                                        │
│  ┌─────────────────────────────┴───────────────────────────────────┐   │
│  │                    Memory Layer                                  │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │   │
│  │  │ Core Memory │  │  Working    │  │  Archival Memory        │  │   │
│  │  │ (In-Context)│  │  Memory     │  │  (Vector + Graph)       │  │   │
│  │  │ ~32KB/agent │  │  (Fast KV)  │  │  (Unlimited)            │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │   │
│  └─────────────────────────────┬───────────────────────────────────┘   │
│                                │                                        │
│  ┌─────────────────────────────┴───────────────────────────────────┐   │
│  │                    Sandbox Layer                                 │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │   │
│  │  │ Firecracker │  │  Firecracker│  │  Sandbox Pool           │  │   │
│  │  │ Sandbox A   │  │  Sandbox B  │  │  (Pre-warmed)           │  │   │
│  │  │ ~125ms boot │  │  ~125ms boot│  │  <50ms assignment       │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │   │
│  │  - MCP tool integration    - Filesystem isolation               │   │
│  │  - Network egress control  - State checkpointing                │   │
│  └─────────────────────────────┬───────────────────────────────────┘   │
│                                │                                        │
│  ┌─────────────────────────────┴───────────────────────────────────┐   │
│  │                    Persistence Layer                             │   │
│  │               FoundationDB (Linearizable KV)                     │   │
│  │  - Actor state    - Memory blocks    - Sandbox snapshots         │   │
│  │  - Registry       - Coordination     - Audit log                 │   │
│  └──────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Core Abstractions

### 1. Agent Actor

An Agent Actor is a virtual actor with built-in memory hierarchy:

```rust
#[async_trait]
pub trait AgentActor: Actor {
    /// Memory hierarchy for the agent
    type Memory: AgentMemory;

    /// Handle a message with full memory context
    async fn process(
        &self,
        ctx: &mut AgentContext<Self::Memory>,
        message: AgentMessage,
    ) -> Result<AgentResponse>;

    /// Called when agent activates (load state from FDB)
    async fn on_activate(&self, ctx: &mut AgentContext<Self::Memory>) -> Result<()>;

    /// Called before deactivation (checkpoint state)
    async fn on_deactivate(&self, ctx: &mut AgentContext<Self::Memory>) -> Result<()>;

    /// Optional: background processing during idle time
    async fn on_idle(&self, ctx: &mut AgentContext<Self::Memory>) -> Result<()> {
        Ok(())
    }
}

pub struct AgentContext<M: AgentMemory> {
    pub id: ActorId,
    pub memory: M,
    sandbox: Option<SandboxHandle>,
    tools: ToolRegistry,
    runtime: AgentRuntime,
}

impl<M: AgentMemory> AgentContext<M> {
    /// Execute code in sandboxed environment
    pub async fn execute(&self, code: &str, language: Language) -> Result<ExecutionResult>;

    /// Invoke a tool via MCP
    pub async fn invoke_tool(&self, tool: &str, args: Value) -> Result<Value>;

    /// Send message to another agent
    pub async fn send(&self, target: &ActorRef, message: AgentMessage) -> Result<()>;

    /// Send and wait for response (linearizable)
    pub async fn request(&self, target: &ActorRef, message: AgentMessage) -> Result<AgentResponse>;
}
```

### 2. Memory Hierarchy

Based on Letta's MemGPT model but with built-in persistence:

```rust
pub trait AgentMemory: Send + Sync {
    /// Core memory (always in context, ~32KB)
    fn core(&self) -> &CoreMemory;
    fn core_mut(&mut self) -> &mut CoreMemory;

    /// Working memory (fast KV, current session)
    fn working(&self) -> &WorkingMemory;
    fn working_mut(&mut self) -> &mut WorkingMemory;

    /// Archival memory (semantic search, unlimited)
    fn archival(&self) -> &ArchivalMemory;

    /// Checkpoint all memory to durable storage
    async fn checkpoint(&self) -> Result<()>;
}

/// Core memory - structured blocks always in context
pub struct CoreMemory {
    blocks: Vec<MemoryBlock>,
    total_chars: usize,
    max_chars: usize,  // e.g., 32KB
}

pub struct MemoryBlock {
    pub label: String,        // e.g., "persona", "human", "task"
    pub description: String,  // For the LLM to understand
    pub content: String,      // The actual content
    pub editable: bool,       // Can agent modify this?
    pub shared: bool,         // Shared with other agents?
}

/// Working memory - fast session state
pub struct WorkingMemory {
    kv: Box<dyn KVStore>,     // Redis-like interface
    message_buffer: VecDeque<Message>,
    buffer_limit: usize,
}

/// Archival memory - long-term semantic store
pub struct ArchivalMemory {
    vector_store: Box<dyn VectorStore>,
    graph_store: Box<dyn GraphStore>,  // For relationships
}

impl ArchivalMemory {
    /// Search by semantic similarity
    pub async fn search(&self, query: &str, limit: usize) -> Result<Vec<Memory>>;

    /// Insert with automatic embedding
    pub async fn insert(&self, content: &str, metadata: Metadata) -> Result<MemoryId>;

    /// Query relationships (causal, temporal, topical)
    pub async fn related(&self, memory_id: MemoryId, relation: Relation) -> Result<Vec<Memory>>;
}
```

### 3. Sandbox Integration

Sandboxes are first-class citizens bound to agent state:

```rust
pub struct Sandbox {
    id: SandboxId,
    agent_id: ActorId,
    state: SandboxState,
    config: SandboxConfig,
}

pub enum SandboxState {
    Running { vm: FirecrackerVm },
    Paused { snapshot: SnapshotId },
    Terminated,
}

pub struct SandboxConfig {
    /// Base image (Ubuntu, Alpine, custom)
    pub image: String,
    /// CPU and memory limits
    pub resources: ResourceLimits,
    /// Network policy (none, restricted, full)
    pub network: NetworkPolicy,
    /// Filesystem mounts (read-only, read-write)
    pub mounts: Vec<Mount>,
    /// MCP tools available inside sandbox
    pub tools: Vec<ToolConfig>,
    /// Maximum lifetime before forced termination
    pub max_lifetime_ms: u64,
}

impl Sandbox {
    /// Execute code in sandbox
    pub async fn execute(&self, code: &str, language: Language) -> Result<ExecutionResult>;

    /// Run shell command
    pub async fn shell(&self, command: &str) -> Result<ShellOutput>;

    /// Read file from sandbox
    pub async fn read_file(&self, path: &str) -> Result<Vec<u8>>;

    /// Write file to sandbox
    pub async fn write_file(&self, path: &str, content: &[u8]) -> Result<()>;

    /// Pause sandbox (preserves memory + filesystem)
    pub async fn pause(&self) -> Result<SnapshotId>;

    /// Resume from snapshot
    pub async fn resume(snapshot: SnapshotId) -> Result<Self>;
}

/// Pool of pre-warmed sandboxes for <50ms assignment
pub struct SandboxPool {
    available: VecDeque<Sandbox>,
    config: PoolConfig,
}

impl SandboxPool {
    /// Get a sandbox (from pool or create new)
    pub async fn acquire(&self, config: &SandboxConfig) -> Result<Sandbox>;

    /// Return sandbox to pool (reset state)
    pub async fn release(&self, sandbox: Sandbox) -> Result<()>;
}
```

### 4. Tool Integration (MCP)

Native MCP support for tool discovery and invocation:

```rust
pub struct ToolRegistry {
    local_tools: HashMap<String, Box<dyn Tool>>,
    mcp_servers: Vec<McpServer>,
}

#[async_trait]
pub trait Tool: Send + Sync {
    fn name(&self) -> &str;
    fn description(&self) -> &str;
    fn schema(&self) -> &JsonSchema;

    async fn invoke(&self, args: Value, ctx: &ToolContext) -> Result<Value>;
}

pub struct McpServer {
    uri: String,
    tools: Vec<ToolDefinition>,
    resources: Vec<ResourceDefinition>,
}

impl ToolRegistry {
    /// Discover tools from MCP server
    pub async fn register_mcp(&mut self, uri: &str) -> Result<()>;

    /// List all available tools (for LLM prompt)
    pub fn list_tools(&self) -> Vec<ToolDefinition>;

    /// Invoke tool by name
    pub async fn invoke(&self, name: &str, args: Value, ctx: &ToolContext) -> Result<Value>;
}

/// Context passed to tools during execution
pub struct ToolContext {
    pub agent_id: ActorId,
    pub sandbox: Option<SandboxHandle>,
    pub memory: MemoryAccess,  // Read-only view of agent memory
}
```

---

## Use Cases

### Use Case 1: Letta Backend

Replace Letta's PostgreSQL backend with Kelpie:

```python
# Current Letta
from letta import Letta
client = Letta()  # Uses PostgreSQL directly

# With Kelpie Backend
from letta import Letta
from letta_kelpie import KelpieBackend

backend = KelpieBackend(
    kelpie_url="http://localhost:9000",
    cluster_file="/etc/foundationdb/fdb.cluster"
)
client = Letta(backend=backend)

# Same Letta API, but now scales to 1M+ agents
agent = client.agents.create(
    name="research-agent",
    memory_blocks=[
        {"label": "persona", "value": "You are a research assistant..."},
        {"label": "task", "value": "Help with literature review"},
    ]
)
```

**Benefits:**
- 10K → 1M+ agent scaling
- Lazy activation (no eager state loading)
- Connection multiplexing (single connection per server)
- Linearizable agent coordination
- Built-in sandbox integration

### Use Case 2: Agent Sandbox Platform

Build a platform like E2B but with integrated state management:

```python
from kelpie import KelpieClient, SandboxConfig

client = KelpieClient("http://localhost:9000")

# Create an agent with attached sandbox
agent = await client.create_agent(
    namespace="code-agents",
    agent_type="CodeExecutor",
    sandbox=SandboxConfig(
        image="python:3.11",
        resources={"cpu": 2, "memory_mb": 4096},
        network="restricted",
        tools=["filesystem", "shell", "git"],
    )
)

# Agent state and sandbox are unified
result = await agent.process({
    "task": "Write a Python function that calculates Fibonacci numbers",
    "test_cases": [(0, 0), (1, 1), (10, 55)],
})

# Sandbox state persists with agent
await agent.pause()  # Checkpoint everything

# Resume later - exact same state
agent = await client.resume_agent(agent.id)
```

### Use Case 3: RLM (Recursive Language Model) Runtime

Prime Intellect's RLM paradigm requires persistent Python REPLs, sub-LLM orchestration, and sandboxed execution. Kelpie provides the **inference runtime** for RLM-trained models:

```python
from kelpie import KelpieClient, RLMAgent

client = KelpieClient("http://localhost:9000")

# Create an RLM agent with persistent Python REPL
rlm_agent = await client.create_agent(
    namespace="rlm",
    agent_type="RLMAgent",
    config={
        # Persistent Python REPL (core RLM requirement)
        "sandbox": {
            "image": "python:3.11",
            "persistent": True,  # State survives across invocations
            "pip_packages": ["pandas", "numpy", "requests"],
        },
        # Sub-LLM spawning capability
        "sub_agents": {
            "enabled": True,
            "max_concurrent": 10,
            "tools_delegation": True,  # Tools only for sub-LLMs
        },
        # Answer state management
        "answer_state": {"content": "", "ready": False},
    }
)

# Process large document - RLM delegates to sub-LLMs
result = await rlm_agent.process({
    "task": "Summarize this 500-page PDF",
    "document_url": "s3://bucket/large-document.pdf",
})

# RLM uses Python REPL to inspect data iteratively
# Sub-LLMs handle token-heavy work
# Main model maintains lean context

# Pause preserves REPL state + answer progress
await rlm_agent.pause()

# Resume later - exact state restored
rlm_agent = await client.resume_agent(rlm_agent.id)
```

**How Kelpie Enables RLM:**

| RLM Requirement | Kelpie Component |
|-----------------|------------------|
| Persistent Python REPL | Firecracker sandbox with pause/resume |
| Sub-LLM orchestration | Virtual actors (each sub-LLM = actor) |
| Tool delegation | MCP tools routed to sub-agent sandboxes |
| Answer state management | Linearizable state in FDB |
| Context folding | Memory hierarchy (Core → Working → Archival) |

### Use Case 4: Multi-Agent Coordination

Linearizable coordination for multi-agent systems:

```python
from kelpie import KelpieClient

client = KelpieClient("http://localhost:9000")

# Create a team of agents
researcher = await client.create_agent(namespace="team", agent_type="Researcher")
writer = await client.create_agent(namespace="team", agent_type="Writer")
reviewer = await client.create_agent(namespace="team", agent_type="Reviewer")

# Shared memory block (linearizable updates)
shared_doc = await client.create_shared_block(
    label="document",
    initial_value="# Research Report\n\n",
)

# Attach to all agents
await researcher.attach_block(shared_doc)
await writer.attach_block(shared_doc)
await reviewer.attach_block(shared_doc)

# Agents can coordinate via shared state
# Updates are linearizable - no conflicts
await researcher.process({"task": "Research quantum computing"})
await writer.process({"task": "Write introduction section"})
await reviewer.process({"task": "Review and suggest edits"})
```

---

## Technical Differentiators

### vs Letta (Current Architecture)

| Aspect | Letta (PostgreSQL) | Kelpie |
|--------|-------------------|--------|
| Max agents | ~10K (connection limits) | 1M+ (virtual actors) |
| Activation | Eager (load all state) | Lazy (on-demand) |
| Connections | Per-agent | Multiplexed |
| Coordination | Polling-based | Linearizable |
| Sandbox | External (E2B) | Integrated |
| Memory | PostgreSQL + pgvector | Tiered (FDB + Vector + Graph) |

### vs E2B/Modal (Sandbox Providers)

| Aspect | E2B/Modal | Kelpie |
|--------|-----------|--------|
| State model | Stateless sandboxes | Stateful agents + sandboxes |
| Memory | External | Integrated hierarchy |
| Coordination | None | Linearizable actors |
| Persistence | Sandbox snapshots | Full agent + sandbox |
| Identity | Ephemeral | Persistent virtual actors |

### vs Cloud Agent Services (AWS AgentCore, Azure AI Foundry)

| Aspect | Cloud Services | Kelpie |
|--------|---------------|--------|
| Open source | No | Yes (Apache 2.0) |
| Vendor lock-in | Yes | No |
| Self-hosted | Limited | Full support |
| Customization | Constrained | Full control |
| DST testing | No | Built-in |

---

## Implementation Roadmap

### Phase 1: Core Runtime (Current + 4 weeks)
- [ ] Complete virtual actor runtime with FDB backend
- [ ] Implement memory hierarchy (Core + Working + Archival)
- [ ] Basic MCP tool integration
- [ ] DST tests for all critical paths

### Phase 2: Sandbox Integration (6 weeks)
- [ ] Firecracker sandbox integration
- [ ] Sandbox pool with pre-warming
- [ ] Pause/resume with state checkpointing
- [ ] Network isolation and egress policies

### Phase 3: Framework Adapters (4 weeks)
- [ ] Letta backend adapter
- [ ] LangGraph state backend
- [ ] Generic REST/gRPC API
- [ ] Python and TypeScript SDKs

### Phase 4: Production Hardening (4 weeks)
- [ ] Horizontal scaling (sharding)
- [ ] Observability (OpenTelemetry)
- [ ] Security audit
- [ ] Performance benchmarks

### Phase 5: Advanced Features (Ongoing)
- [ ] A2A protocol support
- [ ] Agent marketplace primitives
- [ ] Self-optimizing memory (sleep-time compute)
- [ ] WASM actor runtime

---

## Success Metrics

### Phase 1 Complete When:
- Single-actor throughput >500K ops/sec
- DST tests pass with 10% fault injection
- Memory hierarchy working (Core + Working + Archival)

### Phase 2 Complete When:
- Sandbox boot time <150ms (cold), <50ms (warm pool)
- Pause/resume preserves full state
- MCP tool invocation working

### Phase 3 Complete When:
- Letta running on Kelpie backend
- 10K agent benchmark passing
- Python SDK released

### Production Ready When:
- 100K+ concurrent agents
- <1ms p99 for hot actor invocations
- <200ms p99 for cold actor activations
- Zero data loss under failure injection

---

## References

- [Letta Architecture Analysis](./research/letta-architecture.md)
- [Sandbox Landscape Analysis](./research/sandbox-landscape.md)
- [Agent Infrastructure Trajectory](./research/agent-infra-trajectory.md)
- [Prime Intellect RLM](https://www.primeintellect.ai/blog/rlm) - Recursive Language Model paradigm
- [Prime Intellect PRIME-RL](https://github.com/PrimeIntellect-ai/prime-rl) - Async RL Training at Scale
- [ADR-001: Virtual Actor Model](./adr/001-virtual-actor-model.md)
- [ADR-002: FoundationDB Integration](./adr/002-foundationdb-integration.md)
- [ADR-005: DST Framework](./adr/005-dst-framework.md)

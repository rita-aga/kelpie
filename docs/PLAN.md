# Kelpie: The Open-Source Agent Runtime

## Revised Vision (January 2025)

**Kelpie** has evolved from a generic virtual actor system to an **open-source agent runtime** - the infrastructure layer for building production-grade AI agent systems.

### Core Insight

Research into Letta.ai, E2B, and the agent infrastructure landscape revealed:

1. **Letta hits a wall at 10K agents** - PostgreSQL connection exhaustion, eager state loading, no connection multiplexing
2. **Sandbox providers are stateless** - E2B/Modal don't integrate with agent memory
3. **No unified open-source alternative** to cloud agent services (AWS AgentCore, Azure AI Foundry)

### The Opportunity

Position Kelpie as the **open-source agent runtime** that provides:
- **Scalable backend for Letta** (and other agent frameworks)
- **Integrated sandbox execution** (like E2B but with state continuity)
- **Linearizable multi-agent coordination**

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           Kelpie Runtime                                 │
├─────────────────────────────────────────────────────────────────────────┤
│  Agent Layer: Virtual actors with memory hierarchy                       │
│  - On-demand activation (lazy, not eager)                               │
│  - Connection multiplexing (not per-agent connections)                   │
│  - Linearizable state (single activation guarantee)                      │
├─────────────────────────────────────────────────────────────────────────┤
│  Memory Layer: Hierarchical context management                           │
│  - Core Memory (~32KB in-context, always loaded)                        │
│  - Working Memory (Redis-like fast KV)                                   │
│  - Archival Memory (Vector + Graph, semantic search)                     │
├─────────────────────────────────────────────────────────────────────────┤
│  Sandbox Layer: Secure tool execution                                    │
│  - Firecracker microVMs (~125ms boot, <5MB overhead)                    │
│  - Pre-warmed pools (<50ms assignment)                                   │
│  - MCP tool integration                                                  │
│  - Pause/resume with full state                                          │
├─────────────────────────────────────────────────────────────────────────┤
│  Persistence Layer: FoundationDB                                         │
│  - Actor state, memory blocks, sandbox snapshots                         │
│  - Linearizable transactions                                             │
│  - Automatic sharding                                                    │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Updated Crate Structure

```
kelpie/
├── crates/
│   ├── kelpie-core/          # Core types, errors, constants (DONE)
│   ├── kelpie-dst/           # DST framework (DONE)
│   ├── kelpie-storage/       # Per-actor KV storage (DONE)
│   ├── kelpie-runtime/       # Actor runtime and dispatcher
│   │
│   ├── kelpie-memory/        # NEW: Memory hierarchy
│   │   ├── core.rs           # Core memory (in-context blocks)
│   │   ├── working.rs        # Working memory (fast KV)
│   │   ├── archival.rs       # Archival memory (vector + graph)
│   │   └── checkpoint.rs     # Memory checkpointing
│   │
│   ├── kelpie-sandbox/       # NEW: Sandbox integration
│   │   ├── firecracker.rs    # Firecracker VM management
│   │   ├── pool.rs           # Pre-warmed sandbox pool
│   │   ├── snapshot.rs       # Pause/resume snapshots
│   │   └── isolation.rs      # Network/filesystem isolation
│   │
│   ├── kelpie-tools/         # NEW: MCP tool integration
│   │   ├── mcp.rs            # MCP client implementation
│   │   ├── registry.rs       # Tool discovery and registration
│   │   └── builtin.rs        # Built-in tools (shell, fs, etc.)
│   │
│   ├── kelpie-registry/      # Actor placement and discovery
│   ├── kelpie-cluster/       # Cluster coordination
│   ├── kelpie-agent/         # Agent actor abstractions
│   ├── kelpie-wasm/          # WASM actor runtime
│   ├── kelpie-server/        # Standalone server binary
│   └── kelpie-cli/           # CLI tools
│
├── adapters/                  # NEW: Framework adapters
│   ├── letta/                 # Letta backend adapter
│   ├── langgraph/             # LangGraph state backend
│   └── sdk/                   # Python/TypeScript SDKs
│
└── docs/
    ├── adr/                   # Architecture decisions
    ├── VISION.md              # NEW: Detailed vision document
    └── research/              # Research summaries
```

---

## Primary Goals (Updated)

1. **Scalable Letta Backend** - Replace PostgreSQL, scale to 1M+ agents
2. **Integrated Sandbox Execution** - Firecracker VMs with state continuity
3. **Memory Hierarchy** - Core/Working/Archival memory tiers
4. **Linearizable Coordination** - Multi-agent state sharing
5. **MCP Tool Integration** - Native Model Context Protocol support

---

## Success Metrics (Updated)

| Metric | Target | Rationale |
|--------|--------|-----------|
| Concurrent agents | 1M+ | 100x Letta's current limit |
| Hot actor invocation | <1ms p99 | Fast for in-memory state |
| Cold actor activation | <200ms p99 | Acceptable for first message |
| Sandbox cold start | <150ms | Match E2B performance |
| Sandbox warm start | <50ms | Pre-warmed pool |
| Memory checkpoint | <10ms | Fast persistence |
| DST coverage | 100% critical paths | FoundationDB-grade reliability |

---

## Implementation Phases (Revised)

### Phase 0: Bootstrap [COMPLETE]
- [x] Create GitHub repo nerdsane/kelpie
- [x] Initialize Cargo workspace
- [x] Create kelpie-core with types and constants
- [x] Create kelpie-dst with DST framework
- [x] Create kelpie-storage with KV abstraction
- [x] Set up CI (GitHub Actions)
- [x] Create ADRs and documentation

### Phase 1: Actor Runtime (Weeks 1-2)
- [ ] Implement Actor trait and ActorContext
- [ ] Implement Dispatcher (single-threaded per actor)
- [ ] Implement activation/deactivation lifecycle
- [ ] Connection multiplexing (not per-actor connections)
- [ ] DST tests for actor lifecycle
- [ ] Stateright model for single activation

**Deliverable:** Working single-node actor runtime

### Phase 2: Memory Hierarchy (Weeks 3-4)
- [ ] Core Memory (in-context blocks, ~32KB)
- [ ] Working Memory (Redis-like fast KV)
- [ ] Archival Memory (vector store integration)
- [ ] Memory checkpointing to FDB
- [ ] Memory search (semantic + temporal)
- [ ] DST tests for memory operations

**Deliverable:** Letta-compatible memory hierarchy

### Phase 3: Sandbox Integration (Weeks 5-7)
- [ ] Firecracker VM integration
- [ ] Sandbox lifecycle (create/start/pause/resume/kill)
- [ ] Pre-warmed sandbox pool
- [ ] Filesystem and network isolation
- [ ] State checkpointing (memory + filesystem)
- [ ] DST tests for sandbox operations

**Deliverable:** Integrated sandbox execution

### Phase 4: Tool Integration (Weeks 8-9)
- [ ] MCP client implementation
- [ ] Tool registry and discovery
- [ ] Built-in tools (shell, filesystem, git)
- [ ] Tool execution in sandbox
- [ ] Tool result validation and sandboxing

**Deliverable:** MCP-compatible tool system

### Phase 5: Cluster Mode (Weeks 10-12)
- [ ] Node lifecycle and membership
- [ ] Heartbeat and failure detection
- [ ] Actor migration on failure
- [ ] Inter-node RPC
- [ ] Horizontal sharding
- [ ] DST tests for partitions and failures

**Deliverable:** Multi-node cluster

### Phase 6: Framework Adapters (Weeks 13-14)
- [ ] Letta backend adapter
- [ ] Python SDK
- [ ] REST/gRPC API
- [ ] Integration tests with real Letta

**Deliverable:** Letta running on Kelpie

### Phase 7: Production Hardening (Weeks 15-16)
- [ ] Observability (OpenTelemetry)
- [ ] Security audit
- [ ] Performance benchmarks
- [ ] Documentation and guides

**Deliverable:** Production-ready release

---

## Key Technical Decisions

### Why Firecracker for Sandboxes?
- **Security**: VM-level isolation (not shared kernel like containers)
- **Performance**: ~125ms boot, <5MB memory overhead
- **Proven**: Powers AWS Lambda, widely used in production
- **Snapshotting**: Built-in pause/resume support

### Why Memory Hierarchy (not just PostgreSQL)?
- **Tiered access**: Core (always loaded) vs Archival (on-demand)
- **Semantic search**: Vector embeddings for relevant memory retrieval
- **Graph relationships**: Causal, temporal, topical connections
- **Efficient persistence**: Only checkpoint what changed

### Why MCP for Tools?
- **Industry standard**: Adopted by OpenAI, Microsoft, Google, Anthropic
- **Ecosystem**: Thousands of MCP servers available
- **Composability**: Tools from multiple providers
- **Security**: Sandboxed execution with defined interfaces

### Why FoundationDB?
- **Linearizability**: Critical for single activation guarantee
- **Proven at scale**: Apple, Snowflake, etc.
- **Transaction support**: ACID for actor state
- **Automatic sharding**: Horizontal scaling without manual partitioning

---

## Research Insights

### From Letta Analysis
- PostgreSQL connection pool exhaustion at 10K agents
- Eager state loading creates startup latency
- No connection multiplexing (each agent = new connections)
- Memory hierarchy is right model but wrong implementation

### From Sandbox Analysis
- Firecracker is gold standard for agent sandboxes
- State persistence (pause/resume) is critical for long-running agents
- MCP becoming the standard for tool integration
- Defense-in-depth security is mandatory

### From Infrastructure Trajectory
- Memory becoming a managed service
- MCP + A2A becoming "HTTP for agents"
- Agent runtimes emerging as new category
- Cloud providers building pieces but no unified open-source alternative

---

## Competitive Positioning

| Feature | Kelpie | Letta | E2B | AWS AgentCore |
|---------|--------|-------|-----|---------------|
| Open source | Yes | Yes | Yes | No |
| Virtual actors | Yes | No | No | No |
| Memory hierarchy | Yes | Yes | No | Yes |
| Integrated sandbox | Yes | No | Yes | Yes |
| Linearizable state | Yes | No | No | Unknown |
| DST testing | Yes | No | No | No |
| Self-hosted | Yes | Yes | Yes | Limited |

---

## Next Steps

1. **Complete Phase 1** (Actor Runtime) - 2 weeks
2. **Begin Phase 2** (Memory Hierarchy) - Parallel with Phase 1 completion
3. **Create detailed ADRs** for memory and sandbox architecture
4. **Prototype Letta adapter** to validate integration path

---

## References

- [VISION.md](../docs/VISION.md) - Detailed vision document
- [Letta Architecture Analysis](../docs/research/letta-architecture.md)
- [Sandbox Landscape Analysis](../docs/research/sandbox-landscape.md)
- [Agent Infrastructure Trajectory](../docs/research/agent-infra-trajectory.md)

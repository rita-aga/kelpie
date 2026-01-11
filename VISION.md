# Kelpie Vision

## What is Kelpie?

Kelpie is an **open-source agent runtime** that provides stateful, sandboxed execution for AI agents. It combines the virtual actor model with a hierarchical memory system, enabling agents that persist state, execute tools safely, and coordinate with other agents.

## Core Principles

### 1. Stateful by Default

Unlike stateless function-as-a-service platforms, Kelpie treats state as a first-class concern:

- **Per-agent state** persists automatically across invocations
- **Memory hierarchy** provides in-context, working, and archival storage tiers
- **Checkpointing** enables pause/resume of agent execution

### 2. Safety First (TigerStyle)

Following TigerBeetle's engineering philosophy: **Safety > Performance > Developer Experience**

- Explicit limits with units in names (`MEMORY_BYTES_MAX`, `TIMEOUT_MS`)
- 2+ assertions per non-trivial function
- No silent truncation or implicit conversions
- Deterministic simulation testing for all critical paths

### 3. MCP-Native Tool Ecosystem

The Model Context Protocol (MCP) is the standard for tool integration:

- All external tools are MCP servers (stdio, HTTP, or SSE transport)
- Tool discovery, schema validation, and execution handled uniformly
- No custom tool abstraction layer - MCP is the abstraction

### 4. Progressive Isolation

Sandbox isolation scales with trust requirements:

| Level | Implementation | Use Case |
|-------|---------------|----------|
| None | Direct execution | Trusted internal tools |
| Process | OS process isolation | Semi-trusted code |
| VM | Firecracker microVM | Untrusted user code |

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                           Client SDKs                               │
│                    (Python, TypeScript, REST)                       │
└─────────────────────────────────┬───────────────────────────────────┘
                                  │
┌─────────────────────────────────┴───────────────────────────────────┐
│                         Kelpie Server                               │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────────┐  │
│  │  REST API    │  │  LLM Client  │  │  Tool Registry (MCP)     │  │
│  │  (Axum)      │  │  (Claude/GPT)│  │  (stdio, HTTP, SSE)      │  │
│  └──────┬───────┘  └──────┬───────┘  └──────────┬───────────────┘  │
│         │                 │                      │                  │
│  ┌──────┴─────────────────┴──────────────────────┴───────────────┐  │
│  │                      Agent Runtime                             │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐    │  │
│  │  │  Dispatcher │  │  Registry   │  │  Sandbox Pool       │    │  │
│  │  │  (actors)   │  │  (placement)│  │  (Process/Firecracker)   │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘    │  │
│  └───────────────────────────┬───────────────────────────────────┘  │
│                              │                                      │
│  ┌───────────────────────────┴───────────────────────────────────┐  │
│  │                     Memory System                              │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐    │  │
│  │  │ Core Memory │  │  Working    │  │  Archival Memory    │    │  │
│  │  │ (32KB ctx)  │  │  Memory(KV) │  │  (Vector Search)    │    │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘    │  │
│  └───────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────┬───────────────────────────────────┘
                                  │
┌─────────────────────────────────┴───────────────────────────────────┐
│                        Storage Backend                              │
│           (In-Memory / FoundationDB / PostgreSQL)                   │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Memory Hierarchy

Kelpie implements a three-tier memory system inspired by Letta/MemGPT:

### Core Memory (~32KB)
- Always included in LLM context window
- Contains: system prompt, persona, user info, key facts
- Structured as labeled blocks with size limits
- Agent can read/write via memory tools

### Working Memory (Unbounded KV)
- Fast key-value store for session state
- Redis-like operations: get, set, delete, incr, append
- TTL support for temporary data
- Not included in LLM context (must be explicitly retrieved)

### Archival Memory (Vector Store)
- Long-term storage with semantic search
- Embeddings generated locally or via API
- Used for: conversation history, learned facts, documents
- Pagination for large result sets

---

## What Kelpie Is NOT

### Not a Model Router
Kelpie doesn't route between LLM providers or manage model selection. Use LiteLLM, OpenRouter, or similar for that.

### Not a Prompt Framework
Kelpie doesn't provide prompt templates, chains, or DAGs. Use LangChain, DSPy, or similar for that.

### Not a Vector Database
Kelpie's archival memory is for agent state, not general-purpose vector search. Use Pinecone, Weaviate, or similar for that.

### Not a Workflow Engine
Kelpie doesn't orchestrate multi-step workflows with branches and conditions. Use Temporal, Prefect, or similar for that.

---

## Target Use Cases

### 1. Letta-Compatible Backend
Drop-in replacement for Letta server with:
- Same REST API endpoints
- Same memory block semantics
- Compatible Python/TypeScript SDKs

### 2. Agent Sandbox Platform
Like E2B or Modal, but stateful:
- Agents can pause/resume execution
- State persists across sandbox restarts
- Secure isolation via Firecracker VMs

### 3. Multi-Agent Coordination
Agents that work together:
- Message passing between agents
- Shared archival memory
- Consistent state via linearizable storage

### 4. Persistent Tool Execution
Long-running tool operations:
- Python REPL that persists between calls
- Browser sessions that survive agent restarts
- File system state that accumulates

---

## Implementation Status

### Complete

| Component | Status | Notes |
|-----------|--------|-------|
| Actor Runtime | Complete | Dispatcher, single-activation, state persistence |
| Core Memory | Complete | Blocks, labels, size limits, rendering |
| Working Memory | Complete | KV store with TTL, transactions |
| Process Sandbox | Complete | OS isolation, exec, environment |
| Firecracker Sandbox | Complete | VM lifecycle, snapshots, vsock |
| MCP Client | Complete | stdio, HTTP, SSE transports |
| Tool Registry | Complete | Registration, discovery, execution |
| REST API | Complete | Agents, blocks, messages endpoints |
| LLM Integration | Complete | Anthropic, OpenAI support |
| TCP Transport | Complete | Cluster node communication |
| OpenTelemetry | Complete | OTLP export, tracing |
| Vector Search | Complete | Cosine similarity, semantic queries |
| DST Framework | Complete | Fault injection, deterministic replay |
| Local Embeddings | Complete | Fastembed integration (optional feature) |
| Server Wire-up | Complete | Tools, archival memory, capabilities endpoints |
| Letta Adapter | Complete | letta-code compatible (ADR-006) |

### Not Started

| Component | Priority | Notes |
|-----------|----------|-------|
| FoundationDB Backend | P0 | Critical for persistence |
| Agent Framework | P0 | Critical for SDK usability |
| Authentication | P1 | Required for production |
| PostgreSQL Backend | P2 | Alternative to FDB |
| WASM Actors | P3 | Nice-to-have |

---

## Design Decisions

### Why Virtual Actors?

The virtual actor model (Orleans, NOLA) provides:
- **Location transparency**: Call any actor without knowing its location
- **Single activation**: At most one instance exists at any time
- **Automatic lifecycle**: Actors activate on demand, deactivate when idle

This maps perfectly to AI agents: each agent is an actor with identity, state, and message handling.

### Why MCP for Tools?

Model Context Protocol provides:
- **Standard schema**: JSON Schema for inputs, structured outputs
- **Multiple transports**: stdio for local, HTTP/SSE for remote
- **Discovery**: List available tools without hardcoding
- **Ecosystem**: Growing library of MCP servers

Custom tool abstractions add complexity without benefit.

### Why Firecracker?

Firecracker microVMs provide:
- **Strong isolation**: Hardware-level separation via KVM
- **Fast boot**: ~125ms cold start
- **Snapshots**: Pause/resume VM state instantly
- **Minimal footprint**: <5MB memory overhead

For untrusted agent code, process isolation isn't sufficient.

### Why Not Kubernetes?

Kubernetes is designed for stateless microservices. Kelpie needs:
- **Sub-second activation**: K8s pod startup is too slow
- **Fine-grained state**: Per-actor, not per-pod
- **Deterministic testing**: K8s adds non-determinism

Kelpie can run ON Kubernetes, but doesn't use it for actor scheduling.

---

## Performance Targets

| Metric | Target | Current |
|--------|--------|---------|
| Agent activation | <10ms | ~5ms (in-memory) |
| Message latency | <100ms | ~50ms (LLM call excluded) |
| Memory block read | <1ms | <1ms |
| Sandbox exec | <50ms | ~30ms (process) |
| Snapshot/restore | <500ms | Implemented (Firecracker) |
| Vector search (1M) | <100ms | ~10ms (in-memory) |
| Local embedding | <50ms | ~30ms (all-MiniLM-L6-v2) |

## Test Coverage

| Category | Test Count | Status |
|----------|------------|--------|
| Core types | 25 | ✅ Passing |
| Runtime | 29 | ✅ Passing |
| Memory | 81 | ✅ Passing |
| Storage | 43 | ✅ Passing |
| DST Framework | 49 | ✅ Passing |
| Server API | 22 | ✅ Passing |
| Tools | 23 | ✅ Passing |
| **Total** | **300+** | ✅ All Passing |

---

## Roadmap

### Phase 1: Production Foundation (Current)
- [x] Wire new features to REST API (tools, archival, capabilities)
- [x] Local embeddings via fastembed (optional feature)
- [x] Letta API compatibility layer
- [ ] FoundationDB integration for persistence **(P0 - Critical)**
- [ ] Agent framework abstraction (kelpie-agent) **(P0 - Critical)**
- [ ] Authentication and rate limiting **(P1)**

### Phase 2: Framework Integration
- [ ] Letta runtime adapter (full integration, not just API compat)
- [ ] LangGraph state backend
- [ ] CrewAI agent backend
- [ ] PostgreSQL backend alternative **(P2)**

### Phase 3: Scale
- [ ] Multi-node cluster with consensus
- [ ] Actor migration and rebalancing
- [ ] Geo-distributed deployment
- [ ] WASM actor support **(P3)**

### Phase 4: Enterprise
- [ ] Audit logging
- [ ] Role-based access control
- [ ] SOC 2 compliance

---

## Inspiration

- **[NOLA](https://github.com/richardartoul/nola)**: Go virtual actors with linearizability
- **[Orleans](https://github.com/dotnet/orleans)**: .NET virtual actor framework
- **[Letta](https://github.com/letta-ai/letta)**: Stateful agents with memory hierarchy
- **[FoundationDB](https://www.foundationdb.org/)**: Simulation testing pioneer
- **[TigerBeetle](https://github.com/tigerbeetle/tigerbeetle)**: TigerStyle engineering
- **[Firecracker](https://github.com/firecracker-microvm/firecracker)**: Lightweight VMs

---

## Contributing

See [CLAUDE.md](./CLAUDE.md) for development guidelines.

Key principles:
1. No stubs in main branch - features are complete or not merged
2. Tests must pass before commit
3. TigerStyle naming and assertions
4. DST coverage for critical paths

## License

Apache-2.0

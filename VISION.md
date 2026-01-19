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

## Implementation Status

### Phase 0: Bootstrap [COMPLETE]
- [x] Create GitHub repo nerdsane/kelpie
- [x] Initialize Cargo workspace
- [x] Create kelpie-core with types and constants
- [x] Create kelpie-dst with DST framework
- [x] Create kelpie-storage with KV abstraction
- [x] Set up CI (GitHub Actions)
- [x] Create ADRs and documentation

### Phase 1: Actor Runtime [COMPLETE]
- [x] Actor trait with invoke/on_activate/on_deactivate hooks
- [x] Dispatcher with single-threaded per-actor execution
- [x] Activation/deactivation with state persistence via ScopedKV
- [x] Connection multiplexing via bounded mailbox
- [x] DST tests for actor lifecycle (7+ tests)

**Acceptance Criteria Met:**
- `cargo test -p kelpie-runtime` passes all tests
- Actors can be invoked, state persists across deactivation/reactivation
- Single-threaded guarantee verified via dispatcher tests

### Phase 2: Memory Hierarchy [COMPLETE]
- [x] Core Memory (in-context blocks, 32KB default, capacity enforced)
- [x] Working Memory (Redis-like KV with TTL, expiration cleanup)
- [x] Memory checkpointing (serialize/deserialize full state)
- [x] Block management (System, Persona, Human, Facts, Scratch, Custom)
- [x] Text + metadata search with temporal/tag filters

**Acceptance Criteria Met:**
- `cargo test -p kelpie-memory` passes all tests (30+)
- Memory blocks render to XML for LLM context
- Checkpoint roundtrip preserves all state

**Gap:** Semantic/vector search not implemented (text only)

### Phase 3: Sandbox Integration [PARTIAL]
- [x] Sandbox trait with full lifecycle (start/stop/pause/resume/exec)
- [x] MockSandbox for testing (in-memory, configurable handlers)
- [x] ProcessSandbox for real execution (OS process with isolation)
- [x] SandboxPool with pre-warming and acquire/release
- [x] ExecOptions (timeout, workdir, env, output limits)
- [ ] **FirecrackerSandbox** (VM-level isolation) - NOT IMPLEMENTED
- [ ] **VM snapshotting** (pause/resume with memory) - NOT IMPLEMENTED

**Acceptance Criteria NOT Met:**
- ProcessSandbox provides basic isolation but NOT security boundary
- No VM-level isolation for untrusted code
- Snapshot/restore returns error (not implemented)

**To Complete:**
1. Implement FirecrackerSandbox with real VM management
2. Add VM snapshot/restore for pause/resume
3. Verify via: spawn VM, execute code, snapshot, restore, verify state

### Phase 4: Tool Integration [PARTIAL]
- [x] Tool trait with validation, execution, metadata
- [x] ToolRegistry for registration and discovery
- [x] Built-in ShellTool (working with ProcessSandbox)
- [x] Built-in FilesystemTool (read/write/list)
- [x] MCP types and message structures
- [ ] **MCP Client** - STUB (connect/discover/execute are simulated)

**Acceptance Criteria NOT Met:**
- MCP client `connect()` logs "Would connect" but doesn't actually connect
- `discover_tools()` returns cached mock data
- `execute_tool()` returns hardcoded "Mock result"

**To Complete:**
1. Implement real stdio transport (spawn MCP server process)
2. Implement JSON-RPC over stdin/stdout
3. Verify via: connect to real MCP server, discover tools, execute tool

### Phase 5: Cluster Mode [PARTIAL]
- [x] ClusterState lifecycle (Stopped/Starting/Running/Stopping)
- [x] Heartbeat protocol with sequence and timestamps
- [x] Migration protocol (3-phase: Prepare/Transfer/Complete)
- [x] RPC message types (15+ variants)
- [x] MemoryTransport for in-process testing
- [ ] **TCP Transport** - NOT IMPLEMENTED (only in-memory)
- [ ] **Consensus/Leader Election** - NOT IMPLEMENTED

**Acceptance Criteria NOT Met:**
- Cannot run actual multi-node cluster over network
- No leader election or split-brain handling

**To Complete:**
1. Implement TCP-based RpcTransport
2. Test with actual network (2+ processes)
3. Consider Raft for consensus (or document single-leader assumption)

### Phase 6: Framework Adapters [PARTIAL]
- [x] REST API (kelpie-server with full Letta-compatible endpoints)
- [x] Python SDK (full client with agents/blocks/messages)
- [x] TypeScript SDK (full client with types)
- [x] LLM integration (Anthropic/OpenAI with tool calling)
- [ ] **Letta Backend Adapter** - NOT IMPLEMENTED

**Acceptance Criteria NOT Met:**
- SDKs are clients TO Kelpie, not backends FOR Letta
- Cannot run Letta with Kelpie as storage backend

**To Complete:**
1. Create `adapters/letta/` that implements Letta's storage interface
2. Verify via: run Letta, configure Kelpie backend, create agent, send message

### Phase 7: Production Hardening [NOT STARTED]
- [ ] **OpenTelemetry** - NOT IMPLEMENTED
- [ ] **Security audit** - NOT DONE
- [ ] **Performance benchmarks** - NOT DONE
- [x] Documentation (CLAUDE.md with acceptance criteria)

**Acceptance Criteria NOT Met:**
- No tracing/metrics infrastructure
- Performance claims (1M agents, <1ms invocation) unverified

**To Complete:**
1. Add tracing spans to all async operations
2. Add metrics (agent count, invocation latency, memory usage)
3. Run benchmarks and document results
4. Security review of sandbox isolation

---

## What "FULL Implementation" Means

Each phase is COMPLETE when:

### General Criteria (All Phases)
- [ ] All code compiles with `cargo build`
- [ ] All tests pass with `cargo test`
- [ ] No stubs, TODOs, or "not implemented" in code
- [ ] Feature works end-to-end (manually verified)
- [ ] Edge cases tested (empty input, large input, errors)

### Phase-Specific Acceptance

**Phase 3 - Sandbox: FULL means**
```bash
# This must work:
cargo run --example firecracker_sandbox
# 1. Spawns Firecracker VM
# 2. Executes untrusted code in VM
# 3. Snapshots VM state
# 4. Restores from snapshot
# 5. Verifies state preserved
```

**Phase 4 - Tools: FULL means**
```bash
# This must work:
cargo run --example mcp_client
# 1. Connects to real MCP server (e.g., filesystem server)
# 2. Discovers available tools
# 3. Executes a tool
# 4. Returns real result
```

**Phase 5 - Cluster: FULL means**
```bash
# This must work (two terminals):
# Terminal 1:
KELPIE_NODE=node1 cargo run -p kelpie-server -- --port 8283
# Terminal 2:
KELPIE_NODE=node2 cargo run -p kelpie-server -- --port 8284 --join node1:8283

# Verify:
# - Nodes discover each other
# - Actor created on node1 can be invoked from node2
# - Kill node1, actor migrates to node2
```

**Phase 6 - Letta Adapter: FULL means**
```bash
# This must work:
pip install letta
letta configure --backend kelpie --url http://localhost:8283
letta run
# Agent created in Letta uses Kelpie for storage
```

**Phase 7 - Production: FULL means**
- Grafana dashboard showing Kelpie metrics
- Benchmark results documented (agents/sec, latency percentiles)
- Security model documented with threat analysis

---

## Priority Order for Completion

1. **MCP Client** (Phase 4) - Highest value, enables tool ecosystem
2. **TCP Transport** (Phase 5) - Enables real distributed deployment
3. **Letta Adapter** (Phase 6) - Key differentiator per vision
4. **FirecrackerSandbox** (Phase 3) - Production security requirement
5. **OpenTelemetry** (Phase 7) - Production observability
6. **Benchmarks** (Phase 7) - Validate performance claims

---

## Success Metrics

| Metric | Target | Current Status |
|--------|--------|----------------|
| Concurrent agents | 1M+ | Unverified |
| Hot actor invocation | <1ms p99 | Unverified |
| Cold actor activation | <200ms p99 | Unverified |
| Sandbox cold start | <150ms | N/A (no Firecracker) |
| Sandbox warm start | <50ms | ProcessSandbox ~10ms |
| Memory checkpoint | <10ms | Unverified |
| DST coverage | 100% critical paths | Partial |

---

## References

- [CLAUDE.md](../CLAUDE.md) - Development guide with acceptance criteria
- [TigerStyle](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md)
- [Letta Architecture](https://github.com/letta-ai/letta)
- [Firecracker](https://github.com/firecracker-microvm/firecracker)
- [MCP Specification](https://modelcontextprotocol.io/)

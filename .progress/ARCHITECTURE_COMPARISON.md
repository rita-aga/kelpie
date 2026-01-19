# Kelpie vs Letta: Architecture Comparison

**Created:** 2026-01-15 16:15:00
**Context:** Final architecture after Phase 0.5 decision (Double Sandboxing - THE KELPIE WAY)

---

## Executive Summary

| Aspect | Letta | Kelpie |
|--------|-------|--------|
| **Agent Isolation** | ❌ In-process | ✅ **LibkrunSandbox (MicroVM)** |
| **Tool Isolation** | ✅ E2B cloud sandbox | ✅ **Process (inside MicroVM)** |
| **Multi-tenant Security** | Database + RBAC | **Hardware-level (VM isolation)** |
| **Agent Crash Isolation** | ❌ Crashes server | ✅ **Isolated to one VM** |
| **Tool Crash Isolation** | ✅ Isolated | ✅ **Isolated + doesn't crash agent** |
| **Cloud Dependencies** | E2B (optional) | ❌ **None (fully self-hosted)** |
| **Defense in Depth** | ❌ Single layer | ✅ **Double layer (VM + Process)** |

**Verdict:** Kelpie offers **SUPERIOR isolation** with no cloud dependencies.

---

## Visual Architecture Comparison

### Letta Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  Letta Server Process                                       │
│                                                              │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐           │
│  │ Agent 1    │  │ Agent 2    │  │ Agent 3    │           │
│  │ (in-proc)  │  │ (in-proc)  │  │ (in-proc)  │           │
│  │            │  │            │  │            │           │
│  │ Shared     │  │ Shared     │  │ Shared     │           │
│  │ Memory     │  │ Memory     │  │ Memory     │           │
│  └──────┬─────┘  └──────┬─────┘  └──────┬─────┘           │
│         │                │                │                  │
│         └────────────────┴────────────────┘                  │
│                          │                                   │
│                          │ Tool calls                        │
│                          ▼                                   │
│                  ┌───────────────┐                          │
│                  │  E2B Cloud    │                          │
│                  │  Sandbox      │                          │
│                  │  (external)   │                          │
│                  └───────────────┘                          │
└─────────────────────────────────────────────────────────────┘

Issues:
- Agent crash → Server crash (all agents down)
- Agent memory leak → Affects all agents
- Agent CPU spike → Starves all agents
- Shared memory space → Security risk
- E2B dependency → Must trust third party
```

### Kelpie Architecture (THE KELPIE WAY)

```
┌─────────────────────────────────────────────────────────────┐
│  Kelpie Server Process (Coordinator)                        │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  LibkrunSandbox (Agent 1's MicroVM)                  │  │
│  │  ────────────────────────────────────────────────    │  │
│  │  Hardware-level isolation (KVM/HVF)                  │  │
│  │  512MB RAM, 2 vCPUs, Network isolated               │  │
│  │                                                       │  │
│  │  ┌────────────────────────────────────────────────┐ │  │
│  │  │ Agent 1 Runtime (PID 1 inside VM)             │ │  │
│  │  │ - Memory blocks (isolated)                     │ │  │
│  │  │ - LLM client (via vsock)                       │ │  │
│  │  │ - Storage client (via vsock)                   │ │  │
│  │  └────────────────────────────────────────────────┘ │  │
│  │                                                       │  │
│  │  Tool execution (when agent calls tool):             │  │
│  │  ┌────────────────────────────────────────────────┐ │  │
│  │  │ Child Process (Linux namespaces)              │ │  │
│  │  │ - PID namespace (isolated process tree)        │ │  │
│  │  │ - Mount namespace (isolated filesystem)        │ │  │
│  │  │ - Network namespace (isolated network)         │ │  │
│  │  │ - cgroups (256MB RAM, 80% CPU max)             │ │  │
│  │  │ - seccomp (syscall filtering)                  │ │  │
│  │  │ - 30s timeout                                   │ │  │
│  │  └────────────────────────────────────────────────┘ │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  LibkrunSandbox (Agent 2's MicroVM)                  │  │
│  │  ────────────────────────────────────────────────    │  │
│  │  Separate hardware isolation (cannot access Agent 1) │  │
│  │                                                       │  │
│  │  [Agent 2 Runtime + Tool processes]                  │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  LibkrunSandbox (Agent 3's MicroVM)                  │  │
│  │  [Agent 3 Runtime + Tool processes]                  │  │
│  └──────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘

Benefits:
✅ Agent crash → Only that VM crashes (others unaffected)
✅ Agent memory leak → Contained to VM (doesn't affect others)
✅ Agent CPU spike → VM limits enforced (doesn't starve others)
✅ Separate memory space → Cannot access other agents
✅ Tool crash → Only process dies (doesn't crash agent)
✅ No cloud dependencies → Fully self-hosted
✅ Defense in depth → VM layer + Process layer
```

---

## Isolation Levels Explained

### Layer 1: MicroVM Isolation (Agent ↔ Agent)

**What it provides:**
- Hardware-level isolation via KVM/HVF
- Separate memory space per agent
- Separate CPU allocation per agent
- Separate network stack per agent
- Separate filesystem per agent

**Protection:**
- Agent 1 CANNOT read Agent 2's memory (hardware boundary)
- Agent 1 crash CANNOT affect Agent 2 (separate VM)
- Agent 1 memory leak CANNOT affect Agent 2 (separate RAM allocation)
- Agent 1 CPU spike CANNOT starve Agent 2 (separate vCPUs)

**Technology:**
- **LibkrunSandbox:** Uses libkrun (KVM on Linux, HVF on macOS)
- **Boot time:** ~50-100ms per agent
- **Memory overhead:** ~50MB per agent (VM + runtime)
- **Resource limits:** 512MB RAM, 2 vCPUs per agent (configurable)

### Layer 2: Process Isolation (Agent ↔ Tool)

**What it provides:**
- Linux namespaces (PID, mount, network, user)
- cgroups resource limits (memory, CPU)
- seccomp syscall filtering
- Separate process tree
- Timeout enforcement

**Protection:**
- Tool CANNOT read agent's memory (separate process)
- Tool CANNOT crash agent (separate process tree)
- Tool CANNOT starve agent (cgroup limits)
- Tool CANNOT escape VM (seccomp + namespaces)
- Tool timeout kills only tool, not agent

**Technology:**
- **Process sandboxing:** fork/exec with unshare
- **Namespaces:** PID, mount, network, user
- **cgroups:** Memory (256MB max), CPU (80% max)
- **seccomp:** Whitelist safe syscalls, block dangerous ones
- **Timeout:** 30s max per tool execution

---

## Security Comparison

### Scenario 1: Malicious Agent Code

**Letta:**
- Malicious agent runs in-process
- Can potentially read other agents' memory
- Can crash entire server
- Can starve other agents with CPU/memory usage
- **Risk:** HIGH

**Kelpie:**
- Malicious agent runs in isolated MicroVM
- CANNOT read other agents' memory (hardware boundary)
- Crash isolated to one VM
- Resource limits enforced by VM (512MB RAM, 2 vCPUs)
- **Risk:** LOW (isolated)

---

### Scenario 2: Malicious Tool Code

**Letta:**
- Tool runs in E2B cloud sandbox
- Isolated from other tools
- **Risk:** LOW (but depends on E2B)

**Kelpie:**
- Tool runs in process sandbox inside VM
- Isolated from agent (process boundary)
- Isolated from other tools (separate processes)
- CANNOT escape VM (seccomp + namespaces)
- **Risk:** VERY LOW (double isolation)

---

### Scenario 3: Tool Goes Rogue (infinite loop, memory leak)

**Letta:**
- E2B handles timeout/resource limits
- **Result:** Tool killed, agent continues

**Kelpie:**
- cgroups enforce 256MB RAM, 80% CPU limits
- 30s timeout enforced
- Kill only tool process, not agent
- **Result:** Tool killed, agent continues, VM resources protected

---

### Scenario 4: Agent Crash

**Letta:**
- Agent crash in shared process
- **Result:** Entire server crashes (all agents down)

**Kelpie:**
- Agent crash in isolated VM
- **Result:** Only that VM crashes (other agents unaffected)
- VM can be restarted automatically
- Agent state recovered from FDB

---

### Scenario 5: Multi-Tenant SaaS

**Letta:**
- All tenants' agents in same process
- Isolation via database + RBAC
- **Security boundary:** Software-only
- **Compliance:** Difficult (shared memory)

**Kelpie:**
- Each tenant's agents in separate VMs
- Isolation via hardware + database + RBAC
- **Security boundary:** Hardware-enforced
- **Compliance:** Easy (hardware isolation for SOC2, HIPAA, PCI)

---

## Performance Comparison

| Metric | Letta | Kelpie | Impact |
|--------|-------|--------|--------|
| **Agent activation** | ~1ms (in-process) | ~50-100ms (VM boot) | Acceptable (one-time) |
| **Agent message** | ~50-100ms (LLM) | ~50-100ms (LLM) | Same (LLM dominates) |
| **Tool execution** | ~100-500ms (E2B) | ~101-505ms (+1-5ms) | Negligible overhead |
| **Memory per agent** | ~10MB (shared) | ~60MB (VM + runtime) | Acceptable for isolation |
| **Concurrent agents** | 1000+ (shared) | 100+ (limited by VMs) | Trade-off for security |

**Verdict:** Slight overhead for VASTLY better security. Worth it.

---

## Implementation Phases

### Phase 0.5: Agent-Level Sandboxing (5 days)

**Day 1-2: LibkrunSandbox Integration**
- Wire AgentActor to run inside LibkrunSandbox
- vsock communication for control plane
- Message handling through vsock
- LLM calls forwarded to host
- Storage operations forwarded to host

**Day 3-4: Tool Process Isolation**
- Implement process sandboxing inside VM
- Linux namespaces (PID, mount, network, user)
- cgroups resource limits (256MB RAM, 80% CPU)
- seccomp syscall filtering
- Timeout enforcement (30s)

**Day 5: Optimization & Testing**
- VM image optimization (<100MB)
- VM pool management (pre-warm VMs)
- Boot time optimization (<100ms)
- DST tests with VM crashes, resource exhaustion
- Performance benchmarks

---

## Marketing Value

### Headline

**"Same Letta API, Better Isolation"**

### Key Messages

1. **Hardware-Level Security:**
   - "Kelpie isolates agents at the hardware level, not just software"
   - "Your agents can't access each other's memory - guaranteed by KVM/HVF"

2. **Defense in Depth:**
   - "Two layers of isolation: MicroVM for agents, process for tools"
   - "Tool bugs can't crash agents, agent bugs can't crash server"

3. **No Cloud Dependencies:**
   - "Fully self-hosted - no E2B, no third-party sandboxes"
   - "Your code executes on YOUR hardware, not the cloud"

4. **Compliance Ready:**
   - "Hardware isolation meets SOC2, HIPAA, PCI requirements"
   - "Multi-tenant SaaS with true tenant isolation"

5. **Same API, Better Foundation:**
   - "Drop-in Letta replacement with superior architecture"
   - "Migrate with one line change, get enterprise-grade isolation"

---

## User Decision Summary

**User requirement:** "Do it the Kelpie way, no cheating"

**Decision made:** Option A - Double Sandboxing
- Agent-level: LibkrunSandbox (MicroVM per agent)
- Tool-level: Process isolation inside VM

**Why this matters:**
- ProcessSandbox alone is weak (just OS process isolation)
- Letta's approach is weak (agents in-process)
- **This IS what makes Kelpie better than Letta**
- **This IS the point of the drop-in replacement**

**No cheating. The Kelpie way.**

---

**Updated timeline:** 32-38 days (6-8 weeks full-time)

**Next step:** Phase 0 (path alias) → Phase 0.5 (agent sandboxing) → Phase 1 (tools)

---

## Related Documentation

**For detailed information on Kelpie's capabilities:**
- **`.progress/CAPABILITY_LEVELS.md`** - How Kelpie can support "omnipotent" agents (SSH, Docker, etc.) with configurable capability levels (L0-L4)
- **`.progress/SANDBOXING_STRATEGY.md`** - Complete sandboxing strategy (double sandboxing architecture)
- **`.progress/CODING_AGENTS_COMPARISON.md`** - Comparison with Claude Code, Letta Code, Clawdbot for coding agent use cases
- **`.progress/014_20260115_143000_letta_api_full_compatibility.md`** - Master implementation plan for 100% Letta API compatibility

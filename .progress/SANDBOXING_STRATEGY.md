# Kelpie Sandboxing Strategy

**Created:** 2026-01-15 15:45:00
**Context:** Clarifying sandboxing architecture for Letta compatibility + Kelpie advantages

---

## Executive Summary

**DECISION: Kelpie implements DOUBLE SANDBOXING (Option A) - THE KELPIE WAY**

Kelpie implements **TWO levels of sandboxing** with **THREE sandbox implementations**:

1. **Agent-level sandboxing** - LibkrunSandbox (MicroVM per agent) - **DEFAULT**
2. **Tool-level sandboxing** - Process isolation inside VM - **ALWAYS ON**

**This is NOT optional. This IS Kelpie's differentiator. No cheating.**

---

## 1. Letta's Sandboxing Model (What We Need for Compatibility)

Based on research ([AWS Blog](https://aws.amazon.com/blogs/database/how-letta-builds-production-ready-ai-agents-with-amazon-aurora-postgresql/), [Letta Agent Architecture](https://www.letta.com/blog/letta-v1-agent), [Client-side Tool Execution](https://docs.letta.com/guides/agents/tool-execution-client-side/)):

### Agent Execution
- **Agents run IN-PROCESS** within the Letta server
- **NO per-agent sandboxing**
- Multi-tenancy achieved via:
  - Database isolation (PostgreSQL with tenant IDs)
  - RBAC (role-based access control)
  - SSO (SAML/OIDC)

### Tool Execution
- **Each tool execution is sandboxed**
- Two execution modes:
  1. **Server-side:** Tools run in E2B cloud sandbox (requires `E2B_API_KEY`)
  2. **Client-side:** Tools run on user's machine (opt-in)

**Letta's security boundary: Tools are untrusted, agents are trusted**

---

## 2. Kelpie's Sandboxing Architecture

### Available Sandbox Implementations

| Sandbox Type | Technology | Platform | Isolation Level | Boot Time | Use Case |
|--------------|------------|----------|-----------------|-----------|----------|
| **ProcessSandbox** | OS process | All platforms | Process isolation | ~1ms | **Tools (default)** |
| **FirecrackerSandbox** | MicroVM (KVM) | Linux only | Hardware-level | ~125ms | **Agents (high security)** |
| **LibkrunSandbox** | MicroVM (libkrun) | macOS/Linux | VM-level | ~50ms | **Agents (cross-platform)** |

### Security Boundaries

```
┌────────────────────────────────────────────────────────────────┐
│  Kelpie Server Process                                         │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐ │
│  │  Agent 1 (IN-PROCESS - Letta compatible)                 │ │
│  │  - Memory blocks                                          │ │
│  │  - LLM calls                                              │ │
│  │  │                                                         │ │
│  │  │  Tool calls → SANDBOXED (per-tool isolation)          │ │
│  │  │  ┌────────────────────────────────────────────┐       │ │
│  │  └─▶│ ProcessSandbox (30s timeout, 256MB limit) │       │ │
│  │     │ - Python runtime                            │       │ │
│  │     │ - Injected environment (LETTA_AGENT_ID)     │       │ │
│  │     │ - Network isolation (only Kelpie API)       │       │ │
│  │     └────────────────────────────────────────────┘       │ │
│  └──────────────────────────────────────────────────────────┘ │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐ │
│  │  Agent 2 (SANDBOXED - Kelpie advantage, optional)        │ │
│  │  ┌──────────────────────────────────────────────────────┐│ │
│  │  │  FirecrackerSandbox (entire agent in MicroVM)        ││ │
│  │  │  - Guest kernel                                       ││ │
│  │  │  - Agent runtime                                      ││ │
│  │  │  - Memory blocks (isolated)                           ││ │
│  │  │  - LLM calls (via vsock)                              ││ │
│  │  │                                                        ││ │
│  │  │  Tool calls → DOUBLE SANDBOXED                        ││ │
│  │  │  ┌────────────────────────────────────┐              ││ │
│  │  │  │ ProcessSandbox (inside MicroVM)    │              ││ │
│  │  │  └────────────────────────────────────┘              ││ │
│  │  └──────────────────────────────────────────────────────┘│ │
│  └──────────────────────────────────────────────────────────┘ │
└────────────────────────────────────────────────────────────────┘
```

---

## 3. Sandboxing Strategy for Letta Compatibility

### Phase 1.5 & 9: Tool Sandboxing (REQUIRED)

**For 100% Letta compatibility, tools MUST be sandboxed:**

#### Tool Types & Sandbox Assignment

| Tool Type | Sandbox | Rationale |
|-----------|---------|-----------|
| `web_search` | ProcessSandbox | HTTP client, no code execution |
| `run_code` | ProcessSandbox | Multi-language code execution |
| Custom Python tools | ProcessSandbox | User-defined functions from SDK |
| `send_message` | None | Built-in, trusted |
| Memory tools | None | Built-in, trusted |
| MCP tools (stdio) | ProcessSandbox | External process communication |
| MCP tools (HTTP) | None | HTTP client only |
| MCP tools (SSE) | None | HTTP client only |

#### ProcessSandbox Configuration for Tools

```rust
SandboxConfig {
    limits: ResourceLimits {
        memory_bytes_max: 256 * 1024 * 1024,  // 256MB
        cpu_cores_max: 1,
        cpu_percent_max: 80,
        disk_bytes_max: 1 * 1024 * 1024 * 1024,  // 1GB
        execution_timeout_ms: 30_000,  // 30s
    },
    network_isolation: NetworkIsolation::AllowKelpieApiOnly,
    filesystem_isolation: FilesystemIsolation::ReadOnlyExceptTmp,
}
```

#### Environment Injection (Letta compatibility)

Every tool execution sandbox receives:
```bash
LETTA_AGENT_ID=agent-uuid-here
LETTA_PROJECT_ID=project-uuid-here  # If applicable
LETTA_API_KEY=api-key-here
LETTA_BASE_URL=http://localhost:8283
```

**Plus pre-initialized Letta client:**
```python
# Available in tool sandbox automatically
from letta import LettaClient
client = LettaClient(
    base_url=os.environ["LETTA_BASE_URL"],
    api_key=os.environ["LETTA_API_KEY"]
)
```

---

## 4. Agent Sandboxing (KELPIE ADVANTAGE - Optional)

**This is NOT required for Letta compatibility but is a KELPIE DIFFERENTIATOR.**

### Why Agent-Level Sandboxing?

Letta runs all agents in-process. This is fine for trusted environments but has risks:

**Risks of In-Process Agents:**
- Agent bug crashes entire server
- Memory leak in one agent affects all agents
- Agent CPU spike degrades all agents
- Compromised agent can access other agents' memory
- No hardware-level isolation for multi-tenant SaaS

**Kelpie Advantage: Optional Agent Sandboxing**

### When to Use Agent Sandboxing

| Scenario | Sandbox Type | Rationale |
|----------|--------------|-----------|
| **Single-tenant, trusted agents** | None (in-process) | Letta-compatible, maximum performance |
| **Multi-tenant SaaS** | FirecrackerSandbox | Hardware isolation, security compliance |
| **Untrusted agent code** | FirecrackerSandbox | VM escape prevention |
| **Resource guarantees** | LibkrunSandbox | Per-agent CPU/memory limits |
| **Development/testing** | ProcessSandbox | Lightweight isolation, fast iteration |

### Configuration Strategy

**Default (Letta-compatible):**
```rust
// Agent runs in-process (like Letta)
let agent = AgentActor::new(agent_id, config);
// Tools use ProcessSandbox
```

**Multi-tenant (Kelpie advantage):**
```rust
// Agent runs in Firecracker MicroVM
let agent_sandbox = FirecrackerSandbox::new(FirecrackerConfig {
    kernel_image: "/var/lib/kelpie/vmlinux.bin",
    rootfs_image: "/var/lib/kelpie/rootfs.ext4",
    memory_mb: 512,
    vcpu_count: 2,
    ..Default::default()
});
let agent = AgentActor::new_in_sandbox(agent_id, config, agent_sandbox);
// Tools STILL use ProcessSandbox (inside MicroVM = double isolation)
```

---

## 5. Firecracker vs libkrun Decision Matrix

Both provide VM-level isolation. When to use which?

### FirecrackerSandbox

**Best for:**
- Production multi-tenant SaaS (Linux servers)
- Compliance requirements (SOC2, HIPAA, PCI)
- Financial/healthcare agents
- Maximum security (hardware-level isolation)

**Requirements:**
- Linux with KVM (`/dev/kvm`)
- Root/sudo access
- `firecracker` binary
- Guest kernel + rootfs images

**Specs:**
- Boot time: ~125ms
- Memory overhead: ~5MB per VM
- Snapshot/restore: Yes
- Live migration: Possible

### LibkrunSandbox

**Best for:**
- Cross-platform deployments (macOS development, Linux production)
- Lighter resource footprint than Firecracker
- Development/testing environments
- Agents that don't need maximum security

**Requirements:**
- macOS (HVF) or Linux (KVM)
- `libkrun` library
- Root filesystem image

**Specs:**
- Boot time: ~50ms
- Memory overhead: ~3MB per VM
- Snapshot/restore: Via libkrun
- Cross-platform: Yes

### Recommendation

**DECISION MADE: LibkrunSandbox for ALL agents (Phase 0.5)**
- **Agents:** LibkrunSandbox (MicroVM per agent) - DEFAULT
- **Tools:** Process isolation inside VM - ALWAYS
- **NOT optional:** This IS the Kelpie way

**Why LibkrunSandbox (not Firecracker):**
- Cross-platform (macOS development + Linux production)
- Faster boot (~50ms vs ~125ms)
- Lighter overhead (~3MB vs ~5MB per VM)
- Sufficient isolation for most use cases
- Can upgrade to Firecracker for max security if needed

---

## 6. Implementation Phases

### Phase 1.5: Tool Sandboxing with ProcessSandbox (3 days)

**Scope:**
- Extend ProcessSandbox for Python runtime
- Implement environment injection (LETTA_AGENT_ID, etc.)
- Pre-initialize Letta client in sandbox
- Network isolation (only Kelpie API accessible)
- Filesystem isolation (read-only except /tmp)

**Tools covered:**
- `run_code` (Python, JS, TS, R, Java)
- `web_search` (HTTP client, no sandbox needed)

### Phase 9: Custom Tool Execution (4 days)

**Scope:**
- Store Python source code in FDB
- Wire UnifiedToolRegistry to ProcessSandbox
- Execute custom tools from Letta Python SDK

**Sandbox features:**
- Source code loading from storage
- Dependency management (pip install in sandbox)
- Per-tool venv caching
- Timeout enforcement (30s)
- Resource limits (256MB, 1 core)

### Future: Agent Sandboxing (NOT in current plan)

**Would add (if user requests):**
- Agent sandbox configuration API
- FirecrackerSandbox integration for agents
- LibkrunSandbox integration for agents
- Sandbox pool management (pre-warmed VMs)
- Live migration between sandboxes
- Per-agent resource quotas

**Effort estimate:** 5-7 days

---

## 7. Security Comparison: Kelpie vs Letta

| Security Feature | Letta | Kelpie (Default) | Kelpie (Optional) |
|------------------|-------|------------------|-------------------|
| **Tool sandboxing** | ✅ E2B cloud | ✅ ProcessSandbox | ✅ ProcessSandbox |
| **Agent sandboxing** | ❌ In-process | ❌ In-process | ✅ MicroVM |
| **Multi-tenant isolation** | Database/RBAC | Database/RBAC | **Hardware-level** |
| **Resource limits (tools)** | ✅ E2B manages | ✅ Configurable | ✅ Configurable |
| **Resource limits (agents)** | ❌ Shared | ❌ Shared | ✅ Per-VM |
| **Agent crash isolation** | ❌ Crashes server | ❌ Crashes server | ✅ Isolated |
| **Self-hosted** | ✅ Yes | ✅ Yes | ✅ Yes |
| **Cloud dependencies** | E2B (optional) | ❌ None | ❌ None |

**Kelpie Advantage:** Can offer **stronger isolation** than Letta with optional agent sandboxing.

---

## 8. Configuration Examples

### Letta-Compatible (Default)

```rust
// No special configuration needed
// Tools automatically use ProcessSandbox
// Agents run in-process (Letta-compatible)

let server = KelpieServer::new(KelpieConfig::default()).await?;
```

### Multi-Tenant with Agent Sandboxing

```rust
let config = KelpieConfig {
    agent_sandbox_type: SandboxType::Firecracker,
    agent_sandbox_config: FirecrackerConfig {
        kernel_image: "/var/lib/kelpie/vmlinux.bin",
        rootfs_image: "/var/lib/kelpie/rootfs.ext4",
        memory_mb: 512,
        vcpu_count: 2,
        ..Default::default()
    },
    tool_sandbox_type: SandboxType::Process,  // Tools still use ProcessSandbox
    tool_sandbox_config: ProcessSandboxConfig {
        timeout_ms: 30_000,
        memory_bytes_max: 256 * 1024 * 1024,
        ..Default::default()
    },
    ..Default::default()
};

let server = KelpieServer::new(config).await?;
```

---

## 9. Answer to Original Question

**Q: "For sandboxing, are we doing per-agent sandboxing? How are we using Firecracker and libkrun? Would that be used when Letta drop-in replacement?"**

**A:**

### For Letta Compatibility (Current Plan):
- **Agents:** Run in-process (NO sandboxing) - same as Letta
- **Tools:** ProcessSandbox (per-tool isolation) - REQUIRED for compatibility
- **Firecracker/libkrun:** NOT used in compatibility mode

### Kelpie Advantage (Optional, Future):
- **Agents:** CAN be sandboxed in Firecracker/libkrun MicroVMs
- **Use cases:**
  - Multi-tenant SaaS (tenant isolation)
  - Untrusted agents (security)
  - Resource guarantees (QoS)
- **This is a KELPIE DIFFERENTIATOR** - Letta doesn't offer this

### Tool Execution (Required):
- **All tools run in ProcessSandbox** (30s timeout, 256MB, network isolation)
- **Custom Python tools** from Letta SDK execute in sandbox with:
  - Injected environment (LETTA_AGENT_ID, API key)
  - Pre-initialized Letta client
  - Pip dependency management
  - Per-tool venv caching

### When to Use Which Sandbox:

**Now (Phases 1-10):**
- Tools → ProcessSandbox ✅
- Agents → In-process ✅

**Future (if user wants stronger security):**
- Tools → ProcessSandbox ✅
- Agents → FirecrackerSandbox (Linux) or LibkrunSandbox (macOS/Linux) ✅

---

## 10. Next Steps

**For current plan (Letta compatibility):**
1. ✅ Clarified: Tools use ProcessSandbox, agents in-process
2. ✅ No Firecracker/libkrun needed for compatibility
3. Phase 1.5: Implement ProcessSandbox for `run_code` tool
4. Phase 9: Wire ProcessSandbox for custom Python tools

**For future (Kelpie advantage):**
- Add agent sandboxing configuration API
- Integrate Firecracker/libkrun for agents
- Document security benefits vs Letta
- Marketing: "Same API, Better Isolation"

---

**Sources:**
- [Letta Multi-Tenant Security](https://aws.amazon.com/blogs/database/how-letta-builds-production-ready-ai-agents-with-amazon-aurora-postgresql/)
- [Letta Agent Architecture](https://www.letta.com/blog/letta-v1-agent)
- [Client-side Tool Execution](https://docs.letta.com/guides/agents/tool-execution-client-side/)

# Coding Agents Sandboxing: Kelpie vs Claude Code vs Letta Code vs Clawdbot

**Created:** 2026-01-15 16:45:00
**Context:** Comparing sandboxing approaches for coding agents

---

## Executive Summary

| Agent | Agent Isolation | Tool/Code Isolation | Filesystem Access | Network Access | Sandboxing Quality |
|-------|----------------|---------------------|-------------------|----------------|-------------------|
| **Kelpie** | ✅ **LibkrunSandbox (MicroVM)** | ✅ **Process (namespaces, cgroups, seccomp)** | ✅ **Controlled via mount namespaces** | ✅ **Controlled via network namespaces** | **EXCELLENT (Defense in depth)** |
| **Claude Code** | ❌ Runs in CLI process | ✅ **Bubblewrap (Linux) / Seatbelt (macOS)** | ✅ **CWD read/write, rest read-only** | ✅ **Proxy with domain allowlist** | **GOOD (OS-level)** |
| **Letta Code** | ❌ In-process | ✅ **E2B cloud sandbox** | ✅ **E2B manages** | ✅ **E2B manages** | **FAIR (Cloud dependency)** |
| **Clawdbot** | ❌ Gateway on host | ⚠️ **Optional Docker (non-main only)** | ⚠️ **Full host access (main)** | ⚠️ **Full host access (main)** | **WEAK (Default unsandboxed)** |

**Verdict:** Kelpie offers **the strongest isolation** with defense-in-depth architecture.

---

## Detailed Comparison

### 1. Claude Code

**What it is:** Official Anthropic CLI coding agent

**Architecture:**
```
┌─────────────────────────────────────────────────┐
│  Host Machine (Your Computer)                   │
│                                                  │
│  ┌───────────────────────────────────────────┐ │
│  │  Claude Code Process (Python CLI)         │ │
│  │  - Runs directly on host                  │ │
│  │  - No agent-level isolation               │ │
│  │                                            │ │
│  │  When executing bash tool:                │ │
│  │  ┌─────────────────────────────────────┐ │ │
│  │  │ OS-Level Sandbox                    │ │ │
│  │  │ ──────────────────                  │ │ │
│  │  │ Linux: bubblewrap                   │ │ │
│  │  │ macOS: sandbox-exec (Seatbelt)      │ │ │
│  │  │                                      │ │ │
│  │  │ Filesystem:                          │ │ │
│  │  │ - CWD: read/write                    │ │ │
│  │  │ - Rest of system: read-only          │ │ │
│  │  │ - Deny: ~/.ssh, ~/.bashrc, etc.      │ │ │
│  │  │                                      │ │ │
│  │  │ Network:                             │ │ │
│  │  │ - Unix socket to proxy               │ │ │
│  │  │ - Proxy enforces domain allowlist    │ │ │
│  │  │ - User confirms new domains          │ │ │
│  │  └─────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────┘ │
└─────────────────────────────────────────────────┘
```

**Key Features:**
- **Filesystem Isolation:** CWD read/write, rest of system read-only
- **Network Isolation:** Proxy with domain allowlist (requires user confirmation)
- **OS Primitives:** bubblewrap (Linux), Seatbelt (macOS)
- **Applies to:** All subprocesses spawned by bash tool

**Strengths:**
- ✅ Strong filesystem isolation (can't modify ~/.ssh, ~/.bashrc, etc.)
- ✅ Network isolation prevents data exfiltration
- ✅ OS-level enforcement (kernel-level)
- ✅ Open source ([sandbox-runtime](https://github.com/anthropic-experimental/sandbox-runtime))

**Weaknesses:**
- ❌ No agent-level isolation (Claude Code itself runs on host)
- ❌ Single point of failure (Claude Code bug crashes entire process)
- ❌ Shared resources (memory, CPU) with host

**Security Issues:**
- CVE-2025-66479: Network isolation bypass (fixed within 3 days)
- `allowedDomains: []` was wide open, allowed connections to any server
- Opaque changelog, no CVE for Claude Code itself

**Sources:**
- [Claude Code Sandboxing](https://www.anthropic.com/engineering/claude-code-sandboxing)
- [sandbox-runtime GitHub](https://github.com/anthropic-experimental/sandbox-runtime)
- [CVE-2025-66479](https://oddguan.com/blog/anthropic-sandbox-cve-2025-66479/)

---

### 2. Letta Code

**What it is:** Memory-first coding agent (like Claude Code but with persistent memory)

**Architecture:**
```
┌─────────────────────────────────────────────────┐
│  Letta Server (Your Machine or Letta Cloud)    │
│                                                  │
│  ┌───────────────────────────────────────────┐ │
│  │  Letta Agent Process (In-process)         │ │
│  │  - All agents in shared process           │ │
│  │  - Memory persistence across sessions     │ │
│  │                                            │ │
│  │  When executing run_code tool:            │ │
│  │         │                                  │ │
│  └─────────┼──────────────────────────────────┘ │
│            │ HTTP to E2B API                    │
│            ▼                                     │
└────────────┼──────────────────────────────────────┘
             │
  ┌──────────▼──────────────────────────────────┐
  │  E2B Cloud Sandbox (External Service)       │
  │  ───────────────────────────────────────    │
  │  - Isolated container in E2B cloud          │
  │  - Filesystem isolation                      │
  │  - Network isolation                         │
  │  - Languages: Python, JS, TS, R, Java       │
  │  - Requires E2B_API_KEY                      │
  └──────────────────────────────────────────────┘
```

**Key Features:**
- **Cloud Sandbox:** E2B handles all isolation
- **Multi-language:** Python, JavaScript, TypeScript, R, Java
- **Memory:** Agent remembers codebase, preferences, past interactions
- **Model Agnostic:** Works with Claude, GPT, Gemini

**Strengths:**
- ✅ Strong isolation (E2B manages containers)
- ✅ Multi-language support
- ✅ Works out of the box (on Letta Cloud)
- ✅ Stateful agents (memory across sessions)

**Weaknesses:**
- ❌ No agent-level isolation (agents in-process)
- ❌ Cloud dependency (requires E2B API key for self-hosted)
- ❌ Third-party trust (E2B sees your code)
- ❌ Cost (per-execution pricing)
- ❌ Latency (network round trip to E2B)

**Sources:**
- [Letta Code](https://www.letta.com/blog/letta-code)
- [Code interpreter docs](https://docs.letta.com/guides/agents/run-code/)

---

### 3. Clawdbot

**What it is:** Personal AI assistant you run locally, integrates with WhatsApp, Telegram, Discord, etc.

**Architecture:**
```
┌─────────────────────────────────────────────────┐
│  Your Computer (Full Host Access)              │
│                                                  │
│  ┌───────────────────────────────────────────┐ │
│  │  Clawdbot Gateway (WebSocket Server)     │ │
│  │  ws://127.0.0.1:18789                     │ │
│  │  - Runs on host (no isolation)            │ │
│  │  - Full filesystem access                 │ │
│  │  - Full network access                    │ │
│  │                                            │ │
│  │  Main Session:                            │ │
│  │  ┌─────────────────────────────────────┐ │ │
│  │  │ Tools run ON HOST                   │ │ │
│  │  │ - Full access (by design)           │ │ │
│  │  │ - "It's just you"                   │ │ │
│  │  └─────────────────────────────────────┘ │ │
│  │                                            │ │
│  │  Group/Channel Sessions (Optional):       │ │
│  │  ┌─────────────────────────────────────┐ │ │
│  │  │ Docker Container (if enabled)       │ │ │
│  │  │ - Per-session isolation             │ │ │
│  │  │ - Config: sandbox.mode = "non-main" │ │ │
│  │  └─────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────┘ │
└─────────────────────────────────────────────────┘
```

**Key Features:**
- **Default:** Tools run on host with full access (main session)
- **Optional:** Docker sandboxing for group/channel sessions
- **Sandbox scope:** Per-agent or per-session containers
- **DM Security:** Pairing code verification for unknown senders

**Configuration:**
```yaml
agents:
  defaults:
    sandbox:
      mode: "non-main"  # Sandbox group chats, not main
      scope: "agent"    # One container per agent (or "session", "shared")
      allowlist: [bash, process, read, write, edit]
      denylist: [browser, canvas, cron, discord, gateway]
```

**Strengths:**
- ✅ Local control (runs on your machine)
- ✅ Flexible sandboxing (configure per session)
- ✅ Multi-platform (WhatsApp, Telegram, Discord, etc.)
- ✅ Pairing mode for DM security

**Weaknesses:**
- ❌ **Default is UNSANDBOXED** (main session has full host access)
- ❌ No agent-level isolation (gateway runs on host)
- ❌ User must explicitly enable Docker sandboxing
- ❌ "Tools run on host for main session" by design

**Security Concerns:**
- **Recent update:** Locked down inbound DMs by default (bots were open to anyone)
- **Design trade-off:** "Full access when it's just you" vs security
- **Opt-in sandboxing:** Users must configure `sandbox.mode` themselves

**Sources:**
- [Clawdbot GitHub](https://github.com/clawdbot/clawdbot)
- [Clawdbot Security](https://github.com/clawdbot/clawdbot/security)

---

## 4. Kelpie (The Kelpie Way)

**What it is:** Virtual actor system with LibkrunSandbox agent isolation + process tool isolation

**Architecture:**
```
┌──────────────────────────────────────────────────────────────┐
│  Kelpie Server (Coordinator)                                 │
│                                                               │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  LibkrunSandbox (Agent's MicroVM)                       ││
│  │  ═════════════════════════════════════════════════      ││
│  │  Hardware-level isolation (KVM/HVF)                     ││
│  │  512MB RAM, 2 vCPUs, Isolated network/filesystem       ││
│  │                                                          ││
│  │  ┌──────────────────────────────────────────────────┐  ││
│  │  │ Agent Runtime (PID 1 inside VM)                 │  ││
│  │  │ - Memory blocks (isolated in VM)                │  ││
│  │  │ - LLM client (via vsock to host)                │  ││
│  │  │ - Storage client (via vsock to host)            │  ││
│  │  │ - Message handling                               │  ││
│  │  └──────────────────────────────────────────────────┘  ││
│  │                                                          ││
│  │  When agent calls tool (bash, run_code, custom):       ││
│  │  ┌──────────────────────────────────────────────────┐  ││
│  │  │ Tool Process (Child process INSIDE VM)          │  ││
│  │  │ ─────────────────────────────────────────────   │  ││
│  │  │ Linux Namespaces:                                │  ││
│  │  │ - PID namespace (isolated process tree)         │  ││
│  │  │ - Mount namespace (controlled filesystem)       │  ││
│  │  │ - Network namespace (controlled network)        │  ││
│  │  │ - User namespace (unprivileged user)            │  ││
│  │  │                                                   │  ││
│  │  │ cgroups:                                          │  ││
│  │  │ - Memory limit: 256MB                            │  ││
│  │  │ - CPU limit: 80% max                             │  ││
│  │  │                                                   │  ││
│  │  │ seccomp:                                          │  ││
│  │  │ - Whitelist: read, write, open, exec, etc.      │  ││
│  │  │ - Blacklist: ptrace, reboot, mount, etc.        │  ││
│  │  │                                                   │  ││
│  │  │ Timeout: 30s max per tool execution             │  ││
│  │  └──────────────────────────────────────────────────┘  ││
│  └─────────────────────────────────────────────────────────┘│
│                                                               │
│  ┌─────────────────────────────────────────────────────────┐│
│  │  LibkrunSandbox (Another Agent's MicroVM)               ││
│  │  - SEPARATE hardware isolation                          ││
│  │  - CANNOT access first agent's memory                   ││
│  └─────────────────────────────────────────────────────────┘│
└──────────────────────────────────────────────────────────────┘

LAYER 1: MicroVM isolation (Agent ↔ Agent) - Hardware-level
LAYER 2: Process isolation (Agent ↔ Tool) - OS-level
```

**Key Features:**
- **Agent Isolation:** Each agent in LibkrunSandbox (MicroVM)
- **Tool Isolation:** Process sandboxing inside VM (namespaces, cgroups, seccomp)
- **Defense in Depth:** Two layers of isolation
- **Self-Hosted:** No cloud dependencies

**Strengths:**
- ✅ **Hardware-level agent isolation** (MicroVM)
- ✅ **Process-level tool isolation** (inside VM)
- ✅ **Agent crash isolated** (doesn't crash server)
- ✅ **Tool crash isolated** (doesn't crash agent)
- ✅ **No cloud dependencies** (fully self-hosted)
- ✅ **Cross-platform** (macOS dev, Linux prod)
- ✅ **Configurable** (filesystem, network per VM)
- ✅ **Defense in depth** (VM + Process layers)

**Weaknesses:**
- ⚠️ Boot time overhead (~50-100ms per agent)
- ⚠️ Memory overhead (~50MB per agent)
- ⚠️ Implementation complexity (VM management, vsock, etc.)

---

## Can Kelpie Implement Claude Code / Letta Code?

### YES - With SUPERIOR isolation ✅

**Architecture for Kelpie Code Agent:**

```
┌──────────────────────────────────────────────────────────┐
│  Kelpie Server                                           │
│                                                           │
│  ┌───────────────────────────────────────────────────┐  │
│  │  LibkrunSandbox (Coding Agent's MicroVM)          │  │
│  │  ═══════════════════════════════════════════════  │  │
│  │  - Current working directory mounted from host    │  │
│  │  - Git operations via host (vsock)                │  │
│  │  - Editor integration via host                    │  │
│  │  - Network access: configurable per project       │  │
│  │                                                    │  │
│  │  ┌────────────────────────────────────────────┐  │  │
│  │  │ Coding Agent Runtime                       │  │  │
│  │  │ - Claude/GPT via vsock                     │  │  │
│  │  │ - Project memory (codebase understanding)  │  │  │
│  │  │ - Chat history                             │  │  │
│  │  └────────────────────────────────────────────┘  │  │
│  │                                                    │  │
│  │  When agent writes code, runs tests, etc:         │  │
│  │  ┌────────────────────────────────────────────┐  │  │
│  │  │ Tool Process (inside VM)                   │  │  │
│  │  │ ────────────────────────                   │  │  │
│  │  │ bash: Run commands                         │  │  │
│  │  │ read: Read files in CWD                    │  │  │
│  │  │ write: Write files in CWD                  │  │  │
│  │  │ edit: Edit files                           │  │  │
│  │  │ run_code: Execute Python/JS/etc.           │  │  │
│  │  │                                             │  │  │
│  │  │ Process isolation:                          │  │  │
│  │  │ - CWD: read/write (like Claude Code)       │  │  │
│  │  │ - ~: read-only (protect .ssh, etc.)        │  │  │
│  │  │ - Network: allowlist domains               │  │  │
│  │  │ - Timeout: 30s per command                 │  │  │
│  │  └────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────┘
```

**How it works:**

1. **Agent in VM:** Coding agent runs in LibkrunSandbox
2. **CWD Access:** Project directory mounted into VM (read/write)
3. **Home Protection:** User's home directory read-only (can't modify ~/.ssh)
4. **Tool Sandboxing:** bash, read, write, edit tools run in process sandboxes
5. **Network Control:** Allowlist domains (e.g., github.com, npm registry)
6. **LLM Access:** Via vsock to host (agent doesn't need network access)

**Kelpie vs Claude Code for Coding:**

| Feature | Claude Code | Kelpie Code |
|---------|-------------|-------------|
| Agent Isolation | ❌ Runs on host | ✅ **MicroVM** |
| CWD Access | ✅ Read/write | ✅ **Read/write** |
| Home Protection | ✅ Read-only | ✅ **Read-only** |
| Tool Sandboxing | ✅ OS-level | ✅ **Process (inside VM)** |
| Network Isolation | ✅ Proxy | ✅ **Network namespace** |
| Multi-project | ❌ One agent | ✅ **VM per project** |
| Crash Isolation | ❌ Crashes CLI | ✅ **VM isolated** |

**Kelpie's advantages for coding:**

1. **Multi-project isolation:** Each project gets its own VM
   - Project A can't access Project B's files
   - Project A crash doesn't affect Project B
   - Different network rules per project

2. **Agent crash resilience:**
   - Coding agent bug crashes VM, not host
   - Can restart VM without affecting other projects
   - State recovered from persistent storage

3. **Tool crash resilience:**
   - Test suite hangs → kill tool process, agent continues
   - Infinite loop in script → timeout enforced, agent fine
   - Memory leak in tool → cgroup limits prevent VM crash

4. **Network granularity:**
   - Project A: Allow github.com, block everything else
   - Project B: Allow internal API, block public internet
   - Configurable per VM

---

## Filesystem Access Comparison

### Claude Code Filesystem Rules:

```
Read Access (Default: Permissive with deny list):
  ✅ /Users/you/project/         (CWD - read/write)
  ✅ /usr/                        (system files - read)
  ✅ /Library/                    (macOS libs - read)
  ❌ ~/.ssh/                      (denied)
  ❌ ~/.bashrc                    (denied)
  ❌ ~/.git/hooks/                (denied)

Write Access (Default: Restrictive with allow list):
  ✅ /Users/you/project/         (CWD only)
  ❌ Everything else              (denied)
```

### Kelpie Filesystem Rules (Same, but inside VM):

```
Inside MicroVM:

Read Access:
  ✅ /workspace/                 (CWD mounted - read/write)
  ✅ /home/agent/                (read-only - can't modify ~/.ssh)
  ✅ /usr/, /lib/                (system libs - read)
  ❌ Sensitive files blocked     (via mount namespace)

Write Access:
  ✅ /workspace/                 (CWD only)
  ✅ /tmp/                       (temporary files)
  ❌ Everything else              (read-only)

Additional VM-level protection:
  - /workspace mounted from host (bind mount)
  - Changes in /workspace persist to host
  - Changes outside /workspace lost on VM restart
  - Can't escape to access host filesystem
```

**Key difference:** Kelpie adds VM boundary on top of filesystem rules.

---

## Network Access Comparison

### Claude Code Network Rules:

```
Network Traffic Flow:

Tool process → Unix socket → Proxy (on host) → Domain check → Internet
                                    │
                                    ├─ Allowlist: github.com ✅
                                    ├─ Denylist: malicious.com ❌
                                    └─ New domain → User prompt
```

### Kelpie Network Rules (More flexible):

```
Network Traffic Flow:

Tool process (in VM) → Network namespace → vsock → Host → Internet
                            │
                            ├─ Option 1: Complete isolation (no internet)
                            ├─ Option 2: Allowlist domains (like Claude Code)
                            ├─ Option 3: Full internet (for trusted tools)
                            └─ Configurable per VM

Agent process (in VM) → vsock → Host LLM client → Claude/GPT API
                                (Agent doesn't need internet)
```

**Key differences:**
1. **Network namespace:** Kernel-level isolation (stronger than proxy)
2. **Per-VM rules:** Different projects, different network policies
3. **Agent isolation:** Agent doesn't need internet (only LLM via vsock)

---

## Security Comparison Matrix

### Threat: Malicious prompt injection makes agent delete ~/.ssh

| System | Protected? | How |
|--------|-----------|-----|
| **Kelpie** | ✅ **YES** | VM mount namespace blocks ~/.ssh access, tool process has no route to host home |
| **Claude Code** | ✅ **YES** | Seatbelt/bubblewrap deny list blocks ~/.ssh |
| **Letta Code** | ✅ **YES** | E2B container doesn't have ~/.ssh |
| **Clawdbot** | ❌ **NO** | Default main session has full host access |

### Threat: Agent exfiltrates source code to attacker server

| System | Protected? | How |
|--------|-----------|-----|
| **Kelpie** | ✅ **YES** | Network namespace + allowlist blocks unauthorized connections |
| **Claude Code** | ✅ **YES** | Proxy enforces domain allowlist, requires user confirmation |
| **Letta Code** | ✅ **YES** | E2B network isolation |
| **Clawdbot** | ❌ **NO** | Default main session has full network access |

### Threat: Agent bug causes crash

| System | Impact | Isolation |
|--------|--------|-----------|
| **Kelpie** | ✅ **VM crashes, host fine** | Other agents unaffected, restart VM |
| **Claude Code** | ❌ **CLI crashes** | User must restart CLI |
| **Letta Code** | ❌ **Server crashes** | All agents down |
| **Clawdbot** | ❌ **Gateway crashes** | All connections down |

### Threat: Tool goes into infinite loop

| System | Handled? | How |
|--------|----------|-----|
| **Kelpie** | ✅ **YES** | 30s timeout kills tool process, agent continues, cgroup prevents CPU starvation |
| **Claude Code** | ✅ **YES** | User can Ctrl+C, kills tool subprocess |
| **Letta Code** | ✅ **YES** | E2B timeout kills tool |
| **Clawdbot** | ⚠️ **PARTIAL** | Depends on tool implementation |

### Threat: Tool memory leak (allocates 10GB)

| System | Protected? | How |
|--------|-----------|-----|
| **Kelpie** | ✅ **YES** | cgroup enforces 256MB limit, OOM kills only tool process, agent fine, VM has 512MB limit |
| **Claude Code** | ⚠️ **PARTIAL** | OS may OOM kill entire process |
| **Letta Code** | ✅ **YES** | E2B container limits |
| **Clawdbot** | ❌ **NO** | Can consume all host memory |

---

## Sandboxing Quality Rankings

### Overall Security (Defense in Depth):

1. **🥇 Kelpie:** Agent in VM + Tool in process = **EXCELLENT**
2. **🥈 Claude Code:** Tool in OS sandbox = **GOOD**
3. **🥉 Letta Code:** Tool in E2B cloud = **FAIR** (cloud dependency)
4. **⚠️ Clawdbot:** Optional Docker = **WEAK** (default unsandboxed)

### Agent Isolation:

1. **🥇 Kelpie:** Hardware-level (MicroVM) = **EXCELLENT**
2. **❌ Claude Code:** None (runs on host) = **NONE**
3. **❌ Letta Code:** None (in-process) = **NONE**
4. **❌ Clawdbot:** None (gateway on host) = **NONE**

### Tool Isolation:

1. **🥇 Kelpie:** Process + inside VM = **EXCELLENT**
2. **🥈 Claude Code:** OS-level (bubblewrap/seatbelt) = **GOOD**
3. **🥉 Letta Code:** E2B cloud container = **FAIR**
4. **⚠️ Clawdbot:** Optional Docker (off by default) = **WEAK**

### Self-Hosted Security:

1. **🥇 Kelpie:** No cloud dependencies = **EXCELLENT**
2. **🥈 Claude Code:** No cloud dependencies = **GOOD**
3. **⚠️ Letta Code:** Requires E2B = **POOR** (cloud trust)
4. **🥈 Clawdbot:** Local by design = **GOOD**

---

## Recommendation: Can Kelpie Implement Coding Agents?

### YES - With Superior Architecture ✅

**Implementation Strategy:**

1. **Kelpie Code Agent** (like Claude Code + Letta Code):
   - Agent runtime in LibkrunSandbox (MicroVM)
   - Project directory mounted into VM
   - Tools (bash, read, write, edit) sandboxed in processes
   - LLM access via vsock to host
   - Persistent memory (like Letta Code)
   - Multi-model support (Claude, GPT, Gemini)

2. **Sandboxing Configuration:**
   ```rust
   KelpieCodeConfig {
       agent_sandbox: LibkrunSandbox {
           memory_mb: 512,
           vcpu_count: 2,
           mounts: vec![
               Mount { host: "/Users/you/project", guest: "/workspace", rw: true },
               Mount { host: "/Users/you", guest: "/home/agent", rw: false },
           ],
           network: NetworkPolicy::Allowlist(vec!["github.com", "npmjs.org"]),
       },
       tool_sandbox: ProcessSandbox {
           memory_bytes_max: 256 * 1024 * 1024,
           cpu_percent_max: 80,
           timeout_ms: 30_000,
           namespaces: vec![PID, Mount, Network, User],
       },
   }
   ```

3. **Kelpie's Advantages:**
   - **Multi-project:** VM per project (can't access each other)
   - **Crash resilience:** Agent bug isolated to VM
   - **Tool resilience:** Tool bug isolated to process
   - **Network granularity:** Per-project policies
   - **No cloud dependency:** Fully self-hosted

---

## Summary: The Kelpie Way for Coding Agents

**Kelpie can implement Claude Code / Letta Code functionality with SUPERIOR isolation:**

```
┌─────────────────────────────────────────────────────────┐
│ Traditional Coding Agents (Claude Code, Letta Code)   │
│ ─────────────────────────────────────────────────────  │
│ Agent on host + Tool in sandbox                        │
│ Issue: Agent crash = everything down                   │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ Kelpie Coding Agents (THE KELPIE WAY)                 │
│ ═══════════════════════════════════════════════════    │
│ Agent in VM + Tool in process (inside VM)              │
│ Result: Agent crash = only VM down, host fine          │
│ Result: Tool crash = only process down, agent fine     │
│ Result: Multi-project = isolated VMs                   │
└─────────────────────────────────────────────────────────┘
```

**No cheating. Defense in depth. The Kelpie way.**

---

**Next step:** Implement Phase 0.5 (agent-level sandboxing), then Phase 1+ (tools), then we can build Kelpie Code on this foundation.

**Sources:**
- [Claude Code Sandboxing](https://www.anthropic.com/engineering/claude-code-sandboxing)
- [sandbox-runtime](https://github.com/anthropic-experimental/sandbox-runtime)
- [Letta Code](https://www.letta.com/blog/letta-code)
- [Clawdbot](https://github.com/clawdbot/clawdbot)
- [CVE-2025-66479](https://oddguan.com/blog/anthropic-sandbox-cve-2025-66479/)
- [Docker Sandboxes](https://www.docker.com/blog/docker-sandboxes-a-new-approach-for-coding-agent-safety/)

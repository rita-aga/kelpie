# CLAUDE.md - Kelpie Development Guide

This document provides guidance for AI assistants (and human developers) contributing to Kelpie.

## Project Overview

Kelpie is a distributed virtual actor system with linearizability guarantees, designed for AI agent orchestration and general stateful distributed systems. Built with DST-first (Deterministic Simulation Testing) and TigerStyle engineering principles.

## Quick Commands

```bash
# Build the entire workspace
cargo build

# Run all tests
cargo test

# Run tests with DST seed for reproduction
DST_SEED=12345 cargo test -p kelpie-dst

# Run specific crate tests
cargo test -p kelpie-core
cargo test -p kelpie-dst

# Format code
cargo fmt

# Run clippy
cargo clippy --all-targets --all-features

# Run benchmarks
cargo bench -p kelpie-runtime

# Observability: Run server with tracing
RUST_LOG=info cargo run -p kelpie-server

# Observability: Export traces to OTLP collector (Jaeger, Zipkin, etc.)
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 \
RUST_LOG=info \
cargo run -p kelpie-server --features otel

# Observability: Check metrics endpoint
curl http://localhost:8283/metrics
```

## Architecture

```
kelpie/
├── crates/
│   ├── kelpie-core/      # Core types, errors, constants
│   ├── kelpie-runtime/   # Actor runtime and dispatcher
│   ├── kelpie-registry/  # Actor placement and discovery
│   ├── kelpie-storage/   # Per-actor KV storage
│   ├── kelpie-wasm/      # WASM actor runtime
│   ├── kelpie-cluster/   # Cluster coordination
│   ├── kelpie-agent/     # AI agent abstractions
│   ├── kelpie-dst/       # Deterministic Simulation Testing
│   ├── kelpie-server/    # Standalone server binary
│   └── kelpie-cli/       # CLI tools
├── docs/                 # Documentation
│   ├── adr/              # Architecture Decision Records
│   ├── VISION.md         # Project goals and architecture (moved from root)
│   └── LETTA_MIGRATION_GUIDE.md # Letta migration guide (moved from root)
├── images/               # Base image build system
│   ├── Dockerfile        # Alpine base image
│   ├── build.sh          # Multi-arch build script
│   ├── guest-agent/      # Rust guest agent
│   ├── base/             # Init system and configs
│   └── kernel/           # Kernel extraction
└── tests/                # Integration tests
```

## Base Images

Kelpie agents run in lightweight Alpine Linux microVMs for isolation and teleportation. The base image system (Phases 5.1-5.6) provides:

### Quick Reference

```bash
# Build images locally
cd images && ./build.sh --arch arm64 --version 1.0.0

# Extract kernel/initramfs
cd images/kernel && ./extract-kernel.sh

# Run tests
cargo test -p kelpie-server --test version_validation_test
```

### Key Features

1. **Alpine 3.19 Base** (~28.8MB)
   - Essential packages: busybox, bash, coreutils, util-linux
   - Multi-arch: ARM64 + x86_64
   - VM-optimized kernel (linux-virt 6.6.x)

2. **Guest Agent** (Rust)
   - Unix socket communication (virtio-vsock in production)
   - Command execution with stdin/stdout/stderr
   - File operations (read, write, list)
   - Health monitoring (ping/pong)

3. **Custom Init System**
   - Mounts essential filesystems (proc, sys, dev, tmp, run)
   - Starts guest agent automatically
   - Graceful shutdown handling
   - Boot time: <1s

4. **Version Compatibility**
   - Format: `MAJOR.MINOR.PATCH[-prerelease]-DATE-GITSHA`
   - MAJOR.MINOR must match for teleport compatibility
   - PATCH differences allowed (with warning)
   - Prerelease metadata ignored

5. **CI/CD Pipeline**
   - GitHub Actions with native ARM64 + x86_64 runners
   - Automated builds on push/release
   - Upload to GitHub Releases + Container Registry
   - Multi-arch Docker manifests

### Documentation

See `images/README.md` for:
- Build instructions
- Image structure
- Guest agent protocol
- Troubleshooting
- Development workflow

### Status

- ✅ Phase 5.1: Build System (complete)
- ✅ Phase 5.2: Guest Agent (complete, 4 tests)
- ✅ Phase 5.3: Init System (complete)
- ✅ Phase 5.4: Kernel Extraction (complete)
- ✅ Phase 5.5: Distribution (complete, GitHub Actions)
- ✅ Phase 5.6: Version Validation (complete, 5 tests)
- ✅ Phase 5.7: libkrun Integration (complete, testing/reference only)
- ✅ Phase 5.9: VM Backends (complete, Apple Vz + Firecracker with DST coverage)

## VM Backends & Hypervisors

Kelpie uses a **multi-backend architecture** for VM management, allowing different hypervisors based on platform and use case.

### Backend Selection Strategy

| Backend | Platform | Use Case | Snapshot Support |
|---------|----------|----------|------------------|
| **MockVm** | All | Testing, DST, CI/CD | ✅ Simulated |
| **Apple Vz** | macOS | Production (Mac dev) | ✅ Native API (macOS 14+) |
| **Firecracker** | Linux | Production (cloud) | ✅ Production-proven |

### Why Multiple Backends?

1. **Platform-Native Performance**: Use native hypervisors for best performance
2. **Testing Everywhere**: MockVm works without system dependencies
3. **Production-Ready**: Apple Vz and Firecracker have mature snapshot APIs
4. **Cross-Platform Development**: Mac devs use Apple Vz, Linux devs use Firecracker

### Quick Testing Guide

```bash
# Default: MockVm (no system dependencies, works everywhere)
cargo test -p kelpie-vm

# Apple Vz backend (macOS only)
cargo test -p kelpie-vm --features vz

# Firecracker backend (Linux only)
cargo test -p kelpie-vm --features firecracker
```

### Platform-Specific Commands

```bash
# macOS Development
cargo test -p kelpie-vm --features vz
cargo run -p kelpie-server --features vz

# Linux Development
cargo test -p kelpie-vm --features firecracker
cargo run -p kelpie-server --features firecracker

# Testing (all platforms)
cargo test -p kelpie-vm  # Uses MockVm by default
DST_SEED=12345 cargo test -p kelpie-dst
```

### Architecture Compatibility

**Same-Architecture Teleport** (VM Snapshot):
- ✅ Mac ARM64 → AWS Graviton ARM64
- ✅ Linux x86_64 → Linux x86_64
- ✅ Full VM memory state preserved
- ✅ Fast restore (~125-500ms)

**Cross-Architecture Migration** (Checkpoint):
- ✅ Mac ARM64 → Linux x86_64 (agent state only)
- ✅ Linux x86_64 → Mac ARM64 (agent state only)
- ❌ VM memory cannot be transferred (CPU incompatibility)
- ⚠️ Slower (VM restarts fresh, agent state reloaded)

**Implementation Plan**: See `.progress/016_20260115_121324_teleport-dual-backend-implementation.md`

## TigerStyle Engineering Principles

Kelpie follows TigerBeetle's TigerStyle: **Safety > Performance > DX**

### 1. Explicit Constants with Units

All limits are named constants with units in the name:

```rust
// Good - unit in name, explicit limit
pub const ACTOR_INVOCATION_TIMEOUT_MS_MAX: u64 = 30_000;
pub const ACTOR_STATE_SIZE_BYTES_MAX: usize = 10 * 1024 * 1024;

// Bad - unclear units, magic number
pub const TIMEOUT: u64 = 30000;
const MAX_SIZE: usize = 10485760;
```

### 2. Big-Endian Naming

Name identifiers from big to small concept:

```rust
// Good - big to small
actor_id_length_bytes_max
network_latency_ms_base
storage_write_batch_size

// Bad - small to big
max_actor_id_length
base_latency_ms
batch_size_storage_write
```

### 3. Assertions (2+ per Function)

Every non-trivial function should have at least 2 assertions:

```rust
pub fn set_timeout(&mut self, timeout_ms: u64) {
    // Precondition
    assert!(timeout_ms > 0, "timeout must be positive");
    assert!(timeout_ms <= TIMEOUT_MS_MAX, "timeout exceeds maximum");

    self.timeout_ms = timeout_ms;

    // Postcondition
    assert!(self.timeout_ms > 0);
}
```

### 4. Prefer u64 Over usize for Sizes

Use fixed-width integers for portability:

```rust
// Good - portable across platforms
pub fn size_bytes(&self) -> u64;
pub fn item_count(&self) -> u64;

// Bad - varies by platform
pub fn size_bytes(&self) -> usize;
```

### 5. No Silent Truncation

Avoid implicit conversions that could truncate:

```rust
// Good - explicit conversion with assertion
let size: u64 = data.len() as u64;
assert!(size <= u32::MAX as u64, "size too large for u32");
let size_u32: u32 = size as u32;

// Bad - silent truncation
let size: u32 = data.len() as u32;
```

### 6. Explicit Error Handling

No unwrap() in production code (only tests):

```rust
// Good - explicit error handling
let value = self.storage.get(key)?;
let config = Config::load().map_err(|e| Error::ConfigInvalid { reason: e.to_string() })?;

// Bad - panics in production
let value = self.storage.get(key).unwrap();
```

### 7. Debug Assertions for Expensive Checks

Use `debug_assert!` for checks that are too expensive for release:

```rust
pub fn insert(&mut self, key: &[u8], value: &[u8]) {
    // Cheap check - always run
    assert!(key.len() <= KEY_LENGTH_BYTES_MAX);

    // Expensive check - debug only
    debug_assert!(self.validate_key_uniqueness(key));

    // ...
}
```

## Verification Pyramid (CLI-First)

Kelpie uses a **verification pyramid** with increasing confidence levels. Run these directly via CLI (not through MCP tool wrappers).

### Quick Reference

```bash
# Level 1: Unit Tests (~1-5 seconds)
cargo test -p kelpie-core
cargo test -p kelpie-server --lib

# Level 2: DST - Deterministic Simulation (~5-30 seconds)
cargo test -p kelpie-dst --release
DST_SEED=12345 cargo test -p kelpie-dst  # Reproducible

# Level 3: Integration Tests (~30-60 seconds)
cargo test -p kelpie-server --test '*'

# Level 4: Stateright Model Checking (~60+ seconds)
cargo test stateright_* -- --ignored

# Level 5: Kani Bounded Proofs (when installed)
cargo kani --package kelpie-core --harness verify_single_activation

# Full Verification (before commit)
cargo test --workspace && cargo clippy --workspace -- -D warnings && cargo fmt --check
```

### When to Use Each Level

| Level | Time | Use When |
|-------|------|----------|
| **Unit** | ~5s | After every change |
| **DST** | ~30s | After logic changes, before commit |
| **Integration** | ~60s | Before merging PRs |
| **Stateright** | ~60s+ | For distributed invariants |
| **Kani** | varies | For critical proofs |

### Hard Controls Enforce This

- Pre-commit hook runs `cargo test` + `cargo clippy`
- Task completion requires verification evidence
- Index queries warn if code changed since last test

## DST (Deterministic Simulation Testing)

### Core Principles

1. **All randomness flows from a single seed** - set `DST_SEED` to reproduce
2. **Simulated time** - `SimClock` replaces wall clock
3. **Explicit fault injection** - 16+ fault types with configurable probability
4. **Deterministic network** - `SimNetwork` with partitions, delays, reordering

### Running DST Tests

```bash
# Run with random seed (logged for reproduction)
cargo test -p kelpie-dst

# Reproduce specific run
DST_SEED=12345 cargo test -p kelpie-dst

# Stress test (longer, more iterations)
cargo test -p kelpie-dst stress --release -- --ignored
```

### Writing DST Tests

```rust
use kelpie_dst::{Simulation, SimConfig, FaultConfig, FaultType};

#[test]
fn test_actor_under_faults() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.05))
        .run(|env| async move {
            // Test logic using env.storage, env.network, env.clock
            env.storage.write(b"key", b"value").await?;

            // Advance simulated time
            env.advance_time_ms(1000);

            // Verify invariants
            let value = env.storage.read(b"key").await?;
            assert_eq!(value, Some(Bytes::from("value")));

            Ok(())
        });

    assert!(result.is_ok());
}
```

### Fault Types

| Category | Fault Types |
|----------|-------------|
| Storage | `StorageWriteFail`, `StorageReadFail`, `StorageCorruption`, `StorageLatency`, `DiskFull` |
| Crash | `CrashBeforeWrite`, `CrashAfterWrite`, `CrashDuringTransaction` |
| Network | `NetworkPartition`, `NetworkDelay`, `NetworkPacketLoss`, `NetworkMessageReorder` |
| Time | `ClockSkew`, `ClockJump` |
| Resource | `OutOfMemory`, `CPUStarvation` |

### Test Categories

Kelpie has two types of tests with distinct purposes and characteristics:

#### True DST Tests (`*_dst.rs`)

**Characteristics:**
- Fully deterministic (same seed = same result)
- Use `Simulation` harness or DST components (SimStorage, SimClock, DeterministicRng)
- No external dependencies or uncontrolled systems
- Instant execution (virtual time, no real I/O)
- Reproducible with `DST_SEED` environment variable

**Examples:**
- `actor_lifecycle_dst.rs` - Actor state machine tests
- `memory_dst.rs` - Memory system tests
- `integration_chaos_dst.rs` - Many faults simultaneously (still deterministic!)

**When to use:** Testing distributed system logic, fault handling, race conditions, state machines

#### Chaos Tests (`*_chaos.rs`)

**Characteristics:**
- Non-deterministic (depend on external system state)
- Integrate with uncontrolled external systems
- Real I/O (slower)
- Harder to reproduce (external dependencies)
- Provide value for integration testing

**Examples:**
- `vm_backend_firecracker_chaos.rs` - Real Firecracker VM integration
- Tests using real network calls to external APIs
- Tests spawning external processes (git, shell, etc.)

**When to use:** Integration testing with real external systems that can't be fully mocked

**Note:** "Chaos" in test names like `integration_chaos_dst.rs` refers to **chaos engineering** (many simultaneous faults), not non-deterministic execution. These are still TRUE DST tests!

**Rule of thumb:** If it uses `Simulation` or DST components (SimStorage, SimClock, etc.), it's a DST test. If it requires real Firecracker, real network, or real external binaries, it's a Chaos test.

## Repo OS Infrastructure

Kelpie includes a **Repo OS** infrastructure for AI agent-driven development. This provides structural indexes, MCP tools, and verification-first workflows.

### Quick Reference

```bash
# Build all indexes (Python indexer with tree-sitter)
cd tools/mcp-kelpie-python && uv run --prerelease=allow python3 -c "
from mcp_kelpie.indexer import build_indexes
build_indexes('/path/to/kelpie', '.kelpie-index/structural')
"

# Run indexer tests
cd tools/mcp-kelpie-python && uv run --prerelease=allow pytest tests/test_indexer.py -v

# Run MCP server tests (92 tests)
cd tools/mcp-kelpie-python && uv run --prerelease=allow pytest tests/ -v
```

### Structural Indexes

Located in `.kelpie-index/structural/`:

| Index | Description | Query Example |
|-------|-------------|---------------|
| `symbols.json` | Functions, structs, traits, impls | Find all `pub async fn` |
| `dependencies.json` | Crate dependency graph | Which crates depend on kelpie-core? |
| `tests.json` | All tests with topics and commands | Find tests for "storage" |
| `modules.json` | Module hierarchy per crate | What modules exist in kelpie-server? |

### MCP Server (VDE-Aligned Python)

The MCP server (`tools/mcp-kelpie-python/`) provides 33 tools for AI agent development, built with VDE (Verification-Driven Exploration) architecture.

**Architecture:**
- **Single Python server** - All tools in one MCP server (not separate TypeScript/Rust)
- **tree-sitter indexing** - Fast, accurate Rust parsing for structural indexes
- **AgentFS integration** - Persistent state via `agentfs-sdk`
- **Sandboxed execution** - RLM REPL with RestrictedPython

**Tool categories (33 tools):**
- **REPL (5)** - `repl_load`, `repl_exec`, `repl_query`, `repl_state`, `repl_clear`
- **VFS/AgentFS (11)** - `vfs_init`, `vfs_fact_*`, `vfs_invariant_*`, `vfs_tool_*`
- **Index (6)** - `index_symbols`, `index_tests`, `index_modules`, `index_deps`, `index_status`, `index_refresh`
- **Verification (4)** - `verify_claim`, `verify_all_tests`, `verify_clippy`, `verify_fmt`
- **DST (3)** - `dst_coverage_check`, `dst_gaps_report`, `harness_check`
- **Codebase (4)** - `codebase_grep`, `codebase_peek`, `codebase_read_section`, `codebase_list_files`

**Running the server:**
```bash
cd tools/mcp-kelpie-python
KELPIE_CODEBASE_PATH=/path/to/kelpie uv run --prerelease=allow mcp-kelpie
```

**Note**: For verification, prefer CLI commands directly over MCP wrappers. MCP is for state management, indexing, and RLM execution.

### Hard Controls

The infrastructure enforces verification-first development:

1. **Pre-commit hooks** - Tests, clippy, and formatting must pass
2. **Index freshness gates** - Stale indexes trigger warnings
3. **Completion verification** - `state_task_complete` requires proof
4. **Audit trail** - All MCP operations logged to `.agentfs/agent.db`

### AgentFS Storage

State is stored using [Turso AgentFS](https://github.com/tursodatabase/agentfs) Python SDK:

```bash
# Namespaced keys (VFS pattern)
session:{id}     # Verification session
fact:{id}        # Verified facts with evidence
invariant:{name} # Invariant verification status
tool:{id}        # Tool call tracking

# Storage location
.agentfs/agentfs-{session_id}.db  # SQLite database per session
```

The `agentfs-sdk` Python package handles all persistence. State survives across MCP restarts.

### RLM Skills (Verification-First Development)

**Core Principle**: Trust execution, not documentation. Verify before claiming complete.

```
┌─────────────────────────────────────┐
│  Trusted Sources                    │
├─────────────────────────────────────┤
│  ✅ Test execution output           │
│  ✅ Command execution results       │
│  ✅ Actual code (after reading it)  │
└─────────────────────────────────────┘

┌─────────────────────────────────────┐
│  Untrusted Sources                  │
├─────────────────────────────────────┤
│  ❌ Documentation (might be stale)  │
│  ❌ Comments (might be outdated)    │
│  ❌ Plan checkboxes (might be lies) │
└─────────────────────────────────────┘
```

#### Task Workflow (`/rlm-task`)
For any non-trivial task:
1. **Load constraints** - Read `.vision/CONSTRAINTS.md` (non-negotiable rules)
2. **Query indexes** - Use `index_symbols`, `index_modules` to understand scope
3. **Create plan** - Save to `.progress/NNN_YYYYMMDD_task-name.md`
4. **Execute phases** - Verify each by running tests, not reading docs
5. **Final verification** - `cargo test`, `cargo clippy`, `cargo fmt`

#### Verification Workflow (`/rlm-verify`)
When asked "Is X implemented?" or "Does Y work?":
1. **Find tests** - Search for relevant test files
2. **Run tests** - Execute and capture output
3. **Report results** - What you OBSERVED, not what docs claim

```bash
# Example: Verifying snapshot feature
cargo test snapshot  # Run relevant tests
# Report: "Ran 5 snapshot tests, 4 passed, 1 failed (restore_concurrent)"
```

#### Exploration Workflow (`/rlm-explore`)
Start broad, narrow down:
1. **Modules** - `cargo metadata` to see crate structure
2. **Dependencies** - `index_deps` to understand relationships
3. **Symbols** - `grep` for specific implementations
4. **Code reading** - Read the actual implementation
5. **Test verification** - Run tests to confirm understanding

#### Handoff Protocol (`/rlm-handoff`)
When taking over from another agent:
1. **NEVER trust checkboxes** - Re-verify completed phases
2. **Run the tests** - See if claimed work actually passes
3. **Check for regressions** - Code may have changed since completion
4. **Document findings** - Update plan with actual verification status

#### Slop Hunt (`/rlm-slop-hunt`)
Periodic cleanup for:
- **Dead code** - Unused functions, dependencies
- **Orphaned code** - Old implementations not deleted
- **Duplicates** - Same logic in multiple places
- **Fake DST** - Tests claiming determinism but aren't
- **Incomplete code** - TODOs, stubs in production

```bash
# Detection
grep -r "TODO\|FIXME" crates/ --include="*.rs"
grep -r "unwrap()\|expect(" crates/ --include="*.rs"
cargo clippy --workspace -- -W dead_code
```

### Test Coverage

| Component | Tests | Command |
|-----------|-------|---------|
| Indexer (Python) | 21 | `cd tools/mcp-kelpie-python && uv run pytest tests/test_indexer.py -v` |
| RLM Environment | 49 | `cd tools/mcp-kelpie-python && uv run pytest tests/test_rlm.py -v` |
| MCP Tools | 22 | `cd tools/mcp-kelpie-python && uv run pytest tests/test_tools.py -v` |
| **Total** | **92** | `cd tools/mcp-kelpie-python && uv run pytest tests/ -v` |

## Vision-Aligned Planning (MANDATORY)

### Before Starting ANY Non-Trivial Task

**STOP.** Before starting work that requires 3+ steps, touches multiple files, or needs research, you MUST:

#### 1. Check for Vision Files

- **Read `.vision/CONSTRAINTS.md`** - Non-negotiable rules and principles
- **Read `VISION.md`** - Project goals and architecture (in root)
- **Read existing `.progress/` plans** - Understand current state

#### 2. Create a Numbered Plan File

**ALWAYS** save to `.progress/NNN_YYYYMMDD_HHMMSS_task-name.md` BEFORE writing code.

- `NNN` = next sequence number (001, 002, etc.)
- Use `.progress/templates/plan.md` as the template
- Fill in ALL required sections (see template)

**DO NOT skip planning. DO NOT start coding without a plan file.**

#### 3. Required Plan Sections (DO NOT SKIP)

These sections are **MANDATORY**:

1. **Options & Decisions**
   - List 2-3 options considered for each major decision
   - Explain pros/cons of each
   - State which option chosen and WHY (reasoning)
   - List trade-offs accepted

2. **Quick Decision Log**
   - Log ALL decisions, even small ones
   - Format: Time | Decision | Rationale | Trade-off
   - This is your audit trail

3. **What to Try** (UPDATE AFTER EVERY PHASE)
   - Works Now: What user can test, exact steps, expected result
   - Doesn't Work Yet: What's missing, why, when expected
   - Known Limitations: Caveats, edge cases

**If you skip these sections, the plan is incomplete.**

### During Execution

1. **Update plan after each phase** - Mark phases complete, log findings
2. **Log decisions in Quick Decision Log** - Every choice, with rationale
3. **Update "What to Try" after EVERY phase** - Not just at the end
4. **Re-read plan before major decisions** - Keeps goals in attention window
5. **Document deviations** - If implementation differs from plan, note why

**The 2-Action Rule:** After every 2 significant operations, save key findings to the plan file.

### Before Completion

1. **Verify required sections are filled** - Options, Decision Log, What to Try
2. **Run verification checks:**
   ```bash
   cargo test           # All tests must pass
   cargo clippy         # Fix all warnings
   cargo fmt --check    # Code must be formatted
   ```
3. **Run `/no-cap`** - Verify no hacks, placeholders, or incomplete code
4. **Check vision alignment** - Does result match CONSTRAINTS.md requirements?
5. **Verify DST coverage** - Critical paths have simulation tests?
6. **Update plan status** - Mark as complete with verification status
7. **Commit and push** - Use conventional commit format

### Multi-Instance Coordination

When multiple Claude instances work on shared tasks:
- Read `.progress/` plans before starting work
- Claim phases in the Instance Log section
- Update status frequently to avoid conflicts
- Use findings section for shared discoveries

### Plan File Format

`.progress/NNN_YYYYMMDD_HHMMSS_descriptive-task-name.md`

Where:
- `NNN` = sequence number (001, 002, 003, ...)
- `YYYYMMDD_HHMMSS` = timestamp
- `descriptive-task-name` = kebab-case description

Example: `.progress/001_20260112_120000_add-fdb-backend.md`

### Quick Workflow Reference

```
┌─────────────────────────────────────────────────────────────┐
│  Before Starting                                            │
│  1. Read .vision/CONSTRAINTS.md                             │
│  2. Read existing .progress/ plans                          │
│  3. Create new numbered plan file                           │
│  4. Fill in: Options, Decisions, Quick Log                  │
├─────────────────────────────────────────────────────────────┤
│  During Work                                                │
│  1. Update plan after each phase                            │
│  2. Log all decisions                                       │
│  3. Update "What to Try" section                            │
│  4. Re-read plan before big decisions                       │
├─────────────────────────────────────────────────────────────┤
│  Before Completing                                          │
│  1. cargo test && cargo clippy && cargo fmt                 │
│  2. Run /no-cap                                             │
│  3. Verify DST coverage                                     │
│  4. Update plan completion notes                            │
│  5. Commit and push                                         │
└─────────────────────────────────────────────────────────────┘
```

---

## Code Style

### Module Organization

```rust
//! Module-level documentation with TigerStyle note
//!
//! TigerStyle: Brief description of the module's invariants.

// Imports grouped by: std, external crates, internal crates, local modules
use std::collections::HashMap;
use std::sync::Arc;

use bytes::Bytes;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use kelpie_core::{ActorId, Error, Result};

use crate::internal_module;
```

### Struct Layout

```rust
/// Brief description
///
/// Longer description if needed.
#[derive(Debug, Clone)]
pub struct ActorContext<S> {
    // Public fields at top with documentation
    /// The actor's unique identifier
    pub id: ActorId,
    /// The actor's state
    pub state: S,

    // Private fields below
    kv: Box<dyn ActorKV>,
    runtime: ActorRuntime,
}
```

### Function Signatures

```rust
/// Brief description of what the function does.
///
/// # Arguments
/// * `key` - The key to look up
///
/// # Returns
/// The value if found, None otherwise
///
/// # Errors
/// Returns `Error::StorageReadFailed` if the storage operation fails
pub async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> {
    // Preconditions
    assert!(!key.is_empty(), "key cannot be empty");
    assert!(key.len() <= KEY_LENGTH_BYTES_MAX);

    // Implementation...
}
```

## Testing Guidelines

### Test Naming

```rust
#[test]
fn test_actor_id_valid() { }           // Positive case
#[test]
fn test_actor_id_too_long() { }        // Edge case
#[test]
fn test_actor_id_invalid_chars() { }   // Error case
```

### Property-Based Testing

Use proptest for invariant testing:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_actor_id_roundtrip(namespace in "[a-z]{1,10}", id in "[a-z0-9]{1,10}") {
        let actor_id = ActorId::new(&namespace, &id).unwrap();
        let serialized = serde_json::to_string(&actor_id).unwrap();
        let deserialized: ActorId = serde_json::from_str(&serialized).unwrap();
        assert_eq!(actor_id, deserialized);
    }
}
```

### DST Test Coverage

Every critical path must have DST coverage:
- [ ] Actor activation/deactivation
- [ ] State persistence and recovery
- [ ] Cross-actor invocation
- [ ] Failure detection and recovery
- [ ] Migration correctness

## Error Handling

### Error Types (kelpie-core)

```rust
#[derive(Error, Debug)]
pub enum Error {
    #[error("actor not found: {id}")]
    ActorNotFound { id: String },

    #[error("storage read failed for key '{key}': {reason}")]
    StorageReadFailed { key: String, reason: String },

    // ...
}
```

### Result Type

```rust
// All fallible operations return kelpie_core::Result
pub type Result<T> = std::result::Result<T, Error>;
```

### Retriable Errors

```rust
impl Error {
    /// Whether this error is retriable
    pub fn is_retriable(&self) -> bool {
        matches!(self,
            Error::StorageReadFailed { .. } |
            Error::NetworkTimeout { .. } |
            Error::TransactionConflict
        )
    }
}
```

## Performance Guidelines

### Allocation

- Prefer stack allocation for small, fixed-size data
- Use `Bytes` for byte buffers (zero-copy slicing)
- Pool allocations for hot paths

### Async

- Use `tokio` runtime with `current_thread` flavor for DST
- Avoid blocking operations in async contexts
- Use channels for cross-task communication

### Benchmarking

```bash
# Run all benchmarks
cargo bench

# Run specific benchmark
cargo bench -p kelpie-runtime -- single_actor
```

## Documentation

### ADRs (Architecture Decision Records)

All significant architectural decisions are documented in `docs/adr/`:

- `001-virtual-actor-model.md` - Why virtual actors
- `002-foundationdb-integration.md` - Storage layer design
- `003-wasm-actor-runtime.md` - WASM support
- `004-linearizability-guarantees.md` - Consistency model
- `005-dst-framework.md` - Testing approach

### Code Documentation

- All public items must have doc comments
- Include examples for complex APIs
- Document invariants and safety requirements

## Commit Policy: Only Working Software

**Never commit broken code.** Every commit must represent working software.

### Pre-Commit Verification

Before every commit, you MUST verify the code works:

```bash
# Required before EVERY commit
cargo test           # All tests must pass
cargo clippy         # No warnings allowed
cargo fmt --check    # Code must be formatted
```

### Why This Matters

- Every commit is a potential rollback point
- Broken commits make `git bisect` useless
- CI should never be the first place code is tested
- Other developers should be able to checkout any commit

### Commit Checklist

Before running `git commit`:

1. **Run `cargo test`** - All tests must pass (currently 74+ tests)
2. **Run `cargo clippy`** - Fix any warnings
3. **Run `cargo fmt`** - Code must be formatted
4. **Review changes** - `git diff` to verify what's being committed
5. **Write clear message** - Describe what and why, not how

### If Tests Fail

Do NOT commit. Instead:
1. Fix the failing tests
2. If the fix is complex, consider `git stash` to save work
3. Never use `--no-verify` to skip pre-commit hooks
4. Never commit with `// TODO: fix this test` comments

## Acceptance Criteria: No Stubs, Verification First

**Every feature must have real implementation and empirical verification.**

### No Stubs Policy

Code must be functional, not placeholder:

```rust
// FORBIDDEN - stub implementation
fn execute_tool(&self, name: &str) -> String {
    "Tool execution not yet implemented".to_string()
}

// FORBIDDEN - TODO comments as implementation
async fn snapshot(&self) -> Result<Snapshot> {
    // TODO: implement snapshotting
    Ok(Snapshot::empty())
}

// REQUIRED - real implementation or don't merge
fn execute_tool(&self, name: &str, input: &Value) -> String {
    match name {
        "shell" => {
            let command = input.get("command").and_then(|v| v.as_str()).unwrap_or("");
            self.sandbox.exec("sh", &["-c", command]).await
        }
        _ => format!("Unknown tool: {}", name),
    }
}
```

### Verification-First Development

You must **empirically prove** features work before considering them done:

1. **Unit tests** - Function-level correctness
2. **Integration tests** - Component interaction
3. **Manual verification** - Actually run it and see it work
4. **DST coverage** - Behavior under faults

### Verification Checklist

Before marking any feature complete:

| Check | How to Verify |
|-------|---------------|
| Code compiles | `cargo build` |
| Tests pass | `cargo test` |
| No warnings | `cargo clippy` |
| Actually works | Run the server, hit the endpoint, see real output |
| Edge cases handled | Test with empty input, large input, malformed input |
| Errors are meaningful | Trigger errors, verify messages are actionable |

### Example: Verifying LLM Integration

Don't just write the code. Prove it works:

```bash
# 1. Start the server
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server

# 2. Create an agent with memory
curl -X POST http://localhost:8283/v1/agents \
  -H "Content-Type: application/json" \
  -d '{"name": "test", "memory_blocks": [{"label": "persona", "value": "You are helpful"}]}'

# 3. Send a message and verify LLM response (not stub)
curl -X POST http://localhost:8283/v1/agents/{id}/messages \
  -H "Content-Type: application/json" \
  -d '{"role": "user", "content": "What is 2+2?"}'

# 4. Verify response is from real LLM, not "stub response"
# 5. Verify memory blocks appear in the prompt (check logs)
# 6. Test tool execution - ask LLM to run a command
```

### What "Done" Means

A feature is done when:

- [ ] Implementation is complete (no TODOs, no stubs)
- [ ] Unit tests exist and pass
- [ ] Integration test exists and passes
- [ ] You have personally run it and seen it work
- [ ] Error paths have been tested
- [ ] Documentation updated if needed

### Current Codebase Audit

Run this evaluation periodically:

```bash
# Find stubs and TODOs
grep -r "TODO" --include="*.rs" crates/
grep -r "unimplemented!" --include="*.rs" crates/
grep -r "stub" --include="*.rs" crates/
grep -r "not yet implemented" --include="*.rs" crates/

# Find empty/placeholder implementations
grep -r "Ok(())" --include="*.rs" crates/ | grep -v test

# Verify all tests pass
cargo test

# Check test coverage (if installed)
cargo tarpaulin --out Html
```

## Contributing

1. Create a branch from `main`
2. Make changes following this guide
3. **Run `cargo test` and ensure ALL tests pass**
4. **Run `cargo clippy` and fix ALL warnings**
5. Run `cargo fmt` to format code
6. **Manually verify the feature works end-to-end**
7. Update documentation as needed
8. Create PR with clear description

## References

- [TigerStyle](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md)
- [NOLA - Go Virtual Actors](https://github.com/richardartoul/nola)
- [FoundationDB Testing](https://www.foundationdb.org/files/fdb-paper.pdf)
- [Stateright - Rust Model Checker](https://github.com/stateright/stateright)

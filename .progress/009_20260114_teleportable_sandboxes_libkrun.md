# Task: Teleportable Sandboxes with libkrun

**Created:** 2026-01-14 10:00:00
**State:** PLANNING

---

## Vision Alignment

**Vision files read:** CONSTRAINTS.md

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - DST coverage for sandbox lifecycle
- TigerStyle safety principles (CONSTRAINTS.md §3) - Explicit constants, assertions
- No placeholders in production (CONSTRAINTS.md §4)
- Tool execution with sandbox isolation is a critical path requiring DST

---

## Task Description

Implement **teleportable sandboxes** using [libkrun](https://github.com/containers/libkrun) to enable:

1. **Cross-platform development**: Develop on Mac (Apple Silicon), deploy to Linux cloud
2. **Full mid-execution teleportation**: Snapshot running agents mid-tool-execution
3. **Architecture-aware teleportation**: Full VM snapshots within same architecture, application checkpoints across architectures

**Key capability:** An agent running locally on a Mac can be teleported mid-execution to AWS Graviton (ARM64), continue running, and teleport back.

---

## Options & Decisions [REQUIRED]

### Decision 1: Virtualization Backend

**Context:** Need VM-level isolation that works on both macOS (Apple Silicon) and Linux.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: libkrun | Lightweight VM library using HVF (Mac) / KVM (Linux) | Cross-platform, ~50ms boot, minimal footprint, Rust impl | Newer, less battle-tested than Firecracker |
| B: Firecracker only | Keep existing Firecracker, add Mac workaround | Battle-tested, proven at scale | Linux-only, no native Mac support |
| C: QEMU | Full VM emulation | Very mature, cross-arch emulation | Heavy, slow boot, complex |
| D: Docker + Lima | Containers on Mac via Lima | Easy setup | Not true VM isolation, no mid-exec snapshot |

**Decision:** **Option A (libkrun)** - Only option providing native VM isolation on both macOS ARM64 and Linux with snapshot/restore capabilities. We'll keep Firecracker as a feature-gated alternative for Linux deployments that prefer it.

**Trade-offs accepted:**
- libkrun is newer/less proven than Firecracker - mitigated by DST testing
- Smaller community - acceptable given active development by Red Hat
- We maintain two VM backends - worth it for cross-platform support

---

### Decision 2: Snapshot Type Architecture

**Context:** Need to support both same-architecture (full VM snapshot) and cross-architecture (app-level checkpoint) teleportation.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Single snapshot type | One format for all cases | Simple | Can't do mid-exec cross-arch |
| B: Two types (VM + App) | VM snapshot for same-arch, app checkpoint for cross-arch | Covers all cases | Two code paths |
| C: Three types (Suspend + Teleport + Checkpoint) | Add memory-only suspend for same-host | Maximum flexibility | More complexity |

**Decision:** **Option C (Three types)** - Different use cases have different needs:
- **Suspend**: Fast same-host pause/resume (memory only, ~50MB, <1s)
- **Teleport**: Same-architecture transfer with mid-exec (memory + CPU + disk, ~500MB-2GB, ~5s)
- **Checkpoint**: Cross-architecture transfer at safe points (app state + workspace, ~10-100MB, <1s)

**Trade-offs accepted:**
- More complex snapshot system - worth it for flexibility
- Three code paths to maintain - each is relatively simple
- Users need to understand which type to use - we can auto-select based on target

---

### Decision 3: Teleport Package Storage

**Context:** Where to store teleport packages for transfer between machines.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: S3/GCS | Cloud object storage | Scalable, accessible anywhere | External dependency, latency |
| B: FoundationDB | Use existing FDB cluster | Already integrated, transactional | Size limits, not designed for blobs |
| C: Hybrid | Metadata in FDB, blobs in S3 | Best of both | More complex |
| D: Direct transfer | P2P between nodes | No storage needed | Requires both online simultaneously |

**Decision:** **Option C (Hybrid)** - Store teleport metadata and small checkpoints in FDB, large VM snapshots in S3/GCS. This aligns with how we handle actor state (FDB) vs large blobs.

**Trade-offs accepted:**
- Two storage systems to manage - FDB already exists, S3 is standard
- Requires S3 credentials for full teleport - checkpoint-only mode works with just FDB

---

### Decision 4: Base Image Strategy

**Context:** VMs need a base filesystem image. How to manage these across architectures.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Single multi-arch image | One image built for both ARM64 and x86_64 | Consistent environment | Larger build process |
| B: Separate images per arch | Different images for each architecture | Simpler builds | Potential drift |
| C: Minimal base + overlay | Tiny base, agent-specific overlays | Flexible, small | More complexity |

**Decision:** **Option A (Single multi-arch image)** - Build one logical image with ARM64 and x86_64 variants. Use Alpine Linux for minimal size. Version-lock the image to ensure teleport compatibility.

**Trade-offs accepted:**
- Build process more complex - one-time setup
- Must keep images in sync - versioning handles this

---

### Decision 5: libkrun Integration Approach

**Context:** libkrun is a C library. How to integrate with Rust.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: FFI bindings | Direct C bindings via bindgen | Full control, minimal overhead | Manual memory management |
| B: Safe wrapper crate | Create kelpie-libkrun crate with safe Rust API | Safe, idiomatic | More code to maintain |
| C: Fork libkrunrs | Use/fork existing Rust wrapper | Less work | May not have all features |

**Decision:** **Option B (Safe wrapper crate)** - Create `kelpie-libkrun` crate that provides safe Rust bindings to libkrun. This isolates unsafe code and provides idiomatic Rust API.

**Trade-offs accepted:**
- More upfront work - pays off in safety and maintainability
- Must track libkrun API changes - pin to stable version

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| Planning | Use libkrun over QEMU/others | Only cross-platform option with VM snapshots | Less battle-tested |
| Planning | Three snapshot types | Different use cases need different granularity | More complexity |
| Planning | Hybrid storage (FDB + S3) | Metadata in FDB, blobs in S3 | Two systems |
| Planning | Multi-arch Alpine base image | Consistency across architectures | Build complexity |
| Planning | Safe Rust wrapper for libkrun | Isolate unsafe code | More upfront work |
| Planning | **Phase 0 = DST Harness First** | CONSTRAINTS.md mandates simulation-first | Upfront harness work before any feature code |
| Planning | DST tests written BEFORE impl | Find bugs through simulation, not production | Tests fail initially (expected) |
| Planning | 12 new fault types for sandbox/teleport | Need fault injection for VM crashes, snapshot corruption, teleport failures | Harness complexity |

---

## Implementation Plan

> **⚠️ DST-FIRST MANDATE**: Every phase follows the simulation-first workflow from CONSTRAINTS.md:
> 1. **HARNESS CHECK** - Extend kelpie-dst if needed for new fault types
> 2. **WRITE DST TEST FIRST** - Test must fail initially (feature doesn't exist)
> 3. **IMPLEMENT** - Write production code
> 4. **RUN SIMULATION** - Execute with fault injection, multiple seeds
> 5. **FIX & ITERATE** - Fix bugs found by simulation until passing
> 6. **VERIFY DETERMINISM** - Same seed = same behavior

---

### Phase 0: DST Harness Extension (MUST DO FIRST)

**Goal:** Extend kelpie-dst to support sandbox simulation BEFORE any implementation.

**Harness Check - New Fault Types Needed:**

| Fault Type | Description | Category |
|------------|-------------|----------|
| `SandboxBootFail` | VM fails to boot | Sandbox |
| `SandboxCrash` | VM crashes unexpectedly | Sandbox |
| `SandboxPauseFail` | Pause operation fails | Sandbox |
| `SandboxResumeFail` | Resume operation fails | Sandbox |
| `SnapshotCreateFail` | Snapshot creation fails | Snapshot |
| `SnapshotCorruption` | Snapshot data corrupted | Snapshot |
| `SnapshotRestoreFail` | Restore from snapshot fails | Snapshot |
| `TeleportUploadFail` | Upload to storage fails | Teleport |
| `TeleportDownloadFail` | Download from storage fails | Teleport |
| `TeleportTimeout` | Transfer times out | Teleport |
| `ArchitectureMismatch` | Wrong arch on restore | Teleport |
| `BaseImageMismatch` | Wrong base image version | Teleport |

**Implementation:**
- [ ] Add `FaultType::Sandbox*` variants to kelpie-dst
- [ ] Add `FaultType::Snapshot*` variants
- [ ] Add `FaultType::Teleport*` variants
- [ ] Implement `SimSandbox` - simulated sandbox for DST
- [ ] Implement `SimTeleportStorage` - simulated S3/FDB for DST
- [ ] Verify harness can inject all fault types

**Files:**
```
crates/kelpie-dst/src/
├── fault.rs           # Add new fault types
├── sim_sandbox.rs     # NEW: Simulated sandbox
├── sim_teleport.rs    # NEW: Simulated teleport storage
└── sim_env.rs         # Update to include sandbox/teleport
```

**Validation:** Harness must be able to run this test skeleton:
```rust
#[test]
fn test_sandbox_lifecycle_with_faults() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.1))
        .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.05))
        .run(|env| async move {
            // This test will fail until Phase 1-2 implement the feature
            let sandbox = env.sandbox_factory.create(config).await?;
            sandbox.start().await?;
            let snapshot = sandbox.snapshot().await?;
            sandbox.restore(&snapshot).await?;
            Ok(())
        });
}
```

---

### Phase 1: libkrun Foundation (kelpie-libkrun crate)

**DST-FIRST WORKFLOW:**

**Step 1.1: Write DST Tests First (tests will fail)**
```rust
// crates/kelpie-dst/tests/libkrun_dst.rs
#[test]
fn test_vm_lifecycle_under_faults() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.05))
        .run(|env| async move {
            let vm = env.create_vm(VmConfig::default()).await?;
            vm.start().await?;

            // Verify VM survives faults or handles them gracefully
            for _ in 0..10 {
                vm.exec("echo", &["test"]).await?;
                env.advance_time_ms(100);
            }

            vm.stop().await?;
            Ok(())
        });
}

#[test]
fn test_vm_pause_resume_under_faults() {
    // ... similar pattern
}
```

**Step 1.2: Implement libkrun Bindings**
- [ ] Create `crates/kelpie-libkrun/` crate
- [ ] Add libkrun C header parsing via bindgen
- [ ] Implement safe Rust wrapper types:
  - [ ] `VmConfig` - VM configuration (vCPUs, memory, devices)
  - [ ] `VmInstance` - Running VM handle
  - [ ] `VirtioFs` - Filesystem passthrough
  - [ ] `VirtioVsock` - Host-guest communication
  - [ ] `VmSnapshot` - Snapshot handle
- [ ] Implement lifecycle methods with TigerStyle assertions
- [ ] Add platform detection (macOS HVF vs Linux KVM)

**Step 1.3: Run DST, Fix Bugs, Iterate**
```bash
# Run with random seeds until passing
cargo test -p kelpie-dst test_vm_lifecycle
DST_SEED=12345 cargo test -p kelpie-dst test_vm_lifecycle

# Stress test
cargo test -p kelpie-dst test_vm_lifecycle --release -- --ignored
```

**Step 1.4: Verify Determinism**
```bash
# Same seed must produce identical results
DST_SEED=99999 cargo test -p kelpie-dst test_vm_lifecycle
DST_SEED=99999 cargo test -p kelpie-dst test_vm_lifecycle  # Must match
```

**Files:**
```
crates/kelpie-libkrun/
├── Cargo.toml
├── build.rs           # bindgen setup
├── src/
│   ├── lib.rs
│   ├── bindings.rs    # Raw FFI bindings
│   ├── config.rs      # VmConfig
│   ├── instance.rs    # VmInstance
│   ├── virtio.rs      # VirtioFs, VirtioVsock
│   ├── snapshot.rs    # VmSnapshot
│   └── platform.rs    # Platform detection
└── tests/
```

---

### Phase 2: LibkrunSandbox Implementation

**DST-FIRST WORKFLOW:**

**Step 2.1: Write DST Tests First (tests will fail)**
```rust
// crates/kelpie-dst/tests/sandbox_dst.rs
#[test]
fn test_sandbox_exec_under_faults() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.1))
        .with_fault(FaultConfig::new(FaultType::NetworkDelay, 0.2))
        .run(|env| async move {
            let sandbox = env.sandbox_factory.create(SandboxConfig::default()).await?;
            sandbox.start().await?;

            // Execute commands - must handle crashes gracefully
            let result = sandbox.exec("echo", &["hello"], ExecOptions::default()).await;

            // Either succeeds or returns proper error (no panics, no hangs)
            match result {
                Ok(output) => assert!(output.status.is_success()),
                Err(e) => assert!(e.is_retriable()),
            }

            Ok(())
        });
}

#[test]
fn test_sandbox_snapshot_restore_under_faults() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.05))
        .with_fault(FaultConfig::new(FaultType::SnapshotRestoreFail, 0.1))
        .run(|env| async move {
            let mut sandbox = env.sandbox_factory.create(SandboxConfig::default()).await?;
            sandbox.start().await?;

            // Modify state
            sandbox.exec("touch", &["/tmp/testfile"], ExecOptions::default()).await?;

            // Snapshot
            let snapshot = sandbox.snapshot().await?;

            // Restore (may fail due to faults - must handle gracefully)
            let restore_result = sandbox.restore(&snapshot).await;

            if restore_result.is_ok() {
                // If restore succeeded, file must exist
                let output = sandbox.exec("ls", &["/tmp/testfile"], ExecOptions::default()).await?;
                assert!(output.status.is_success());
            }

            Ok(())
        });
}
```

**Step 2.2: Implement LibkrunSandbox**
- [ ] Create `LibkrunSandbox` in kelpie-sandbox
- [ ] Implement `Sandbox` trait methods with proper error handling
- [ ] Implement `LibkrunSandboxFactory`
- [ ] Add guest agent for command execution (vsock protocol)
- [ ] Configure virtio-fs for workspace mounting
- [ ] Feature gate: `libkrun` feature

**Step 2.3: Run DST, Fix Bugs, Iterate**

**Step 2.4: Verify Determinism**

**Files:**
```
crates/kelpie-sandbox/src/
├── libkrun.rs         # LibkrunSandbox implementation
├── libkrun_config.rs  # LibkrunConfig
└── guest_agent/       # Guest-side agent (built into base image)
    ├── main.rs
    └── protocol.rs
```

---

### Phase 3: Snapshot Type System

**DST-FIRST WORKFLOW:**

**Step 3.1: Write DST Tests First**
```rust
#[test]
fn test_suspend_snapshot_under_faults() {
    // Test memory-only suspend with crash faults
}

#[test]
fn test_teleport_snapshot_under_faults() {
    // Test full VM snapshot with corruption faults
}

#[test]
fn test_checkpoint_snapshot_under_faults() {
    // Test app-level checkpoint with disk faults
}

#[test]
fn test_architecture_validation() {
    // Test that restoring ARM64 snapshot on x86 fails gracefully
}

#[test]
fn test_base_image_version_validation() {
    // Test that mismatched base image versions fail gracefully
}
```

**Step 3.2: Implement Snapshot Types**
- [ ] Define snapshot type enums and structs
- [ ] Implement `Suspend` snapshot (memory-only, same-host)
- [ ] Implement `Teleport` snapshot (full VM, same-arch)
- [ ] Implement `Checkpoint` snapshot (app state, cross-arch)
- [ ] Add snapshot validation (version, architecture, base image)
- [ ] Implement snapshot serialization (bincode for efficiency)

**Step 3.3: Run DST, Fix Bugs, Iterate**

**Step 3.4: Verify Determinism**

**Files:**
```
crates/kelpie-sandbox/src/
├── snapshot.rs        # Updated with SnapshotKind
├── teleport.rs        # TeleportPackage, teleportation logic
├── checkpoint.rs      # Application-level checkpoint
└── workspace.rs       # Workspace capture/restore
```

---

### Phase 4: Teleportation Service

**DST-FIRST WORKFLOW:**

**Step 4.1: Write DST Tests First**
```rust
#[test]
fn test_teleport_out_under_storage_faults() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::TeleportUploadFail, 0.2))
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .run(|env| async move {
            let agent = env.create_agent().await?;

            // Start tool execution
            agent.exec_tool("shell", json!({"command": "sleep 10"})).await;

            // Teleport mid-execution
            let teleport_result = env.teleport_service
                .teleport_out(&agent.id, Architecture::Arm64)
                .await;

            // Must either succeed or fail gracefully (no partial state)
            match teleport_result {
                Ok(package) => {
                    assert!(package.vm_state.is_some());
                    assert!(package.workspace_ref.is_some());
                }
                Err(e) => {
                    // Agent must still be in consistent state
                    assert!(agent.is_healthy().await);
                }
            }

            Ok(())
        });
}

#[test]
fn test_teleport_in_under_faults() {
    // Test restore with download failures, corruption
}

#[test]
fn test_cross_arch_teleport_requires_safe_point() {
    // Test that ARM64->x86 teleport fails if mid-execution
    // and succeeds if at safe point
}

#[test]
fn test_teleport_roundtrip_preserves_state() {
    // Teleport out -> teleport in -> verify identical state
}
```

**Step 4.2: Implement TeleportService**
- [ ] Create `TeleportService` in kelpie-server
- [ ] Implement storage backend (FDB metadata + S3 blobs)
- [ ] Add teleport API endpoints
- [ ] Implement architecture detection and routing
- [ ] Handle teleport lifecycle with proper cleanup on failure

**Step 4.3: Run DST, Fix Bugs, Iterate**

**Step 4.4: Verify Determinism**

**Files:**
```
crates/kelpie-server/src/
├── service/
│   └── teleport_service.rs
├── api/
│   └── teleport_api.rs
└── storage/
    ├── teleport_storage.rs
    └── blob_storage.rs    # S3/local abstraction
```

---

### Phase 5: Base Image Build System

**Goal:** Create reproducible multi-arch base images for sandboxes.

- [ ] Create base image build scripts (Alpine Linux base)
- [ ] Multi-arch build (ARM64 + x86_64)
- [ ] Image versioning system
- [ ] Image distribution (container registry)
- [ ] Kernel image management

**Files:**
```
images/
├── base/
│   ├── Dockerfile
│   ├── build.sh
│   └── guest-agent/
│       └── kelpie-guest
├── kernel/
│   ├── build-kernel.sh
│   └── config-arm64
│   └── config-x86_64
└── README.md
```

---

### Phase 6: Integration & Stress Testing

**Goal:** Full system DST with all components integrated.

**DST Tests:**
```rust
#[test]
fn test_full_teleport_workflow_under_chaos() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        // All fault types active
        .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.05))
        .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.05))
        .with_fault(FaultConfig::new(FaultType::TeleportUploadFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::NetworkPartition, 0.05))
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.05))
        .run(|env| async move {
            // Create agent, run tools, teleport, verify state
            // Must handle all faults gracefully
        });
}

#[test]
#[ignore] // Long-running stress test
fn stress_test_concurrent_teleports() {
    // 100 concurrent agents teleporting
}

#[test]
#[ignore]
fn stress_test_large_workspace_teleport() {
    // 10GB workspace teleport
}

#[test]
#[ignore]
fn stress_test_rapid_suspend_resume() {
    // 1000 suspend/resume cycles
}
```

---

### Phase 7: CLI & Developer Experience

**Goal:** Make teleportation easy to use from CLI.

- [ ] Add teleport commands to kelpie-cli:
  - [ ] `kelpie teleport out <agent-id> [--target <host>]`
  - [ ] `kelpie teleport in <package-file>`
  - [ ] `kelpie teleport status <teleport-id>`
  - [ ] `kelpie sandbox list` - List running sandboxes
  - [ ] `kelpie sandbox attach <id>` - Attach to sandbox shell
- [ ] Add configuration
- [ ] Developer workflow documentation

---

## Architecture Summary

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           KELPIE SYSTEM                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                      ACTOR RUNTIME                               │   │
│  │  ┌────────────────────────────────────────────────────────────┐ │   │
│  │  │                    AgentActor                               │ │   │
│  │  │  - Conversation history                                     │ │   │
│  │  │  - Memory blocks                                            │ │   │
│  │  │  - Tool execution → delegates to sandbox                   │ │   │
│  │  └────────────────────────────────────────────────────────────┘ │   │
│  └──────────────────────────────┬──────────────────────────────────┘   │
│                                 │                                       │
│  ┌──────────────────────────────▼──────────────────────────────────┐   │
│  │                      SANDBOX LAYER                               │   │
│  │                                                                  │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │   │
│  │  │  LibkrunSandbox │  │ FirecrackerSand │  │  ProcessSandbox │  │   │
│  │  │  (Mac + Linux)  │  │  (Linux only)   │  │   (Fallback)    │  │   │
│  │  │                 │  │                 │  │                 │  │   │
│  │  │  ┌───────────┐  │  │                 │  │                 │  │   │
│  │  │  │ libkrun   │  │  │                 │  │                 │  │   │
│  │  │  │ microVM   │  │  │                 │  │                 │  │   │
│  │  │  │ HVF / KVM │  │  │                 │  │                 │  │   │
│  │  │  └───────────┘  │  │                 │  │                 │  │   │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    TELEPORT SERVICE                              │   │
│  │                                                                  │   │
│  │  Snapshot Types:                                                 │   │
│  │  ┌──────────┐  ┌──────────┐  ┌────────────┐                     │   │
│  │  │ SUSPEND  │  │ TELEPORT │  │ CHECKPOINT │                     │   │
│  │  │ (memory) │  │ (full VM)│  │ (app state)│                     │   │
│  │  │ same-host│  │ same-arch│  │ cross-arch │                     │   │
│  │  │ <1s      │  │ ~5s      │  │ <1s        │                     │   │
│  │  └──────────┘  └──────────┘  └────────────┘                     │   │
│  │                                                                  │   │
│  │  Storage: FDB (metadata) + S3 (blobs)                           │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘

                        TELEPORTATION FLOWS
═══════════════════════════════════════════════════════════════════════════

  SAME ARCHITECTURE (Full Teleport, Mid-Execution OK)
  ───────────────────────────────────────────────────

  Mac ARM64                              AWS Graviton ARM64
  ┌──────────────┐                       ┌──────────────┐
  │ AgentActor   │   TeleportPackage     │ AgentActor   │
  │ LibkrunVM    │ ───────────────────▶  │ LibkrunVM    │
  │ (mid-exec)   │   - VM memory         │ (continues)  │
  └──────────────┘   - CPU state         └──────────────┘
                     - Workspace
                     - Agent state


  CROSS ARCHITECTURE (Checkpoint at Safe Point)
  ─────────────────────────────────────────────

  Mac ARM64                              AWS x86_64
  ┌──────────────┐                       ┌──────────────┐
  │ AgentActor   │   Checkpoint          │ AgentActor   │
  │ LibkrunVM    │ ───────────────────▶  │ LibkrunVM    │
  │ (safe point) │   - Agent state       │ (new VM)     │
  └──────────────┘   - Workspace         └──────────────┘
                     - Environment
                     (no VM state)
```

---

## Checkpoints

- [x] Codebase understood
- [ ] Plan approved
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained**

**DST-First Implementation Order:**
- [ ] **Phase 0: DST Harness Extension** (MUST DO FIRST)
  - [ ] Add 12 new fault types (Sandbox*, Snapshot*, Teleport*)
  - [ ] Implement SimSandbox
  - [ ] Implement SimTeleportStorage
  - [ ] Verify harness can run test skeleton
- [ ] Phase 1: libkrun bindings (DST test first → implement → run DST → fix → verify determinism)
- [ ] Phase 2: LibkrunSandbox (DST test first → implement → run DST → fix → verify determinism)
- [ ] Phase 3: Snapshot types (DST test first → implement → run DST → fix → verify determinism)
- [ ] Phase 4: Teleport service (DST test first → implement → run DST → fix → verify determinism)
- [ ] Phase 5: Base images
- [ ] Phase 6: Integration & Stress testing (full chaos DST)
- [ ] Phase 7: CLI

**Verification:**
- [ ] All DST tests passing with multiple seeds
- [ ] Determinism verified (same seed = same behavior)
- [ ] Stress tests passing (concurrent teleports, large workspaces)
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [ ] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**Unit tests:**
- kelpie-libkrun: Binding tests, config validation
- LibkrunSandbox: Lifecycle tests with mock VM
- Snapshot types: Serialization roundtrips
- TeleportService: Storage operations

**DST tests (critical path):**
- [ ] Sandbox lifecycle under faults (crash, timeout)
- [ ] Teleport with storage failures
- [ ] Checkpoint during agent execution
- [ ] Cross-arch validation
- [ ] Determinism verification

**Integration tests:**
- Full teleport: Mac → Mac (requires two Macs or VMs)
- Full teleport: Linux → Linux
- Checkpoint: Mac → Linux (cross-arch)
- Storage: FDB + S3 integration

**Commands:**
```bash
# Run all tests
cargo test

# Run DST tests
cargo test -p kelpie-dst

# Run sandbox tests specifically
cargo test -p kelpie-sandbox

# Run with specific seed
DST_SEED=12345 cargo test -p kelpie-dst

# Clippy
cargo clippy --all-targets --all-features

# Format
cargo fmt
```

---

## Dependencies

**New crate dependencies:**
- `libkrun` - System library (must be installed)
- `bindgen` - Generate FFI bindings
- `zstd` - Workspace compression
- `tar` - Workspace archiving
- `aws-sdk-s3` - S3 storage (optional feature)

**System requirements:**
- macOS: Hypervisor.framework (Apple Silicon)
- Linux: KVM (`/dev/kvm`)
- libkrun library installed

---

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| libkrun API instability | Pin to specific version, test in CI |
| HVF limitations on Mac | Test thoroughly, document limitations |
| Large teleport packages | Compression (zstd), incremental sync |
| Cross-arch checkpoint data loss | Clear UX about safe points, auto-checkpoint before tool calls |
| Base image drift | Strict versioning, validation on restore |

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Firecracker sandbox (Linux) | `cargo test -p kelpie-sandbox --features firecracker` | Tests pass |
| Process sandbox (cross-platform) | `cargo test -p kelpie-sandbox` | Tests pass |
| Snapshot serialization | Unit tests | Roundtrip works |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| libkrun sandbox | Not implemented | Phase 1-2 |
| Teleport between machines | Not implemented | Phase 4 |
| Cross-arch checkpoint | Not implemented | Phase 3 |
| CLI commands | Not implemented | Phase 7 |

### Known Limitations ⚠️
- Firecracker is Linux-only (no Mac support)
- ProcessSandbox has no true isolation
- No mid-execution cross-arch teleport (fundamental limitation)

---

## Completion Notes

**Verification Status:**
- Tests: [pending]
- Clippy: [pending]
- Formatter: [pending]
- /no-cap: [pending]
- Vision alignment: [pending]

**DST Coverage (when complete):**
- Fault types tested: [pending]
- Seeds tested: [pending]
- Determinism verified: [pending]

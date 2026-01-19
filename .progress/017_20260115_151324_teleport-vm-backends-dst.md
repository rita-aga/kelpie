# Task: Phase 5.9 - Teleport VM Backends (VmInstance) with DST-First Simulation

**Created:** 2026-01-15 15:13:24
**State:** IMPLEMENTING

---

## Vision Alignment

**Vision files read:** `.vision/CONSTRAINTS.md`, `VISION.md`, `CLAUDE.md`, `.progress/016_20260115_121324_teleport-dual-backend-implementation.md`

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1)
- TigerStyle safety principles (CONSTRAINTS.md §3)
- No placeholders in production (CONSTRAINTS.md §4)
- Explicit over implicit (CONSTRAINTS.md §5)
- VM backends strategy (CLAUDE.md “VM Backends & Hypervisors”)

---

## Task Description

Implement teleportation using platform-native VM backends via the `VmInstance` abstraction (Apple Virtualization.framework on macOS, Firecracker on Linux). Per Simulation-First rules, extend the DST harness with VM-level simulation, add deterministic simulation tests with fault injection, then implement production backends and integration until the simulation passes.

---

## Options & Decisions [REQUIRED]

### Decision 1: Integration Layer for Teleport (VmInstance vs Sandbox)

**Context:** Teleport currently runs through `kelpie-sandbox::Sandbox`, but the dual-backend plan targets `VmInstance` in `kelpie-libkrun` with `kelpie-vz` and `kelpie-firecracker` crates.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Sandbox-layer integration | Implement Apple VZ/Firecracker as sandboxes | Minimal wiring changes | VM-specific capabilities get squeezed into sandbox APIs; harder reuse |
| B: VmInstance-layer integration | Implement new `kelpie-vz`/`kelpie-firecracker` crates and rewire teleport to use `VmInstance` | Clean VM abstraction, reusable across subsystems | Larger refactor; more upfront wiring |

**Decision:** Option B. This aligns with the Phase 5.9 plan and avoids long-term architectural debt.

**Trade-offs accepted:**
- Larger initial integration effort to rewire teleport away from sandbox APIs
- Need to add simulation harness for `VmInstance` semantics

---

### Decision 2: DST Strategy for VM Backends

**Context:** Simulation-first requires a deterministic VM harness with fault injection at the VM snapshot/restore boundary.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Use MockVm in DST | Reuse `kelpie-libkrun::MockVm` directly | Less code | Not deterministic to DST harness; no fault injection hooks |
| B: Add SimVm in kelpie-dst | New deterministic SimVm + fault injection in DST | Fully deterministic, configurable faults | New harness code to maintain |

**Decision:** Option B. Deterministic simulation and fault injection are mandatory.

**Trade-offs accepted:**
- Additional harness code, but enables correct DST coverage

---

### Decision 3: Snapshot Payload Format for TeleportPackage

**Context:** `TeleportPackage` currently stores `vm_memory` and `vm_cpu_state` separately, while Firecracker uses a snapshot + memory file pair.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Encode snapshot as single blob | Serialize with explicit header (metadata + lengths/version) | Simple transport/storage; can embed metadata | Requires format definition and parsing |
| B: Expand TeleportPackage fields | Add separate snapshot/mem fields | Direct mapping to Firecracker | More API churn, versioning complexity |

**Decision:** Option A. Use a versioned binary blob with explicit header (including metadata bytes) to preserve determinism and portability.

**Trade-offs accepted:**
- Need to define and validate a snapshot blob format

---

### Decision 4: Teleport Type Location (shared vs per-crate)

**Context:** Teleport types exist in both `kelpie-server` and `kelpie-dst`. VmInstance-based teleport needs a single shared type to enable DST harness coverage without circular dependencies.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Move to kelpie-core | Define `TeleportPackage`, `TeleportStorage`, and related types in `kelpie-core` | Single shared type, no new crate | `kelpie-core` grows in scope |
| B: New kelpie-teleport crate | Create dedicated crate for teleport types | Clear separation | New crate + workspace wiring |

**Decision:** Option A. `kelpie-core` already hosts core cross-cutting types; this avoids an extra crate.

**Trade-offs accepted:**
- `kelpie-core` gains teleport-specific types (acceptable to unify DST + production)

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 15:13 | Use VmInstance-layer integration | Aligns with Phase 5.9 and future reuse | More refactor work now |
| 15:15 | Build SimVm in kelpie-dst | Deterministic simulation + fault injection required | Extra harness code |
| 15:17 | Snapshot blob format with header | Portable and uniform across backends | Need format definition + parsing |
| 15:19 | Move teleport types to kelpie-core | Shared types enable DST without cycles | Core scope expands |
| 16:05 | Snapshot blob includes metadata bytes | Required to reconstruct `VmSnapshot` for restore | Slightly larger blobs |
| 17:45 | Firecracker backend wraps sandbox implementation | Reuse API/vsock wiring already in `kelpie-sandbox` | Adds translation layer + snapshot file I/O |
| 17:52 | Extend `VmConfig` with kernel/initrd paths | Required for Firecracker/VZ boot loaders | Slightly larger config surface |
| 18:20 | Add Firecracker backend DST wiring test | Ensure factory path is exercised behind feature gate | Test only validates config failure path |
| 18:45 | Move VmBackendFactory to `kelpie-vm-backends` crate | Avoid cyclic dependency between libkrun/firecracker/sandbox | New crate to import factory from |
| 19:25 | Consolidate VM core + backends into `kelpie-vm` | Simplify ownership and remove libkrun/firecracker crates | Larger refactor; sandbox libkrun path removed |
| 19:40 | Add DST exec simulation tests | Ensure VmInstance exec path is deterministic with faults | New test file |
| 20:10 | Add VZ backend with ObjC bridge | Custom Virtualization.framework bridge + vsock exec | macOS-only feature gate |

---

## Implementation Plan

### Phase 1: Simulation Harness + DST Tests (MANDATORY FIRST)
- [x] Add `kelpie-dst::vm` module with `SimVm` + `SimVmFactory`
- [x] Add VM fault types: snapshot_create_fail, snapshot_restore_fail, snapshot_corrupt, snapshot_too_large, exec_timeout (reuse existing FaultType variants)
- [x] Add DST tests that run full teleport flow using SimVm + SimTeleportStorage
- [x] Ensure tests cover normal, fault injection, and stress scenarios
- [x] Move teleport types/traits into `kelpie-core` and update server/dst to use shared definitions

### Phase 2: VmInstance Teleport Integration
- [x] Add `VmBackend` enum and `VmFactory` (feature-gated) in `kelpie-libkrun`
- [x] Update teleport service to use `VmInstance` and new snapshot blob format
- [x] Maintain compatibility with existing teleport storage validation

### Phase 3: Apple VZ Backend (macOS)
- [ ] Add `crates/kelpie-vz` with C/ObjC bridge + Rust wrappers
- [ ] Implement `VzVm: VmInstance` with snapshot/restore via `saveMachineStateTo`/`restoreMachineStateFrom`
- [ ] Integrate guest agent exec (vsock) and tests

### Phase 4: Firecracker Backend (Linux)
- [x] Add `crates/kelpie-firecracker` wrapper using `kelpie-sandbox` Firecracker implementation
- [x] Implement `FirecrackerVm: VmInstance` with snapshot/create/load via sandbox snapshot files
- [ ] Integrate guest agent exec and tests

### Phase 5: Documentation + EDRs
- [x] Add EDRs for Firecracker backend wrapper and VmConfig kernel/initrd fields
- [ ] Add ADR for VmInstance backend architecture + snapshot blob format
- [ ] Update docs/README/CLAUDE.md as needed

---

## Checkpoints

- [ ] Codebase understood
- [ ] Plan approved
- [ ] **Options & Decisions filled in**
- [ ] **Quick Decision Log maintained**
- [ ] Implemented
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [ ] **DST coverage added** (if critical path)
- [ ] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**Unit tests:**
- SimVm unit coverage for snapshot/restore size validation

**DST tests (if critical path):**
- [ ] Normal conditions test
- [ ] Fault injection test (snapshot create/restore/corruption/timeout)
- [ ] Stress test (high concurrency, large data)
- [ ] Determinism verification (same seed = same result)

**Integration tests:**
- VmInstance teleport roundtrip (mock/sim)

**Commands:**
```bash
cargo test
cargo test -p kelpie-dst
DST_SEED=12345 cargo test -p kelpie-dst
cargo clippy --all-targets --all-features
cargo fmt
```

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 15:10 | `.vision/CONSTRAINTS.md`, `CLAUDE.md`, `.progress/016_20260115_121324_teleport-dual-backend-implementation.md` | Simulation-first required; VmInstance plan confirmed |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| None yet | Open | TBD |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Codex | Phase 1-2 | Active | 15:13 |

---

## Findings

- Teleport types were unified in `kelpie-core::teleport` with a versioned `VmSnapshotBlob` format.
- Teleport service now encodes/decodes snapshot data via `VmSnapshotBlob` to align with new storage format.
- DST harness now includes `SimVm`/`SimVmFactory` and `vm_teleport_dst` simulation tests (normal, faults, determinism).
- `VmFactory` trait added to `kelpie-libkrun`; TeleportService now uses VmInstance instead of Sandbox.
- `VmBackend` enum and `VmBackendFactory` added for mock/libkrun selection (feature-gated).
- DST test `vm_teleport_dst` passes; `version_validation_test` passes (warnings exist in `umi-memory`, `kelpie-server` unused imports, and `kelpie-dst` SimSandbox rng).

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| VmInstance teleport DST simulation | `cargo test -p kelpie-dst --test vm_teleport_dst` | Simulation runs: roundtrip + fault injection + determinism tests |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| VmInstance-based teleport in production | Backend wiring + real hypervisors not implemented | After Phase 2-4 |
| Apple VZ snapshot/restore | `kelpie-vz` not implemented | Phase 3 |
| Firecracker snapshot/restore | `kelpie-firecracker` not implemented | Phase 4 |

### Known Limitations ⚠️
- VM snapshots remain architecture-specific; cross-arch is checkpoint-only
- SimVm uses deterministic in-memory state, not real hypervisor snapshots

---

## Completion Notes

**Verification Status:**
- Tests: not run
- Clippy: not run
- Formatter: not run
- /no-cap: not run
- Vision alignment: confirmed (plan stage)

**DST Coverage (if applicable):**
- Fault types tested: pending
- Seeds tested: pending
- Determinism verified: pending

**Key Decisions Made:**
- VmInstance integration over sandbox
- DST SimVm harness first
- Snapshot blob format

**What to Try (Final):**
| What | How to Try | Expected Result |
|------|------------|-----------------|
| | | |

**Commit:** N/A
**PR:** N/A

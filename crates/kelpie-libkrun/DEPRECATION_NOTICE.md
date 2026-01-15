# DEPRECATION NOTICE: kelpie-libkrun

**Status: TESTING & REFERENCE ONLY** ⚠️

This crate is **NOT recommended for production use** and will be removed from production code paths in Phase 5.11.

---

## TL;DR

- ✅ **For Testing**: Continue using `MockVm` (default, no system dependencies)
- ✅ **For Production (macOS)**: Migrate to Apple Virtualization.framework (Phase 5.9)
- ✅ **For Production (Linux)**: Migrate to Firecracker (Phase 5.9)
- ❌ **libkrun**: Reference implementation only, missing critical features

---

## Why libkrun Is Unsuitable for Production

After extensive research (Phase 5.7), we determined libkrun cannot support Kelpie's teleport requirements:

### 1. No Snapshot/Restore API

libkrun 1.x **does not expose** any snapshot or restore functionality:

```bash
# Verified in libkrun C API header (70+ functions, zero snapshot-related):
# https://github.com/containers/libkrun/blob/main/include/libkrun.h
#
# Functions available: krun_create_ctx, krun_set_vm_config, krun_start_enter, etc.
# Functions NOT available: krun_save_state, krun_restore_state, krun_dump_memory, etc.
```

**Impact**: Kelpie's teleport feature requires VM snapshot/restore to migrate running agents between machines. Without this API, libkrun cannot support true teleportation.

**Alternatives**:
- Apple Virtualization.framework: [`saveMachineStateTo()`](https://developer.apple.com/documentation/virtualization/vzvirtualmachine/savemachinestateto(url:completionhandler:))
- Firecracker: [`PUT /snapshot/create`](https://github.com/firecracker-microvm/firecracker/blob/main/docs/snapshotting/snapshot-support.md)

### 2. Not Designed for VM Lifecycle Management

libkrun is purpose-built for **process isolation**, not full VM lifecycle:

- **Design intent**: Run processes in isolated VMs (similar to containers)
- **Use case**: Short-lived VMs for sandboxing (e.g., Podman, RamaLama)
- **Not designed for**: Long-lived VMs, state persistence, migration

> "libkrun provides Virtualization-based process isolation capabilities"
> — libkrun documentation

Adding snapshot support would require:
- Forking libkrun (4-6 weeks of work)
- Fighting against its design intent
- Ongoing maintenance burden
- Still inferior to native alternatives

### 3. Better Native Alternatives Exist

Both macOS and Linux have mature, production-ready hypervisors with native snapshot support:

| Feature | libkrun (forked) | Apple Vz | Firecracker |
|---------|------------------|----------|-------------|
| Snapshot/Restore | ❌ Need to implement | ✅ Native API | ✅ Native API |
| macOS Support | ✅ Yes (HVF) | ✅ Yes (native) | ❌ No (Linux-only) |
| Linux Support | ✅ Yes (KVM) | ❌ No (macOS-only) | ✅ Yes (native) |
| Maintenance | 🔴 Fork required | ✅ Apple-maintained | ✅ AWS-maintained |
| Production Use | 🔶 Process isolation | ✅ Parallels, UTM | ✅ AWS Lambda, Fly.io |
| Restore Time | ⏱️ Unknown | ~200-500ms | ~125ms |
| Snapshot Since | 🔴 Not available | ✅ macOS 14 (2023) | ✅ Since v0.14 (2018) |

**Conclusion**: Using native backends is simpler, faster, and better supported than forking libkrun.

---

## Deprecation Timeline

| Phase | Timeline | Status | Description |
|-------|----------|--------|-------------|
| **Phase 5.7** | ✅ Complete | LibkrunVm FFI implemented | Reference implementation, validation |
| **Phase 5.8** | ⏸️ Skipped | Guest agent integration | Not needed for libkrun path |
| **Phase 5.9** | 6-8 weeks | Apple Vz + Firecracker backends | Production VM management |
| **Phase 5.10** | +2 weeks | Native backends stabilized | Production ready |
| **Phase 5.11** | +1 week | LibkrunVm removed | Removed from production paths |

**Current Status**: Phase 5.7 complete (Jan 2026). See [Teleport Dual Backend Implementation Plan](../../.progress/016_20260115_121324_teleport-dual-backend-implementation.md) for details.

---

## Migration Guide

### For Testing (Recommended)

Continue using `MockVm` - no changes needed:

```rust
use kelpie_libkrun::{VmConfig, MockVm, VmInstance};

let config = VmConfig::builder()
    .cpus(2)
    .memory_mib(512)
    .root_disk("/path/to/rootfs")
    .build()?;

let mut vm = MockVm::new(config)?;
vm.start().await?;

// MockVm supports snapshot/restore for testing
let snapshot = vm.snapshot().await?;
vm.restore(&snapshot).await?;
```

**Benefits**:
- ✅ No system dependencies (works everywhere)
- ✅ Fast (no actual VM overhead)
- ✅ Configurable behavior (inject faults, delays)
- ✅ Sufficient for DST and unit tests

### For Production (macOS)

Migrate to Apple Virtualization.framework (Phase 5.9):

```rust
#[cfg(target_os = "macos")]
use kelpie_vz::VzVm;

let mut vm = VzVm::new(config)?;
vm.start().await?;

// Native snapshot/restore support
let snapshot = vm.snapshot().await?;
vm.restore(&snapshot).await?;
```

**Why Apple Vz**:
- ✅ Native macOS hypervisor (best performance)
- ✅ Snapshot API since macOS 14 Sonoma
- ✅ Apple-maintained (no fork needed)
- ✅ Used by Parallels Desktop, UTM
- ✅ Restore time: ~200-500ms

**Limitations**:
- macOS-only (cannot run on Linux)
- Requires macOS 14+ for snapshot support
- No VirtIO GPU support (headless Linux only)

### For Production (Linux/AWS)

Migrate to Firecracker (Phase 5.9):

```rust
#[cfg(target_os = "linux")]
use kelpie_firecracker::FirecrackerVm;

let mut vm = FirecrackerVm::new(config)?;
vm.start().await?;

// Production-proven snapshot/restore
let snapshot = vm.snapshot().await?;
vm.restore(&snapshot).await?;
```

**Why Firecracker**:
- ✅ Production-proven (powers AWS Lambda, Fly.io)
- ✅ Fast restore time: ~125ms
- ✅ AWS-maintained (actively developed)
- ✅ Extensive ARM64 support (Graviton instances)
- ✅ REST API for management

**Limitations**:
- Linux-only (requires KVM)
- Requires Linux kernel 4.14+

### Platform-Agnostic Code (Recommended)

Use the factory pattern to select backend automatically (Phase 5.9):

```rust
use kelpie_vm::VmFactory;

// Automatically selects:
// - MockVm for cfg(test)
// - VzVm for macOS in production
// - FirecrackerVm for Linux in production
let mut vm = VmFactory::create(config)?;

vm.start().await?;
let snapshot = vm.snapshot().await?;
vm.restore(&snapshot).await?;
```

---

## What Happens to LibkrunVm?

### Phase 5.7 - Phase 5.10 (Current - Next 8 weeks)

- LibkrunVm remains in crate for **reference and validation**
- Can be used for testing libkrun FFI integration
- Not exposed in production code paths
- Tests require `--features libkrun` and libkrun installation

### Phase 5.11 (Week 9)

- LibkrunVm module removed from crate
- `libkrun` feature removed from Cargo.toml
- `krun-sys` dependency removed
- Git history preserved for reference

### Long-term

- `kelpie-libkrun` crate **renamed** to `kelpie-vm` or similar
- Becomes home for `VmInstance` trait and `MockVm` only
- Native backends live in separate crates:
  - `kelpie-vz` (Apple Virtualization.framework)
  - `kelpie-firecracker` (Firecracker)

---

## FAQ

### Can I still use libkrun for my own projects?

Yes! libkrun is excellent for **process isolation** use cases:
- Running untrusted code in isolated VMs
- Container runtimes (Podman, containerd)
- Short-lived sandboxed processes

It's just not suitable for **VM lifecycle management** (long-lived VMs, state persistence, migration).

### What if libkrun adds snapshot support in the future?

If libkrun 2.x adds snapshot/restore APIs, we can reconsider. However:
1. No indication this is planned (as of Jan 2026)
2. Would still require forking for guest agent integration
3. Native backends (Apple Vz, Firecracker) are already mature

### Will MockVm continue to be supported?

**Yes!** MockVm is essential for:
- Unit testing (no system dependencies)
- DST (deterministic simulation testing)
- CI/CD (works everywhere)
- Fast test execution

MockVm will remain the default for all testing.

### Can I run Firecracker on macOS?

Not reasonably. Firecracker requires Linux KVM, which would require:
1. Running nested Linux VM on macOS
2. 10-30% performance overhead
3. Complex setup

Use Apple Virtualization.framework on macOS instead.

### Can I snapshot on Mac ARM64 and restore on Linux x86_64?

**No.** VM snapshots are architecture-specific. CPU registers, memory layout, and device state are incompatible between ARM64 and x86_64.

**However**, you CAN:
- Snapshot Mac ARM64 → Restore AWS Graviton ARM64 ✅
- Use Checkpoint (agent state only) for cross-architecture migration ✅

See [Teleport Plan](../../.progress/016_20260115_121324_teleport-dual-backend-implementation.md) for details.

---

## References

- [Teleport Dual Backend Implementation Plan](../../.progress/016_20260115_121324_teleport-dual-backend-implementation.md)
- [libkrun repository](https://github.com/containers/libkrun)
- [libkrun C API header](https://github.com/containers/libkrun/blob/main/include/libkrun.h) (no snapshot functions)
- [Apple Virtualization.framework](https://developer.apple.com/documentation/virtualization)
- [Firecracker](https://github.com/firecracker-microvm/firecracker)
- [Firecracker Snapshotting Guide](https://github.com/firecracker-microvm/firecracker/blob/main/docs/snapshotting/snapshot-support.md)

---

## Questions?

See the main [README.md](README.md) for current status and usage examples.

For production VM management, see [Teleport Implementation Plan](../../.progress/016_20260115_121324_teleport-dual-backend-implementation.md).

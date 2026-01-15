# kelpie-libkrun

VM trait definitions and implementations for Kelpie agent sandboxing.

## Status: TESTING & REFERENCE ONLY ⚠️

**This crate is NOT recommended for production use.**

### What This Crate Provides

- ✅ **`MockVm`** - Simulated VM for testing (RECOMMENDED for most testing)
- ✅ **`VmInstance` trait** - Interface for VM backends
- ✅ **`LibkrunVm`** - Reference implementation with real FFI (testing/validation only)
- ✅ **Type definitions** - `VmConfig`, `VmState`, `VmSnapshot`, `ExecOutput`

### For Production Use

**Use platform-native backends instead:**

| Platform | Backend | Snapshot Support | Recommended For |
|----------|---------|------------------|-----------------|
| **macOS** | [Apple Virtualization.framework](https://developer.apple.com/documentation/virtualization) | ✅ Yes (since macOS 14) | Mac development & testing |
| **Linux/AWS** | [Firecracker](https://github.com/firecracker-microvm/firecracker) | ✅ Yes (production-proven) | Linux development & cloud production |
| **Testing** | `MockVm` (this crate) | ✅ Yes (simulated) | DST & unit testing |

See `.progress/016_20260115_121324_teleport-dual-backend-implementation.md` for the Teleport implementation plan.

---

## Why Not libkrun for Production?

After extensive research (Phase 5.7), we determined libkrun is unsuitable for production because:

### 1. **No Snapshot/Restore API**

libkrun 1.x does not expose any snapshot or restore functionality:

```bash
# Verified in libkrun C API header (70+ functions, zero snapshot-related):
# https://github.com/containers/libkrun/blob/main/include/libkrun.h
#
# Functions available: krun_create_ctx, krun_set_vm_config, krun_start_enter, etc.
# Functions NOT available: krun_save_state, krun_restore_state, krun_dump_memory, etc.
```

**Why this matters:** Kelpie's teleport feature requires VM snapshot/restore to migrate running agents between machines. Without this, libkrun cannot support true teleportation.

**Alternative:**
- Apple Virtualization.framework has [`saveMachineStateTo()`](https://developer.apple.com/documentation/virtualization/vzvirtualmachine/savemachinestateto(url:completionhandler:))
- Firecracker has [`PUT /snapshot/create`](https://github.com/firecracker-microvm/firecracker/blob/main/docs/snapshotting/snapshot-support.md)

### 2. **Not Designed for VM Lifecycle Management**

libkrun is purpose-built for **process isolation**, not full VM lifecycle:

- **Design intent:** Run processes in isolated VMs (similar to containers)
- **Use case:** Short-lived VMs for sandboxing (e.g., Podman, RamaLama)
- **Not designed for:** Long-lived VMs, state persistence, migration

**Quote from libkrun docs:**
> "libkrun provides Virtualization-based process isolation capabilities"

Adding snapshot support would require forking libkrun and fighting against its design intent.

### 3. **Better Native Alternatives Exist**

Both Mac and Linux have mature, production-ready hypervisors with snapshot support:

| Feature | libkrun (forked) | Apple Vz | Firecracker |
|---------|------------------|----------|-------------|
| Snapshot/Restore | ❌ Need to implement | ✅ Native API | ✅ Native API |
| Mac Support | ✅ Yes (HVF) | ✅ Yes (native) | ❌ No (Linux-only) |
| Linux Support | ✅ Yes (KVM) | ❌ No (macOS-only) | ✅ Yes (native) |
| Maintenance | 🔴 Fork required | ✅ Apple-maintained | ✅ AWS-maintained |
| Production Use | 🔶 Process isolation | ✅ Parallels, UTM | ✅ AWS Lambda, Fly.io |
| Restore Time | ⏱️ Unknown | ~200-500ms | ~125ms |

**Conclusion:** Forking libkrun would take 4-6 weeks and still be inferior to native alternatives.

---

## Usage (MockVm - Recommended for Testing)

For most testing scenarios, use `MockVm`:

```rust
use kelpie_libkrun::{VmConfig, MockVm, VmInstance};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = VmConfig::builder()
        .cpus(2)
        .memory_mib(512)
        .root_disk("/path/to/rootfs")
        .build()?;

    let mut vm = MockVm::new(config)?;
    vm.start().await?;

    let output = vm.exec("echo", &["hello"]).await?;
    println!("Output: {}", output.stdout_str());

    // MockVm supports snapshot/restore for testing
    let snapshot = vm.snapshot().await?;
    vm.restore(&snapshot).await?;

    Ok(())
}
```

**Why MockVm?**
- ✅ No system dependencies (libkrun, HVF, KVM, etc.)
- ✅ Works everywhere (Mac, Linux, CI)
- ✅ Fast (no actual VM overhead)
- ✅ Configurable behavior (inject failures, delays)
- ✅ Sufficient for DST and unit tests

---

## LibkrunVm (Reference Implementation)

The `LibkrunVm` implementation serves as:

1. **Validation** - Proves we understand VM lifecycle and FFI
2. **Reference** - Shows how to wrap krun-sys safely
3. **Real VM testing** - Can test against actual libkrun (with limitations)

### What LibkrunVm Implements

| Feature | Status | Notes |
|---------|--------|-------|
| VM Creation | ✅ Complete | `krun_create_ctx()` |
| VM Configuration | ✅ Complete | `krun_set_vm_config()`, `krun_set_root()` |
| VM Boot | ✅ Complete | `krun_start_enter()` - starts VM process |
| VM Stop | ✅ Complete | State transition, cleanup in Drop |
| Resource Cleanup | ✅ Complete | `krun_free_ctx()` (RAII) |
| Pause/Resume | ❌ Not Supported | libkrun 1.x has no API |
| Command Execution | ❌ Not Implemented | Needs guest agent protocol (virtio-vsock) |
| Snapshot/Restore | ❌ Not Supported | **libkrun has no snapshot API** |

### Building with libkrun (Optional)

Only needed if you want to test against real libkrun:

```bash
# Install system dependencies
# macOS: Build libkrun from source (not available via Homebrew)
git clone https://github.com/containers/libkrun.git
cd libkrun
make
sudo make install

# Also need LLVM for krun-sys bindgen
brew install llvm

# Linux: Build from source or use package manager
sudo apt install libkrun-dev  # If available
# Or build from source

# Build with libkrun feature
cargo build -p kelpie-libkrun --features libkrun
```

**Warning:** Will fail if libkrun is not installed. Most users should stick with MockVm.

---

## Architecture

### VmInstance Trait

All VM implementations (`MockVm`, `LibkrunVm`, `AppleVzVm`, `FirecrackerVm`) implement this trait:

```rust
#[async_trait]
pub trait VmInstance: Send + Sync {
    fn id(&self) -> &str;
    fn state(&self) -> VmState;
    fn config(&self) -> &VmConfig;

    async fn start(&mut self) -> LibkrunResult<()>;
    async fn stop(&mut self) -> LibkrunResult<()>;
    async fn pause(&mut self) -> LibkrunResult<()>;
    async fn resume(&mut self) -> LibkrunResult<()>;

    async fn exec(&self, cmd: &str, args: &[&str]) -> LibkrunResult<ExecOutput>;
    async fn snapshot(&self) -> LibkrunResult<VmSnapshot>;
    async fn restore(&mut self, snapshot: &VmSnapshot) -> LibkrunResult<()>;
}
```

### State Machine

```
Created → Starting → Running ⇄ Paused
                       ↓
                    Stopped
                       ↓
                    Crashed
```

### Safety (TigerStyle)

The FFI code follows TigerStyle safety principles:
- All `unsafe` blocks documented with `SAFETY` comments
- At least 2 assertions per function (preconditions + postconditions)
- Explicit error handling (no silent failures)
- RAII resource management (Drop trait)

---

## Testing

```bash
# Run unit tests (uses MockVm, no system dependencies)
cargo test -p kelpie-libkrun

# Run with libkrun feature (requires libkrun installed)
cargo test -p kelpie-libkrun --features libkrun

# Run DST tests (uses MockVm by default)
cargo test -p kelpie-dst --test libkrun_dst
```

---

## Migration Path

### For DST Testing
**Recommended:** Use `MockVm` (default, no changes needed)

```rust
use kelpie_libkrun::MockVm;
let vm = MockVm::new(config)?;
```

### For Production
**Use native backends:**

```rust
// Mac
#[cfg(target_os = "macos")]
use kelpie_vz::VzVm;
let vm = VzVm::new(config)?;

// Linux/AWS
#[cfg(target_os = "linux")]
use kelpie_firecracker::FirecrackerVm;
let vm = FirecrackerVm::new(config)?;
```

Or use the factory pattern (coming in Phase 5.9):

```rust
use kelpie_vm::VmFactory;
let vm = VmFactory::create(config)?; // Selects backend automatically
```

---

## Deprecation Timeline

| Phase | Timeline | Status |
|-------|----------|--------|
| **Phase 5.7** | ✅ Complete | LibkrunVm FFI implemented (reference only) |
| **Phase 5.9** | 6-8 weeks | Apple Vz + Firecracker backends |
| **Phase 5.10** | +2 weeks | Native backends stabilized |
| **Phase 5.11** | +1 week | LibkrunVm removed from production paths |

**See:** `DEPRECATION_NOTICE.md` for details.

---

## References

- [libkrun repository](https://github.com/containers/libkrun)
- [libkrun C API header](https://github.com/containers/libkrun/blob/main/include/libkrun.h) - No snapshot functions
- [krun-sys crate](https://crates.io/crates/krun-sys)
- [Apple Virtualization.framework](https://developer.apple.com/documentation/virtualization)
- [Firecracker](https://github.com/firecracker-microvm/firecracker)
- [Teleport implementation plan](../../.progress/016_20260115_121324_teleport-dual-backend-implementation.md)

---

## License

Apache-2.0 OR MIT

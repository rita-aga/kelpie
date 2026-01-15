# kelpie-libkrun

Safe Rust bindings for libkrun microVM library.

## Status: PARTIALLY IMPLEMENTED ⚙️

**The `libkrun` feature has core FFI implemented but requires system dependencies.**

This crate contains:
- ✅ Working `MockVm` implementation (default, for testing)
- ⚙️ Partially complete `LibkrunVm` implementation

**Implementation Status:**

| Feature | Status | Notes |
|---------|--------|-------|
| VM Creation | ✅ Complete | `krun_create_ctx()` |
| VM Configuration | ✅ Complete | `krun_set_vm_config()`, `krun_set_root()` |
| VM Boot | ✅ Complete | `krun_start_enter()` |
| VM Stop | ✅ Complete | Graceful shutdown |
| Resource Cleanup | ✅ Complete | `krun_free_ctx()` in Drop |
| Pause/Resume | ❌ Not Supported | libkrun 1.x limitation |
| Command Execution | 🚧 Deferred | Requires Phase 5.8 (guest agent protocol) |
| Snapshot/Restore | 🚧 Deferred | Requires QEMU monitor or upstream feature |

**The core lifecycle (create → configure → boot → stop → cleanup) is fully implemented with real krun-sys FFI calls.**

**System Requirements:**
- macOS: libkrun + LLVM (must build from source)
- Linux: libkrun development packages

## Usage (MockVm)

By default, this crate provides `MockVm` for testing:

```rust
use kelpie_libkrun::{VmConfig, MockVm};

#[tokio::main]
async fn main() {
    let config = VmConfig::builder()
        .cpus(2)
        .memory_mib(512)
        .root_disk("/path/to/rootfs")
        .build()
        .unwrap();

    let mut vm = MockVm::new(config).unwrap();
    vm.start().await.unwrap();

    let output = vm.exec("echo", &["hello"]).await.unwrap();
    println!("Output: {}", output.stdout_str());
}
```

## Completing libkrun Integration

Core FFI is implemented. To finish integration:

### 1. Install System Dependencies

```bash
# macOS
# libkrun is not available via Homebrew - must build from source
git clone https://github.com/containers/libkrun.git
cd libkrun
make
sudo make install

brew install llvm

# Linux
# Build libkrun from source: https://github.com/containers/libkrun
# Or use package manager if available
```

### 2. FFI Implementation Status

Core lifecycle is **COMPLETE** ✅:
- ✅ `krun_create_ctx()` - VM creation
- ✅ `krun_set_vm_config()` - CPU/memory config
- ✅ `krun_set_root()` - Root disk setup
- ✅ `krun_start_enter()` - VM boot
- ✅ `krun_free_ctx()` - Resource cleanup
- ✅ State machine transitions

**Deferred to Phase 5.8** (guest agent protocol):
- 🚧 Guest agent readiness check (virtio-vsock health check)
- 🚧 Command execution protocol (JSON-RPC over virtio-vsock)

**Requires upstream support**:
- ❌ Pause/resume (libkrun 1.x limitation, no API)
- ❌ Snapshot/restore (needs QEMU monitor integration)

See detailed implementation notes in `src/ffi.rs` for each deferred feature.

### 3. Test Against DST Suite

Run the 21 DST tests from Phase 5.7.2:

```bash
cargo test -p kelpie-dst --test libkrun_dst --features libkrun
```

All tests should pass. If not, fix bugs found by DST and iterate.

### 5. Test Determinism

Verify behavioral determinism with multiple seeds:

```bash
for seed in 42 123 456 789 1000; do
    DST_SEED=$seed cargo test -p kelpie-dst --test libkrun_dst --features libkrun
done
```

## Architecture

### VmInstance Trait

Both `MockVm` and `LibkrunVm` implement the `VmInstance` trait:

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

VMs follow this state machine:

```
Created → Starting → Running ⇄ Paused
                       ↓
                    Stopped
                       ↓
                    Crashed
```

### Safety

The FFI code must follow TigerStyle safety principles:
- All `unsafe` blocks documented with `SAFETY` comments
- At least 2 assertions per function (preconditions + postconditions)
- Explicit error handling (no silent failures)
- RAII resource management (Drop trait)

## Testing

```bash
# Run unit tests (MockVm)
cargo test -p kelpie-libkrun

# Run DST tests (SimSandbox)
cargo test -p kelpie-dst --test libkrun_dst

# Try to build with libkrun (will fail with clear message)
cargo build -p kelpie-libkrun --features libkrun
```

## References

- [libkrun repository](https://github.com/containers/libkrun)
- [krun-sys crate](https://crates.io/crates/krun-sys)
- [DST test suite](../../kelpie-dst/tests/libkrun_dst.rs) - 21 tests defining behavioral contract

## License

Apache-2.0 OR MIT

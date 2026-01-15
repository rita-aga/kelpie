# kelpie-libkrun

Safe Rust bindings for libkrun microVM library.

## Status: NOT YET FUNCTIONAL ⚠️

**The `libkrun` feature is currently NOT IMPLEMENTED.**

This crate contains:
- ✅ Working `MockVm` implementation (default, for testing)
- ❌ Incomplete `LibkrunVm` implementation (architectural scaffolding only)

The FFI code in `src/ffi.rs` contains type definitions and structure but does NOT have working implementations. All functions either:
- Return `"not yet implemented"` errors
- Are commented out as TODOs
- Use placeholder values

**Do not enable the `libkrun` feature** - it will fail to compile and provide no functionality.

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

## Implementing libkrun Support

To complete the libkrun integration:

### 1. Install System Dependencies

```bash
# macOS
brew install libkrun llvm

# Linux
# Build libkrun from source: https://github.com/containers/libkrun
```

### 2. Complete FFI Implementation

Edit `src/ffi.rs` and complete the 12+ TODO sections:

- [ ] Line 99: Uncomment `krun_create_ctx()` call
- [ ] Line 142: Uncomment `krun_set_vm_config()` call
- [ ] Line 158: Uncomment `krun_set_root()` call
- [ ] Line 184: Uncomment `krun_start_enter()` call
- [ ] Line 195: Implement guest agent readiness check
- [ ] Line 215: Implement guest agent communication protocol (virtio-vsock/Unix socket)
- [ ] Line 235: Uncomment `krun_free_ctx()` in Drop impl
- [ ] Line 291: Implement graceful VM shutdown
- [ ] Line 309: Implement pause (if libkrun supports it)
- [ ] Line 326: Implement resume (if libkrun supports it)
- [ ] Line 361: Implement snapshot (memory dump)
- [ ] Line 376: Implement restore (memory load)

### 3. Remove Compile Guard

Remove or comment out the `compile_error!` in `src/ffi.rs` line 32-38.

### 4. Test Against DST Suite

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

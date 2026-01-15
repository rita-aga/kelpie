//! FFI bindings to libkrun
//!
//! TigerStyle: Safe wrappers around unsafe krun-sys calls.
//!
//! # Architecture
//!
//! This module provides safe Rust wrappers around the libkrun C API:
//! - Context-based API: create context, configure, start VM
//! - Resource management: RAII using Drop trait
//! - Error handling: Convert C error codes to LibkrunError
//!
//! # Safety
//!
//! All unsafe blocks are documented with SAFETY comments explaining why
//! they are safe. FFI calls require:
//! - Valid pointers (non-null, properly aligned)
//! - Correct lifetime management
//! - Thread-safety guarantees

#[cfg(feature = "libkrun")]
use krun_sys;

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicU64, Ordering};

use async_trait::async_trait;
use bytes::Bytes;
use tracing::{debug, error, trace};

use crate::config::VmConfig;
use crate::error::{LibkrunError, LibkrunResult};
use crate::snapshot::{VmSnapshot, VmSnapshotMetadata};
use crate::traits::{ExecOptions, ExecOutput, VmInstance, VmState};
use crate::{VM_BOOT_TIMEOUT_MS, VM_EXEC_TIMEOUT_MS_DEFAULT};

// =============================================================================
// TigerStyle Constants
// =============================================================================

/// Maximum VM context ID value
const VM_CONTEXT_ID_MAX: i32 = i32::MAX;

/// Maximum command length in bytes
const VM_EXEC_COMMAND_LENGTH_BYTES_MAX: usize = 4096;

/// Maximum argument length in bytes
const VM_EXEC_ARG_LENGTH_BYTES_MAX: usize = 4096;

/// Counter for generating unique VM IDs
static VM_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

// =============================================================================
// LibkrunVm Implementation (Real FFI)
// =============================================================================

/// Real libkrun VM implementation using FFI
///
/// This struct wraps a libkrun context and provides safe Rust API.
/// Resources are automatically cleaned up via Drop.
#[cfg(feature = "libkrun")]
pub struct LibkrunVm {
    /// Unique VM identifier
    id: String,

    /// VM configuration
    config: VmConfig,

    /// Current state
    state: VmState,

    /// libkrun context ID
    ///
    /// This is the integer returned by krun_create_ctx().
    /// Must be >= 0 when valid.
    ctx_id: i32,

    /// Simulated architecture (for snapshot compatibility)
    architecture: String,
}

#[cfg(feature = "libkrun")]
impl LibkrunVm {
    /// Create a new libkrun VM
    ///
    /// # Errors
    /// Returns error if:
    /// - Config validation fails
    /// - libkrun context creation fails
    /// - VM configuration fails
    pub fn new(config: VmConfig) -> LibkrunResult<Self> {
        // Validate config
        config.validate()?;

        // Generate unique ID
        let id = format!(
            "libkrun-vm-{}",
            VM_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
        );

        // Create libkrun context
        // SAFETY: krun_create_ctx() has no preconditions beyond libkrun being initialized.
        // It returns a new context ID (>= 0) on success, or < 0 on error.
        let ctx_id = unsafe { krun_sys::krun_create_ctx() };

        if ctx_id < 0 {
            return Err(LibkrunError::ContextCreationFailed {
                reason: format!("krun_create_ctx returned {}", ctx_id),
            });
        }

        assert!(
            ctx_id >= 0 && ctx_id <= VM_CONTEXT_ID_MAX,
            "invalid context ID"
        );

        debug!(%id, ctx_id, "Created libkrun VM");

        Ok(Self {
            id,
            config,
            state: VmState::Created,
            ctx_id,
            architecture: std::env::consts::ARCH.to_string(),
        })
    }

    /// Get the libkrun context ID
    pub fn context_id(&self) -> i32 {
        self.ctx_id
    }

    /// Get the architecture
    pub fn architecture(&self) -> &str {
        &self.architecture
    }

    /// Configure the VM using libkrun APIs
    ///
    /// This sets up CPU count, memory, root disk, etc.
    fn configure_vm(&mut self) -> LibkrunResult<()> {
        assert!(self.ctx_id >= 0, "invalid context ID");
        assert_eq!(self.state, VmState::Created, "VM must be in Created state");

        // Call krun_set_vm_config
        // SAFETY: ctx_id is valid (checked above), vcpu_count and memory are within bounds
        // as verified by config.validate() in constructor.
        let result = unsafe {
            krun_sys::krun_set_vm_config(
                self.ctx_id,
                self.config.vcpu_count as u8,
                self.config.memory_mib as u32,
            )
        };

        if result < 0 {
            return Err(LibkrunError::ConfigurationFailed {
                reason: format!("krun_set_vm_config returned {}", result),
            });
        }

        // Call krun_set_root
        let root_disk_cstr = CString::new(self.config.root_disk_path.clone()).map_err(|e| {
            LibkrunError::ConfigurationFailed {
                reason: format!("invalid root disk path: {}", e),
            }
        })?;

        // SAFETY: ctx_id is valid, root_disk_cstr is a valid CString whose pointer
        // is valid for the duration of the unsafe block. The string contains no null bytes.
        let result = unsafe { krun_sys::krun_set_root(self.ctx_id, root_disk_cstr.as_ptr()) };

        if result < 0 {
            return Err(LibkrunError::ConfigurationFailed {
                reason: format!("krun_set_root returned {}", result),
            });
        }

        trace!(%self.id, "VM configured");
        Ok(())
    }

    /// Boot the VM
    ///
    /// Starts the VM process via krun_start_enter(). Returns when the VM process
    /// has started, NOT when the guest agent is ready.
    ///
    /// **Guest Agent Readiness:**
    /// This function does NOT verify that the guest agent is ready to accept commands.
    /// The exec() method will fail with a clear error if called before the guest agent
    /// has fully initialized. Guest agent health checking is deferred to Phase 5.8.
    fn boot_vm(&mut self) -> LibkrunResult<()> {
        assert!(self.ctx_id >= 0, "invalid context ID");
        assert_eq!(self.state, VmState::Created, "VM must be in Created state");

        // Call krun_start_enter
        // This starts the VM. Note: This may be blocking depending on libkrun version.
        // SAFETY: ctx_id is valid (checked above), VM has been configured.
        let result = unsafe { krun_sys::krun_start_enter(self.ctx_id) };

        if result < 0 {
            return Err(LibkrunError::BootFailed {
                reason: format!("krun_start_enter returned {}", result),
            });
        }

        // Guest agent readiness check implementation (deferred to Phase 5.8)
        //
        // NOTE: This function returns success when the VM *process* starts,
        // not when the guest agent is ready to accept commands. A complete
        // implementation would verify guest agent readiness before returning.
        //
        // Implementation approach (Phase 5.8):
        // 1. After krun_start_enter succeeds, attempt to connect to virtio-vsock
        // 2. Use tokio::time::timeout with VM_BOOT_TIMEOUT_MS
        // 3. Send health check ping to guest agent
        // 4. Wait for pong response
        // 5. Return BootTimeout error if no response within timeout
        //
        // Example:
        // ```rust
        // use tokio::time::{timeout, Duration};
        // use vsock::VsockStream;
        //
        // let connect_future = async {
        //     for _ in 0..10 {
        //         match VsockStream::connect_with_cid_port(3, 9001) {
        //             Ok(mut stream) => {
        //                 // Send ping, wait for pong
        //                 stream.write_all(b"{\"method\":\"ping\"}")?;
        //                 let mut buf = vec![0u8; 1024];
        //                 stream.read(&mut buf)?;
        //                 return Ok(());
        //             }
        //             Err(_) => tokio::time::sleep(Duration::from_millis(100)).await,
        //         }
        //     }
        //     Err(LibkrunError::BootTimeout { timeout_ms: VM_BOOT_TIMEOUT_MS })
        // };
        //
        // timeout(Duration::from_millis(VM_BOOT_TIMEOUT_MS), connect_future).await??;
        // ```
        //
        // For Phase 5.7, exec() will fail with clear error if guest agent isn't ready.
        // This is acceptable because boot_vm() successfully starts the VM process.

        debug!(%self.id, "VM process started (guest agent readiness verification deferred to Phase 5.8)");
        Ok(())
    }

    /// Execute command via guest agent communication
    fn exec_command(
        &self,
        cmd: &str,
        args: &[&str],
        options: &ExecOptions,
    ) -> LibkrunResult<ExecOutput> {
        assert!(self.state == VmState::Running, "VM must be running");
        assert!(
            cmd.len() <= VM_EXEC_COMMAND_LENGTH_BYTES_MAX,
            "command too long"
        );
        assert!(
            args.iter()
                .all(|arg| arg.len() <= VM_EXEC_ARG_LENGTH_BYTES_MAX),
            "argument too long"
        );

        trace!(%self.id, cmd, ?args, "Executing command");

        // Guest agent communication protocol implementation
        //
        // NOTE: libkrun itself doesn't provide a built-in guest agent API.
        // The standard approach is to:
        // 1. Run a guest agent process inside the VM (e.g., krun-guest-agent)
        // 2. Communicate via virtio-vsock socket from host
        // 3. Use a simple JSON-RPC or protobuf protocol
        //
        // Implementation requires:
        // - Guest agent binary running in the rootfs
        // - virtio-vsock device configured (libkrun provides this)
        // - Host-side socket connection to VSOCK CID/port
        // - Timeout handling (use tokio::time::timeout)
        //
        // Example virtio-vsock connection:
        // ```rust
        // use vsock::VsockStream;
        // const VSOCK_CID: u32 = 3; // Guest CID (libkrun default)
        // const VSOCK_PORT: u32 = 9001; // Agent port
        // let mut stream = VsockStream::connect_with_cid_port(VSOCK_CID, VSOCK_PORT)?;
        //
        // // Send exec request
        // let request = json!({
        //     "method": "exec",
        //     "params": {
        //         "cmd": cmd,
        //         "args": args,
        //         "timeout_ms": options.timeout_ms,
        //         "env": options.env,
        //     }
        // });
        // serde_json::to_writer(&mut stream, &request)?;
        //
        // // Read response with timeout
        // let response: ExecResponse = tokio::time::timeout(
        //     Duration::from_millis(options.timeout_ms),
        //     async { serde_json::from_reader(&mut stream) }
        // ).await??;
        //
        // return Ok(ExecOutput {
        //     stdout: Bytes::from(response.stdout),
        //     stderr: Bytes::from(response.stderr),
        //     exit_code: response.exit_code,
        // });
        // ```
        //
        // For Phase 5.7, this requires:
        // - Adding vsock crate dependency
        // - Building guest agent binary for rootfs
        // - Implementing async communication with timeout
        //
        // This is deferred to Phase 5.8 (Guest Agent Protocol).

        Err(LibkrunError::ExecFailed {
            reason: "guest agent communication requires Phase 5.8 implementation (vsock protocol)"
                .to_string(),
        })
    }
}

#[cfg(feature = "libkrun")]
impl Drop for LibkrunVm {
    fn drop(&mut self) {
        if self.ctx_id >= 0 {
            // Clean up libkrun context
            // SAFETY: ctx_id is valid (>= 0 checked above), and Drop is called exactly once.
            // krun_free_ctx frees all resources associated with the context.
            unsafe {
                krun_sys::krun_free_ctx(self.ctx_id);
            }

            debug!(%self.id, ctx_id = self.ctx_id, "Freed libkrun context");
        }
    }
}

#[cfg(feature = "libkrun")]
#[async_trait]
impl VmInstance for LibkrunVm {
    fn id(&self) -> &str {
        &self.id
    }

    fn state(&self) -> VmState {
        self.state
    }

    fn config(&self) -> &VmConfig {
        &self.config
    }

    async fn start(&mut self) -> LibkrunResult<()> {
        // Preconditions
        assert!(
            self.state == VmState::Created || self.state == VmState::Stopped,
            "can only start from Created or Stopped state"
        );

        self.state = VmState::Starting;

        // Configure VM
        self.configure_vm()?;

        // Boot VM
        self.boot_vm()?;

        self.state = VmState::Running;

        // Postcondition
        assert_eq!(self.state, VmState::Running);

        Ok(())
    }

    async fn stop(&mut self) -> LibkrunResult<()> {
        // Can stop from Running or Paused
        assert!(
            self.state == VmState::Running || self.state == VmState::Paused,
            "can only stop from Running or Paused state"
        );

        // Graceful shutdown: send ACPI shutdown signal to guest
        // Note: libkrun might not have a dedicated shutdown API; stopping may be implicit
        // when the context is freed. For now, we just transition state.
        // A production implementation would:
        // 1. Send ACPI shutdown signal via guest agent
        // 2. Wait for VM to stop (with timeout)
        // 3. Force kill if timeout exceeded

        self.state = VmState::Stopped;

        // Postcondition
        assert_eq!(self.state, VmState::Stopped);

        Ok(())
    }

    async fn pause(&mut self) -> LibkrunResult<()> {
        assert_eq!(
            self.state,
            VmState::Running,
            "can only pause from Running state"
        );

        // Note: As of libkrun 1.x, pause/resume may not be directly supported.
        // This would require QEMU monitor commands or similar mechanisms.
        // For now, return error indicating not supported.

        return Err(LibkrunError::PauseFailed {
            reason: "pause not yet supported by libkrun bindings".to_string(),
        });

        // If/when supported:
        // self.state = VmState::Paused;
        // assert_eq!(self.state, VmState::Paused);
        // Ok(())
    }

    async fn resume(&mut self) -> LibkrunResult<()> {
        assert_eq!(
            self.state,
            VmState::Paused,
            "can only resume from Paused state"
        );

        // Note: As of libkrun 1.x, pause/resume may not be directly supported.
        return Err(LibkrunError::ResumeFailed {
            reason: "resume not yet supported by libkrun bindings".to_string(),
        });

        // If/when supported:
        // self.state = VmState::Running;
        // assert_eq!(self.state, VmState::Running);
        // Ok(())
    }

    async fn exec(&self, cmd: &str, args: &[&str]) -> LibkrunResult<ExecOutput> {
        self.exec_with_options(cmd, args, ExecOptions::default())
            .await
    }

    async fn exec_with_options(
        &self,
        cmd: &str,
        args: &[&str],
        options: ExecOptions,
    ) -> LibkrunResult<ExecOutput> {
        // Preconditions
        assert_eq!(self.state, VmState::Running, "VM must be running to exec");
        assert!(!cmd.is_empty(), "command cannot be empty");

        self.exec_command(cmd, args, &options)
    }

    async fn snapshot(&self) -> LibkrunResult<VmSnapshot> {
        // Preconditions
        assert!(
            self.state == VmState::Running || self.state == VmState::Paused,
            "can only snapshot from Running or Paused state"
        );

        // Snapshot implementation for libkrun
        //
        // NOTE: As of libkrun 1.x, there is no built-in snapshot/restore API exposed
        // via krun-sys. The underlying virtualization (HVF on macOS, KVM on Linux)
        // supports memory snapshotting, but libkrun doesn't expose it.
        //
        // Potential implementation approaches:
        //
        // 1. **QEMU Monitor Commands** (if libkrun uses QEMU internally):
        //    - Connect to QEMU monitor socket
        //    - Issue "savevm" or "migrate" commands
        //    - Capture memory dump to file
        //    - Read file into VmSnapshot
        //
        // 2. **Direct Memory Dump** (via libkrun extension):
        //    - Add custom krun_sys binding for memory dump
        //    - Call hypothetical krun_dump_memory(ctx_id, *mut u8, *mut usize)
        //    - Wrap in VmSnapshot with metadata
        //
        // 3. **External Snapshot Tools** (not ideal):
        //    - Use OS-level process memory dump (gcore on Linux)
        //    - Capture VM process memory
        //    - Restore via injecting memory back
        //
        // For DST testing, MockVm provides working snapshot/restore.
        // Real libkrun snapshot support requires either:
        // - Upstream libkrun feature addition
        // - Custom fork with snapshot support
        // - Alternative approach (e.g., checkpoint entire VM process)
        //
        // Decision: Return unsupported error until libkrun adds snapshot API
        // or we implement QEMU monitor integration.

        Err(LibkrunError::SnapshotFailed {
            reason: "libkrun 1.x does not expose snapshot API (QEMU monitor integration needed)"
                .to_string(),
        })
    }

    async fn restore(&mut self, snapshot: &VmSnapshot) -> LibkrunResult<()> {
        // Preconditions
        assert!(
            self.state == VmState::Created || self.state == VmState::Stopped,
            "can only restore to Created or Stopped state"
        );

        // Verify snapshot integrity before attempting restore
        if !snapshot.verify_checksum() {
            return Err(LibkrunError::SnapshotCorrupted);
        }

        // Verify architecture compatibility
        if snapshot.metadata().architecture != self.architecture {
            return Err(LibkrunError::RestoreFailed {
                reason: format!(
                    "architecture mismatch: snapshot is {}, VM is {}",
                    snapshot.metadata().architecture,
                    self.architecture
                ),
            });
        }

        // Restore implementation for libkrun
        //
        // NOTE: As of libkrun 1.x, there is no built-in restore API.
        // This is the counterpart to snapshot() and has similar limitations.
        //
        // Implementation approach (when snapshot is available):
        //
        // 1. **QEMU Monitor Commands**:
        //    - Write snapshot memory to file
        //    - Connect to QEMU monitor
        //    - Issue "loadvm" or "migrate" command with file path
        //    - Wait for restore completion
        //    - Verify VM state
        //
        // 2. **Direct Memory Load** (via libkrun extension):
        //    - Call hypothetical krun_restore_memory(ctx_id, *const u8, size)
        //    - Wait for completion
        //    - Transition to Running state
        //
        // 3. **Process Memory Injection**:
        //    - Stop VM process
        //    - Use ptrace or similar to inject memory
        //    - Resume VM process
        //
        // The restore process must also:
        // - Restore VM configuration (CPU, memory, devices)
        // - Restore device state (disk, network)
        // - Synchronize with guest agent
        //
        // For DST testing, MockVm provides working restore.
        // Real libkrun restore requires snapshot() to be implemented first.
        //
        // Decision: Return unsupported error until snapshot/restore pipeline
        // is implemented via QEMU monitor or upstream libkrun feature.

        Err(LibkrunError::RestoreFailed {
            reason:
                "libkrun 1.x does not expose restore API (requires snapshot implementation first)"
                    .to_string(),
        })
    }
}

#[cfg(test)]
#[cfg(feature = "libkrun")]
mod tests {
    use super::*;

    fn test_config() -> VmConfig {
        VmConfig::builder()
            .cpus(2)
            .memory_mib(512)
            .root_disk("/tmp/test-rootfs")
            .build()
            .unwrap()
    }

    #[test]
    fn test_libkrun_vm_creation_with_real_ffi() {
        // REQUIRES: libkrun installed on system (will fail if not installed)
        //
        // This test verifies real FFI integration:
        // - Calls krun_create_ctx() and receives valid context ID
        // - Validates context ID is non-negative
        // - Verifies initial state is Created
        // - Tests Drop trait cleanup (krun_free_ctx called on drop)

        let result = LibkrunVm::new(test_config());

        // If libkrun is installed, this should succeed
        // If not installed, krun_create_ctx will fail and we'll get ContextCreationFailed
        if result.is_err() {
            let err = result.unwrap_err();
            eprintln!("Note: libkrun appears not to be installed: {}", err);
            eprintln!("This is expected if running tests without libkrun system dependencies.");
            eprintln!("To install libkrun: https://github.com/containers/libkrun");
            // Don't panic - just log and return
            // This allows CI to run without requiring libkrun installation
            return;
        }

        let vm = result.unwrap();

        // Verify FFI actually worked
        assert_eq!(vm.state(), VmState::Created);
        assert!(vm.context_id() >= 0, "context ID must be non-negative");
        assert!(!vm.id().is_empty(), "VM ID must be set");
        assert_eq!(vm.architecture(), std::env::consts::ARCH);

        // vm drops here, should call krun_free_ctx
    }

    #[tokio::test]
    async fn test_libkrun_vm_start_requires_valid_rootfs() {
        // REQUIRES: libkrun installed on system
        //
        // This test verifies that start() actually calls the FFI chain:
        // - configure_vm() -> krun_set_vm_config() + krun_set_root()
        // - boot_vm() -> krun_start_enter()
        //
        // Expected to FAIL because /tmp/test-rootfs doesn't exist.
        // This proves we're calling real FFI, not fake stubs.

        let config = test_config();
        let result = LibkrunVm::new(config);

        if result.is_err() {
            eprintln!("Note: libkrun not installed, skipping start test");
            return;
        }

        let mut vm = result.unwrap();
        assert_eq!(vm.state(), VmState::Created);

        // Attempt to start - this should fail because /tmp/test-rootfs doesn't exist
        let start_result = vm.start().await;

        // We expect this to fail with ConfigurationFailed or BootFailed
        // because the rootfs path is invalid
        assert!(
            start_result.is_err(),
            "start() should fail with invalid rootfs path - if it succeeded, FFI might not be working"
        );

        let err = start_result.unwrap_err();
        eprintln!("Expected error (proves real FFI): {}", err);

        // Error should be ConfigurationFailed or BootFailed
        assert!(
            matches!(
                err,
                LibkrunError::ConfigurationFailed { .. } | LibkrunError::BootFailed { .. }
            ),
            "Expected ConfigurationFailed or BootFailed, got: {:?}",
            err
        );
    }

    #[test]
    fn test_libkrun_vm_context_id_uniqueness() {
        // REQUIRES: libkrun installed
        //
        // Verify that multiple VMs get unique context IDs from libkrun

        let config1 = test_config();
        let config2 = test_config();

        let result1 = LibkrunVm::new(config1);
        let result2 = LibkrunVm::new(config2);

        if result1.is_err() || result2.is_err() {
            eprintln!("Note: libkrun not installed, skipping uniqueness test");
            return;
        }

        let vm1 = result1.unwrap();
        let vm2 = result2.unwrap();

        // Context IDs should be different
        assert_ne!(
            vm1.context_id(),
            vm2.context_id(),
            "Each VM should get a unique context ID from libkrun"
        );

        // VM IDs should also be different
        assert_ne!(vm1.id(), vm2.id(), "VM IDs should be unique");
    }

    #[tokio::test]
    async fn test_libkrun_vm_exec_returns_phase_5_8_error() {
        // REQUIRES: libkrun installed
        //
        // Verify that exec() correctly returns the Phase 5.8 deferred error
        // (not a fake success or silent failure)

        let config = test_config();
        let result = LibkrunVm::new(config);

        if result.is_err() {
            eprintln!("Note: libkrun not installed, skipping exec test");
            return;
        }

        let vm = result.unwrap();

        // Manually set state to Running to test exec
        let mut vm_mut = vm;
        vm_mut.state = VmState::Running;

        // Try to exec - should fail with clear Phase 5.8 message
        let exec_result = vm_mut.exec("echo", &["hello"]).await;

        assert!(
            exec_result.is_err(),
            "exec should return error (Phase 5.8 not implemented)"
        );

        let err = exec_result.unwrap_err();
        let err_string = err.to_string();

        assert!(
            err_string.contains("Phase 5.8") || err_string.contains("vsock protocol"),
            "Error should mention Phase 5.8 or vsock protocol, got: {}",
            err_string
        );
    }
}

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
        let id = format!("libkrun-vm-{}", VM_ID_COUNTER.fetch_add(1, Ordering::SeqCst));

        // TODO: Create libkrun context
        // SAFETY: krun_create_ctx() has no preconditions beyond libkrun being initialized
        // let ctx_id = unsafe { krun_sys::krun_create_ctx() };
        //
        // if ctx_id < 0 {
        //     return Err(LibkrunError::ContextCreationFailed {
        //         reason: format!("krun_create_ctx returned {}", ctx_id),
        //     });
        // }
        //
        // assert!(ctx_id >= 0 && ctx_id <= VM_CONTEXT_ID_MAX, "invalid context ID");

        // Placeholder for now (Phase 3 incomplete)
        let ctx_id = -1; // Invalid context - real impl will call krun_create_ctx()

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

        // TODO: Call krun_set_vm_config
        // SAFETY: ctx_id is valid (checked above), vcpu_count and memory are within bounds
        // let result = unsafe {
        //     krun_sys::krun_set_vm_config(
        //         self.ctx_id,
        //         self.config.vcpu_count as u8,
        //         self.config.memory_mib as u32,
        //     )
        // };
        //
        // if result < 0 {
        //     return Err(LibkrunError::ConfigurationFailed {
        //         reason: format!("krun_set_vm_config returned {}", result),
        //     });
        // }

        // TODO: Call krun_set_root
        // let root_disk_cstr = CString::new(self.config.root_disk_path.clone())
        //     .map_err(|e| LibkrunError::ConfigurationFailed {
        //         reason: format!("invalid root disk path: {}", e),
        //     })?;
        //
        // SAFETY: ctx_id is valid, root_disk_cstr is valid UTF-8 CString
        // let result = unsafe {
        //     krun_sys::krun_set_root(self.ctx_id, root_disk_cstr.as_ptr())
        // };
        //
        // if result < 0 {
        //     return Err(LibkrunError::ConfigurationFailed {
        //         reason: format!("krun_set_root returned {}", result),
        //     });
        // }

        trace!(%self.id, "VM configured");
        Ok(())
    }

    /// Boot the VM and wait for guest agent ready
    fn boot_vm(&mut self) -> LibkrunResult<()> {
        assert!(self.ctx_id >= 0, "invalid context ID");
        assert_eq!(self.state, VmState::Created, "VM must be in Created state");

        // TODO: Call krun_start_enter
        // This starts the VM and enters the guest
        // SAFETY: ctx_id is valid, boot should be safe to call
        // let result = unsafe { krun_sys::krun_start_enter(self.ctx_id) };
        //
        // if result < 0 {
        //     return Err(LibkrunError::BootFailed {
        //         reason: format!("krun_start_enter returned {}", result),
        //     });
        // }

        // TODO: Wait for guest agent to be ready
        // This involves checking if the virtio-vsock socket is available

        debug!(%self.id, "VM booted successfully");
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

        // TODO: Implement guest agent communication
        // This involves:
        // 1. Connect to virtio-vsock or Unix socket
        // 2. Send exec request (JSON or protobuf)
        // 3. Read response with stdout/stderr/exit code
        // 4. Handle timeouts

        trace!(%self.id, cmd, ?args, "Executing command");

        // Placeholder for now
        Err(LibkrunError::ExecFailed {
            reason: "guest agent communication not yet implemented".to_string(),
        })
    }
}

#[cfg(feature = "libkrun")]
impl Drop for LibkrunVm {
    fn drop(&mut self) {
        if self.ctx_id >= 0 {
            // TODO: Clean up libkrun context
            // SAFETY: ctx_id is valid (checked above)
            // unsafe {
            //     krun_sys::krun_free_ctx(self.ctx_id);
            // }

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

        // TODO: Implement graceful shutdown
        // Send shutdown signal to guest, wait for clean exit

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

        // TODO: Call krun_pause or equivalent

        self.state = VmState::Paused;

        // Postcondition
        assert_eq!(self.state, VmState::Paused);

        Ok(())
    }

    async fn resume(&mut self) -> LibkrunResult<()> {
        assert_eq!(
            self.state,
            VmState::Paused,
            "can only resume from Paused state"
        );

        // TODO: Call krun_resume or equivalent

        self.state = VmState::Running;

        // Postcondition
        assert_eq!(self.state, VmState::Running);

        Ok(())
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
        // Can snapshot from Running or Paused
        assert!(
            self.state == VmState::Running || self.state == VmState::Paused,
            "can only snapshot from Running or Paused state"
        );

        // TODO: Implement libkrun snapshot
        // This may involve calling krun_get_memory_dump or similar

        Err(LibkrunError::SnapshotFailed {
            reason: "snapshot not yet implemented".to_string(),
        })
    }

    async fn restore(&mut self, snapshot: &VmSnapshot) -> LibkrunResult<()> {
        // Can restore to Created or Stopped
        assert!(
            self.state == VmState::Created || self.state == VmState::Stopped,
            "can only restore to Created or Stopped state"
        );

        // TODO: Implement libkrun restore
        // This may involve calling krun_set_memory_dump or similar

        // Verify checksum
        if !snapshot.verify_checksum() {
            return Err(LibkrunError::SnapshotCorrupted);
        }

        Err(LibkrunError::RestoreFailed {
            reason: "restore not yet implemented".to_string(),
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
    fn test_libkrun_vm_creation() {
        // This test will fail until real libkrun integration is complete
        let result = LibkrunVm::new(test_config());

        // With placeholder implementation, context creation returns -1 (invalid)
        // Real implementation will return valid context ID
        assert!(result.is_ok());
        let vm = result.unwrap();
        assert_eq!(vm.state(), VmState::Created);
    }

    #[tokio::test]
    async fn test_libkrun_vm_invalid_start() {
        let config = test_config();
        let mut vm = LibkrunVm::new(config).unwrap();

        // Can't test actual start without libkrun installed
        // But we can verify state machine logic compiles
        assert_eq!(vm.state(), VmState::Created);
    }
}

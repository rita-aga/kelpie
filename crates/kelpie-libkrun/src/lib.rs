//! Safe Rust bindings for libkrun microVM library
//!
//! TigerStyle: Type-safe VM lifecycle with explicit state transitions.
//!
//! # Overview
//!
//! This crate provides safe Rust bindings for libkrun, a lightweight
//! library for running microVMs using the hypervisor framework (HVF on
//! macOS, KVM on Linux).
//!
//! # Architecture
//!
//! - **VmConfig**: Configuration for VM instances (CPU, memory, disk)
//! - **VmInstance**: Running VM with lifecycle management
//! - **VirtioFs**: Filesystem sharing between host and guest
//! - **Snapshot**: VM state capture for pause/resume/teleport
//!
//! # Feature Flags
//!
//! - `libkrun`: Enable actual libkrun FFI bindings (requires libkrun installed)
//! - Default: Mock implementation for testing
//!
//! # Usage
//!
//! ```ignore
//! use kelpie_libkrun::{VmConfig, VmInstance, VmState};
//!
//! // Create a VM configuration
//! let config = VmConfig::builder()
//!     .cpus(2)
//!     .memory_mib(512)
//!     .root_disk("/path/to/rootfs.ext4")
//!     .build()?;
//!
//! // Create and start a VM
//! let vm = VmInstance::create(config).await?;
//! vm.start().await?;
//!
//! // Execute a command
//! let output = vm.exec("echo", &["hello"]).await?;
//!
//! // Snapshot for teleportation
//! let snapshot = vm.snapshot().await?;
//! ```

mod config;
mod error;
mod snapshot;
mod traits;
mod virtio_fs;

#[cfg(feature = "libkrun")]
mod ffi;

#[cfg(not(feature = "libkrun"))]
mod mock;

pub use config::{VmConfig, VmConfigBuilder};
pub use error::{LibkrunError, LibkrunResult};
pub use snapshot::{VmSnapshot, VmSnapshotMetadata};
pub use traits::{ExecOptions as VmExecOptions, ExecOutput as VmExecOutput, VmInstance, VmState};
pub use virtio_fs::{VirtioFsMount, VirtioFsConfig};

#[cfg(feature = "libkrun")]
pub use ffi::LibkrunVm;

#[cfg(not(feature = "libkrun"))]
pub use mock::{MockVm, MockVmFactory};

// ============================================================================
// TigerStyle Constants
// ============================================================================

/// Maximum number of vCPUs per VM
pub const VM_VCPU_COUNT_MAX: u32 = 32;

/// Minimum memory for a VM in MiB
pub const VM_MEMORY_MIB_MIN: u32 = 128;

/// Maximum memory for a VM in MiB (16 GiB)
pub const VM_MEMORY_MIB_MAX: u32 = 16_384;

/// Default memory for a VM in MiB
pub const VM_MEMORY_MIB_DEFAULT: u32 = 512;

/// Default number of vCPUs
pub const VM_VCPU_COUNT_DEFAULT: u32 = 2;

/// Boot timeout in milliseconds
pub const VM_BOOT_TIMEOUT_MS: u64 = 30_000;

/// Exec timeout in milliseconds (default)
pub const VM_EXEC_TIMEOUT_MS_DEFAULT: u64 = 60_000;

/// Maximum snapshot size in bytes (1 GiB)
pub const VM_SNAPSHOT_SIZE_BYTES_MAX: u64 = 1024 * 1024 * 1024;

/// Maximum root disk path length
pub const VM_ROOT_DISK_PATH_LENGTH_MAX: usize = 4096;

/// Maximum virtio-fs tag length
pub const VIRTIO_FS_TAG_LENGTH_MAX: usize = 36;

/// Maximum number of virtio-fs mounts per VM
pub const VIRTIO_FS_MOUNT_COUNT_MAX: usize = 16;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants_reasonable() {
        assert!(VM_VCPU_COUNT_MAX >= 1);
        assert!(VM_MEMORY_MIB_MAX >= VM_MEMORY_MIB_MIN);
        assert!(VM_MEMORY_MIB_DEFAULT >= VM_MEMORY_MIB_MIN);
        assert!(VM_MEMORY_MIB_DEFAULT <= VM_MEMORY_MIB_MAX);
        assert!(VM_VCPU_COUNT_DEFAULT >= 1);
        assert!(VM_VCPU_COUNT_DEFAULT <= VM_VCPU_COUNT_MAX);
    }
}

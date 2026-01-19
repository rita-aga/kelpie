//! VM core types and backend implementations for Kelpie
//!
//! TigerStyle: Explicit lifecycle, errors, and feature-gated backends.

mod backend;
mod config;
mod error;
mod mock;
mod snapshot;
mod traits;
mod virtio_fs;

#[cfg(any(feature = "firecracker", feature = "vz"))]
mod backends;

pub use backend::{VmBackend, VmBackendFactory, VmBackendKind};
pub use config::{VmConfig, VmConfigBuilder};
pub use error::{VmError, VmResult};
pub use mock::{MockVm, MockVmFactory};
pub use snapshot::{VmSnapshot, VmSnapshotMetadata};
pub use traits::{ExecOptions as VmExecOptions, ExecOutput as VmExecOutput};
pub use traits::{ExecOptions, ExecOutput, VmFactory, VmInstance, VmState};
pub use virtio_fs::{VirtioFsConfig, VirtioFsMount};

#[cfg(feature = "firecracker")]
pub use backends::firecracker::{FirecrackerConfig, FirecrackerVm, FirecrackerVmFactory};

#[cfg(all(feature = "vz", target_os = "macos"))]
pub use backends::vz::{VzConfig, VzVm, VzVmFactory};

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

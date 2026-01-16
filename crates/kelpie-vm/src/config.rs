//! VM configuration types
//!
//! TigerStyle: Builder pattern with validation assertions.

use crate::error::{VmError, VmResult};
use crate::virtio_fs::VirtioFsMount;
use crate::{
    VIRTIO_FS_MOUNT_COUNT_MAX, VM_MEMORY_MIB_DEFAULT, VM_MEMORY_MIB_MAX, VM_MEMORY_MIB_MIN,
    VM_ROOT_DISK_PATH_LENGTH_MAX, VM_VCPU_COUNT_DEFAULT, VM_VCPU_COUNT_MAX,
};

/// Configuration for a VM instance
#[derive(Debug, Clone)]
pub struct VmConfig {
    /// Number of virtual CPUs
    pub vcpu_count: u32,

    /// Memory in MiB
    pub memory_mib: u32,

    /// Path to root disk image
    pub root_disk_path: String,

    /// Whether root disk is read-only
    pub root_disk_readonly: bool,

    /// Kernel command line arguments
    pub kernel_args: Option<String>,

    /// Path to kernel image (required for Firecracker/Apple VZ)
    pub kernel_image_path: Option<String>,

    /// Path to initrd image (optional for Firecracker/Apple VZ)
    pub initrd_path: Option<String>,

    /// VirtioFs mounts for filesystem sharing
    pub virtio_fs_mounts: Vec<VirtioFsMount>,

    /// Enable networking
    pub networking_enabled: bool,

    /// Working directory inside the VM
    pub workdir: Option<String>,

    /// Environment variables to pass to the VM
    pub env_vars: Vec<(String, String)>,
}

impl Default for VmConfig {
    fn default() -> Self {
        Self {
            vcpu_count: VM_VCPU_COUNT_DEFAULT,
            memory_mib: VM_MEMORY_MIB_DEFAULT,
            root_disk_path: String::new(),
            root_disk_readonly: false,
            kernel_args: None,
            kernel_image_path: None,
            initrd_path: None,
            virtio_fs_mounts: Vec::new(),
            networking_enabled: true,
            workdir: None,
            env_vars: Vec::new(),
        }
    }
}

impl VmConfig {
    /// Create a new builder for VmConfig
    pub fn builder() -> VmConfigBuilder {
        VmConfigBuilder::new()
    }

    /// Validate the configuration
    pub fn validate(&self) -> VmResult<()> {
        // Preconditions
        assert!(VM_VCPU_COUNT_MAX >= 1);
        assert!(VM_MEMORY_MIB_MAX >= VM_MEMORY_MIB_MIN);

        // vCPU validation
        if self.vcpu_count == 0 {
            return Err(VmError::ConfigInvalid {
                reason: "vcpu_count must be at least 1".into(),
            });
        }
        if self.vcpu_count > VM_VCPU_COUNT_MAX {
            return Err(VmError::ConfigInvalid {
                reason: format!(
                    "vcpu_count {} exceeds max {}",
                    self.vcpu_count, VM_VCPU_COUNT_MAX
                ),
            });
        }

        // Memory validation
        if self.memory_mib < VM_MEMORY_MIB_MIN {
            return Err(VmError::ConfigInvalid {
                reason: format!(
                    "memory_mib {} below minimum {}",
                    self.memory_mib, VM_MEMORY_MIB_MIN
                ),
            });
        }
        if self.memory_mib > VM_MEMORY_MIB_MAX {
            return Err(VmError::ConfigInvalid {
                reason: format!(
                    "memory_mib {} exceeds max {}",
                    self.memory_mib, VM_MEMORY_MIB_MAX
                ),
            });
        }

        // Root disk validation
        if self.root_disk_path.is_empty() {
            return Err(VmError::ConfigInvalid {
                reason: "root_disk_path cannot be empty".into(),
            });
        }
        if self.root_disk_path.len() > VM_ROOT_DISK_PATH_LENGTH_MAX {
            return Err(VmError::ConfigInvalid {
                reason: format!(
                    "root_disk_path length {} exceeds max {}",
                    self.root_disk_path.len(),
                    VM_ROOT_DISK_PATH_LENGTH_MAX
                ),
            });
        }

        if let Some(kernel_path) = &self.kernel_image_path {
            if kernel_path.is_empty() {
                return Err(VmError::ConfigInvalid {
                    reason: "kernel_image_path cannot be empty".into(),
                });
            }
            if kernel_path.len() > VM_ROOT_DISK_PATH_LENGTH_MAX {
                return Err(VmError::ConfigInvalid {
                    reason: format!(
                        "kernel_image_path length {} exceeds max {}",
                        kernel_path.len(),
                        VM_ROOT_DISK_PATH_LENGTH_MAX
                    ),
                });
            }
        }

        if let Some(initrd_path) = &self.initrd_path {
            if initrd_path.is_empty() {
                return Err(VmError::ConfigInvalid {
                    reason: "initrd_path cannot be empty".into(),
                });
            }
            if initrd_path.len() > VM_ROOT_DISK_PATH_LENGTH_MAX {
                return Err(VmError::ConfigInvalid {
                    reason: format!(
                        "initrd_path length {} exceeds max {}",
                        initrd_path.len(),
                        VM_ROOT_DISK_PATH_LENGTH_MAX
                    ),
                });
            }
        }

        // VirtioFs mounts validation
        if self.virtio_fs_mounts.len() > VIRTIO_FS_MOUNT_COUNT_MAX {
            return Err(VmError::VirtioFsTooManyMounts {
                count: self.virtio_fs_mounts.len(),
                max: VIRTIO_FS_MOUNT_COUNT_MAX,
            });
        }

        for mount in &self.virtio_fs_mounts {
            mount.validate()?;
        }

        Ok(())
    }
}

/// Builder for VmConfig
#[derive(Debug, Default)]
pub struct VmConfigBuilder {
    vcpu_count: Option<u32>,
    memory_mib: Option<u32>,
    root_disk_path: Option<String>,
    root_disk_readonly: bool,
    kernel_args: Option<String>,
    kernel_image_path: Option<String>,
    initrd_path: Option<String>,
    virtio_fs_mounts: Vec<VirtioFsMount>,
    networking_enabled: bool,
    workdir: Option<String>,
    env_vars: Vec<(String, String)>,
}

impl VmConfigBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            networking_enabled: true,
            ..Default::default()
        }
    }

    /// Set the number of vCPUs
    pub fn vcpu_count(mut self, count: u32) -> Self {
        self.vcpu_count = Some(count);
        self
    }

    /// Alias for vcpu_count for convenience
    pub fn cpus(self, count: u32) -> Self {
        self.vcpu_count(count)
    }

    /// Set memory in MiB
    pub fn memory_mib(mut self, mib: u32) -> Self {
        self.memory_mib = Some(mib);
        self
    }

    /// Set the root disk path
    pub fn root_disk(mut self, path: impl Into<String>) -> Self {
        self.root_disk_path = Some(path.into());
        self
    }

    /// Set root disk as read-only
    pub fn root_disk_readonly(mut self, readonly: bool) -> Self {
        self.root_disk_readonly = readonly;
        self
    }

    /// Set kernel command line arguments
    pub fn kernel_args(mut self, args: impl Into<String>) -> Self {
        self.kernel_args = Some(args.into());
        self
    }

    /// Set the kernel image path
    pub fn kernel_image(mut self, path: impl Into<String>) -> Self {
        self.kernel_image_path = Some(path.into());
        self
    }

    /// Set the initrd path
    pub fn initrd(mut self, path: impl Into<String>) -> Self {
        self.initrd_path = Some(path.into());
        self
    }

    /// Add a VirtioFs mount
    pub fn add_virtio_fs(mut self, mount: VirtioFsMount) -> Self {
        self.virtio_fs_mounts.push(mount);
        self
    }

    /// Enable or disable networking
    pub fn networking(mut self, enabled: bool) -> Self {
        self.networking_enabled = enabled;
        self
    }

    /// Set the working directory
    pub fn workdir(mut self, dir: impl Into<String>) -> Self {
        self.workdir = Some(dir.into());
        self
    }

    /// Add an environment variable
    pub fn env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.env_vars.push((key.into(), value.into()));
        self
    }

    /// Build the configuration, validating all values
    pub fn build(self) -> VmResult<VmConfig> {
        let config = VmConfig {
            vcpu_count: self.vcpu_count.unwrap_or(VM_VCPU_COUNT_DEFAULT),
            memory_mib: self.memory_mib.unwrap_or(VM_MEMORY_MIB_DEFAULT),
            root_disk_path: self.root_disk_path.unwrap_or_default(),
            root_disk_readonly: self.root_disk_readonly,
            kernel_args: self.kernel_args,
            kernel_image_path: self.kernel_image_path,
            initrd_path: self.initrd_path,
            virtio_fs_mounts: self.virtio_fs_mounts,
            networking_enabled: self.networking_enabled,
            workdir: self.workdir,
            env_vars: self.env_vars,
        };

        config.validate()?;
        Ok(config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_builder_defaults() {
        let config = VmConfig::builder()
            .root_disk("/path/to/rootfs.ext4")
            .build()
            .unwrap();

        assert_eq!(config.vcpu_count, VM_VCPU_COUNT_DEFAULT);
        assert_eq!(config.memory_mib, VM_MEMORY_MIB_DEFAULT);
        assert!(config.networking_enabled);
    }

    #[test]
    fn test_config_builder_full() {
        let config = VmConfig::builder()
            .cpus(4)
            .memory_mib(1024)
            .root_disk("/path/to/rootfs.ext4")
            .root_disk_readonly(true)
            .kernel_args("console=ttyS0")
            .networking(false)
            .workdir("/app")
            .env("PATH", "/usr/bin")
            .build()
            .unwrap();

        assert_eq!(config.vcpu_count, 4);
        assert_eq!(config.memory_mib, 1024);
        assert!(config.root_disk_readonly);
        assert!(!config.networking_enabled);
        assert_eq!(config.workdir, Some("/app".into()));
        assert_eq!(config.env_vars.len(), 1);
    }

    #[test]
    fn test_config_validation_no_root_disk() {
        let result = VmConfig::builder().build();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, VmError::ConfigInvalid { .. }));
    }

    #[test]
    fn test_config_validation_vcpu_zero() {
        let result = VmConfig::builder()
            .vcpu_count(0)
            .root_disk("/path/to/rootfs.ext4")
            .build();

        assert!(result.is_err());
    }

    #[test]
    fn test_config_validation_vcpu_too_high() {
        let result = VmConfig::builder()
            .vcpu_count(VM_VCPU_COUNT_MAX + 1)
            .root_disk("/path/to/rootfs.ext4")
            .build();

        assert!(result.is_err());
    }

    #[test]
    fn test_config_validation_memory_too_low() {
        let result = VmConfig::builder()
            .memory_mib(VM_MEMORY_MIB_MIN - 1)
            .root_disk("/path/to/rootfs.ext4")
            .build();

        assert!(result.is_err());
    }

    #[test]
    fn test_config_validation_memory_too_high() {
        let result = VmConfig::builder()
            .memory_mib(VM_MEMORY_MIB_MAX + 1)
            .root_disk("/path/to/rootfs.ext4")
            .build();

        assert!(result.is_err());
    }
}

//! VirtioFs filesystem sharing
//!
//! TigerStyle: Validated mount configuration with explicit permissions.

use crate::error::{LibkrunError, LibkrunResult};
use crate::VIRTIO_FS_TAG_LENGTH_MAX;

/// Configuration for VirtioFs
#[derive(Debug, Clone, Default)]
pub struct VirtioFsConfig {
    /// Number of request queues
    pub queue_count: u32,
    /// Whether to enable DAX (Direct Access)
    pub dax_enabled: bool,
    /// DAX window size in MiB (if DAX enabled)
    pub dax_window_mib: u32,
}

impl VirtioFsConfig {
    /// Create default VirtioFs config
    pub fn new() -> Self {
        Self {
            queue_count: 1,
            dax_enabled: false,
            dax_window_mib: 0,
        }
    }

    /// Enable DAX with specified window size
    pub fn with_dax(mut self, window_mib: u32) -> Self {
        self.dax_enabled = true;
        self.dax_window_mib = window_mib;
        self
    }
}

/// A VirtioFs mount point
#[derive(Debug, Clone)]
pub struct VirtioFsMount {
    /// Tag used to identify the mount (max 36 chars)
    pub tag: String,
    /// Path on the host filesystem
    pub host_path: String,
    /// Mount point inside the guest
    pub guest_mount_point: String,
    /// Whether the mount is read-only
    pub readonly: bool,
    /// VirtioFs configuration
    pub config: VirtioFsConfig,
}

impl VirtioFsMount {
    /// Create a new VirtioFs mount
    pub fn new(
        tag: impl Into<String>,
        host_path: impl Into<String>,
        guest_mount_point: impl Into<String>,
    ) -> Self {
        Self {
            tag: tag.into(),
            host_path: host_path.into(),
            guest_mount_point: guest_mount_point.into(),
            readonly: false,
            config: VirtioFsConfig::new(),
        }
    }

    /// Create a read-only mount
    pub fn readonly(
        tag: impl Into<String>,
        host_path: impl Into<String>,
        guest_mount_point: impl Into<String>,
    ) -> Self {
        Self {
            tag: tag.into(),
            host_path: host_path.into(),
            guest_mount_point: guest_mount_point.into(),
            readonly: true,
            config: VirtioFsConfig::new(),
        }
    }

    /// Set the VirtioFs configuration
    pub fn with_config(mut self, config: VirtioFsConfig) -> Self {
        self.config = config;
        self
    }

    /// Validate the mount configuration
    pub fn validate(&self) -> LibkrunResult<()> {
        // Tag validation
        if self.tag.is_empty() {
            return Err(LibkrunError::ConfigInvalid {
                reason: "virtio-fs tag cannot be empty".into(),
            });
        }
        if self.tag.len() > VIRTIO_FS_TAG_LENGTH_MAX {
            return Err(LibkrunError::ConfigInvalid {
                reason: format!(
                    "virtio-fs tag length {} exceeds max {}",
                    self.tag.len(),
                    VIRTIO_FS_TAG_LENGTH_MAX
                ),
            });
        }

        // Host path validation
        if self.host_path.is_empty() {
            return Err(LibkrunError::ConfigInvalid {
                reason: "virtio-fs host_path cannot be empty".into(),
            });
        }

        // Guest mount point validation
        if self.guest_mount_point.is_empty() {
            return Err(LibkrunError::ConfigInvalid {
                reason: "virtio-fs guest_mount_point cannot be empty".into(),
            });
        }
        if !self.guest_mount_point.starts_with('/') {
            return Err(LibkrunError::ConfigInvalid {
                reason: "virtio-fs guest_mount_point must be absolute path".into(),
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_virtio_fs_mount_creation() {
        let mount = VirtioFsMount::new("workdir", "/home/user/project", "/workspace");

        assert_eq!(mount.tag, "workdir");
        assert_eq!(mount.host_path, "/home/user/project");
        assert_eq!(mount.guest_mount_point, "/workspace");
        assert!(!mount.readonly);
    }

    #[test]
    fn test_virtio_fs_mount_readonly() {
        let mount = VirtioFsMount::readonly("tools", "/usr/local/bin", "/tools");

        assert!(mount.readonly);
    }

    #[test]
    fn test_virtio_fs_mount_validation_success() {
        let mount = VirtioFsMount::new("myfs", "/host/path", "/guest/path");
        assert!(mount.validate().is_ok());
    }

    #[test]
    fn test_virtio_fs_mount_validation_empty_tag() {
        let mount = VirtioFsMount::new("", "/host/path", "/guest/path");
        let result = mount.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_virtio_fs_mount_validation_tag_too_long() {
        let long_tag = "a".repeat(VIRTIO_FS_TAG_LENGTH_MAX + 1);
        let mount = VirtioFsMount::new(long_tag, "/host/path", "/guest/path");
        let result = mount.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_virtio_fs_mount_validation_empty_host_path() {
        let mount = VirtioFsMount::new("myfs", "", "/guest/path");
        let result = mount.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_virtio_fs_mount_validation_relative_guest_path() {
        let mount = VirtioFsMount::new("myfs", "/host/path", "relative/path");
        let result = mount.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_virtio_fs_config_with_dax() {
        let config = VirtioFsConfig::new().with_dax(512);

        assert!(config.dax_enabled);
        assert_eq!(config.dax_window_mib, 512);
    }
}

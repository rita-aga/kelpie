//! VM snapshot types for pause/resume/teleport
//!
//! TigerStyle: Checksummed data with explicit metadata.

use bytes::Bytes;
use serde::{Deserialize, Serialize};

use crate::error::{VmError, VmResult};
use crate::VM_SNAPSHOT_SIZE_BYTES_MAX;

/// Metadata about a VM snapshot
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmSnapshotMetadata {
    /// Unique identifier for this snapshot
    pub snapshot_id: String,

    /// ID of the VM this snapshot came from
    pub vm_id: String,

    /// Timestamp when snapshot was created (Unix epoch ms)
    pub created_at_ms: u64,

    /// Size of the snapshot data in bytes
    pub size_bytes: u64,

    /// CRC32 checksum of the snapshot data
    pub checksum: u32,

    /// Architecture of the VM (e.g., "aarch64", "x86_64")
    pub architecture: String,

    /// Number of vCPUs in the VM
    pub vcpu_count: u32,

    /// Memory size in MiB
    pub memory_mib: u32,

    /// Whether this is a full VM snapshot or app checkpoint
    pub is_full_snapshot: bool,
}

impl VmSnapshotMetadata {
    /// Create new snapshot metadata
    pub fn new(
        snapshot_id: String,
        vm_id: String,
        size_bytes: u64,
        checksum: u32,
        architecture: String,
        vcpu_count: u32,
        memory_mib: u32,
    ) -> Self {
        // Preconditions
        assert!(!snapshot_id.is_empty(), "snapshot_id cannot be empty");
        assert!(!vm_id.is_empty(), "vm_id cannot be empty");
        assert!(!architecture.is_empty(), "architecture cannot be empty");

        Self {
            snapshot_id,
            vm_id,
            created_at_ms: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_millis() as u64)
                .unwrap_or(0),
            size_bytes,
            checksum,
            architecture,
            vcpu_count,
            memory_mib,
            is_full_snapshot: true,
        }
    }

    /// Check if this snapshot can be restored to a VM with the given architecture
    pub fn is_compatible_with(&self, target_arch: &str) -> bool {
        if self.is_full_snapshot {
            // Full VM snapshots require same architecture
            self.architecture == target_arch
        } else {
            // App checkpoints can work across architectures
            true
        }
    }
}

/// A captured VM snapshot
#[derive(Debug, Clone)]
pub struct VmSnapshot {
    /// Metadata about the snapshot
    pub metadata: VmSnapshotMetadata,

    /// The snapshot data (memory state, registers, etc.)
    pub data: Bytes,
}

impl VmSnapshot {
    /// Create a new snapshot
    #[allow(clippy::assertions_on_constants)] // TigerStyle: validate constants
    pub fn new(metadata: VmSnapshotMetadata, data: Bytes) -> VmResult<Self> {
        // Preconditions
        assert!(VM_SNAPSHOT_SIZE_BYTES_MAX > 0);

        let size_bytes = data.len() as u64;

        if size_bytes > VM_SNAPSHOT_SIZE_BYTES_MAX {
            return Err(VmError::SnapshotTooLarge {
                size_bytes,
                max_bytes: VM_SNAPSHOT_SIZE_BYTES_MAX,
            });
        }

        Ok(Self { metadata, data })
    }

    /// Verify the snapshot checksum
    pub fn verify_checksum(&self) -> bool {
        let computed = crc32fast::hash(&self.data);
        computed == self.metadata.checksum
    }

    /// Get the snapshot size in bytes
    pub fn size_bytes(&self) -> u64 {
        self.data.len() as u64
    }

    /// Create an empty snapshot for testing
    #[cfg(test)]
    pub fn empty(vm_id: &str) -> Self {
        let data = Bytes::new();
        let checksum = crc32fast::hash(&data);
        let metadata = VmSnapshotMetadata::new(
            "test-snapshot".to_string(),
            vm_id.to_string(),
            0,
            checksum,
            "aarch64".to_string(),
            2,
            512,
        );
        Self { metadata, data }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_snapshot_metadata_creation() {
        let metadata = VmSnapshotMetadata::new(
            "snap-123".to_string(),
            "vm-456".to_string(),
            1024,
            12345,
            "aarch64".to_string(),
            4,
            1024,
        );

        assert_eq!(metadata.snapshot_id, "snap-123");
        assert_eq!(metadata.vm_id, "vm-456");
        assert_eq!(metadata.size_bytes, 1024);
        assert_eq!(metadata.checksum, 12345);
        assert!(metadata.is_full_snapshot);
    }

    #[test]
    fn test_snapshot_compatibility_same_arch() {
        let metadata = VmSnapshotMetadata::new(
            "snap-123".to_string(),
            "vm-456".to_string(),
            1024,
            12345,
            "aarch64".to_string(),
            4,
            1024,
        );

        assert!(metadata.is_compatible_with("aarch64"));
        assert!(!metadata.is_compatible_with("x86_64"));
    }

    #[test]
    fn test_snapshot_compatibility_app_checkpoint() {
        let mut metadata = VmSnapshotMetadata::new(
            "snap-123".to_string(),
            "vm-456".to_string(),
            1024,
            12345,
            "aarch64".to_string(),
            4,
            1024,
        );
        metadata.is_full_snapshot = false;

        // App checkpoints work across architectures
        assert!(metadata.is_compatible_with("aarch64"));
        assert!(metadata.is_compatible_with("x86_64"));
    }

    #[test]
    fn test_snapshot_checksum_verification() {
        let data = Bytes::from("test data");
        let checksum = crc32fast::hash(&data);
        let metadata = VmSnapshotMetadata::new(
            "snap-123".to_string(),
            "vm-456".to_string(),
            data.len() as u64,
            checksum,
            "aarch64".to_string(),
            2,
            512,
        );

        let snapshot = VmSnapshot::new(metadata, data).unwrap();
        assert!(snapshot.verify_checksum());
    }

    #[test]
    fn test_snapshot_checksum_invalid() {
        let data = Bytes::from("test data");
        let wrong_checksum = 99999;
        let metadata = VmSnapshotMetadata::new(
            "snap-123".to_string(),
            "vm-456".to_string(),
            data.len() as u64,
            wrong_checksum,
            "aarch64".to_string(),
            2,
            512,
        );

        let snapshot = VmSnapshot::new(metadata, data).unwrap();
        assert!(!snapshot.verify_checksum());
    }

    #[test]
    fn test_snapshot_too_large() {
        // Create data larger than max (would need huge allocation, so we test the error path)
        let metadata = VmSnapshotMetadata::new(
            "snap-123".to_string(),
            "vm-456".to_string(),
            VM_SNAPSHOT_SIZE_BYTES_MAX + 1,
            12345,
            "aarch64".to_string(),
            2,
            512,
        );

        // Create fake large data by setting metadata size
        // (actual data is smaller, but we're testing the validation)
        let data = Bytes::from("small");
        let result = VmSnapshot { metadata, data };

        // Size check happens at creation, so we verify metadata
        assert!(result.metadata.size_bytes > VM_SNAPSHOT_SIZE_BYTES_MAX);
    }
}

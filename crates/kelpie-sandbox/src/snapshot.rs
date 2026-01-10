//! Sandbox snapshot types for state checkpointing
//!
//! TigerStyle: Explicit snapshot boundaries with versioned metadata.

use bytes::Bytes;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Snapshot format version
pub const SNAPSHOT_FORMAT_VERSION: u32 = 1;

/// Metadata for a sandbox snapshot
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotMetadata {
    /// Snapshot ID
    pub id: String,
    /// Sandbox ID this snapshot belongs to
    pub sandbox_id: String,
    /// Format version
    pub version: u32,
    /// When the snapshot was created
    pub created_at: DateTime<Utc>,
    /// Memory size in bytes
    pub memory_bytes: u64,
    /// Disk size in bytes
    pub disk_bytes: u64,
    /// Whether the snapshot includes memory state
    pub includes_memory: bool,
    /// Whether the snapshot includes disk state
    pub includes_disk: bool,
    /// Optional description
    pub description: Option<String>,
}

impl SnapshotMetadata {
    /// Create new snapshot metadata
    pub fn new(sandbox_id: impl Into<String>) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            sandbox_id: sandbox_id.into(),
            version: SNAPSHOT_FORMAT_VERSION,
            created_at: Utc::now(),
            memory_bytes: 0,
            disk_bytes: 0,
            includes_memory: true,
            includes_disk: true,
            description: None,
        }
    }

    /// Set memory size
    pub fn with_memory_size(mut self, bytes: u64) -> Self {
        self.memory_bytes = bytes;
        self
    }

    /// Set disk size
    pub fn with_disk_size(mut self, bytes: u64) -> Self {
        self.disk_bytes = bytes;
        self
    }

    /// Set description
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = Some(description.into());
        self
    }

    /// Mark as memory-only snapshot
    pub fn memory_only(mut self) -> Self {
        self.includes_disk = false;
        self
    }

    /// Mark as disk-only snapshot
    pub fn disk_only(mut self) -> Self {
        self.includes_memory = false;
        self
    }

    /// Total snapshot size
    pub fn total_bytes(&self) -> u64 {
        self.memory_bytes + self.disk_bytes
    }
}

/// A complete sandbox snapshot
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Snapshot {
    /// Metadata
    pub metadata: SnapshotMetadata,
    /// Memory state (if included)
    pub memory: Option<Bytes>,
    /// Disk state (if included) - typically a reference/path rather than inline
    pub disk_reference: Option<String>,
    /// CPU/register state (implementation-specific)
    pub cpu_state: Option<Bytes>,
    /// Environment state
    pub env_state: Option<Vec<(String, String)>>,
}

impl Snapshot {
    /// Create a new snapshot
    pub fn new(sandbox_id: impl Into<String>) -> Self {
        Self {
            metadata: SnapshotMetadata::new(sandbox_id),
            memory: None,
            disk_reference: None,
            cpu_state: None,
            env_state: None,
        }
    }

    /// Get the snapshot ID
    pub fn id(&self) -> &str {
        &self.metadata.id
    }

    /// Get the sandbox ID
    pub fn sandbox_id(&self) -> &str {
        &self.metadata.sandbox_id
    }

    /// Set memory state
    pub fn with_memory(mut self, memory: impl Into<Bytes>) -> Self {
        let memory = memory.into();
        self.metadata.memory_bytes = memory.len() as u64;
        self.memory = Some(memory);
        self
    }

    /// Set disk reference
    pub fn with_disk_reference(mut self, reference: impl Into<String>) -> Self {
        self.disk_reference = Some(reference.into());
        self
    }

    /// Set CPU state
    pub fn with_cpu_state(mut self, state: impl Into<Bytes>) -> Self {
        self.cpu_state = Some(state.into());
        self
    }

    /// Set environment state
    pub fn with_env_state(mut self, env: Vec<(String, String)>) -> Self {
        self.env_state = Some(env);
        self
    }

    /// Serialize to bytes
    pub fn to_bytes(&self) -> Result<Bytes, serde_json::Error> {
        serde_json::to_vec(self).map(Bytes::from)
    }

    /// Deserialize from bytes
    pub fn from_bytes(data: &[u8]) -> Result<Self, serde_json::Error> {
        serde_json::from_slice(data)
    }

    /// Check if this is a complete snapshot (both memory and disk)
    pub fn is_complete(&self) -> bool {
        self.metadata.includes_memory
            && self.metadata.includes_disk
            && self.memory.is_some()
            && self.disk_reference.is_some()
    }

    /// Check if this snapshot has memory state
    pub fn has_memory(&self) -> bool {
        self.memory.is_some()
    }

    /// Check if this snapshot has disk reference
    pub fn has_disk(&self) -> bool {
        self.disk_reference.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_snapshot_metadata_new() {
        let meta = SnapshotMetadata::new("sandbox-123");
        assert_eq!(meta.sandbox_id, "sandbox-123");
        assert_eq!(meta.version, SNAPSHOT_FORMAT_VERSION);
        assert!(meta.includes_memory);
        assert!(meta.includes_disk);
    }

    #[test]
    fn test_snapshot_metadata_builder() {
        let meta = SnapshotMetadata::new("sandbox-123")
            .with_memory_size(1024)
            .with_disk_size(2048)
            .with_description("Test snapshot");

        assert_eq!(meta.memory_bytes, 1024);
        assert_eq!(meta.disk_bytes, 2048);
        assert_eq!(meta.total_bytes(), 3072);
        assert_eq!(meta.description, Some("Test snapshot".to_string()));
    }

    #[test]
    fn test_snapshot_metadata_memory_only() {
        let meta = SnapshotMetadata::new("sandbox-123").memory_only();
        assert!(meta.includes_memory);
        assert!(!meta.includes_disk);
    }

    #[test]
    fn test_snapshot_new() {
        let snapshot = Snapshot::new("sandbox-123");
        assert_eq!(snapshot.sandbox_id(), "sandbox-123");
        assert!(snapshot.memory.is_none());
        assert!(snapshot.disk_reference.is_none());
    }

    #[test]
    fn test_snapshot_with_memory() {
        let snapshot = Snapshot::new("sandbox-123").with_memory(Bytes::from("memory data"));

        assert!(snapshot.has_memory());
        assert!(!snapshot.has_disk());
        assert_eq!(snapshot.metadata.memory_bytes, 11); // "memory data".len()
    }

    #[test]
    fn test_snapshot_serialization() {
        let snapshot = Snapshot::new("sandbox-123")
            .with_memory(Bytes::from("test"))
            .with_disk_reference("/snapshots/disk-123");

        let bytes = snapshot.to_bytes().unwrap();
        let restored = Snapshot::from_bytes(&bytes).unwrap();

        assert_eq!(restored.sandbox_id(), "sandbox-123");
        assert!(restored.has_memory());
        assert!(restored.has_disk());
    }

    #[test]
    fn test_snapshot_completeness() {
        let incomplete = Snapshot::new("sandbox-123").with_memory(Bytes::from("test"));

        assert!(!incomplete.is_complete());

        let complete = incomplete.with_disk_reference("/disk");
        assert!(complete.is_complete());
    }
}

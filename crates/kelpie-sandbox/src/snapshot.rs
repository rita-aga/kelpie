//! Sandbox snapshot types for state checkpointing
//!
//! TigerStyle: Explicit snapshot boundaries with versioned metadata.
//!
//! # Snapshot Types
//!
//! Three snapshot types support different teleportation scenarios:
//!
//! - **Suspend**: Memory-only, same-host pause/resume (~50MB, <1s)
//! - **Teleport**: Full VM state, same-architecture transfer (~500MB-2GB, ~5s)
//! - **Checkpoint**: Application state only, cross-architecture transfer (~10-100MB, <1s)

use bytes::Bytes;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

// ============================================================================
// TigerStyle Constants
// ============================================================================

/// Snapshot format version
pub const SNAPSHOT_FORMAT_VERSION: u32 = 2;

/// Maximum suspend snapshot size in bytes (100 MiB)
pub const SNAPSHOT_SUSPEND_SIZE_BYTES_MAX: u64 = 100 * 1024 * 1024;

/// Maximum teleport snapshot size in bytes (4 GiB)
pub const SNAPSHOT_TELEPORT_SIZE_BYTES_MAX: u64 = 4 * 1024 * 1024 * 1024;

/// Maximum checkpoint snapshot size in bytes (500 MiB)
pub const SNAPSHOT_CHECKPOINT_SIZE_BYTES_MAX: u64 = 500 * 1024 * 1024;

/// Maximum base image version length
pub const BASE_IMAGE_VERSION_LENGTH_MAX: usize = 64;

// ============================================================================
// Snapshot Kind
// ============================================================================

/// Kind of snapshot for teleportation
///
/// Different snapshot types serve different purposes:
/// - Suspend: Fast pause/resume on same host
/// - Teleport: Full VM migration within same architecture
/// - Checkpoint: Application-level state for cross-architecture transfer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SnapshotKind {
    /// Memory-only snapshot for same-host pause/resume
    ///
    /// Contents: VM memory state only
    /// Size: ~50MB typical
    /// Speed: <1s
    /// Use case: Quick pause/resume during local development
    Suspend,

    /// Full VM snapshot for same-architecture teleportation
    ///
    /// Contents: VM memory + CPU registers + disk state
    /// Size: ~500MB-2GB typical
    /// Speed: ~5s
    /// Use case: Mid-execution migration to another host with same CPU architecture
    Teleport,

    /// Application-level checkpoint for cross-architecture transfer
    ///
    /// Contents: Agent state + workspace (no VM state)
    /// Size: ~10-100MB typical
    /// Speed: <1s
    /// Use case: Migration between ARM64 and x86_64 at safe points
    Checkpoint,
}

impl SnapshotKind {
    /// Get the maximum size in bytes for this snapshot kind
    pub fn max_size_bytes(&self) -> u64 {
        match self {
            SnapshotKind::Suspend => SNAPSHOT_SUSPEND_SIZE_BYTES_MAX,
            SnapshotKind::Teleport => SNAPSHOT_TELEPORT_SIZE_BYTES_MAX,
            SnapshotKind::Checkpoint => SNAPSHOT_CHECKPOINT_SIZE_BYTES_MAX,
        }
    }

    /// Check if this snapshot kind requires same architecture for restore
    pub fn requires_same_architecture(&self) -> bool {
        match self {
            SnapshotKind::Suspend | SnapshotKind::Teleport => true,
            SnapshotKind::Checkpoint => false,
        }
    }

    /// Check if this snapshot kind includes VM state
    pub fn includes_vm_state(&self) -> bool {
        matches!(self, SnapshotKind::Suspend | SnapshotKind::Teleport)
    }

    /// Check if this snapshot kind includes CPU registers
    pub fn includes_cpu_state(&self) -> bool {
        matches!(self, SnapshotKind::Teleport)
    }
}

impl std::fmt::Display for SnapshotKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnapshotKind::Suspend => write!(f, "suspend"),
            SnapshotKind::Teleport => write!(f, "teleport"),
            SnapshotKind::Checkpoint => write!(f, "checkpoint"),
        }
    }
}

// ============================================================================
// Architecture
// ============================================================================

/// CPU architecture for snapshot compatibility
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Architecture {
    /// ARM64 (Apple Silicon, AWS Graviton, Ampere)
    Arm64,
    /// x86_64 (Intel/AMD)
    X86_64,
}

impl Architecture {
    /// Get the current host architecture
    pub fn current() -> Self {
        #[cfg(target_arch = "aarch64")]
        {
            Architecture::Arm64
        }
        #[cfg(target_arch = "x86_64")]
        {
            Architecture::X86_64
        }
        #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
        {
            // Default to ARM64 for unsupported architectures (development)
            Architecture::Arm64
        }
    }

    /// Check if two architectures are compatible for VM snapshot restoration
    pub fn is_compatible_with(&self, other: &Architecture) -> bool {
        self == other
    }
}

impl std::fmt::Display for Architecture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Architecture::Arm64 => write!(f, "arm64"),
            Architecture::X86_64 => write!(f, "x86_64"),
        }
    }
}

impl std::str::FromStr for Architecture {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "arm64" | "aarch64" => Ok(Architecture::Arm64),
            "x86_64" | "amd64" => Ok(Architecture::X86_64),
            _ => Err(format!("Unknown architecture: {}", s)),
        }
    }
}

// ============================================================================
// Snapshot Metadata
// ============================================================================

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
    /// Kind of snapshot
    pub kind: SnapshotKind,
    /// Source architecture
    pub architecture: Architecture,
    /// Base image version (for compatibility validation)
    pub base_image_version: String,
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
    pub fn new(sandbox_id: impl Into<String>, kind: SnapshotKind) -> Self {
        let (includes_memory, includes_disk) = match kind {
            SnapshotKind::Suspend => (true, false),
            SnapshotKind::Teleport => (true, true),
            SnapshotKind::Checkpoint => (false, false), // Only app state
        };

        Self {
            id: Uuid::new_v4().to_string(),
            sandbox_id: sandbox_id.into(),
            version: SNAPSHOT_FORMAT_VERSION,
            created_at: Utc::now(),
            kind,
            architecture: Architecture::current(),
            base_image_version: "1.0.0".to_string(),
            memory_bytes: 0,
            disk_bytes: 0,
            includes_memory,
            includes_disk,
            description: None,
        }
    }

    /// Set architecture
    pub fn with_architecture(mut self, arch: Architecture) -> Self {
        self.architecture = arch;
        self
    }

    /// Set base image version
    pub fn with_base_image_version(mut self, version: impl Into<String>) -> Self {
        let version = version.into();
        assert!(
            version.len() <= BASE_IMAGE_VERSION_LENGTH_MAX,
            "base image version too long"
        );
        self.base_image_version = version;
        self
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

    /// Validate this snapshot can be restored on the given architecture
    pub fn validate_restore(
        &self,
        target_arch: Architecture,
    ) -> Result<(), SnapshotValidationError> {
        // Check architecture compatibility
        if self.kind.requires_same_architecture() && self.architecture != target_arch {
            return Err(SnapshotValidationError::ArchitectureMismatch {
                snapshot_arch: self.architecture,
                target_arch,
            });
        }

        // Check size limits
        let max_size = self.kind.max_size_bytes();
        if self.total_bytes() > max_size {
            return Err(SnapshotValidationError::SizeTooLarge {
                actual_bytes: self.total_bytes(),
                max_bytes: max_size,
            });
        }

        Ok(())
    }

    /// Validate base image version matches
    pub fn validate_base_image(
        &self,
        expected_version: &str,
    ) -> Result<(), SnapshotValidationError> {
        if self.base_image_version != expected_version {
            return Err(SnapshotValidationError::BaseImageMismatch {
                snapshot_version: self.base_image_version.clone(),
                expected_version: expected_version.to_string(),
            });
        }
        Ok(())
    }
}

// ============================================================================
// Snapshot Validation Error
// ============================================================================

/// Errors during snapshot validation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SnapshotValidationError {
    /// Architecture mismatch prevents restoration
    ArchitectureMismatch {
        snapshot_arch: Architecture,
        target_arch: Architecture,
    },
    /// Base image version mismatch
    BaseImageMismatch {
        snapshot_version: String,
        expected_version: String,
    },
    /// Snapshot size exceeds limit
    SizeTooLarge { actual_bytes: u64, max_bytes: u64 },
    /// Snapshot format version unsupported
    UnsupportedVersion {
        snapshot_version: u32,
        supported_version: u32,
    },
}

impl std::fmt::Display for SnapshotValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnapshotValidationError::ArchitectureMismatch {
                snapshot_arch,
                target_arch,
            } => {
                write!(
                    f,
                    "Architecture mismatch: snapshot is {}, target is {}",
                    snapshot_arch, target_arch
                )
            }
            SnapshotValidationError::BaseImageMismatch {
                snapshot_version,
                expected_version,
            } => {
                write!(
                    f,
                    "Base image version mismatch: snapshot is {}, expected {}",
                    snapshot_version, expected_version
                )
            }
            SnapshotValidationError::SizeTooLarge {
                actual_bytes,
                max_bytes,
            } => {
                write!(
                    f,
                    "Snapshot size {} bytes exceeds maximum {} bytes",
                    actual_bytes, max_bytes
                )
            }
            SnapshotValidationError::UnsupportedVersion {
                snapshot_version,
                supported_version,
            } => {
                write!(
                    f,
                    "Snapshot format version {} is not supported (expected {})",
                    snapshot_version, supported_version
                )
            }
        }
    }
}

impl std::error::Error for SnapshotValidationError {}

// ============================================================================
// Snapshot
// ============================================================================

/// A complete sandbox snapshot
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Snapshot {
    /// Metadata
    pub metadata: SnapshotMetadata,
    /// Memory state (for Suspend and Teleport)
    pub memory: Option<Bytes>,
    /// CPU/register state (for Teleport only)
    pub cpu_state: Option<Bytes>,
    /// Disk state reference (for Teleport)
    pub disk_reference: Option<String>,
    /// Agent state (for Checkpoint)
    pub agent_state: Option<Bytes>,
    /// Workspace reference (for Checkpoint and Teleport)
    pub workspace_ref: Option<String>,
    /// Environment state
    pub env_state: Option<Vec<(String, String)>>,
}

impl Snapshot {
    /// Create a new snapshot of the given kind
    pub fn new(sandbox_id: impl Into<String>, kind: SnapshotKind) -> Self {
        Self {
            metadata: SnapshotMetadata::new(sandbox_id, kind),
            memory: None,
            cpu_state: None,
            disk_reference: None,
            agent_state: None,
            workspace_ref: None,
            env_state: None,
        }
    }

    /// Create a Suspend snapshot (memory-only, same-host)
    pub fn suspend(sandbox_id: impl Into<String>) -> Self {
        Self::new(sandbox_id, SnapshotKind::Suspend)
    }

    /// Create a Teleport snapshot (full VM, same-architecture)
    pub fn teleport(sandbox_id: impl Into<String>) -> Self {
        Self::new(sandbox_id, SnapshotKind::Teleport)
    }

    /// Create a Checkpoint snapshot (app state, cross-architecture)
    pub fn checkpoint(sandbox_id: impl Into<String>) -> Self {
        Self::new(sandbox_id, SnapshotKind::Checkpoint)
    }

    /// Get the snapshot ID
    pub fn id(&self) -> &str {
        &self.metadata.id
    }

    /// Get the sandbox ID
    pub fn sandbox_id(&self) -> &str {
        &self.metadata.sandbox_id
    }

    /// Get the snapshot kind
    pub fn kind(&self) -> SnapshotKind {
        self.metadata.kind
    }

    /// Get the source architecture
    pub fn architecture(&self) -> Architecture {
        self.metadata.architecture
    }

    /// Set architecture
    pub fn with_architecture(mut self, arch: Architecture) -> Self {
        self.metadata.architecture = arch;
        self
    }

    /// Set base image version
    pub fn with_base_image_version(mut self, version: impl Into<String>) -> Self {
        self.metadata = self.metadata.with_base_image_version(version);
        self
    }

    /// Set memory state
    pub fn with_memory(mut self, memory: impl Into<Bytes>) -> Self {
        let memory = memory.into();
        self.metadata.memory_bytes = memory.len() as u64;
        self.memory = Some(memory);
        self
    }

    /// Set CPU state (for Teleport)
    pub fn with_cpu_state(mut self, state: impl Into<Bytes>) -> Self {
        self.cpu_state = Some(state.into());
        self
    }

    /// Set disk reference (for Teleport)
    pub fn with_disk_reference(mut self, reference: impl Into<String>) -> Self {
        self.disk_reference = Some(reference.into());
        self
    }

    /// Set agent state (for Checkpoint)
    pub fn with_agent_state(mut self, state: impl Into<Bytes>) -> Self {
        self.agent_state = Some(state.into());
        self
    }

    /// Set workspace reference (for Checkpoint and Teleport)
    pub fn with_workspace_ref(mut self, reference: impl Into<String>) -> Self {
        self.workspace_ref = Some(reference.into());
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

    /// Check if this is a full VM teleport (memory + CPU)
    pub fn is_full_teleport(&self) -> bool {
        self.memory.is_some() && self.cpu_state.is_some()
    }

    /// Check if this is a checkpoint (app state only)
    pub fn is_checkpoint(&self) -> bool {
        self.metadata.kind == SnapshotKind::Checkpoint
    }

    /// Check if this snapshot has memory state
    pub fn has_memory(&self) -> bool {
        self.memory.is_some()
    }

    /// Check if this snapshot has disk reference
    pub fn has_disk(&self) -> bool {
        self.disk_reference.is_some()
    }

    /// Check if this is a complete snapshot for its kind
    pub fn is_complete(&self) -> bool {
        match self.metadata.kind {
            SnapshotKind::Suspend => self.memory.is_some(),
            SnapshotKind::Teleport => {
                self.memory.is_some() && self.cpu_state.is_some() && self.disk_reference.is_some()
            }
            SnapshotKind::Checkpoint => self.agent_state.is_some(),
        }
    }

    /// Validate this snapshot can be restored on the given architecture
    pub fn validate_for_restore(
        &self,
        target_arch: Architecture,
    ) -> Result<(), SnapshotValidationError> {
        self.metadata.validate_restore(target_arch)
    }

    /// Validate base image version matches
    pub fn validate_base_image(
        &self,
        expected_version: &str,
    ) -> Result<(), SnapshotValidationError> {
        self.metadata.validate_base_image(expected_version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // SnapshotKind Tests
    // ========================================================================

    #[test]
    fn test_snapshot_kind_properties() {
        // Suspend
        assert!(SnapshotKind::Suspend.requires_same_architecture());
        assert!(SnapshotKind::Suspend.includes_vm_state());
        assert!(!SnapshotKind::Suspend.includes_cpu_state());

        // Teleport
        assert!(SnapshotKind::Teleport.requires_same_architecture());
        assert!(SnapshotKind::Teleport.includes_vm_state());
        assert!(SnapshotKind::Teleport.includes_cpu_state());

        // Checkpoint
        assert!(!SnapshotKind::Checkpoint.requires_same_architecture());
        assert!(!SnapshotKind::Checkpoint.includes_vm_state());
        assert!(!SnapshotKind::Checkpoint.includes_cpu_state());
    }

    #[test]
    fn test_snapshot_kind_max_sizes() {
        assert_eq!(
            SnapshotKind::Suspend.max_size_bytes(),
            SNAPSHOT_SUSPEND_SIZE_BYTES_MAX
        );
        assert_eq!(
            SnapshotKind::Teleport.max_size_bytes(),
            SNAPSHOT_TELEPORT_SIZE_BYTES_MAX
        );
        assert_eq!(
            SnapshotKind::Checkpoint.max_size_bytes(),
            SNAPSHOT_CHECKPOINT_SIZE_BYTES_MAX
        );
    }

    #[test]
    fn test_snapshot_kind_display() {
        assert_eq!(format!("{}", SnapshotKind::Suspend), "suspend");
        assert_eq!(format!("{}", SnapshotKind::Teleport), "teleport");
        assert_eq!(format!("{}", SnapshotKind::Checkpoint), "checkpoint");
    }

    // ========================================================================
    // Architecture Tests
    // ========================================================================

    #[test]
    fn test_architecture_display() {
        assert_eq!(format!("{}", Architecture::Arm64), "arm64");
        assert_eq!(format!("{}", Architecture::X86_64), "x86_64");
    }

    #[test]
    fn test_architecture_from_str() {
        assert_eq!(
            "arm64".parse::<Architecture>().unwrap(),
            Architecture::Arm64
        );
        assert_eq!(
            "aarch64".parse::<Architecture>().unwrap(),
            Architecture::Arm64
        );
        assert_eq!(
            "x86_64".parse::<Architecture>().unwrap(),
            Architecture::X86_64
        );
        assert_eq!(
            "amd64".parse::<Architecture>().unwrap(),
            Architecture::X86_64
        );
        assert!("unknown".parse::<Architecture>().is_err());
    }

    #[test]
    fn test_architecture_compatibility() {
        assert!(Architecture::Arm64.is_compatible_with(&Architecture::Arm64));
        assert!(!Architecture::Arm64.is_compatible_with(&Architecture::X86_64));
    }

    // ========================================================================
    // SnapshotMetadata Tests
    // ========================================================================

    #[test]
    fn test_snapshot_metadata_new_suspend() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Suspend);
        assert_eq!(meta.sandbox_id, "sandbox-123");
        assert_eq!(meta.kind, SnapshotKind::Suspend);
        assert!(meta.includes_memory);
        assert!(!meta.includes_disk); // Suspend is memory-only
    }

    #[test]
    fn test_snapshot_metadata_new_teleport() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Teleport);
        assert_eq!(meta.kind, SnapshotKind::Teleport);
        assert!(meta.includes_memory);
        assert!(meta.includes_disk); // Teleport includes everything
    }

    #[test]
    fn test_snapshot_metadata_new_checkpoint() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Checkpoint);
        assert_eq!(meta.kind, SnapshotKind::Checkpoint);
        assert!(!meta.includes_memory); // Checkpoint is app-only
        assert!(!meta.includes_disk);
    }

    #[test]
    fn test_snapshot_metadata_builder() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Teleport)
            .with_architecture(Architecture::X86_64)
            .with_base_image_version("2.0.0")
            .with_memory_size(1024)
            .with_disk_size(2048)
            .with_description("Test snapshot");

        assert_eq!(meta.architecture, Architecture::X86_64);
        assert_eq!(meta.base_image_version, "2.0.0");
        assert_eq!(meta.memory_bytes, 1024);
        assert_eq!(meta.disk_bytes, 2048);
        assert_eq!(meta.total_bytes(), 3072);
        assert_eq!(meta.description, Some("Test snapshot".to_string()));
    }

    #[test]
    fn test_snapshot_metadata_validate_restore_same_arch() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Teleport)
            .with_architecture(Architecture::Arm64);

        assert!(meta.validate_restore(Architecture::Arm64).is_ok());
        assert!(meta.validate_restore(Architecture::X86_64).is_err());
    }

    #[test]
    fn test_snapshot_metadata_validate_restore_checkpoint_cross_arch() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Checkpoint)
            .with_architecture(Architecture::Arm64);

        // Checkpoint should work on any architecture
        assert!(meta.validate_restore(Architecture::Arm64).is_ok());
        assert!(meta.validate_restore(Architecture::X86_64).is_ok());
    }

    #[test]
    fn test_snapshot_metadata_validate_base_image() {
        let meta = SnapshotMetadata::new("sandbox-123", SnapshotKind::Teleport)
            .with_base_image_version("1.0.0");

        assert!(meta.validate_base_image("1.0.0").is_ok());
        assert!(meta.validate_base_image("2.0.0").is_err());
    }

    // ========================================================================
    // Snapshot Tests
    // ========================================================================

    #[test]
    fn test_snapshot_suspend() {
        let snapshot = Snapshot::suspend("sandbox-123").with_memory(Bytes::from("memory state"));

        assert_eq!(snapshot.kind(), SnapshotKind::Suspend);
        assert!(snapshot.has_memory());
        assert!(snapshot.is_complete());
        assert!(!snapshot.is_full_teleport()); // No CPU state
    }

    #[test]
    fn test_snapshot_teleport() {
        let snapshot = Snapshot::teleport("sandbox-123")
            .with_memory(Bytes::from("memory"))
            .with_cpu_state(Bytes::from("cpu"))
            .with_disk_reference("/snapshots/disk-123");

        assert_eq!(snapshot.kind(), SnapshotKind::Teleport);
        assert!(snapshot.has_memory());
        assert!(snapshot.has_disk());
        assert!(snapshot.is_full_teleport());
        assert!(snapshot.is_complete());
    }

    #[test]
    fn test_snapshot_checkpoint() {
        let snapshot = Snapshot::checkpoint("sandbox-123")
            .with_agent_state(Bytes::from("agent state"))
            .with_workspace_ref("s3://bucket/workspace");

        assert_eq!(snapshot.kind(), SnapshotKind::Checkpoint);
        assert!(snapshot.is_checkpoint());
        assert!(snapshot.is_complete());
        assert!(!snapshot.is_full_teleport());
    }

    #[test]
    fn test_snapshot_completeness() {
        // Incomplete suspend (no memory)
        let incomplete_suspend = Snapshot::suspend("sandbox-123");
        assert!(!incomplete_suspend.is_complete());

        // Incomplete teleport (no CPU state)
        let incomplete_teleport =
            Snapshot::teleport("sandbox-123").with_memory(Bytes::from("memory"));
        assert!(!incomplete_teleport.is_complete());

        // Incomplete checkpoint (no agent state)
        let incomplete_checkpoint = Snapshot::checkpoint("sandbox-123");
        assert!(!incomplete_checkpoint.is_complete());
    }

    #[test]
    fn test_snapshot_serialization() {
        let snapshot = Snapshot::teleport("sandbox-123")
            .with_memory(Bytes::from("test"))
            .with_cpu_state(Bytes::from("cpu"))
            .with_disk_reference("/snapshots/disk-123")
            .with_base_image_version("1.0.0");

        let bytes = snapshot.to_bytes().unwrap();
        let restored = Snapshot::from_bytes(&bytes).unwrap();

        assert_eq!(restored.sandbox_id(), "sandbox-123");
        assert_eq!(restored.kind(), SnapshotKind::Teleport);
        assert!(restored.has_memory());
        assert!(restored.has_disk());
    }

    #[test]
    fn test_snapshot_validate_for_restore() {
        let teleport = Snapshot::teleport("sandbox-123").with_architecture(Architecture::Arm64);

        assert!(teleport.validate_for_restore(Architecture::Arm64).is_ok());
        assert!(teleport.validate_for_restore(Architecture::X86_64).is_err());

        let checkpoint = Snapshot::checkpoint("sandbox-123").with_architecture(Architecture::Arm64);

        assert!(checkpoint
            .validate_for_restore(Architecture::X86_64)
            .is_ok());
    }

    // ========================================================================
    // SnapshotValidationError Tests
    // ========================================================================

    #[test]
    fn test_snapshot_validation_error_display() {
        let arch_err = SnapshotValidationError::ArchitectureMismatch {
            snapshot_arch: Architecture::Arm64,
            target_arch: Architecture::X86_64,
        };
        assert!(arch_err.to_string().contains("arm64"));
        assert!(arch_err.to_string().contains("x86_64"));

        let version_err = SnapshotValidationError::BaseImageMismatch {
            snapshot_version: "1.0.0".to_string(),
            expected_version: "2.0.0".to_string(),
        };
        assert!(version_err.to_string().contains("1.0.0"));
        assert!(version_err.to_string().contains("2.0.0"));
    }
}

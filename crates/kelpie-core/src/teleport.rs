//! Teleport package types and storage traits
//!
//! TigerStyle: Explicit limits, versioned snapshot blobs, and strict validation.

use async_trait::async_trait;
use bytes::Bytes;
use serde::{Deserialize, Serialize};

/// CPU architecture for teleportation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Architecture {
    /// ARM64 (Apple Silicon, AWS Graviton)
    Arm64,
    /// x86_64 (Intel/AMD)
    X86_64,
}

impl Architecture {
    /// Get the current host architecture
    #[cfg(target_arch = "aarch64")]
    pub fn current() -> Self {
        Architecture::Arm64
    }

    /// Get the current host architecture
    #[cfg(target_arch = "x86_64")]
    pub fn current() -> Self {
        Architecture::X86_64
    }

    /// Get the current host architecture (fallback for other architectures)
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    pub fn current() -> Self {
        Architecture::X86_64
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

/// Snapshot kind for teleportation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SnapshotKind {
    /// Memory-only, same-host resume (fastest)
    Suspend,
    /// Full VM state, same-architecture teleport
    Teleport,
    /// Application state only, cross-architecture checkpoint
    Checkpoint,
}

/// Maximum teleport package ID length in bytes
pub const TELEPORT_ID_LENGTH_BYTES_MAX: usize = 128;

/// Teleport snapshot blob magic header: "KLP1"
pub const TELEPORT_SNAPSHOT_MAGIC_BYTES: [u8; 4] = *b"KLP1";

/// Teleport snapshot blob format version
pub const TELEPORT_SNAPSHOT_FORMAT_VERSION: u32 = 1;

/// Teleport snapshot blob header size in bytes
pub const TELEPORT_SNAPSHOT_HEADER_BYTES: usize = 4 + 4 + 8 + 8 + 8;

/// Errors related to snapshot blob encoding/decoding
#[derive(Debug, Clone)]
pub enum TeleportSnapshotError {
    /// Blob is too small to contain a valid header
    HeaderTooSmall { size_bytes: u64 },
    /// Magic bytes do not match
    InvalidMagic { expected: [u8; 4], actual: [u8; 4] },
    /// Snapshot format version is not supported
    UnsupportedVersion { expected: u32, actual: u32 },
    /// Blob length does not match header sizes
    LengthMismatch { expected: u64, actual: u64 },
}

impl std::fmt::Display for TeleportSnapshotError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TeleportSnapshotError::HeaderTooSmall { size_bytes } => {
                write!(f, "snapshot blob too small: {} bytes", size_bytes)
            }
            TeleportSnapshotError::InvalidMagic { expected, actual } => {
                write!(
                    f,
                    "invalid snapshot magic: expected {:?}, got {:?}",
                    expected, actual
                )
            }
            TeleportSnapshotError::UnsupportedVersion { expected, actual } => {
                write!(
                    f,
                    "unsupported snapshot version: expected {}, got {}",
                    expected, actual
                )
            }
            TeleportSnapshotError::LengthMismatch { expected, actual } => {
                write!(
                    f,
                    "snapshot length mismatch: expected {}, got {}",
                    expected, actual
                )
            }
        }
    }
}

impl std::error::Error for TeleportSnapshotError {}

/// Versioned blob format for VM snapshots
#[derive(Debug, Clone)]
pub struct VmSnapshotBlob {
    /// Serialized metadata bytes (opaque to storage)
    pub metadata_bytes: Bytes,
    /// Hypervisor snapshot bytes
    pub snapshot_bytes: Bytes,
    /// Optional memory bytes (Firecracker split snapshots)
    pub memory_bytes: Bytes,
}

impl VmSnapshotBlob {
    /// Encode metadata + snapshot + memory into a single versioned blob
    pub fn encode(metadata_bytes: Bytes, snapshot_bytes: Bytes, memory_bytes: Bytes) -> Bytes {
        let metadata_len = metadata_bytes.len() as u64;
        let snapshot_len = snapshot_bytes.len() as u64;
        let memory_len = memory_bytes.len() as u64;
        let total_len =
            TELEPORT_SNAPSHOT_HEADER_BYTES as u64 + metadata_len + snapshot_len + memory_len;

        assert!(metadata_len <= u64::MAX);
        assert!(snapshot_len <= u64::MAX);
        assert!(memory_len <= u64::MAX);
        assert!(total_len <= u64::MAX);

        let mut data = Vec::with_capacity(total_len as usize);
        data.extend_from_slice(&TELEPORT_SNAPSHOT_MAGIC_BYTES);
        data.extend_from_slice(&TELEPORT_SNAPSHOT_FORMAT_VERSION.to_le_bytes());
        data.extend_from_slice(&metadata_len.to_le_bytes());
        data.extend_from_slice(&snapshot_len.to_le_bytes());
        data.extend_from_slice(&memory_len.to_le_bytes());
        data.extend_from_slice(&metadata_bytes);
        data.extend_from_slice(&snapshot_bytes);
        data.extend_from_slice(&memory_bytes);

        Bytes::from(data)
    }

    /// Decode a versioned blob into snapshot + memory parts
    pub fn decode(blob: &Bytes) -> Result<Self, TeleportSnapshotError> {
        let blob_len = blob.len() as u64;
        if blob_len < TELEPORT_SNAPSHOT_HEADER_BYTES as u64 {
            return Err(TeleportSnapshotError::HeaderTooSmall {
                size_bytes: blob_len,
            });
        }

        let magic = [blob[0], blob[1], blob[2], blob[3]];
        if magic != TELEPORT_SNAPSHOT_MAGIC_BYTES {
            return Err(TeleportSnapshotError::InvalidMagic {
                expected: TELEPORT_SNAPSHOT_MAGIC_BYTES,
                actual: magic,
            });
        }

        let version = u32::from_le_bytes([blob[4], blob[5], blob[6], blob[7]]);
        if version != TELEPORT_SNAPSHOT_FORMAT_VERSION {
            return Err(TeleportSnapshotError::UnsupportedVersion {
                expected: TELEPORT_SNAPSHOT_FORMAT_VERSION,
                actual: version,
            });
        }

        let metadata_len = u64::from_le_bytes([
            blob[8], blob[9], blob[10], blob[11], blob[12], blob[13], blob[14], blob[15],
        ]);
        let snapshot_len = u64::from_le_bytes([
            blob[16], blob[17], blob[18], blob[19], blob[20], blob[21], blob[22], blob[23],
        ]);
        let memory_len = u64::from_le_bytes([
            blob[24], blob[25], blob[26], blob[27], blob[28], blob[29], blob[30], blob[31],
        ]);
        let expected_len =
            TELEPORT_SNAPSHOT_HEADER_BYTES as u64 + metadata_len + snapshot_len + memory_len;
        if blob_len != expected_len {
            return Err(TeleportSnapshotError::LengthMismatch {
                expected: expected_len,
                actual: blob_len,
            });
        }

        let metadata_start = TELEPORT_SNAPSHOT_HEADER_BYTES;
        let metadata_end = metadata_start + metadata_len as usize;
        let snapshot_end = metadata_end + snapshot_len as usize;
        let memory_end = snapshot_end + memory_len as usize;

        let metadata_bytes = blob.slice(metadata_start..metadata_end);
        let snapshot_bytes = blob.slice(metadata_end..snapshot_end);
        let memory_bytes = blob.slice(snapshot_end..memory_end);

        Ok(Self {
            metadata_bytes,
            snapshot_bytes,
            memory_bytes,
        })
    }
}

/// A teleport package containing agent state for migration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TeleportPackage {
    /// Unique package ID
    pub id: String,
    /// Agent ID this package belongs to
    pub agent_id: String,
    /// Source architecture
    pub source_arch: Architecture,
    /// Snapshot kind
    pub kind: SnapshotKind,
    /// Base image version (for validation)
    pub base_image_version: String,
    /// Creation timestamp (milliseconds since epoch)
    pub created_at_ms: u64,
    /// Package size in bytes
    pub size_bytes: u64,

    // State components
    /// VM snapshot blob (for Suspend/Teleport)
    pub vm_snapshot: Option<Bytes>,
    /// Workspace filesystem reference
    pub workspace_ref: Option<String>,
    /// Agent state (memory blocks, conversation, etc.)
    pub agent_state: Option<Bytes>,
    /// Environment variables
    pub env_vars: Vec<(String, String)>,
}

impl TeleportPackage {
    /// Create a new teleport package
    pub fn new(
        id: impl Into<String>,
        agent_id: impl Into<String>,
        source_arch: Architecture,
        kind: SnapshotKind,
    ) -> Self {
        let id = id.into();
        assert!(
            id.len() <= TELEPORT_ID_LENGTH_BYTES_MAX,
            "teleport ID too long"
        );

        Self {
            id,
            agent_id: agent_id.into(),
            source_arch,
            kind,
            base_image_version: "1.0.0".to_string(),
            created_at_ms: 0,
            size_bytes: 0,
            vm_snapshot: None,
            workspace_ref: None,
            agent_state: None,
            env_vars: Vec::new(),
        }
    }

    /// Set VM snapshot blob
    pub fn with_vm_snapshot(mut self, snapshot: impl Into<Bytes>) -> Self {
        let snapshot = snapshot.into();
        self.size_bytes += snapshot.len() as u64;
        self.vm_snapshot = Some(snapshot);
        self
    }

    /// Set workspace reference
    pub fn with_workspace_ref(mut self, reference: impl Into<String>) -> Self {
        self.workspace_ref = Some(reference.into());
        self
    }

    /// Set agent state
    pub fn with_agent_state(mut self, state: impl Into<Bytes>) -> Self {
        let state = state.into();
        self.size_bytes += state.len() as u64;
        self.agent_state = Some(state);
        self
    }

    /// Set environment variables
    pub fn with_env_vars(mut self, vars: Vec<(String, String)>) -> Self {
        self.env_vars = vars;
        self
    }

    /// Set creation timestamp
    pub fn with_created_at(mut self, ms: u64) -> Self {
        self.created_at_ms = ms;
        self
    }

    /// Set base image version
    pub fn with_base_image_version(mut self, version: impl Into<String>) -> Self {
        self.base_image_version = version.into();
        self
    }

    /// Check if this is a full VM teleport
    pub fn is_full_teleport(&self) -> bool {
        self.kind == SnapshotKind::Teleport && self.vm_snapshot.is_some()
    }

    /// Check if this is a checkpoint-only package
    pub fn is_checkpoint(&self) -> bool {
        self.kind == SnapshotKind::Checkpoint
    }

    /// Validate that this package can be restored on the given architecture
    pub fn validate_for_restore(&self, target_arch: Architecture) -> Result<(), String> {
        match self.kind {
            SnapshotKind::Checkpoint => Ok(()),
            SnapshotKind::Suspend | SnapshotKind::Teleport => {
                if self.source_arch != target_arch {
                    Err(format!(
                        "Architecture mismatch: package is {} but target is {}",
                        self.source_arch, target_arch
                    ))
                } else {
                    Ok(())
                }
            }
        }
    }
}

/// Teleport storage error types
#[derive(Debug, Clone)]
pub enum TeleportStorageError {
    /// Package not found
    NotFound { id: String },
    /// Upload failed
    UploadFailed { reason: String },
    /// Download failed
    DownloadFailed { reason: String },
    /// Timeout
    Timeout { timeout_ms: u64 },
    /// Architecture mismatch
    ArchMismatch {
        expected: Architecture,
        actual: Architecture,
    },
    /// Base image version mismatch
    ImageMismatch { expected: String, actual: String },
    /// Package too large
    TooLarge { size_bytes: u64, max_bytes: u64 },
    /// Internal error
    Internal { message: String },
}

impl std::fmt::Display for TeleportStorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TeleportStorageError::NotFound { id } => {
                write!(f, "Teleport package not found: {}", id)
            }
            TeleportStorageError::UploadFailed { reason } => write!(f, "Upload failed: {}", reason),
            TeleportStorageError::DownloadFailed { reason } => {
                write!(f, "Download failed: {}", reason)
            }
            TeleportStorageError::Timeout { timeout_ms } => {
                write!(f, "Teleport operation timed out after {}ms", timeout_ms)
            }
            TeleportStorageError::ArchMismatch { expected, actual } => {
                write!(
                    f,
                    "Architecture mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            TeleportStorageError::ImageMismatch { expected, actual } => {
                write!(
                    f,
                    "Base image version mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            TeleportStorageError::TooLarge {
                size_bytes,
                max_bytes,
            } => {
                write!(
                    f,
                    "Package too large: {} bytes exceeds max {} bytes",
                    size_bytes, max_bytes
                )
            }
            TeleportStorageError::Internal { message } => write!(f, "Internal error: {}", message),
        }
    }
}

impl std::error::Error for TeleportStorageError {}

impl From<TeleportStorageError> for crate::error::Error {
    fn from(e: TeleportStorageError) -> Self {
        crate::error::Error::Internal {
            message: e.to_string(),
        }
    }
}

/// Result type for teleport storage operations
pub type TeleportStorageResult<T> = Result<T, TeleportStorageError>;

/// Trait for teleport package storage backends
///
/// TigerStyle: Abstract interface enables DST testing with SimTeleportStorage
/// and production use with S3TeleportStorage.
#[async_trait]
pub trait TeleportStorage: Send + Sync {
    /// Upload a teleport package to storage
    async fn upload(&self, package: TeleportPackage) -> TeleportStorageResult<String>;

    /// Download a teleport package from storage
    async fn download(&self, id: &str) -> TeleportStorageResult<TeleportPackage>;

    /// Download and validate a teleport package for restoration
    async fn download_for_restore(
        &self,
        id: &str,
        target_arch: Architecture,
    ) -> TeleportStorageResult<TeleportPackage>;

    /// Delete a teleport package from storage
    async fn delete(&self, id: &str) -> TeleportStorageResult<()>;

    /// List all teleport package IDs
    async fn list(&self) -> Vec<String>;

    /// Upload a workspace blob to storage
    async fn upload_blob(&self, key: &str, data: Bytes) -> TeleportStorageResult<String>;

    /// Download a workspace blob from storage
    async fn download_blob(&self, key: &str) -> TeleportStorageResult<Bytes>;

    /// Get the host architecture this storage is configured for
    fn host_arch(&self) -> Architecture;
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::Bytes;

    #[test]
    fn test_vm_snapshot_blob_roundtrip() {
        let metadata_bytes = Bytes::from("metadata");
        let snapshot_bytes = Bytes::from("snapshot");
        let memory_bytes = Bytes::from(vec![1u8, 2, 3]);
        let blob = VmSnapshotBlob::encode(
            metadata_bytes.clone(),
            snapshot_bytes.clone(),
            memory_bytes.clone(),
        );

        let decoded = VmSnapshotBlob::decode(&blob).expect("decode should succeed");
        assert_eq!(decoded.metadata_bytes, metadata_bytes);
        assert_eq!(decoded.snapshot_bytes, snapshot_bytes);
        assert_eq!(decoded.memory_bytes, memory_bytes);
    }

    #[test]
    fn test_vm_snapshot_blob_invalid_magic() {
        let mut blob = VmSnapshotBlob::encode(Bytes::new(), Bytes::from("snapshot"), Bytes::new());
        let mut data = blob.to_vec();
        data[0] = b'X';
        blob = Bytes::from(data);

        let err = VmSnapshotBlob::decode(&blob).unwrap_err();
        assert!(matches!(err, TeleportSnapshotError::InvalidMagic { .. }));
    }
}

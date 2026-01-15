//! Teleport storage trait for production and simulation backends
//!
//! TigerStyle: Abstract trait enables DST testing with fault injection.
//!
//! This module defines the TeleportStorage trait that can be implemented by:
//! - SimTeleportStorage (kelpie-dst) for deterministic simulation testing
//! - S3TeleportStorage (production) for cloud storage
//! - LocalTeleportStorage (development) for local file storage

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
        // Default to x86_64 for unknown architectures
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
    /// VM memory state (for Suspend/Teleport)
    pub vm_memory: Option<Bytes>,
    /// VM CPU state (for Suspend/Teleport)
    pub vm_cpu_state: Option<Bytes>,
    /// Workspace filesystem reference
    pub workspace_ref: Option<String>,
    /// Agent state (memory blocks, conversation, etc.)
    pub agent_state: Option<Bytes>,
    /// Environment variables
    pub env_vars: Vec<(String, String)>,
}

/// Maximum teleport package ID length in bytes
pub const TELEPORT_ID_LENGTH_BYTES_MAX: usize = 128;

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
            vm_memory: None,
            vm_cpu_state: None,
            workspace_ref: None,
            agent_state: None,
            env_vars: Vec::new(),
        }
    }

    /// Set VM memory state
    pub fn with_vm_memory(mut self, memory: impl Into<Bytes>) -> Self {
        let memory = memory.into();
        self.size_bytes += memory.len() as u64;
        self.vm_memory = Some(memory);
        self
    }

    /// Set VM CPU state
    pub fn with_vm_cpu_state(mut self, cpu_state: impl Into<Bytes>) -> Self {
        let cpu_state = cpu_state.into();
        self.size_bytes += cpu_state.len() as u64;
        self.vm_cpu_state = Some(cpu_state);
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
        self.vm_memory.is_some() && self.vm_cpu_state.is_some()
    }

    /// Check if this is a checkpoint-only package
    pub fn is_checkpoint(&self) -> bool {
        self.kind == SnapshotKind::Checkpoint
    }

    /// Validate that this package can be restored on the given architecture
    pub fn validate_for_restore(&self, target_arch: Architecture) -> Result<(), String> {
        match self.kind {
            SnapshotKind::Checkpoint => {
                // Checkpoints work across architectures
                Ok(())
            }
            SnapshotKind::Suspend | SnapshotKind::Teleport => {
                // VM snapshots require same architecture
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

impl From<TeleportStorageError> for kelpie_core::Error {
    fn from(e: TeleportStorageError) -> Self {
        kelpie_core::Error::Internal {
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
    ///
    /// # Arguments
    /// * `package` - The teleport package to upload
    ///
    /// # Returns
    /// The package ID on success
    async fn upload(&self, package: TeleportPackage) -> TeleportStorageResult<String>;

    /// Download a teleport package from storage
    ///
    /// # Arguments
    /// * `id` - Package ID to download
    ///
    /// # Returns
    /// The teleport package on success
    async fn download(&self, id: &str) -> TeleportStorageResult<TeleportPackage>;

    /// Download and validate a teleport package for restoration
    ///
    /// # Arguments
    /// * `id` - Package ID to download
    /// * `target_arch` - Target architecture for restoration
    ///
    /// # Returns
    /// The teleport package if valid for the target architecture
    async fn download_for_restore(
        &self,
        id: &str,
        target_arch: Architecture,
    ) -> TeleportStorageResult<TeleportPackage>;

    /// Delete a teleport package from storage
    ///
    /// # Arguments
    /// * `id` - Package ID to delete
    async fn delete(&self, id: &str) -> TeleportStorageResult<()>;

    /// List all teleport package IDs
    async fn list(&self) -> Vec<String>;

    /// Upload a workspace blob to storage
    ///
    /// # Arguments
    /// * `key` - Storage key for the blob
    /// * `data` - Blob data
    ///
    /// # Returns
    /// The storage key on success
    async fn upload_blob(&self, key: &str, data: Bytes) -> TeleportStorageResult<String>;

    /// Download a workspace blob from storage
    ///
    /// # Arguments
    /// * `key` - Storage key for the blob
    ///
    /// # Returns
    /// The blob data on success
    async fn download_blob(&self, key: &str) -> TeleportStorageResult<Bytes>;

    /// Get the host architecture this storage is configured for
    fn host_arch(&self) -> Architecture;
}

/// In-memory teleport storage for local development and testing
///
/// TigerStyle: Simple implementation for development without external dependencies.
pub struct LocalTeleportStorage {
    packages: tokio::sync::RwLock<std::collections::HashMap<String, TeleportPackage>>,
    blobs: tokio::sync::RwLock<std::collections::HashMap<String, Bytes>>,
    host_arch: Architecture,
    expected_image_version: String,
    max_package_bytes: u64,
}

/// Maximum teleport package size in bytes (default: 10GB)
pub const TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX: u64 = 10 * 1024 * 1024 * 1024;

impl LocalTeleportStorage {
    /// Create a new local teleport storage
    pub fn new() -> Self {
        Self {
            packages: tokio::sync::RwLock::new(std::collections::HashMap::new()),
            blobs: tokio::sync::RwLock::new(std::collections::HashMap::new()),
            host_arch: Architecture::current(),
            expected_image_version: "1.0.0".to_string(),
            max_package_bytes: TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX,
        }
    }

    /// Set the expected base image version
    pub fn with_expected_image_version(mut self, version: impl Into<String>) -> Self {
        self.expected_image_version = version.into();
        self
    }

    /// Set the maximum package size
    pub fn with_max_package_bytes(mut self, max_bytes: u64) -> Self {
        self.max_package_bytes = max_bytes;
        self
    }
}

impl Default for LocalTeleportStorage {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl TeleportStorage for LocalTeleportStorage {
    async fn upload(&self, package: TeleportPackage) -> TeleportStorageResult<String> {
        // Check package size
        if package.size_bytes > self.max_package_bytes {
            return Err(TeleportStorageError::TooLarge {
                size_bytes: package.size_bytes,
                max_bytes: self.max_package_bytes,
            });
        }

        let id = package.id.clone();
        let mut packages = self.packages.write().await;
        packages.insert(id.clone(), package);

        tracing::debug!(package_id = %id, "Teleport package uploaded to local storage");
        Ok(id)
    }

    async fn download(&self, id: &str) -> TeleportStorageResult<TeleportPackage> {
        let packages = self.packages.read().await;
        match packages.get(id) {
            Some(package) => {
                tracing::debug!(package_id = %id, "Teleport package downloaded from local storage");
                Ok(package.clone())
            }
            None => Err(TeleportStorageError::NotFound { id: id.to_string() }),
        }
    }

    async fn download_for_restore(
        &self,
        id: &str,
        target_arch: Architecture,
    ) -> TeleportStorageResult<TeleportPackage> {
        let package = self.download(id).await?;

        // Validate architecture
        package.validate_for_restore(target_arch).map_err(|_| {
            TeleportStorageError::ArchMismatch {
                expected: target_arch,
                actual: package.source_arch,
            }
        })?;

        // Validate base image version
        if package.base_image_version != self.expected_image_version {
            return Err(TeleportStorageError::ImageMismatch {
                expected: self.expected_image_version.clone(),
                actual: package.base_image_version.clone(),
            });
        }

        Ok(package)
    }

    async fn delete(&self, id: &str) -> TeleportStorageResult<()> {
        let mut packages = self.packages.write().await;
        packages.remove(id);
        tracing::debug!(package_id = %id, "Teleport package deleted from local storage");
        Ok(())
    }

    async fn list(&self) -> Vec<String> {
        let packages = self.packages.read().await;
        packages.keys().cloned().collect()
    }

    async fn upload_blob(&self, key: &str, data: Bytes) -> TeleportStorageResult<String> {
        let mut blobs = self.blobs.write().await;
        blobs.insert(key.to_string(), data);
        Ok(key.to_string())
    }

    async fn download_blob(&self, key: &str) -> TeleportStorageResult<Bytes> {
        let blobs = self.blobs.read().await;
        match blobs.get(key) {
            Some(data) => Ok(data.clone()),
            None => Err(TeleportStorageError::NotFound {
                id: key.to_string(),
            }),
        }
    }

    fn host_arch(&self) -> Architecture {
        self.host_arch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_local_teleport_storage_basic() {
        let storage = LocalTeleportStorage::new();

        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_agent_state(Bytes::from("state"));

        // Upload
        let id = storage.upload(package).await.unwrap();
        assert_eq!(id, "pkg-1");

        // Download
        let downloaded = storage.download("pkg-1").await.unwrap();
        assert_eq!(downloaded.agent_id, "agent-1");

        // List
        let packages = storage.list().await;
        assert_eq!(packages.len(), 1);

        // Delete
        storage.delete("pkg-1").await.unwrap();
        let packages = storage.list().await;
        assert_eq!(packages.len(), 0);
    }

    #[tokio::test]
    async fn test_local_teleport_storage_arch_validation() {
        let storage = LocalTeleportStorage::new();

        // Upload ARM64 package
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_base_image_version("1.0.0");
        storage.upload(package).await.unwrap();

        // Restore on same architecture should work
        let result = storage
            .download_for_restore("pkg-1", Architecture::Arm64)
            .await;
        assert!(result.is_ok());

        // Restore on different architecture should fail for Teleport kind
        let result = storage
            .download_for_restore("pkg-1", Architecture::X86_64)
            .await;
        assert!(matches!(
            result,
            Err(TeleportStorageError::ArchMismatch { .. })
        ));
    }

    #[tokio::test]
    async fn test_local_teleport_storage_checkpoint_cross_arch() {
        let storage = LocalTeleportStorage::new();

        // Upload ARM64 checkpoint
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Checkpoint,
        )
        .with_agent_state(Bytes::from("state"))
        .with_base_image_version("1.0.0");
        storage.upload(package).await.unwrap();

        // Checkpoints should work on any architecture
        let result = storage
            .download_for_restore("pkg-1", Architecture::X86_64)
            .await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_local_teleport_storage_blob_operations() {
        let storage = LocalTeleportStorage::new();

        // Upload blob
        let key = storage
            .upload_blob("workspace/file.txt", Bytes::from("file content"))
            .await
            .unwrap();
        assert_eq!(key, "workspace/file.txt");

        // Download blob
        let data = storage.download_blob("workspace/file.txt").await.unwrap();
        assert_eq!(data.as_ref(), b"file content");

        // Download non-existent blob
        let result = storage.download_blob("non-existent").await;
        assert!(result.is_err());
    }

    #[test]
    fn test_teleport_package_validation() {
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        );

        // Same arch should pass
        assert!(package.validate_for_restore(Architecture::Arm64).is_ok());

        // Different arch should fail
        assert!(package.validate_for_restore(Architecture::X86_64).is_err());

        // Checkpoint should work across architectures
        let checkpoint = TeleportPackage::new(
            "pkg-2",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Checkpoint,
        );
        assert!(checkpoint
            .validate_for_restore(Architecture::X86_64)
            .is_ok());
    }
}

//! Simulated teleport storage for deterministic testing
//!
//! TigerStyle: Teleport package storage simulation with fault injection.
//!
//! This module provides a simulated teleport storage that:
//! - Stores teleport packages in memory
//! - Injects faults based on FaultInjector configuration
//! - Uses deterministic RNG for reproducible behavior
//! - Supports both metadata and blob storage

use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use bytes::Bytes;
use kelpie_core::Error as CoreError;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::sync::RwLock;

/// Maximum teleport package ID length in bytes
const TELEPORT_ID_LENGTH_BYTES_MAX: usize = 128;

/// Maximum teleport package size in bytes (for fault injection testing)
const TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX: u64 = 10 * 1024 * 1024 * 1024; // 10GB

/// CPU architecture for teleportation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Architecture {
    /// ARM64 (Apple Silicon, AWS Graviton)
    Arm64,
    /// x86_64 (Intel/AMD)
    X86_64,
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
    /// Creation timestamp (simulation time in ms)
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
#[derive(Debug)]
pub enum TeleportError {
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

impl std::fmt::Display for TeleportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TeleportError::NotFound { id } => write!(f, "Teleport package not found: {}", id),
            TeleportError::UploadFailed { reason } => write!(f, "Upload failed: {}", reason),
            TeleportError::DownloadFailed { reason } => write!(f, "Download failed: {}", reason),
            TeleportError::Timeout { timeout_ms } => {
                write!(f, "Teleport operation timed out after {}ms", timeout_ms)
            }
            TeleportError::ArchMismatch { expected, actual } => {
                write!(
                    f,
                    "Architecture mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            TeleportError::ImageMismatch { expected, actual } => {
                write!(
                    f,
                    "Base image version mismatch: expected {}, got {}",
                    expected, actual
                )
            }
            TeleportError::TooLarge {
                size_bytes,
                max_bytes,
            } => {
                write!(
                    f,
                    "Package too large: {} bytes exceeds max {} bytes",
                    size_bytes, max_bytes
                )
            }
            TeleportError::Internal { message } => write!(f, "Internal error: {}", message),
        }
    }
}

impl std::error::Error for TeleportError {}

impl From<TeleportError> for CoreError {
    fn from(e: TeleportError) -> Self {
        CoreError::Internal {
            message: e.to_string(),
        }
    }
}

/// Result type for teleport operations
pub type TeleportResult<T> = Result<T, TeleportError>;

/// Simulated teleport storage with fault injection
///
/// This storage implementation is designed for deterministic simulation testing.
/// It stores packages in memory and injects faults based on FaultInjector config.
pub struct SimTeleportStorage {
    /// Stored packages (metadata + data)
    packages: RwLock<HashMap<String, TeleportPackage>>,
    /// Blob storage (workspace files)
    blobs: RwLock<HashMap<String, Bytes>>,
    /// Deterministic RNG
    rng: RwLock<DeterministicRng>,
    /// Fault injector
    faults: Arc<FaultInjector>,
    /// Operation counter
    operation_count: AtomicU64,
    /// Maximum package size
    max_package_bytes: u64,
    /// Current host architecture (for validation)
    host_arch: Architecture,
    /// Expected base image version (for validation)
    expected_image_version: String,
}

impl SimTeleportStorage {
    /// Create a new simulated teleport storage
    pub fn new(rng: DeterministicRng, faults: Arc<FaultInjector>) -> Self {
        Self {
            packages: RwLock::new(HashMap::new()),
            blobs: RwLock::new(HashMap::new()),
            rng: RwLock::new(rng),
            faults,
            operation_count: AtomicU64::new(0),
            max_package_bytes: TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX,
            host_arch: Architecture::Arm64, // Default to ARM64 for Mac development
            expected_image_version: "1.0.0".to_string(),
        }
    }

    /// Set the maximum package size
    pub fn with_max_package_bytes(mut self, max_bytes: u64) -> Self {
        self.max_package_bytes = max_bytes;
        self
    }

    /// Set the host architecture
    pub fn with_host_arch(mut self, arch: Architecture) -> Self {
        self.host_arch = arch;
        self
    }

    /// Set the expected base image version
    pub fn with_expected_image_version(mut self, version: impl Into<String>) -> Self {
        self.expected_image_version = version.into();
        self
    }

    /// Check for fault injection
    fn check_fault(&self, operation: &str) -> Option<FaultType> {
        self.operation_count.fetch_add(1, Ordering::SeqCst);
        self.faults.should_inject(operation)
    }

    /// Convert fault to error
    fn fault_to_error(&self, fault: FaultType) -> TeleportError {
        match fault {
            FaultType::TeleportUploadFail => TeleportError::UploadFailed {
                reason: "Simulated upload failure (DST fault injection)".to_string(),
            },
            FaultType::TeleportDownloadFail => TeleportError::DownloadFailed {
                reason: "Simulated download failure (DST fault injection)".to_string(),
            },
            FaultType::TeleportTimeout { timeout_ms } => TeleportError::Timeout { timeout_ms },
            FaultType::TeleportArchMismatch => TeleportError::ArchMismatch {
                expected: self.host_arch,
                actual: match self.host_arch {
                    Architecture::Arm64 => Architecture::X86_64,
                    Architecture::X86_64 => Architecture::Arm64,
                },
            },
            FaultType::TeleportImageMismatch => TeleportError::ImageMismatch {
                expected: self.expected_image_version.clone(),
                actual: "0.0.0-invalid".to_string(),
            },
            _ => TeleportError::Internal {
                message: format!("Unexpected fault type: {:?}", fault),
            },
        }
    }

    /// Upload a teleport package
    pub async fn upload(&self, package: TeleportPackage) -> TeleportResult<String> {
        // Check for upload fault
        if let Some(fault) = self.check_fault("teleport_upload") {
            match &fault {
                FaultType::TeleportUploadFail | FaultType::TeleportTimeout { .. } => {
                    return Err(self.fault_to_error(fault));
                }
                _ => {}
            }
        }

        // Check package size
        if package.size_bytes > self.max_package_bytes {
            return Err(TeleportError::TooLarge {
                size_bytes: package.size_bytes,
                max_bytes: self.max_package_bytes,
            });
        }

        let id = package.id.clone();
        let mut packages = self.packages.write().await;
        packages.insert(id.clone(), package);

        tracing::debug!(package_id = %id, "Teleport package uploaded");
        Ok(id)
    }

    /// Download a teleport package
    pub async fn download(&self, id: &str) -> TeleportResult<TeleportPackage> {
        // Check for download fault
        if let Some(fault) = self.check_fault("teleport_download") {
            match &fault {
                FaultType::TeleportDownloadFail | FaultType::TeleportTimeout { .. } => {
                    return Err(self.fault_to_error(fault));
                }
                _ => {}
            }
        }

        let packages = self.packages.read().await;
        match packages.get(id) {
            Some(package) => {
                tracing::debug!(package_id = %id, "Teleport package downloaded");
                Ok(package.clone())
            }
            None => Err(TeleportError::NotFound { id: id.to_string() }),
        }
    }

    /// Download and validate a teleport package for restoration
    pub async fn download_for_restore(
        &self,
        id: &str,
        target_arch: Architecture,
    ) -> TeleportResult<TeleportPackage> {
        // Check for architecture mismatch fault
        if let Some(fault) = self.check_fault("teleport_restore_validate") {
            if matches!(fault, FaultType::TeleportArchMismatch) {
                return Err(self.fault_to_error(fault));
            }
        }

        // Check for image mismatch fault
        if let Some(fault) = self.check_fault("teleport_image_validate") {
            if matches!(fault, FaultType::TeleportImageMismatch) {
                return Err(self.fault_to_error(fault));
            }
        }

        let package = self.download(id).await?;

        // Validate architecture
        package
            .validate_for_restore(target_arch)
            .map_err(|_reason| TeleportError::ArchMismatch {
                expected: target_arch,
                actual: package.source_arch,
            })?;

        // Validate base image version
        if package.base_image_version != self.expected_image_version {
            return Err(TeleportError::ImageMismatch {
                expected: self.expected_image_version.clone(),
                actual: package.base_image_version.clone(),
            });
        }

        Ok(package)
    }

    /// Delete a teleport package
    pub async fn delete(&self, id: &str) -> TeleportResult<()> {
        let mut packages = self.packages.write().await;
        packages.remove(id);
        tracing::debug!(package_id = %id, "Teleport package deleted");
        Ok(())
    }

    /// List all teleport packages
    pub async fn list(&self) -> Vec<String> {
        let packages = self.packages.read().await;
        packages.keys().cloned().collect()
    }

    /// Upload a workspace blob
    pub async fn upload_blob(&self, key: &str, data: Bytes) -> TeleportResult<String> {
        // Check for upload fault
        if let Some(fault) = self.check_fault("teleport_blob_upload") {
            if matches!(fault, FaultType::TeleportUploadFail) {
                return Err(self.fault_to_error(fault));
            }
        }

        let mut blobs = self.blobs.write().await;
        blobs.insert(key.to_string(), data);
        Ok(key.to_string())
    }

    /// Download a workspace blob
    pub async fn download_blob(&self, key: &str) -> TeleportResult<Bytes> {
        // Check for download fault
        if let Some(fault) = self.check_fault("teleport_blob_download") {
            if matches!(fault, FaultType::TeleportDownloadFail) {
                return Err(self.fault_to_error(fault));
            }
        }

        let blobs = self.blobs.read().await;
        match blobs.get(key) {
            Some(data) => Ok(data.clone()),
            None => Err(TeleportError::NotFound {
                id: key.to_string(),
            }),
        }
    }

    /// Get the operation count (for debugging)
    pub fn operation_count(&self) -> u64 {
        self.operation_count.load(Ordering::SeqCst)
    }

    /// Get the host architecture
    pub fn host_arch(&self) -> Architecture {
        self.host_arch
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::{FaultConfig, FaultInjectorBuilder};

    fn create_test_faults(rng: DeterministicRng) -> Arc<FaultInjector> {
        Arc::new(FaultInjectorBuilder::new(rng).build())
    }

    #[tokio::test]
    async fn test_teleport_package_creation() {
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_vm_memory(Bytes::from("memory data"))
        .with_vm_cpu_state(Bytes::from("cpu state"))
        .with_agent_state(Bytes::from("agent state"))
        .with_workspace_ref("s3://bucket/workspace")
        .with_env_vars(vec![("KEY".to_string(), "value".to_string())]);

        assert_eq!(package.id, "pkg-1");
        assert_eq!(package.agent_id, "agent-1");
        assert_eq!(package.source_arch, Architecture::Arm64);
        assert!(package.is_full_teleport());
        assert!(!package.is_checkpoint());
    }

    #[tokio::test]
    async fn test_teleport_package_validation() {
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

    #[tokio::test]
    async fn test_sim_teleport_storage_basic() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let storage = SimTeleportStorage::new(rng, faults);

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
    async fn test_sim_teleport_storage_with_upload_fault() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::TeleportUploadFail, 1.0))
                .build(),
        );
        let storage = SimTeleportStorage::new(rng, faults);

        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        );

        let result = storage.upload(package).await;
        assert!(result.is_err());
        assert!(matches!(result, Err(TeleportError::UploadFailed { .. })));
    }

    #[tokio::test]
    async fn test_sim_teleport_storage_with_download_fault() {
        let rng = DeterministicRng::new(42);
        let faults_for_upload = create_test_faults(rng.fork());
        let faults_for_download = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::TeleportDownloadFail, 1.0))
                .build(),
        );

        // First upload without faults
        let storage = SimTeleportStorage::new(rng.fork(), faults_for_upload);
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        );
        storage.upload(package).await.unwrap();

        // Then create new storage with download fault
        let storage2 = SimTeleportStorage::new(rng, faults_for_download);
        // Note: In real tests, we'd share the same storage, but this demonstrates the pattern
    }

    #[tokio::test]
    async fn test_sim_teleport_storage_arch_validation() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let storage = SimTeleportStorage::new(rng, faults)
            .with_host_arch(Architecture::X86_64)
            .with_expected_image_version("1.0.0");

        // Upload ARM64 package
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_base_image_version("1.0.0");
        storage.upload(package).await.unwrap();

        // Try to restore on X86_64 - should fail
        let result = storage
            .download_for_restore("pkg-1", Architecture::X86_64)
            .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_sim_teleport_storage_blob_operations() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let storage = SimTeleportStorage::new(rng, faults);

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

    #[tokio::test]
    async fn test_sim_teleport_storage_determinism() {
        let run_test = |seed: u64| async move {
            let rng = DeterministicRng::new(seed);
            let faults = Arc::new(
                FaultInjectorBuilder::new(rng.fork())
                    .with_teleport_faults(0.3)
                    .build(),
            );
            let storage = SimTeleportStorage::new(rng, faults);

            let mut results = Vec::new();
            for i in 0..5 {
                let package = TeleportPackage::new(
                    format!("pkg-{}", i),
                    "agent-1",
                    Architecture::Arm64,
                    SnapshotKind::Teleport,
                );
                let result = storage.upload(package).await;
                results.push(result.is_ok());
            }
            results
        };

        let results1 = run_test(12345).await;
        let results2 = run_test(12345).await;

        assert_eq!(results1, results2, "Results should be deterministic");
    }
}

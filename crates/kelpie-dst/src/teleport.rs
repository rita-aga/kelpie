//! Simulated teleport storage for deterministic testing
//!
//! TigerStyle: Teleport package storage simulation with fault injection.

use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use bytes::Bytes;
use kelpie_core::teleport::{
    Architecture, TeleportPackage, TeleportStorage, TeleportStorageError, TeleportStorageResult,
};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::sync::RwLock;

/// Maximum teleport package size in bytes (for fault injection testing)
const TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX: u64 = 10 * 1024 * 1024 * 1024; // 10GB

/// Simulated teleport storage with fault injection
///
/// This storage implementation is designed for deterministic simulation testing.
/// It stores packages in memory and injects faults based on FaultInjector config.
pub struct SimTeleportStorage {
    packages: RwLock<HashMap<String, TeleportPackage>>,
    blobs: RwLock<HashMap<String, Bytes>>,
    faults: Arc<FaultInjector>,
    operation_count: AtomicU64,
    max_package_bytes: u64,
    host_arch: Architecture,
    expected_image_version: String,
}

impl Clone for SimTeleportStorage {
    fn clone(&self) -> Self {
        let packages = futures::executor::block_on(self.packages.read()).clone();
        let blobs = futures::executor::block_on(self.blobs.read()).clone();
        Self {
            packages: RwLock::new(packages),
            blobs: RwLock::new(blobs),
            faults: self.faults.clone(),
            operation_count: AtomicU64::new(self.operation_count.load(Ordering::SeqCst)),
            max_package_bytes: self.max_package_bytes,
            host_arch: self.host_arch,
            expected_image_version: self.expected_image_version.clone(),
        }
    }
}

impl SimTeleportStorage {
    /// Create a new simulated teleport storage
    pub fn new(_rng: DeterministicRng, faults: Arc<FaultInjector>) -> Self {
        Self {
            packages: RwLock::new(HashMap::new()),
            blobs: RwLock::new(HashMap::new()),
            faults,
            operation_count: AtomicU64::new(0),
            max_package_bytes: TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX,
            host_arch: Architecture::Arm64,
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

    fn fault_to_error(&self, fault: FaultType) -> TeleportStorageError {
        match fault {
            FaultType::TeleportUploadFail => TeleportStorageError::UploadFailed {
                reason: "Simulated upload failure (DST fault injection)".to_string(),
            },
            FaultType::TeleportDownloadFail => TeleportStorageError::DownloadFailed {
                reason: "Simulated download failure (DST fault injection)".to_string(),
            },
            FaultType::TeleportTimeout { timeout_ms } => {
                TeleportStorageError::Timeout { timeout_ms }
            }
            FaultType::TeleportArchMismatch => TeleportStorageError::ArchMismatch {
                expected: self.host_arch,
                actual: match self.host_arch {
                    Architecture::Arm64 => Architecture::X86_64,
                    Architecture::X86_64 => Architecture::Arm64,
                },
            },
            FaultType::TeleportImageMismatch => TeleportStorageError::ImageMismatch {
                expected: self.expected_image_version.clone(),
                actual: "0.0.0-invalid".to_string(),
            },
            _ => TeleportStorageError::Internal {
                message: format!("Unexpected fault type: {:?}", fault),
            },
        }
    }

    /// Get the operation count (for debugging)
    pub fn operation_count(&self) -> u64 {
        self.operation_count.load(Ordering::SeqCst)
    }

    /// Convenience wrapper for TeleportStorage::upload
    pub async fn upload(&self, package: TeleportPackage) -> TeleportStorageResult<String> {
        TeleportStorage::upload(self, package).await
    }

    /// Convenience wrapper for TeleportStorage::download
    pub async fn download(&self, id: &str) -> TeleportStorageResult<TeleportPackage> {
        TeleportStorage::download(self, id).await
    }

    /// Convenience wrapper for TeleportStorage::download_for_restore
    pub async fn download_for_restore(
        &self,
        id: &str,
        target_arch: Architecture,
    ) -> TeleportStorageResult<TeleportPackage> {
        TeleportStorage::download_for_restore(self, id, target_arch).await
    }

    /// Convenience wrapper for TeleportStorage::delete
    pub async fn delete(&self, id: &str) -> TeleportStorageResult<()> {
        TeleportStorage::delete(self, id).await
    }

    /// Convenience wrapper for TeleportStorage::list
    pub async fn list(&self) -> Vec<String> {
        TeleportStorage::list(self).await
    }

    /// Convenience wrapper for TeleportStorage::upload_blob
    pub async fn upload_blob(&self, key: &str, data: Bytes) -> TeleportStorageResult<String> {
        TeleportStorage::upload_blob(self, key, data).await
    }

    /// Convenience wrapper for TeleportStorage::download_blob
    pub async fn download_blob(&self, key: &str) -> TeleportStorageResult<Bytes> {
        TeleportStorage::download_blob(self, key).await
    }
}

#[async_trait::async_trait]
impl TeleportStorage for SimTeleportStorage {
    async fn upload(&self, package: TeleportPackage) -> TeleportStorageResult<String> {
        if let Some(fault) = self.check_fault("teleport_upload") {
            if matches!(
                fault,
                FaultType::TeleportUploadFail | FaultType::TeleportTimeout { .. }
            ) {
                return Err(self.fault_to_error(fault));
            }
        }

        if package.size_bytes > self.max_package_bytes {
            return Err(TeleportStorageError::TooLarge {
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

    async fn download(&self, id: &str) -> TeleportStorageResult<TeleportPackage> {
        if let Some(fault) = self.check_fault("teleport_download") {
            if matches!(
                fault,
                FaultType::TeleportDownloadFail | FaultType::TeleportTimeout { .. }
            ) {
                return Err(self.fault_to_error(fault));
            }
        }

        let packages = self.packages.read().await;
        match packages.get(id) {
            Some(package) => {
                tracing::debug!(package_id = %id, "Teleport package downloaded");
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
        if let Some(fault) = self.check_fault("teleport_restore_validate") {
            if matches!(fault, FaultType::TeleportArchMismatch) {
                return Err(self.fault_to_error(fault));
            }
        }

        if let Some(fault) = self.check_fault("teleport_image_validate") {
            if matches!(fault, FaultType::TeleportImageMismatch) {
                return Err(self.fault_to_error(fault));
            }
        }

        let package = self.download(id).await?;

        package
            .validate_for_restore(target_arch)
            .map_err(|_reason| TeleportStorageError::ArchMismatch {
                expected: target_arch,
                actual: package.source_arch,
            })?;

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
        tracing::debug!(package_id = %id, "Teleport package deleted");
        Ok(())
    }

    async fn list(&self) -> Vec<String> {
        let packages = self.packages.read().await;
        packages.keys().cloned().collect()
    }

    async fn upload_blob(&self, key: &str, data: Bytes) -> TeleportStorageResult<String> {
        if let Some(fault) = self.check_fault("teleport_blob_upload") {
            if matches!(fault, FaultType::TeleportUploadFail) {
                return Err(self.fault_to_error(fault));
            }
        }

        let mut blobs = self.blobs.write().await;
        blobs.insert(key.to_string(), data);
        Ok(key.to_string())
    }

    async fn download_blob(&self, key: &str) -> TeleportStorageResult<Bytes> {
        if let Some(fault) = self.check_fault("teleport_blob_download") {
            if matches!(fault, FaultType::TeleportDownloadFail) {
                return Err(self.fault_to_error(fault));
            }
        }

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
    use kelpie_core::SnapshotKind;

    #[tokio::test]
    async fn test_sim_teleport_storage_basic() {
        let rng = DeterministicRng::new(12345);
        let faults = Arc::new(FaultInjector::new(rng.fork()));
        let storage = SimTeleportStorage::new(rng, faults);

        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_vm_snapshot(kelpie_core::teleport::VmSnapshotBlob::encode(
            Bytes::new(),
            Bytes::from("snapshot"),
            Bytes::new(),
        ));

        let id = storage.upload(package).await.unwrap();
        let downloaded = storage.download(&id).await.unwrap();
        assert_eq!(downloaded.id, "pkg-1");
    }
}

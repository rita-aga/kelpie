//! Teleport storage backends for production and development
//!
//! TigerStyle: Storage traits live in kelpie-core; this module provides
//! LocalTeleportStorage for development use.

use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::teleport::{
    Architecture, TeleportPackage, TeleportStorage, TeleportStorageError, TeleportStorageResult,
};

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

        package.validate_for_restore(target_arch).map_err(|_| {
            TeleportStorageError::ArchMismatch {
                expected: target_arch,
                actual: package.source_arch,
            }
        })?;

        let package_version = &package.base_image_version;
        let expected_version = &self.expected_image_version;

        let package_parts: Vec<&str> = package_version
            .split('-')
            .next()
            .unwrap_or(package_version)
            .split('.')
            .collect();
        let expected_parts: Vec<&str> = expected_version
            .split('-')
            .next()
            .unwrap_or(expected_version)
            .split('.')
            .collect();

        if package_parts.len() >= 2 && expected_parts.len() >= 2 {
            let package_major = package_parts[0];
            let package_minor = package_parts[1];
            let expected_major = expected_parts[0];
            let expected_minor = expected_parts[1];

            if package_major != expected_major || package_minor != expected_minor {
                return Err(TeleportStorageError::ImageMismatch {
                    expected: format!("{}.{}", expected_major, expected_minor),
                    actual: format!("{}.{}", package_major, package_minor),
                });
            }

            if package_parts.len() >= 3 && expected_parts.len() >= 3 {
                let package_patch = package_parts[2];
                let expected_patch = expected_parts[2];

                if package_patch != expected_patch {
                    tracing::warn!(
                        package_version = %package_version,
                        expected_version = %expected_version,
                        "Base image PATCH version differs (package: {}, host: {}). \
                         This is allowed but may cause subtle issues.",
                        package_patch, expected_patch
                    );
                }
            }
        } else {
            tracing::warn!(
                package_version = %package_version,
                expected_version = %expected_version,
                "Unable to parse version numbers, skipping validation"
            );
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
    use kelpie_core::teleport::{SnapshotKind, TeleportPackage, VmSnapshotBlob};

    #[tokio::test]
    async fn test_local_teleport_storage_basic() {
        let storage = LocalTeleportStorage::new();
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_vm_snapshot(VmSnapshotBlob::encode(
            Bytes::new(),
            Bytes::from("snapshot"),
            Bytes::new(),
        ));

        let id = storage.upload(package).await.unwrap();
        assert_eq!(id, "pkg-1");

        let downloaded = storage.download(&id).await.unwrap();
        assert_eq!(downloaded.id, "pkg-1");
    }

    #[tokio::test]
    async fn test_local_teleport_storage_arch_validation() {
        let storage = LocalTeleportStorage::new();
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_vm_snapshot(VmSnapshotBlob::encode(
            Bytes::new(),
            Bytes::from("snapshot"),
            Bytes::new(),
        ));

        storage.upload(package).await.unwrap();

        let result = storage
            .download_for_restore("pkg-1", Architecture::Arm64)
            .await;
        assert!(result.is_ok());

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
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Checkpoint,
        )
        .with_agent_state(Bytes::from("agent-state"));

        storage.upload(package).await.unwrap();

        let result = storage
            .download_for_restore("pkg-1", Architecture::X86_64)
            .await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_local_teleport_storage_blob_operations() {
        let storage = LocalTeleportStorage::new();
        let key = "workspace-1";
        let data = Bytes::from("hello".to_string());

        let upload_id = storage.upload_blob(key, data.clone()).await.unwrap();
        assert_eq!(upload_id, key);

        let downloaded = storage.download_blob(key).await.unwrap();
        assert_eq!(downloaded, data);
    }

    #[test]
    fn test_teleport_package_validation() {
        let package = TeleportPackage::new(
            "pkg-1",
            "agent-1",
            Architecture::Arm64,
            SnapshotKind::Teleport,
        )
        .with_vm_snapshot(VmSnapshotBlob::encode(
            Bytes::new(),
            Bytes::from("snapshot"),
            Bytes::new(),
        ));

        assert!(package.validate_for_restore(Architecture::Arm64).is_ok());
        assert!(package.validate_for_restore(Architecture::X86_64).is_err());

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

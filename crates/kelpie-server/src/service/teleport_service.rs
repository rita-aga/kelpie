//! Teleport service for agent migration between hosts
//!
//! TigerStyle: Service wraps storage, provides clean API, handles errors.
//!
//! This service provides high-level teleportation operations:
//! - teleport_out: Snapshot agent state and upload to storage
//! - teleport_in: Download from storage and restore agent state
//!
//! DST Support: Works with SimTeleportStorage for fault injection testing.

use crate::storage::{Architecture, SnapshotKind, TeleportPackage, TeleportStorage};
use bytes::Bytes;
use kelpie_core::{Error, Result};
use kelpie_sandbox::{Sandbox, SandboxConfig, SandboxFactory, Snapshot};
use std::sync::Arc;

/// Teleport service for agent migration
///
/// TigerStyle: Clean abstraction, explicit error handling, testable.
#[derive(Clone)]
pub struct TeleportService<S, F>
where
    S: TeleportStorage,
    F: SandboxFactory,
    F::Sandbox: 'static,
{
    /// Teleport storage backend
    storage: Arc<S>,
    /// Sandbox factory for creating sandboxes
    sandbox_factory: Arc<F>,
    /// Expected base image version
    base_image_version: String,
}

impl<S, F> TeleportService<S, F>
where
    S: TeleportStorage,
    F: SandboxFactory,
    F::Sandbox: 'static,
{
    /// Create a new TeleportService
    pub fn new(storage: Arc<S>, sandbox_factory: Arc<F>) -> Self {
        Self {
            storage,
            sandbox_factory,
            base_image_version: "1.0.0".to_string(),
        }
    }

    /// Set the expected base image version
    pub fn with_base_image_version(mut self, version: impl Into<String>) -> Self {
        self.base_image_version = version.into();
        self
    }

    /// Teleport agent OUT (snapshot + upload to storage)
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID to teleport
    /// * `sandbox` - Running sandbox to snapshot
    /// * `agent_state` - Serialized agent state (memory blocks, conversation, etc.)
    /// * `kind` - Type of snapshot (Suspend, Teleport, or Checkpoint)
    ///
    /// # Returns
    /// The teleport package ID on success
    ///
    /// # Errors
    /// - SnapshotCreateFail: Failed to create snapshot
    /// - UploadFailed: Failed to upload package to storage
    ///
    /// # TigerStyle
    /// - Returns package ID for tracking
    /// - Sandbox state is preserved on failure (no partial mutations)
    pub async fn teleport_out(
        &self,
        agent_id: &str,
        sandbox: &mut dyn Sandbox,
        agent_state: Bytes,
        kind: SnapshotKind,
    ) -> Result<String> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent_id must not be empty");

        tracing::info!(agent_id = %agent_id, kind = ?kind, "Teleporting agent OUT");

        // Step 1: Create snapshot of sandbox
        let snapshot = sandbox.snapshot().await.map_err(|e| Error::Internal {
            message: format!("Failed to create snapshot: {}", e),
        })?;

        // Step 2: Build teleport package
        let package_id = format!("teleport-{}-{}", agent_id, uuid::Uuid::new_v4());
        let now_ms = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64;

        let mut package =
            TeleportPackage::new(package_id.clone(), agent_id, self.storage.host_arch(), kind)
                .with_agent_state(agent_state)
                .with_created_at(now_ms)
                .with_base_image_version(&self.base_image_version);

        // Add VM state for full teleport
        match kind {
            SnapshotKind::Suspend | SnapshotKind::Teleport => {
                // For full VM teleport, include memory and CPU state
                // In real implementation, this would be the actual VM state
                // For now, we serialize the snapshot metadata
                let snapshot_data = serde_json::to_vec(&snapshot).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize snapshot: {}", e),
                })?;
                package = package
                    .with_vm_memory(Bytes::from(snapshot_data.clone()))
                    .with_vm_cpu_state(Bytes::from(snapshot_data));
            }
            SnapshotKind::Checkpoint => {
                // Checkpoint only includes agent state, no VM state
            }
        }

        // Step 3: Upload to storage
        let uploaded_id = self
            .storage
            .upload(package)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to upload teleport package: {}", e),
            })?;

        tracing::info!(
            agent_id = %agent_id,
            package_id = %uploaded_id,
            "Agent teleported OUT successfully"
        );

        Ok(uploaded_id)
    }

    /// Teleport agent IN (download + restore from storage)
    ///
    /// # Arguments
    /// * `package_id` - Teleport package ID to restore from
    /// * `sandbox_config` - Configuration for creating new sandbox
    ///
    /// # Returns
    /// Tuple of (created sandbox, agent state bytes)
    ///
    /// # Errors
    /// - NotFound: Package not found in storage
    /// - ArchMismatch: Package architecture doesn't match host
    /// - ImageMismatch: Base image version mismatch (validated by storage)
    /// - DownloadFailed: Failed to download package
    /// - Sandbox creation/restore failed
    ///
    /// # TigerStyle
    /// - Creates new sandbox (caller owns it)
    /// - Returns agent state for caller to deserialize
    /// - Clean failure (no partial state on error)
    /// - Version validation happens in storage layer (MAJOR.MINOR must match)
    pub async fn teleport_in(
        &self,
        package_id: &str,
        sandbox_config: SandboxConfig,
    ) -> Result<(Box<dyn Sandbox>, Bytes)> {
        // Preconditions
        assert!(!package_id.is_empty(), "package_id must not be empty");

        tracing::info!(package_id = %package_id, "Teleporting agent IN");

        // Step 1: Download and validate package
        let host_arch = self.storage.host_arch();
        let package = self
            .storage
            .download_for_restore(package_id, host_arch)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to download teleport package: {}", e),
            })?;

        tracing::debug!(
            package_id = %package_id,
            agent_id = %package.agent_id,
            kind = ?package.kind,
            "Package downloaded successfully (version validated by storage)"
        );

        // Step 2: Create new sandbox
        let mut sandbox = self
            .sandbox_factory
            .create(sandbox_config)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to create sandbox: {}", e),
            })?;

        // Step 3: Start sandbox if not already running
        // Note: Some factories (like MockSandboxFactory) start the sandbox automatically
        use kelpie_sandbox::SandboxState;
        if sandbox.state() != SandboxState::Running {
            sandbox.start().await.map_err(|e| Error::Internal {
                message: format!("Failed to start sandbox: {}", e),
            })?;
        }

        // Step 4: Restore from snapshot (for full teleport/suspend)
        match package.kind {
            SnapshotKind::Suspend | SnapshotKind::Teleport => {
                // Restore VM state from snapshot
                if let Some(ref vm_memory) = package.vm_memory {
                    // Deserialize snapshot metadata
                    let snapshot: Snapshot =
                        serde_json::from_slice(vm_memory).map_err(|e| Error::Internal {
                            message: format!("Failed to deserialize snapshot: {}", e),
                        })?;

                    // Restore sandbox state
                    sandbox
                        .restore(&snapshot)
                        .await
                        .map_err(|e| Error::Internal {
                            message: format!("Failed to restore sandbox: {}", e),
                        })?;
                }
            }
            SnapshotKind::Checkpoint => {
                // Checkpoint doesn't restore VM state, just starts fresh
                // Agent state will be restored by caller
            }
        }

        // Extract agent state
        let agent_state = package.agent_state.unwrap_or_default();

        tracing::info!(
            package_id = %package_id,
            agent_id = %package.agent_id,
            "Agent teleported IN successfully"
        );

        Ok((Box::new(sandbox), agent_state))
    }

    /// List available teleport packages
    pub async fn list_packages(&self) -> Vec<String> {
        self.storage.list().await
    }

    /// Delete a teleport package
    pub async fn delete_package(&self, package_id: &str) -> Result<()> {
        self.storage
            .delete(package_id)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to delete teleport package: {}", e),
            })
    }

    /// Get package details without downloading full state
    pub async fn get_package(&self, package_id: &str) -> Result<TeleportPackage> {
        self.storage
            .download(package_id)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to get teleport package: {}", e),
            })
    }

    /// Get the host architecture
    pub fn host_arch(&self) -> Architecture {
        self.storage.host_arch()
    }
}

/// Request for teleport_out operation
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TeleportOutRequest {
    /// Agent ID to teleport
    pub agent_id: String,
    /// Snapshot kind (Suspend, Teleport, Checkpoint)
    pub kind: SnapshotKind,
}

/// Response from teleport_out operation
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TeleportOutResponse {
    /// Teleport package ID
    pub package_id: String,
    /// Source architecture
    pub source_arch: Architecture,
    /// Package size in bytes
    pub size_bytes: u64,
}

/// Request for teleport_in operation
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TeleportInRequest {
    /// Teleport package ID to restore from
    pub package_id: String,
}

/// Response from teleport_in operation
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TeleportInResponse {
    /// Restored agent ID
    pub agent_id: String,
    /// Snapshot kind that was restored
    pub kind: SnapshotKind,
}

/// Package info for listing
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TeleportPackageInfo {
    /// Package ID
    pub id: String,
    /// Agent ID
    pub agent_id: String,
    /// Source architecture
    pub source_arch: Architecture,
    /// Snapshot kind
    pub kind: SnapshotKind,
    /// Creation timestamp (ms)
    pub created_at_ms: u64,
    /// Package size in bytes
    pub size_bytes: u64,
}

impl From<TeleportPackage> for TeleportPackageInfo {
    fn from(p: TeleportPackage) -> Self {
        TeleportPackageInfo {
            id: p.id,
            agent_id: p.agent_id,
            source_arch: p.source_arch,
            kind: p.kind,
            created_at_ms: p.created_at_ms,
            size_bytes: p.size_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::LocalTeleportStorage;
    use kelpie_sandbox::{MockSandbox, MockSandboxFactory, ResourceLimits};

    fn test_config() -> SandboxConfig {
        SandboxConfig::new()
            .with_limits(
                ResourceLimits::new()
                    .with_memory(512 * 1024 * 1024)
                    .with_vcpus(2),
            )
            .with_workdir("/workspace")
    }

    #[tokio::test]
    async fn test_teleport_service_roundtrip() {
        let storage = Arc::new(LocalTeleportStorage::new());
        let factory = Arc::new(MockSandboxFactory::new());
        let service = TeleportService::new(storage, factory.clone());

        // Create a sandbox for teleport_out (factory.create() starts it automatically)
        let mut sandbox = factory.create(test_config()).await.unwrap();

        // Teleport out
        let agent_state = Bytes::from("test agent state");
        let package_id = service
            .teleport_out(
                "agent-1",
                &mut sandbox,
                agent_state.clone(),
                SnapshotKind::Teleport,
            )
            .await
            .unwrap();

        assert!(package_id.contains("agent-1"));

        // Verify package exists
        let packages = service.list_packages().await;
        assert_eq!(packages.len(), 1);
        assert_eq!(packages[0], package_id);

        // Teleport in
        let (new_sandbox, restored_state) = service
            .teleport_in(&package_id, test_config())
            .await
            .unwrap();
        assert_eq!(restored_state, agent_state);
        assert_eq!(new_sandbox.state(), kelpie_sandbox::SandboxState::Running);

        // Cleanup
        service.delete_package(&package_id).await.unwrap();
        let packages = service.list_packages().await;
        assert!(packages.is_empty());
    }

    #[tokio::test]
    async fn test_teleport_service_checkpoint() {
        let storage = Arc::new(LocalTeleportStorage::new());
        let factory = Arc::new(MockSandboxFactory::new());
        let service = TeleportService::new(storage, factory.clone());

        // Create a sandbox for teleport_out (factory.create() starts it automatically)
        let mut sandbox = factory.create(test_config()).await.unwrap();

        // Teleport out as checkpoint
        let agent_state = Bytes::from("checkpoint state");
        let package_id = service
            .teleport_out(
                "agent-2",
                &mut sandbox,
                agent_state.clone(),
                SnapshotKind::Checkpoint,
            )
            .await
            .unwrap();

        // Get package details
        let package = service.get_package(&package_id).await.unwrap();
        assert_eq!(package.kind, SnapshotKind::Checkpoint);
        assert!(package.is_checkpoint());
        assert!(!package.is_full_teleport()); // Checkpoint has no VM state

        // Teleport in
        let (_new_sandbox, restored_state) = service
            .teleport_in(&package_id, test_config())
            .await
            .unwrap();
        assert_eq!(restored_state, agent_state);
    }
}

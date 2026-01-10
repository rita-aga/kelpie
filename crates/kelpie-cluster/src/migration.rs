//! Actor migration
//!
//! TigerStyle: Explicit migration protocol with atomic state transfer.

use crate::error::{ClusterError, ClusterResult};
use crate::rpc::{RequestId, RpcMessage, RpcTransport};
use bytes::Bytes;
use kelpie_core::actor::ActorId;
use kelpie_core::constants::ACTOR_MIGRATION_COOLDOWN_MS;
use kelpie_registry::{ActorPlacement, NodeId, Registry};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tracing::{debug, info, warn};

/// Migration state for tracking in-progress migrations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MigrationState {
    /// Migration not started
    Idle,
    /// Preparing migration (acquiring locks)
    Preparing,
    /// Transferring actor state
    Transferring,
    /// Completing migration (activating on target)
    Completing,
    /// Migration completed successfully
    Completed,
    /// Migration failed
    Failed,
}

impl MigrationState {
    /// Check if migration is in progress
    pub fn is_in_progress(&self) -> bool {
        matches!(
            self,
            Self::Preparing | Self::Transferring | Self::Completing
        )
    }

    /// Check if migration is terminal
    pub fn is_terminal(&self) -> bool {
        matches!(self, Self::Completed | Self::Failed)
    }
}

/// Tracking information for a migration
#[derive(Debug, Clone)]
pub struct MigrationInfo {
    /// The actor being migrated
    pub actor_id: ActorId,
    /// Source node
    pub from_node: NodeId,
    /// Target node
    pub to_node: NodeId,
    /// Current state
    pub state: MigrationState,
    /// Started at timestamp (Unix ms)
    pub started_at_ms: u64,
    /// Completed at timestamp (Unix ms)
    pub completed_at_ms: Option<u64>,
    /// Error message if failed
    pub error: Option<String>,
}

impl MigrationInfo {
    /// Create a new migration info
    pub fn new(actor_id: ActorId, from_node: NodeId, to_node: NodeId, timestamp_ms: u64) -> Self {
        Self {
            actor_id,
            from_node,
            to_node,
            state: MigrationState::Idle,
            started_at_ms: timestamp_ms,
            completed_at_ms: None,
            error: None,
        }
    }

    /// Mark migration as failed
    pub fn fail(&mut self, error: impl Into<String>, timestamp_ms: u64) {
        self.state = MigrationState::Failed;
        self.completed_at_ms = Some(timestamp_ms);
        self.error = Some(error.into());
    }

    /// Mark migration as completed
    pub fn complete(&mut self, timestamp_ms: u64) {
        self.state = MigrationState::Completed;
        self.completed_at_ms = Some(timestamp_ms);
    }
}

/// Migration coordinator
///
/// Handles the migration protocol between nodes.
pub struct MigrationCoordinator<R: Registry, T: RpcTransport> {
    /// Local node ID (for future use in migration validation)
    #[allow(dead_code)]
    local_node_id: NodeId,
    /// Registry for placement updates
    registry: Arc<R>,
    /// RPC transport for communication
    transport: Arc<T>,
    /// Active migrations
    migrations: RwLock<HashMap<ActorId, MigrationInfo>>,
    /// Cooldowns for actors (to prevent thrashing)
    cooldowns: RwLock<HashMap<ActorId, u64>>,
    /// RPC timeout
    rpc_timeout: Duration,
    /// Next request ID
    next_request_id: std::sync::atomic::AtomicU64,
}

impl<R: Registry, T: RpcTransport> MigrationCoordinator<R, T> {
    /// Create a new migration coordinator
    pub fn new(
        local_node_id: NodeId,
        registry: Arc<R>,
        transport: Arc<T>,
        rpc_timeout: Duration,
    ) -> Self {
        Self {
            local_node_id,
            registry,
            transport,
            migrations: RwLock::new(HashMap::new()),
            cooldowns: RwLock::new(HashMap::new()),
            rpc_timeout,
            next_request_id: std::sync::atomic::AtomicU64::new(1),
        }
    }

    /// Get next request ID
    fn next_request_id(&self) -> RequestId {
        self.next_request_id
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    /// Check if actor is on cooldown
    pub async fn is_on_cooldown(&self, actor_id: &ActorId, now_ms: u64) -> bool {
        let cooldowns = self.cooldowns.read().await;
        if let Some(&cooldown_until) = cooldowns.get(actor_id) {
            return now_ms < cooldown_until;
        }
        false
    }

    /// Set cooldown for an actor
    async fn set_cooldown(&self, actor_id: &ActorId, now_ms: u64) {
        let mut cooldowns = self.cooldowns.write().await;
        cooldowns.insert(actor_id.clone(), now_ms + ACTOR_MIGRATION_COOLDOWN_MS);
    }

    /// Get current migration info for an actor
    pub async fn get_migration_info(&self, actor_id: &ActorId) -> Option<MigrationInfo> {
        let migrations = self.migrations.read().await;
        migrations.get(actor_id).cloned()
    }

    /// Migrate an actor from source to target node
    ///
    /// This is a high-level migration that coordinates the full protocol:
    /// 1. Prepare (acquire locks, check target capacity)
    /// 2. Transfer (serialize and send state)
    /// 3. Complete (activate on target, deactivate on source)
    pub async fn migrate(
        &self,
        actor_id: ActorId,
        from_node: NodeId,
        to_node: NodeId,
        state: Bytes,
        now_ms: u64,
    ) -> ClusterResult<()> {
        // Check cooldown
        if self.is_on_cooldown(&actor_id, now_ms).await {
            return Err(ClusterError::MigrationFailed {
                actor_id: actor_id.qualified_name(),
                from_node: from_node.to_string(),
                to_node: to_node.to_string(),
                reason: "actor on migration cooldown".into(),
            });
        }

        // Check if already migrating
        {
            let migrations = self.migrations.read().await;
            if let Some(info) = migrations.get(&actor_id) {
                if info.state.is_in_progress() {
                    return Err(ClusterError::MigrationFailed {
                        actor_id: actor_id.qualified_name(),
                        from_node: from_node.to_string(),
                        to_node: to_node.to_string(),
                        reason: "migration already in progress".into(),
                    });
                }
            }
        }

        // Initialize migration
        let mut migration_info =
            MigrationInfo::new(actor_id.clone(), from_node.clone(), to_node.clone(), now_ms);

        {
            let mut migrations = self.migrations.write().await;
            migrations.insert(actor_id.clone(), migration_info.clone());
        }

        // Step 1: Prepare
        migration_info.state = MigrationState::Preparing;
        self.update_migration(&actor_id, &migration_info).await;

        let prepare_result = self
            .prepare_migration(&actor_id, &from_node, &to_node)
            .await;
        if let Err(e) = prepare_result {
            migration_info.fail(e.to_string(), now_ms);
            self.update_migration(&actor_id, &migration_info).await;
            return Err(e);
        }

        // Step 2: Transfer state
        migration_info.state = MigrationState::Transferring;
        self.update_migration(&actor_id, &migration_info).await;

        let transfer_result = self
            .transfer_state(&actor_id, &from_node, &to_node, state)
            .await;
        if let Err(e) = transfer_result {
            migration_info.fail(e.to_string(), now_ms);
            self.update_migration(&actor_id, &migration_info).await;
            return Err(e);
        }

        // Step 3: Complete migration
        migration_info.state = MigrationState::Completing;
        self.update_migration(&actor_id, &migration_info).await;

        let complete_result = self.complete_migration(&actor_id, &to_node).await;
        if let Err(e) = complete_result {
            migration_info.fail(e.to_string(), now_ms);
            self.update_migration(&actor_id, &migration_info).await;
            return Err(e);
        }

        // Update registry
        self.registry
            .migrate_actor(&actor_id, &from_node, &to_node)
            .await?;

        // Mark complete and set cooldown
        migration_info.complete(now_ms);
        self.update_migration(&actor_id, &migration_info).await;
        self.set_cooldown(&actor_id, now_ms).await;

        info!(
            actor_id = %actor_id,
            from = %from_node,
            to = %to_node,
            "actor migration completed"
        );

        Ok(())
    }

    /// Prepare migration on target node
    async fn prepare_migration(
        &self,
        actor_id: &ActorId,
        from_node: &NodeId,
        to_node: &NodeId,
    ) -> ClusterResult<()> {
        debug!(
            actor_id = %actor_id,
            from = %from_node,
            to = %to_node,
            "preparing migration"
        );

        let request = RpcMessage::MigratePrepare {
            request_id: self.next_request_id(),
            actor_id: actor_id.clone(),
            from_node: from_node.clone(),
        };

        let response = self
            .transport
            .send_and_recv(to_node, request, self.rpc_timeout)
            .await?;

        match response {
            RpcMessage::MigratePrepareResponse {
                ready: true,
                reason: _,
                ..
            } => Ok(()),
            RpcMessage::MigratePrepareResponse {
                ready: false,
                reason,
                ..
            } => Err(ClusterError::MigrationFailed {
                actor_id: actor_id.qualified_name(),
                from_node: from_node.to_string(),
                to_node: to_node.to_string(),
                reason: reason.unwrap_or_else(|| "target not ready".into()),
            }),
            _ => Err(ClusterError::Internal {
                message: "unexpected response".into(),
            }),
        }
    }

    /// Transfer actor state to target node
    async fn transfer_state(
        &self,
        actor_id: &ActorId,
        from_node: &NodeId,
        to_node: &NodeId,
        state: Bytes,
    ) -> ClusterResult<()> {
        debug!(
            actor_id = %actor_id,
            from = %from_node,
            to = %to_node,
            state_bytes = state.len(),
            "transferring actor state"
        );

        let request = RpcMessage::MigrateTransfer {
            request_id: self.next_request_id(),
            actor_id: actor_id.clone(),
            state,
            from_node: from_node.clone(),
        };

        let response = self
            .transport
            .send_and_recv(to_node, request, self.rpc_timeout)
            .await?;

        match response {
            RpcMessage::MigrateTransferResponse {
                success: true,
                reason: _,
                ..
            } => Ok(()),
            RpcMessage::MigrateTransferResponse {
                success: false,
                reason,
                ..
            } => Err(ClusterError::MigrationFailed {
                actor_id: actor_id.qualified_name(),
                from_node: from_node.to_string(),
                to_node: to_node.to_string(),
                reason: reason.unwrap_or_else(|| "state transfer failed".into()),
            }),
            _ => Err(ClusterError::Internal {
                message: "unexpected response".into(),
            }),
        }
    }

    /// Complete migration on target node
    async fn complete_migration(&self, actor_id: &ActorId, to_node: &NodeId) -> ClusterResult<()> {
        debug!(
            actor_id = %actor_id,
            to = %to_node,
            "completing migration"
        );

        let request = RpcMessage::MigrateComplete {
            request_id: self.next_request_id(),
            actor_id: actor_id.clone(),
        };

        let response = self
            .transport
            .send_and_recv(to_node, request, self.rpc_timeout)
            .await?;

        match response {
            RpcMessage::MigrateCompleteResponse {
                success: true,
                reason: _,
                ..
            } => Ok(()),
            RpcMessage::MigrateCompleteResponse {
                success: false,
                reason,
                ..
            } => Err(ClusterError::MigrationFailed {
                actor_id: actor_id.qualified_name(),
                from_node: "unknown".to_string(),
                to_node: to_node.to_string(),
                reason: reason.unwrap_or_else(|| "completion failed".into()),
            }),
            _ => Err(ClusterError::Internal {
                message: "unexpected response".into(),
            }),
        }
    }

    /// Update migration info in tracking map
    async fn update_migration(&self, actor_id: &ActorId, info: &MigrationInfo) {
        let mut migrations = self.migrations.write().await;
        migrations.insert(actor_id.clone(), info.clone());
    }

    /// Get all in-progress migrations
    pub async fn get_in_progress_migrations(&self) -> Vec<MigrationInfo> {
        let migrations = self.migrations.read().await;
        migrations
            .values()
            .filter(|m| m.state.is_in_progress())
            .cloned()
            .collect()
    }

    /// Clean up completed migrations older than a threshold
    pub async fn cleanup_completed(&self, older_than_ms: u64) {
        let mut migrations = self.migrations.write().await;
        migrations.retain(|_, info| {
            if let Some(completed_at) = info.completed_at_ms {
                completed_at > older_than_ms
            } else {
                true
            }
        });
    }
}

/// Plan migrations for failed node
///
/// Returns a list of (actor_id, target_node) pairs for actors that should be migrated.
pub async fn plan_migrations<R: Registry>(
    registry: &R,
    failed_node: &NodeId,
    max_batch: usize,
) -> ClusterResult<Vec<(ActorPlacement, NodeId)>> {
    use kelpie_registry::{PlacementContext, PlacementDecision};

    let actors_to_migrate = registry.list_actors_on_node(failed_node).await?;

    let mut migrations = Vec::new();

    for placement in actors_to_migrate.into_iter().take(max_batch) {
        // Select a new node for each actor
        let context = PlacementContext::new(placement.actor_id.clone());
        let decision = registry.select_node_for_placement(context).await?;

        match decision {
            PlacementDecision::New(target_node) => {
                migrations.push((placement, target_node));
            }
            PlacementDecision::NoCapacity => {
                warn!(
                    actor_id = %placement.actor_id,
                    "no capacity for migration, skipping"
                );
            }
            PlacementDecision::Existing(_) => {
                // Actor already placed elsewhere, shouldn't happen for failed node
                debug!(
                    actor_id = %placement.actor_id,
                    "actor already has placement"
                );
            }
        }
    }

    Ok(migrations)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_actor_id(n: u32) -> ActorId {
        ActorId::new("test", format!("actor-{}", n)).unwrap()
    }

    fn test_node_id(n: u32) -> NodeId {
        NodeId::new(format!("node-{}", n)).unwrap()
    }

    #[test]
    fn test_migration_state() {
        assert!(MigrationState::Preparing.is_in_progress());
        assert!(MigrationState::Transferring.is_in_progress());
        assert!(MigrationState::Completing.is_in_progress());
        assert!(!MigrationState::Idle.is_in_progress());
        assert!(!MigrationState::Completed.is_in_progress());
        assert!(!MigrationState::Failed.is_in_progress());

        assert!(MigrationState::Completed.is_terminal());
        assert!(MigrationState::Failed.is_terminal());
        assert!(!MigrationState::Preparing.is_terminal());
    }

    #[test]
    fn test_migration_info() {
        let mut info = MigrationInfo::new(test_actor_id(1), test_node_id(1), test_node_id(2), 1000);

        assert_eq!(info.state, MigrationState::Idle);
        assert!(info.completed_at_ms.is_none());

        info.complete(2000);
        assert_eq!(info.state, MigrationState::Completed);
        assert_eq!(info.completed_at_ms, Some(2000));
    }

    #[test]
    fn test_migration_info_fail() {
        let mut info = MigrationInfo::new(test_actor_id(1), test_node_id(1), test_node_id(2), 1000);

        info.fail("some error", 2000);
        assert_eq!(info.state, MigrationState::Failed);
        assert_eq!(info.error, Some("some error".to_string()));
    }
}

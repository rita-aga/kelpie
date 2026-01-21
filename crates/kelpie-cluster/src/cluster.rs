//! Main cluster coordinator
//!
//! TigerStyle: Single entry point for cluster operations.

use crate::config::ClusterConfig;
use crate::error::{ClusterError, ClusterResult};
use crate::migration::{plan_migrations, MigrationCoordinator};
use crate::rpc::{RpcMessage, RpcTransport};
use kelpie_core::actor::ActorId;
use kelpie_core::runtime::{JoinHandle, Runtime};
use kelpie_registry::{Heartbeat, NodeId, NodeInfo, NodeStatus, PlacementDecision, Registry};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Notify, RwLock};
use tracing::{debug, info, warn};

/// Cluster state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClusterState {
    /// Cluster not started
    Stopped,
    /// Cluster is initializing
    Initializing,
    /// Cluster is running
    Running,
    /// Cluster is shutting down
    ShuttingDown,
}

/// The main cluster coordinator
///
/// Manages cluster membership, heartbeats, and actor placement.
pub struct Cluster<R: Registry + 'static, T: RpcTransport + 'static, RT: Runtime + 'static> {
    /// Local node information
    local_node: NodeInfo,
    /// Cluster configuration
    config: ClusterConfig,
    /// Registry for actor placement
    registry: Arc<R>,
    /// RPC transport
    transport: Arc<T>,
    /// Runtime for task spawning and time
    runtime: RT,
    /// Migration coordinator
    migration: Arc<MigrationCoordinator<R, T>>,
    /// Current cluster state
    state: RwLock<ClusterState>,
    /// Heartbeat task handle
    heartbeat_task: RwLock<Option<JoinHandle<()>>>,
    /// Failure detection task handle
    failure_task: RwLock<Option<JoinHandle<()>>>,
    /// Shutdown signal
    shutdown: Arc<Notify>,
    /// Whether shutdown was requested
    shutdown_requested: AtomicBool,
    /// Next heartbeat sequence (for future use in coordinated heartbeats)
    #[allow(dead_code)]
    heartbeat_sequence: AtomicU64,
}

impl<R: Registry + 'static, T: RpcTransport + 'static, RT: Runtime + 'static> Cluster<R, T, RT> {
    /// Create a new cluster instance
    pub fn new(
        local_node: NodeInfo,
        config: ClusterConfig,
        registry: Arc<R>,
        transport: Arc<T>,
        runtime: RT,
    ) -> Self {
        let migration = Arc::new(MigrationCoordinator::new(
            local_node.id.clone(),
            registry.clone(),
            transport.clone(),
            config.rpc_timeout(),
        ));

        Self {
            local_node,
            config,
            registry,
            transport,
            runtime,
            migration,
            state: RwLock::new(ClusterState::Stopped),
            heartbeat_task: RwLock::new(None),
            failure_task: RwLock::new(None),
            shutdown: Arc::new(Notify::new()),
            shutdown_requested: AtomicBool::new(false),
            heartbeat_sequence: AtomicU64::new(0),
        }
    }

    /// Get the local node ID
    pub fn local_node_id(&self) -> &NodeId {
        &self.local_node.id
    }

    /// Get the local node info
    pub fn local_node(&self) -> &NodeInfo {
        &self.local_node
    }

    /// Get the cluster configuration
    pub fn config(&self) -> &ClusterConfig {
        &self.config
    }

    /// Get the current cluster state
    pub async fn state(&self) -> ClusterState {
        *self.state.read().await
    }

    /// Check if cluster is running
    pub async fn is_running(&self) -> bool {
        *self.state.read().await == ClusterState::Running
    }

    /// Start the cluster
    pub async fn start(&self) -> ClusterResult<()> {
        {
            let mut state = self.state.write().await;
            if *state != ClusterState::Stopped {
                return Err(ClusterError::AlreadyStarted);
            }
            *state = ClusterState::Initializing;
        }

        info!(
            node_id = %self.local_node.id,
            addr = %self.config.rpc_addr,
            "starting cluster node"
        );

        // Register local node with registry
        let mut node = self.local_node.clone();
        node.status = NodeStatus::Active;
        self.registry.register_node(node).await?;

        // Start RPC transport
        self.transport.start().await?;

        // Join cluster if we have seed nodes
        if !self.config.seed_nodes.is_empty() {
            self.join_cluster().await?;
        }

        // Start heartbeat task
        self.start_heartbeat_task().await;

        // Start failure detection task
        self.start_failure_detection_task().await;

        {
            let mut state = self.state.write().await;
            *state = ClusterState::Running;
        }

        info!(
            node_id = %self.local_node.id,
            "cluster node started"
        );

        Ok(())
    }

    /// Stop the cluster
    pub async fn stop(&self) -> ClusterResult<()> {
        {
            let state = self.state.read().await;
            if *state == ClusterState::Stopped {
                return Ok(());
            }
        }

        info!(
            node_id = %self.local_node.id,
            "stopping cluster node"
        );

        // Signal shutdown
        self.shutdown_requested.store(true, Ordering::SeqCst);
        self.shutdown.notify_waiters();

        {
            let mut state = self.state.write().await;
            *state = ClusterState::ShuttingDown;
        }

        // Drain actors if configured
        if self.config.drain_on_shutdown {
            if let Err(e) = self.drain_actors().await {
                warn!(error = %e, "failed to drain actors during shutdown");
            }
        }

        // Stop heartbeat task
        if let Some(task) = self.heartbeat_task.write().await.take() {
            // Wait for task to finish (signaled via shutdown notify)
            let _ = task.await;
        }

        // Stop failure detection task
        if let Some(task) = self.failure_task.write().await.take() {
            // Wait for task to finish (signaled via shutdown notify)
            let _ = task.await;
        }

        // Notify cluster of leave
        let leave_msg = RpcMessage::LeaveNotification {
            node_id: self.local_node.id.clone(),
        };
        let _ = self.transport.broadcast(leave_msg).await;

        // Stop transport
        self.transport.stop().await?;

        // Update local node status (transition through Leaving first)
        let _ = self
            .registry
            .update_node_status(&self.local_node.id, NodeStatus::Leaving)
            .await;
        let _ = self
            .registry
            .update_node_status(&self.local_node.id, NodeStatus::Left)
            .await;

        {
            let mut state = self.state.write().await;
            *state = ClusterState::Stopped;
        }

        info!(
            node_id = %self.local_node.id,
            "cluster node stopped"
        );

        Ok(())
    }

    /// Join an existing cluster
    async fn join_cluster(&self) -> ClusterResult<()> {
        info!("joining cluster via seed nodes");

        for seed_addr in &self.config.seed_nodes {
            // For now, we don't have a way to resolve addresses to node IDs
            // In a real implementation, this would involve discovery
            debug!(seed = %seed_addr, "attempting to join via seed");
        }

        Ok(())
    }

    /// Start the heartbeat sending task
    async fn start_heartbeat_task(&self) {
        let registry = self.registry.clone();
        let transport = self.transport.clone();
        let node_id = self.local_node.id.clone();
        let interval = Duration::from_millis(self.config.heartbeat.interval_ms);
        let shutdown = self.shutdown.clone();
        let sequence = Arc::new(AtomicU64::new(0));
        let runtime = self.runtime.clone();

        let task = self.runtime.spawn(async move {
            loop {
                tokio::select! {
                    _ = runtime.sleep(interval) => {
                        // Get current actor count
                        let actor_count = registry
                            .list_actors_on_node(&node_id)
                            .await
                            .map(|a| a.len() as u64)
                            .unwrap_or(0);

                        let seq = sequence.fetch_add(1, Ordering::SeqCst);

                        let heartbeat = Heartbeat::new(
                            node_id.clone(),
                            now_ms(),
                            NodeStatus::Active,
                            actor_count,
                            1_000_000 - actor_count, // Available capacity
                            seq,
                        );

                        // Broadcast heartbeat
                        if let Err(e) = transport.broadcast(RpcMessage::Heartbeat(heartbeat)).await {
                            debug!(error = %e, "failed to broadcast heartbeat");
                        }
                    }
                    _ = shutdown.notified() => {
                        debug!("heartbeat task shutting down");
                        break;
                    }
                }
            }
        });

        *self.heartbeat_task.write().await = Some(task);
    }

    /// Start the failure detection task
    async fn start_failure_detection_task(&self) {
        let registry = self.registry.clone();
        let _migration = self.migration.clone();
        let config = self.config.clone();
        let local_node_id = self.local_node.id.clone();
        let interval = Duration::from_millis(self.config.heartbeat.interval_ms);
        let shutdown = self.shutdown.clone();
        let runtime = self.runtime.clone();

        let task = self.runtime.spawn(async move {
            loop {
                tokio::select! {
                    _ = runtime.sleep(interval) => {
                        // Check for failed nodes (if registry supports it)
                        // For MemoryRegistry, we'd need to add a method to check timeouts

                        // Get nodes that are marked as failed
                        if let Ok(failed_nodes) = registry.list_nodes_by_status(NodeStatus::Failed).await {
                            for node in failed_nodes {
                                if node.id == local_node_id {
                                    continue; // Skip self
                                }

                                if config.auto_migrate_on_failure {
                                    // Plan and execute migrations
                                    match plan_migrations(
                                        registry.as_ref(),
                                        &node.id,
                                        config.migration_batch_size,
                                    ).await {
                                        Ok(migrations) => {
                                            for (placement, target) in migrations {
                                                debug!(
                                                    actor = %placement.actor_id,
                                                    from = %node.id,
                                                    to = %target,
                                                    "planning migration due to node failure"
                                                );
                                                // Migration would be executed here
                                            }
                                        }
                                        Err(e) => {
                                            warn!(
                                                error = %e,
                                                node = %node.id,
                                                "failed to plan migrations"
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ = shutdown.notified() => {
                        debug!("failure detection task shutting down");
                        break;
                    }
                }
            }
        });

        *self.failure_task.write().await = Some(task);
    }

    /// Drain actors from this node (for graceful shutdown)
    async fn drain_actors(&self) -> ClusterResult<()> {
        info!("draining actors from node");

        let actors = self
            .registry
            .list_actors_on_node(&self.local_node.id)
            .await?;

        if actors.is_empty() {
            return Ok(());
        }

        info!(count = actors.len(), "actors to drain");

        // In a real implementation, we would migrate each actor to another node
        // For now, we just unregister them
        for placement in actors {
            if let Err(e) = self.registry.unregister_actor(&placement.actor_id).await {
                warn!(
                    actor = %placement.actor_id,
                    error = %e,
                    "failed to unregister actor during drain"
                );
            }
        }

        Ok(())
    }

    /// Get a placement decision for an actor
    pub async fn get_placement(&self, actor_id: &ActorId) -> ClusterResult<PlacementDecision> {
        let placement = self.registry.get_placement(actor_id).await?;

        if let Some(p) = placement {
            return Ok(PlacementDecision::Existing(p));
        }

        // Select a node for new placement
        let context = kelpie_registry::PlacementContext::new(actor_id.clone());
        let decision = self.registry.select_node_for_placement(context).await?;

        Ok(decision)
    }

    /// Try to claim an actor for the local node
    pub async fn try_claim_local(&self, actor_id: ActorId) -> ClusterResult<PlacementDecision> {
        let decision = self
            .registry
            .try_claim_actor(actor_id, self.local_node.id.clone())
            .await?;

        Ok(decision)
    }

    /// Get migration coordinator
    pub fn migration(&self) -> &MigrationCoordinator<R, T> {
        &self.migration
    }

    /// Get all nodes in the cluster
    pub async fn list_nodes(&self) -> ClusterResult<Vec<NodeInfo>> {
        Ok(self.registry.list_nodes().await?)
    }

    /// Get active nodes in the cluster
    pub async fn list_active_nodes(&self) -> ClusterResult<Vec<NodeInfo>> {
        Ok(self
            .registry
            .list_nodes_by_status(NodeStatus::Active)
            .await?)
    }
}

/// Get current time in milliseconds
fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rpc::MemoryTransport;
    use kelpie_core::TokioRuntime;
    use kelpie_registry::MemoryRegistry;
    use std::net::{IpAddr, Ipv4Addr, SocketAddr};

    fn test_addr(port: u16) -> SocketAddr {
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), port)
    }

    fn test_node_id(n: u32) -> NodeId {
        NodeId::new(format!("node-{}", n)).unwrap()
    }

    #[tokio::test]
    async fn test_cluster_create() {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::new(node_id.clone(), addr);
        node.status = NodeStatus::Active;

        let config = ClusterConfig::single_node(addr);
        let registry = Arc::new(MemoryRegistry::new());
        let runtime = TokioRuntime;
        let transport = Arc::new(MemoryTransport::new(node_id.clone(), addr, runtime.clone()));

        let cluster = Cluster::new(node, config, registry, transport, runtime);

        assert_eq!(cluster.local_node_id(), &node_id);
        assert_eq!(cluster.state().await, ClusterState::Stopped);
    }

    #[tokio::test]
    async fn test_cluster_start_stop() {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, 1000);
        node.status = NodeStatus::Active;

        let config = ClusterConfig::for_testing();
        let registry = Arc::new(MemoryRegistry::new());
        let runtime = TokioRuntime;
        let transport = Arc::new(MemoryTransport::new(node_id.clone(), addr, runtime.clone()));

        let cluster = Cluster::new(node, config, registry, transport, runtime);

        cluster.start().await.unwrap();
        assert!(cluster.is_running().await);

        cluster.stop().await.unwrap();
        assert_eq!(cluster.state().await, ClusterState::Stopped);
    }

    #[tokio::test]
    async fn test_cluster_list_nodes() {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, 1000);
        node.status = NodeStatus::Active;

        let config = ClusterConfig::for_testing();
        let registry = Arc::new(MemoryRegistry::new());
        let runtime = TokioRuntime;
        let transport = Arc::new(MemoryTransport::new(node_id.clone(), addr, runtime.clone()));

        let cluster = Cluster::new(node, config, registry, transport, runtime);
        cluster.start().await.unwrap();

        let nodes = cluster.list_nodes().await.unwrap();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].id, node_id);

        cluster.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_cluster_try_claim() {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, 1000);
        node.status = NodeStatus::Active;

        let config = ClusterConfig::for_testing();
        let registry = Arc::new(MemoryRegistry::new());
        let runtime = TokioRuntime;
        let transport = Arc::new(MemoryTransport::new(node_id.clone(), addr, runtime.clone()));

        let cluster = Cluster::new(node, config, registry, transport, runtime);
        cluster.start().await.unwrap();

        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let decision = cluster.try_claim_local(actor_id.clone()).await.unwrap();

        assert!(matches!(decision, PlacementDecision::New(_)));

        // Second claim should return existing
        let decision2 = cluster.try_claim_local(actor_id).await.unwrap();
        assert!(matches!(decision2, PlacementDecision::Existing(_)));

        cluster.stop().await.unwrap();
    }
}

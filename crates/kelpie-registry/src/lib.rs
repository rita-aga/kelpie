//! Kelpie Registry
//!
//! Actor placement and discovery for Kelpie clusters.
//!
//! # Overview
//!
//! The registry provides:
//! - Actor-to-node placement tracking (single activation guarantee)
//! - Heartbeat-based failure detection
//! - Actor migration coordination
//! - Multiple backends (Memory, FoundationDB planned)
//!
//! # TigerStyle
//! - Explicit placement with linearizable operations
//! - Bounded heartbeat intervals
//! - Observable failure detection
//!
//! # Example
//!
//! ```rust,ignore
//! use kelpie_registry::{MemoryRegistry, Registry, NodeInfo, NodeId};
//!
//! let registry = MemoryRegistry::new();
//!
//! // Register a node
//! let node_id = NodeId::new("node-1")?;
//! let info = NodeInfo::new(node_id.clone(), "127.0.0.1:8080".parse()?);
//! registry.register_node(info).await?;
//!
//! // Register an actor
//! let actor_id = ActorId::new("agents", "agent-1")?;
//! registry.register_actor(actor_id, node_id).await?;
//! ```

mod error;
mod heartbeat;
mod lease;
mod node;
mod placement;
mod registry;

pub use error::{RegistryError, RegistryResult};
pub use heartbeat::{
    Heartbeat, HeartbeatConfig, HeartbeatTracker, NodeHeartbeatState, HEARTBEAT_FAILURE_COUNT,
    HEARTBEAT_INTERVAL_MS_MAX, HEARTBEAT_INTERVAL_MS_MIN, HEARTBEAT_SUSPECT_COUNT,
};
pub use lease::{
    Lease, LeaseConfig, LeaseManager, MemoryLeaseManager, LEASE_DURATION_MS_DEFAULT,
    LEASE_DURATION_MS_MAX, LEASE_DURATION_MS_MIN,
};
pub use node::{NodeId, NodeInfo, NodeStatus, NODE_ID_LENGTH_BYTES_MAX};
pub use placement::{
    validate_placement, ActorPlacement, PlacementContext, PlacementDecision, PlacementStrategy,
};
pub use registry::{Clock, MemoryRegistry, MockClock, Registry, SystemClock};

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr, SocketAddr};

    fn test_addr() -> SocketAddr {
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080)
    }

    #[test]
    fn test_registry_module_compiles() {
        // Verify public types are accessible
        let _node_id = NodeId::new("test-node").unwrap();
        let _status = NodeStatus::Active;
    }

    #[tokio::test]
    async fn test_memory_registry_basic() {
        let registry = MemoryRegistry::new();

        let node_id = NodeId::new("node-1").unwrap();
        let mut info = NodeInfo::new(node_id.clone(), test_addr());
        info.status = NodeStatus::Active;

        registry.register_node(info).await.unwrap();

        let nodes = registry.list_nodes().await.unwrap();
        assert_eq!(nodes.len(), 1);
    }
}

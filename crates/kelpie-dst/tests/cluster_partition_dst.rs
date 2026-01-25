//! DST tests for production Cluster code under network partitions
//!
//! This is the REFERENCE IMPLEMENTATION for Phase 3 of True DST Simulation Architecture.
//! It demonstrates the pattern of using production kelpie-cluster code with SimRpcTransport
//! for testing network partition behavior.
//!
//! Key Pattern:
//! - Use production `Cluster` from kelpie-cluster (not a mock)
//! - Use `SimRpcTransport` which wraps `SimNetwork`
//! - Create partitions via `SimNetwork` while Cluster uses its normal RPC logic
//! - Tests run deterministically under simulated time and network
//!
//! TigerStyle: DST-first testing with explicit partition control, 2+ assertions per test.

use kelpie_cluster::{Cluster, ClusterConfig, ClusterState, RpcMessage, RpcTransport};
use kelpie_core::TokioRuntime;
use kelpie_dst::{DeterministicRng, FaultInjectorBuilder, SimClock, SimNetwork, SimRpcTransport};
use kelpie_registry::{MemoryRegistry, NodeId, NodeInfo, NodeStatus};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::sync::Arc;

// =============================================================================
// Helper Functions
// =============================================================================

fn test_addr(port: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), port)
}

fn test_node(id: u32, clock: &SimClock) -> NodeInfo {
    let node_id = NodeId::new(format!("node-{}", id)).unwrap();
    let addr = test_addr(8000 + id as u16);
    let mut node = NodeInfo::new_with_time(node_id, addr, clock);
    node.status = NodeStatus::Active;
    node
}

fn test_config() -> ClusterConfig {
    ClusterConfig::for_testing()
        .with_heartbeat_interval(100) // 100ms heartbeat interval
        .with_rpc_timeout(1000) // 1s RPC timeout
}

fn create_shared_network(clock: SimClock) -> Arc<SimNetwork> {
    let rng = DeterministicRng::new(42);
    let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
    Arc::new(SimNetwork::new(clock, rng, fault_injector).with_latency(10, 5))
}

// =============================================================================
// Reference DST Tests: Production Cluster + SimRpcTransport + Partitions
// =============================================================================

/// Test cluster startup and shutdown with SimRpcTransport.
///
/// Demonstrates:
/// - Production Cluster code using SimRpcTransport
/// - Basic cluster lifecycle works under simulated network
#[madsim::test]
async fn test_cluster_with_sim_transport() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let network = create_shared_network((*clock).clone());

    let node = test_node(1, &clock);
    let config = test_config();
    let registry = Arc::new(MemoryRegistry::new());
    let addr = node.rpc_addr;
    let runtime = TokioRuntime;

    // Create SimRpcTransport instead of MemoryTransport
    let transport = Arc::new(SimRpcTransport::new(
        node.id.clone(),
        addr,
        network.clone(),
        (*clock).clone(),
    ));

    // Create production Cluster with SimRpcTransport
    let cluster =
        Cluster::with_time_provider(node, config, registry, transport, runtime, clock.clone());

    // Precondition: initial state is Stopped
    assert_eq!(cluster.state().await, ClusterState::Stopped);

    // Start cluster
    cluster.start().await.unwrap();

    // Postconditions
    assert!(cluster.is_running().await);
    assert_eq!(cluster.state().await, ClusterState::Running);

    // Stop cluster
    cluster.stop().await.unwrap();
    assert_eq!(cluster.state().await, ClusterState::Stopped);
}

/// Test that partition blocks RPC messages between nodes.
///
/// Demonstrates:
/// - Creating partition via SimNetwork
/// - Production transport correctly fails on partitioned sends
/// - Healing partition restores connectivity
#[madsim::test]
async fn test_partition_blocks_rpc_send() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let network = create_shared_network((*clock).clone());

    // Create two transports sharing the same network
    let transport1 = Arc::new(SimRpcTransport::new(
        NodeId::new("node-1").unwrap(),
        test_addr(8001),
        network.clone(),
        (*clock).clone(),
    ));
    let transport2 = Arc::new(SimRpcTransport::new(
        NodeId::new("node-2").unwrap(),
        test_addr(8002),
        network.clone(),
        (*clock).clone(),
    ));

    // Register each other's addresses
    transport1
        .register_node(NodeId::new("node-2").unwrap(), test_addr(8002))
        .await;
    transport2
        .register_node(NodeId::new("node-1").unwrap(), test_addr(8001))
        .await;

    // Start transports
    transport1.start().await.unwrap();
    transport2.start().await.unwrap();

    // Send without partition - should succeed
    let heartbeat = RpcMessage::Heartbeat(kelpie_registry::Heartbeat::new(
        NodeId::new("node-1").unwrap(),
        1000,
        NodeStatus::Active,
        0,
        100,
        1,
    ));
    let result = transport1
        .send(&NodeId::new("node-2").unwrap(), heartbeat.clone())
        .await;
    assert!(result.is_ok(), "Send should succeed without partition");

    // Create bidirectional partition
    network.partition("node-1", "node-2").await;

    // Verify partition state
    assert!(
        network.is_partitioned("node-1", "node-2").await,
        "Partition should be active"
    );
    assert!(
        network.is_partitioned("node-2", "node-1").await,
        "Bidirectional partition blocks both directions"
    );

    // Send with partition - should fail
    let result = transport1
        .send(&NodeId::new("node-2").unwrap(), heartbeat.clone())
        .await;
    assert!(result.is_err(), "Send should fail with partition");

    // Heal partition
    network.heal("node-1", "node-2").await;

    // Verify partition healed
    assert!(
        !network.is_partitioned("node-1", "node-2").await,
        "Partition should be healed"
    );

    // Send after heal - should succeed
    let result = transport1
        .send(&NodeId::new("node-2").unwrap(), heartbeat)
        .await;
    assert!(result.is_ok(), "Send should succeed after heal");
}

/// Test one-way partition allows asymmetric communication.
///
/// Demonstrates:
/// - One-way partitions (e.g., leader can send but can't receive votes)
/// - Asymmetric network failures are testable
#[madsim::test]
async fn test_one_way_partition_asymmetric() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let network = create_shared_network((*clock).clone());

    let transport1 = Arc::new(SimRpcTransport::new(
        NodeId::new("leader").unwrap(),
        test_addr(8001),
        network.clone(),
        (*clock).clone(),
    ));
    let transport2 = Arc::new(SimRpcTransport::new(
        NodeId::new("follower").unwrap(),
        test_addr(8002),
        network.clone(),
        (*clock).clone(),
    ));

    transport1
        .register_node(NodeId::new("follower").unwrap(), test_addr(8002))
        .await;
    transport2
        .register_node(NodeId::new("leader").unwrap(), test_addr(8001))
        .await;

    transport1.start().await.unwrap();
    transport2.start().await.unwrap();

    // Create one-way partition: follower -> leader blocked (votes can't reach leader)
    network.partition_one_way("follower", "leader").await;

    // Leader can send heartbeats to follower
    let heartbeat = RpcMessage::Heartbeat(kelpie_registry::Heartbeat::new(
        NodeId::new("leader").unwrap(),
        1000,
        NodeStatus::Active,
        0,
        100,
        1,
    ));
    let result = transport1
        .send(&NodeId::new("follower").unwrap(), heartbeat)
        .await;
    assert!(result.is_ok(), "Leader -> Follower should work");

    // Follower cannot send votes back to leader
    let vote = RpcMessage::HeartbeatAck {
        node_id: NodeId::new("follower").unwrap(),
        sequence: 1,
    };
    let result = transport2.send(&NodeId::new("leader").unwrap(), vote).await;
    assert!(
        result.is_err(),
        "Follower -> Leader should fail (one-way partition)"
    );

    // Heal one-way partition
    network.heal_one_way("follower", "leader").await;

    // Both directions work now
    let vote = RpcMessage::HeartbeatAck {
        node_id: NodeId::new("follower").unwrap(),
        sequence: 2,
    };
    let result = transport2.send(&NodeId::new("leader").unwrap(), vote).await;
    assert!(result.is_ok(), "Follower -> Leader should work after heal");
}

/// Test multi-node cluster with group partition.
///
/// Demonstrates:
/// - 5-node cluster with shared SimNetwork
/// - Group partition isolating minority from majority
/// - Communication within groups still works
#[madsim::test]
async fn test_multi_node_group_partition() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let network = create_shared_network((*clock).clone());

    // Create 5 transports (simulating 5-node cluster)
    let mut transports = Vec::new();
    for i in 1..=5 {
        let node_id = NodeId::new(format!("node-{}", i)).unwrap();
        let transport = Arc::new(SimRpcTransport::new(
            node_id.clone(),
            test_addr(8000 + i),
            network.clone(),
            (*clock).clone(),
        ));

        // Register all other nodes
        for j in 1..=5 {
            if i != j {
                transport
                    .register_node(
                        NodeId::new(format!("node-{}", j)).unwrap(),
                        test_addr(8000 + j),
                    )
                    .await;
            }
        }

        transport.start().await.unwrap();
        transports.push(transport);
    }

    // Partition: [node-1, node-2] isolated from [node-3, node-4, node-5]
    network
        .partition_group(&["node-1", "node-2"], &["node-3", "node-4", "node-5"])
        .await;

    // Verify partition state
    assert!(network.is_partitioned("node-1", "node-3").await);
    assert!(network.is_partitioned("node-2", "node-4").await);

    // Intra-minority communication works
    let msg = RpcMessage::HeartbeatAck {
        node_id: NodeId::new("node-1").unwrap(),
        sequence: 1,
    };
    let result = transports[0]
        .send(&NodeId::new("node-2").unwrap(), msg)
        .await;
    assert!(
        result.is_ok(),
        "Communication within minority group should work"
    );

    // Intra-majority communication works
    let msg = RpcMessage::HeartbeatAck {
        node_id: NodeId::new("node-3").unwrap(),
        sequence: 1,
    };
    let result = transports[2]
        .send(&NodeId::new("node-4").unwrap(), msg)
        .await;
    assert!(
        result.is_ok(),
        "Communication within majority group should work"
    );

    // Cross-partition communication fails
    let msg = RpcMessage::HeartbeatAck {
        node_id: NodeId::new("node-1").unwrap(),
        sequence: 1,
    };
    let result = transports[0]
        .send(&NodeId::new("node-3").unwrap(), msg)
        .await;
    assert!(result.is_err(), "Cross-partition communication should fail");

    // Heal all partitions
    network.heal_all().await;

    // Cross-partition communication works after heal
    let msg = RpcMessage::HeartbeatAck {
        node_id: NodeId::new("node-1").unwrap(),
        sequence: 2,
    };
    let result = transports[0]
        .send(&NodeId::new("node-3").unwrap(), msg)
        .await;
    assert!(result.is_ok(), "Communication should work after heal");
}

/// Test deterministic partition behavior across runs.
///
/// Demonstrates:
/// - Same seed + same partitions = same behavior
/// - Foundation for reproducible DST with network partitions
#[madsim::test]
async fn test_partition_determinism() {
    async fn run_sequence(seed: u64, clock: SimClock) -> Vec<bool> {
        let rng = DeterministicRng::new(seed);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let network =
            Arc::new(SimNetwork::new(clock.clone(), rng, fault_injector).with_latency(10, 5));

        let transport = Arc::new(SimRpcTransport::new(
            NodeId::new("test").unwrap(),
            test_addr(8001),
            network.clone(),
            clock.clone(),
        ));
        transport
            .register_node(NodeId::new("other").unwrap(), test_addr(8002))
            .await;
        transport.start().await.unwrap();

        let mut results = Vec::new();

        // Send 1: no partition
        let msg = RpcMessage::HeartbeatAck {
            node_id: NodeId::new("test").unwrap(),
            sequence: 1,
        };
        results.push(
            transport
                .send(&NodeId::new("other").unwrap(), msg)
                .await
                .is_ok(),
        );

        // Create partition
        network.partition("test", "other").await;

        // Send 2: with partition
        let msg = RpcMessage::HeartbeatAck {
            node_id: NodeId::new("test").unwrap(),
            sequence: 2,
        };
        results.push(
            transport
                .send(&NodeId::new("other").unwrap(), msg)
                .await
                .is_ok(),
        );

        // Heal
        network.heal("test", "other").await;

        // Send 3: after heal
        let msg = RpcMessage::HeartbeatAck {
            node_id: NodeId::new("test").unwrap(),
            sequence: 3,
        };
        results.push(
            transport
                .send(&NodeId::new("other").unwrap(), msg)
                .await
                .is_ok(),
        );

        results
    }

    // Run same sequence twice with same seed
    let clock1 = SimClock::from_millis(1000);
    let clock2 = SimClock::from_millis(1000);

    let run1 = run_sequence(42, clock1).await;
    let run2 = run_sequence(42, clock2).await;

    // Results should be identical
    assert_eq!(run1, run2, "Same seed should produce same results");
    assert_eq!(
        run1,
        vec![true, false, true],
        "Expected: success, fail (partition), success (healed)"
    );
}

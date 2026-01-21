//! DST tests for cluster operations
//!
//! TigerStyle: Deterministic testing of cluster membership, failure detection,
//! actor placement, and migration under fault injection.

use kelpie_cluster::{Cluster, ClusterConfig, ClusterState, MemoryTransport, MigrationState};
use kelpie_core::actor::ActorId;
use kelpie_core::error::Error as CoreError;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_registry::{
    Clock, Heartbeat, HeartbeatConfig, HeartbeatTracker, MemoryRegistry, NodeId, NodeInfo,
    NodeStatus, PlacementContext, PlacementDecision, PlacementStrategy, Registry,
};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

// =============================================================================
// Test Clock (uses AtomicU64 for reliable synchronous reads)
// =============================================================================

/// A test clock using AtomicU64 for reliable synchronous reads
#[derive(Debug)]
struct TestClock {
    time_ms: AtomicU64,
}

impl TestClock {
    fn new(initial_ms: u64) -> Self {
        Self {
            time_ms: AtomicU64::new(initial_ms),
        }
    }

    fn advance(&self, ms: u64) {
        self.time_ms.fetch_add(ms, Ordering::SeqCst);
    }
}

impl Clock for TestClock {
    fn now_ms(&self) -> u64 {
        self.time_ms.load(Ordering::SeqCst)
    }
}

// =============================================================================
// Test Helpers
// =============================================================================

fn test_addr(port: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), port)
}

fn test_node_id(n: u32) -> NodeId {
    NodeId::new(format!("node-{}", n)).unwrap()
}

fn test_actor_id(n: u32) -> ActorId {
    ActorId::new("dst-cluster", format!("actor-{}", n)).unwrap()
}

/// Convert RegistryError to CoreError for test compatibility
fn to_core_error(e: kelpie_registry::RegistryError) -> CoreError {
    CoreError::Internal {
        message: e.to_string(),
    }
}

// =============================================================================
// Node Registration Tests
// =============================================================================

#[test]
fn test_dst_node_registration() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register multiple nodes
        for i in 1..=5 {
            let node_id = test_node_id(i);
            let addr = test_addr(9000 + i as u16);
            let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
            node.status = NodeStatus::Active;
            registry.register_node(node).await.map_err(to_core_error)?;
        }

        // Verify all nodes are registered
        let nodes = registry.list_nodes().await.map_err(to_core_error)?;
        assert_eq!(nodes.len(), 5, "Expected 5 nodes registered");

        // Verify all are active
        let active_nodes = registry
            .list_nodes_by_status(NodeStatus::Active)
            .await
            .map_err(to_core_error)?;
        assert_eq!(active_nodes.len(), 5, "Expected 5 active nodes");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_node_status_transitions() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        let node_id = test_node_id(1);
        let addr = test_addr(9001);

        // Start as Joining
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
        node.status = NodeStatus::Joining;
        registry.register_node(node).await.map_err(to_core_error)?;

        // Transition to Active
        registry
            .update_node_status(&node_id, NodeStatus::Active)
            .await
            .map_err(to_core_error)?;
        let node_info = registry.get_node(&node_id).await.map_err(to_core_error)?;
        assert!(node_info.is_some());
        assert_eq!(node_info.unwrap().status, NodeStatus::Active);

        // Transition to Leaving
        registry
            .update_node_status(&node_id, NodeStatus::Leaving)
            .await
            .map_err(to_core_error)?;
        let node_info = registry.get_node(&node_id).await.map_err(to_core_error)?;
        assert_eq!(node_info.unwrap().status, NodeStatus::Leaving);

        // Transition to Left
        registry
            .update_node_status(&node_id, NodeStatus::Left)
            .await
            .map_err(to_core_error)?;
        let node_info = registry.get_node(&node_id).await.map_err(to_core_error)?;
        assert_eq!(node_info.unwrap().status, NodeStatus::Left);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Heartbeat and Failure Detection Tests
// =============================================================================

#[test]
fn test_dst_heartbeat_tracking() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let heartbeat_config = HeartbeatConfig::new(1000); // 1s interval
        let mut tracker = HeartbeatTracker::new(heartbeat_config);

        let start_time = env.now_ms();

        // Register nodes
        for i in 1..=3 {
            tracker.register_node(test_node_id(i), start_time);
        }

        // Check initial state - should still be healthy
        env.advance_time_ms(500);
        let current = start_time + 500;
        let transitions = tracker.check_all_timeouts(current);
        assert!(transitions.is_empty(), "No transitions expected yet");

        // Record heartbeats using Heartbeat struct
        for i in 1..=3 {
            let heartbeat = Heartbeat::new(test_node_id(i), current, NodeStatus::Active, 0, 100, 1);
            let _ = tracker.receive_heartbeat(heartbeat, current);
        }

        // Advance time past suspect timeout for node-1 (don't update its heartbeat)
        env.advance_time_ms(4000);
        let current = start_time + 4500;
        let heartbeat2 = Heartbeat::new(test_node_id(2), current, NodeStatus::Active, 0, 100, 2);
        let heartbeat3 = Heartbeat::new(test_node_id(3), current, NodeStatus::Active, 0, 100, 2);
        let _ = tracker.receive_heartbeat(heartbeat2, current);
        let _ = tracker.receive_heartbeat(heartbeat3, current);

        let transitions = tracker.check_all_timeouts(current);
        // Node-1 should transition to Suspect
        let node1_transition = transitions.iter().find(|(id, _, _)| id == &test_node_id(1));
        assert!(
            node1_transition.is_some(),
            "Node-1 should have transitioned"
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_failure_detection() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let heartbeat_config = HeartbeatConfig::new(1000); // 1s interval
        let mut tracker = HeartbeatTracker::new(heartbeat_config.clone());

        let start_time = env.now_ms();

        // Register a node
        let node_id = test_node_id(1);
        tracker.register_node(node_id.clone(), start_time);
        let heartbeat = Heartbeat::new(node_id.clone(), start_time, NodeStatus::Active, 0, 100, 1);
        let _ = tracker.receive_heartbeat(heartbeat, start_time);

        // Advance time past failure timeout (suspect_timeout + failure_timeout)
        let total_timeout =
            heartbeat_config.suspect_timeout_ms + heartbeat_config.failure_timeout_ms + 1000;
        env.advance_time_ms(total_timeout);

        let transitions = tracker.check_all_timeouts(start_time + total_timeout);

        // Should see transition to Suspect, then check again for Failed
        // The node should be marked as suspect first
        assert!(!transitions.is_empty(), "Expected status transitions");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Actor Placement Tests
// =============================================================================

#[test]
fn test_dst_actor_placement_least_loaded() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register nodes with different loads
        for i in 1..=3 {
            let node_id = test_node_id(i);
            let addr = test_addr(9000 + i as u16);
            let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
            node.status = NodeStatus::Active;
            node.actor_count = i as u64 * 10; // node-1: 10, node-2: 20, node-3: 30
            node.actor_capacity = 100;
            registry.register_node(node).await.map_err(to_core_error)?;
        }

        // Request placement with LeastLoaded strategy - should choose node-1
        let actor_id = test_actor_id(1);
        let context =
            PlacementContext::new(actor_id.clone()).with_strategy(PlacementStrategy::LeastLoaded);
        let decision = registry
            .select_node_for_placement(context)
            .await
            .map_err(to_core_error)?;

        match decision {
            PlacementDecision::New(node_id) => {
                assert_eq!(
                    node_id,
                    test_node_id(1),
                    "Should place on least loaded node"
                );
            }
            _ => panic!("Expected New placement decision"),
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_actor_claim_and_placement() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register a node
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
        node.status = NodeStatus::Active;
        registry.register_node(node).await.map_err(to_core_error)?;

        // Claim an actor
        let actor_id = test_actor_id(1);
        let decision = registry
            .try_claim_actor(actor_id.clone(), node_id.clone())
            .await
            .map_err(to_core_error)?;

        match decision {
            PlacementDecision::New(claimed_node) => {
                assert_eq!(claimed_node, node_id, "Should claim on specified node");
            }
            _ => panic!("Expected New placement for first claim"),
        }

        // Second claim should return Existing
        let decision2 = registry
            .try_claim_actor(actor_id.clone(), node_id.clone())
            .await
            .map_err(to_core_error)?;

        match decision2 {
            PlacementDecision::Existing(placement) => {
                assert_eq!(placement.node_id, node_id);
                assert_eq!(placement.actor_id, actor_id);
            }
            _ => panic!("Expected Existing placement for second claim"),
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_actor_placement_multiple_actors() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register multiple nodes
        for i in 1..=3 {
            let node_id = test_node_id(i);
            let addr = test_addr(9000 + i as u16);
            let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
            node.status = NodeStatus::Active;
            node.actor_capacity = 100;
            registry.register_node(node).await.map_err(to_core_error)?;
        }

        // Place multiple actors
        let mut placements = Vec::new();
        for i in 1..=10 {
            let actor_id = test_actor_id(i);
            let decision = registry
                .try_claim_actor(actor_id.clone(), test_node_id((i % 3) + 1))
                .await
                .map_err(to_core_error)?;

            if let PlacementDecision::New(node_id) = decision {
                placements.push(node_id);
            }
        }

        assert_eq!(placements.len(), 10, "All actors should be placed");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Actor Migration Tests
// =============================================================================

#[test]
fn test_dst_actor_migration() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register two nodes
        for i in 1..=2 {
            let node_id = test_node_id(i);
            let addr = test_addr(9000 + i as u16);
            let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
            node.status = NodeStatus::Active;
            registry.register_node(node).await.map_err(to_core_error)?;
        }

        // Place actor on node-1
        let actor_id = test_actor_id(1);
        registry
            .try_claim_actor(actor_id.clone(), test_node_id(1))
            .await
            .map_err(to_core_error)?;

        // Verify initial placement
        let placement = registry
            .get_placement(&actor_id)
            .await
            .map_err(to_core_error)?;
        assert!(placement.is_some());
        assert_eq!(placement.unwrap().node_id, test_node_id(1));

        // Advance time before migration (placement timestamps require monotonic time)
        env.advance_time_ms(100);
        clock.advance(100);

        // Migrate to node-2
        registry
            .migrate_actor(&actor_id, &test_node_id(1), &test_node_id(2))
            .await
            .map_err(to_core_error)?;

        // Verify migration
        let new_placement = registry
            .get_placement(&actor_id)
            .await
            .map_err(to_core_error)?;
        assert!(new_placement.is_some());
        assert_eq!(new_placement.unwrap().node_id, test_node_id(2));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_actor_unregister() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register a node
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
        node.status = NodeStatus::Active;
        registry.register_node(node).await.map_err(to_core_error)?;

        // Place and then unregister an actor
        let actor_id = test_actor_id(1);
        registry
            .try_claim_actor(actor_id.clone(), node_id.clone())
            .await
            .map_err(to_core_error)?;

        // Verify placement exists
        assert!(registry
            .get_placement(&actor_id)
            .await
            .map_err(to_core_error)?
            .is_some());

        // Unregister
        registry
            .unregister_actor(&actor_id)
            .await
            .map_err(to_core_error)?;

        // Verify placement is gone
        assert!(registry
            .get_placement(&actor_id)
            .await
            .map_err(to_core_error)?
            .is_none());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Cluster Start/Stop Tests
// =============================================================================

#[test]
fn test_dst_cluster_lifecycle() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, 1000);
        node.status = NodeStatus::Active;

        let cluster_config = ClusterConfig::for_testing();
        let registry = Arc::new(MemoryRegistry::new());
        let transport = Arc::new(MemoryTransport::new(
            node_id.clone(),
            addr,
            kelpie_core::current_runtime(),
        ));

        let cluster = Cluster::new(
            node,
            cluster_config,
            registry,
            transport,
            kelpie_core::current_runtime(),
        );

        // Initial state should be Stopped
        assert_eq!(cluster.state().await, ClusterState::Stopped);

        // Start cluster
        cluster.start().await.map_err(|e| CoreError::Internal {
            message: e.to_string(),
        })?;
        assert!(cluster.is_running().await);
        assert_eq!(cluster.state().await, ClusterState::Running);

        // Stop cluster
        cluster.stop().await.map_err(|e| CoreError::Internal {
            message: e.to_string(),
        })?;
        assert_eq!(cluster.state().await, ClusterState::Stopped);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_cluster_double_start() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, 1000);
        node.status = NodeStatus::Active;

        let cluster_config = ClusterConfig::for_testing();
        let registry = Arc::new(MemoryRegistry::new());
        let transport = Arc::new(MemoryTransport::new(
            node_id.clone(),
            addr,
            kelpie_core::current_runtime(),
        ));

        let cluster = Cluster::new(
            node,
            cluster_config,
            registry,
            transport,
            kelpie_core::current_runtime(),
        );

        // Start cluster
        cluster.start().await.map_err(|e| CoreError::Internal {
            message: e.to_string(),
        })?;

        // Double start should fail
        let result = cluster.start().await;
        assert!(result.is_err(), "Double start should fail");

        cluster.stop().await.map_err(|e| CoreError::Internal {
            message: e.to_string(),
        })?;

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Cluster Actor Placement Tests
// =============================================================================

#[test]
fn test_dst_cluster_try_claim() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let node_id = test_node_id(1);
        let addr = test_addr(9001);
        let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, 1000);
        node.status = NodeStatus::Active;

        let cluster_config = ClusterConfig::for_testing();
        let registry = Arc::new(MemoryRegistry::new());
        let transport = Arc::new(MemoryTransport::new(
            node_id.clone(),
            addr,
            kelpie_core::current_runtime(),
        ));

        let cluster = Cluster::new(
            node,
            cluster_config,
            registry,
            transport,
            kelpie_core::current_runtime(),
        );
        cluster.start().await.map_err(|e| CoreError::Internal {
            message: e.to_string(),
        })?;

        // Claim an actor
        let actor_id = test_actor_id(1);
        let decision = cluster
            .try_claim_local(actor_id.clone())
            .await
            .map_err(|e| CoreError::Internal {
                message: e.to_string(),
            })?;

        match decision {
            PlacementDecision::New(claimed_node) => {
                assert_eq!(claimed_node, node_id, "Should claim on local node");
            }
            _ => panic!("Expected New placement for first claim"),
        }

        // Second claim should return Existing
        let decision2 = cluster
            .try_claim_local(actor_id.clone())
            .await
            .map_err(|e| CoreError::Internal {
                message: e.to_string(),
            })?;
        assert!(
            matches!(decision2, PlacementDecision::Existing(_)),
            "Second claim should return Existing"
        );

        cluster.stop().await.map_err(|e| CoreError::Internal {
            message: e.to_string(),
        })?;

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Node Failure Handling Tests
// =============================================================================

#[test]
fn test_dst_list_actors_on_failed_node() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register two nodes
        for i in 1..=2 {
            let node_id = test_node_id(i);
            let addr = test_addr(9000 + i as u16);
            let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
            node.status = NodeStatus::Active;
            registry.register_node(node).await.map_err(to_core_error)?;
        }

        // Place actors on node-1
        for i in 1..=5 {
            let actor_id = test_actor_id(i);
            registry
                .try_claim_actor(actor_id, test_node_id(1))
                .await
                .map_err(to_core_error)?;
        }

        // Mark node-1 as failed (must transition through Suspect first)
        registry
            .update_node_status(&test_node_id(1), NodeStatus::Suspect)
            .await
            .map_err(to_core_error)?;
        registry
            .update_node_status(&test_node_id(1), NodeStatus::Failed)
            .await
            .map_err(to_core_error)?;

        // List actors on failed node
        let actors = registry
            .list_actors_on_node(&test_node_id(1))
            .await
            .map_err(to_core_error)?;
        assert_eq!(actors.len(), 5, "Should still list actors on failed node");

        // Get failed nodes
        let failed = registry
            .list_nodes_by_status(NodeStatus::Failed)
            .await
            .map_err(to_core_error)?;
        assert_eq!(failed.len(), 1);
        assert_eq!(failed[0].id, test_node_id(1));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Migration State Tests
// =============================================================================

#[test]
fn test_dst_migration_state_machine() {
    // Test MigrationState transitions
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

// =============================================================================
// Fault Injection Tests
// =============================================================================

#[test]
fn test_dst_cluster_with_network_faults() {
    let config = SimConfig::new(42);

    // Run with network packet loss
    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.1))
        .run(|env| async move {
            let clock = Arc::new(TestClock::new(env.now_ms()));
            let registry = MemoryRegistry::with_clock(clock.clone());

            // Register nodes
            for i in 1..=3 {
                let node_id = test_node_id(i);
                let addr = test_addr(9000 + i as u16);
                let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
                node.status = NodeStatus::Active;
                registry.register_node(node).await.map_err(to_core_error)?;
            }

            // Perform operations despite faults
            for i in 1..=10 {
                let actor_id = test_actor_id(i);
                let _ = registry
                    .try_claim_actor(actor_id, test_node_id((i % 3) + 1))
                    .await;
            }

            // Registry should still be consistent
            let nodes = registry.list_nodes().await.map_err(to_core_error)?;
            assert_eq!(nodes.len(), 3, "All nodes should still be registered");

            Ok(())
        });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Determinism Tests
// =============================================================================

#[test]
fn test_dst_cluster_determinism() {
    let seed = 12345;

    let run_test = || {
        let config = SimConfig::new(seed);

        Simulation::new(config).run(|env| async move {
            let clock = Arc::new(TestClock::new(env.now_ms()));
            let registry = MemoryRegistry::with_clock(clock.clone());

            // Register nodes
            for i in 1..=3 {
                let node_id = test_node_id(i);
                let addr = test_addr(9000 + i as u16);
                let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
                node.status = NodeStatus::Active;
                node.actor_count = i as u64 * 10;
                node.actor_capacity = 100;
                registry.register_node(node).await.map_err(to_core_error)?;
            }

            // Place actors and collect placement results
            let mut placements = Vec::new();
            for i in 1..=10 {
                let actor_id = test_actor_id(i);
                let decision = registry
                    .try_claim_actor(actor_id.clone(), test_node_id(1))
                    .await
                    .map_err(to_core_error)?;

                if let PlacementDecision::New(node_id) = decision {
                    placements.push((actor_id.qualified_name(), node_id.to_string()));
                }
            }

            Ok(placements)
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(
        result1, result2,
        "Cluster operations should be deterministic with same seed"
    );
}

// =============================================================================
// Stress Tests (longer duration, marked as ignored for CI)
// =============================================================================

#[test]
#[ignore] // Run with: cargo test -p kelpie-dst -- --ignored
fn test_dst_cluster_stress_many_nodes() {
    let config = SimConfig::from_env_or_random().with_max_steps(1_000_000);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.02))
        .run(|env| async move {
            let clock = Arc::new(TestClock::new(env.now_ms()));
            let registry = MemoryRegistry::with_clock(clock.clone());

            // Register many nodes
            for i in 1..=50 {
                let node_id = test_node_id(i);
                let addr = test_addr(9000 + i as u16);
                let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
                node.status = NodeStatus::Active;
                node.actor_capacity = 1000;
                registry.register_node(node).await.map_err(to_core_error)?;
            }

            // Place many actors
            for i in 1..=500 {
                let actor_id = test_actor_id(i);
                let target_node = test_node_id((i % 50) + 1);
                let _ = registry.try_claim_actor(actor_id, target_node).await;
            }

            // Verify counts
            let nodes = registry.list_nodes().await.map_err(to_core_error)?;
            assert_eq!(nodes.len(), 50, "All nodes should be registered");

            Ok(())
        });

    assert!(result.is_ok(), "Stress test failed: {:?}", result.err());
}

#[test]
#[ignore] // Run with: cargo test -p kelpie-dst -- --ignored
fn test_dst_cluster_stress_migrations() {
    let config = SimConfig::from_env_or_random().with_max_steps(1_000_000);

    let result = Simulation::new(config).run(|env| async move {
        let clock = Arc::new(TestClock::new(env.now_ms()));
        let registry = MemoryRegistry::with_clock(clock.clone());

        // Register nodes
        for i in 1..=10 {
            let node_id = test_node_id(i);
            let addr = test_addr(9000 + i as u16);
            let mut node = NodeInfo::with_timestamp(node_id.clone(), addr, clock.now_ms());
            node.status = NodeStatus::Active;
            registry.register_node(node).await.map_err(to_core_error)?;
        }

        // Place actors
        for i in 1..=100 {
            let actor_id = test_actor_id(i);
            registry
                .try_claim_actor(actor_id, test_node_id((i % 10) + 1))
                .await
                .map_err(to_core_error)?;
        }

        // Perform many migrations
        for i in 1..=100 {
            let actor_id = test_actor_id(i);
            let from_node = test_node_id((i % 10) + 1);
            let to_node = test_node_id(((i + 1) % 10) + 1);

            let _ = registry
                .migrate_actor(&actor_id, &from_node, &to_node)
                .await;
        }

        // Verify all actors still exist
        for i in 1..=100 {
            let actor_id = test_actor_id(i);
            let placement = registry
                .get_placement(&actor_id)
                .await
                .map_err(to_core_error)?;
            assert!(placement.is_some(), "Actor {} should have placement", i);
        }

        Ok(())
    });

    assert!(result.is_ok(), "Stress test failed: {:?}", result.err());
}

//! DST tests for SingleActivation invariant using PRODUCTION code
//!
//! TigerStyle: Tests production MemoryRegistry under simulated time and faults.
//!
//! This module tests the single activation guarantee using the REAL MemoryRegistry
//! implementation instead of mocks. This catches bugs in the actual registry code
//! that mock-based tests would miss.
//!
//! Key differences from single_activation_dst.rs:
//! - Uses production `MemoryRegistry` from kelpie-registry
//! - Uses DST clock injection via `with_providers()`
//! - Tests the REAL OCC semantics, not a simplified simulation
//!
//! TLA+ Spec Reference: `docs/tla/KelpieSingleActivation.tla`

use futures::future::join_all;
use kelpie_core::actor::ActorId;
use kelpie_core::io::TimeProvider;
use kelpie_core::Runtime;
use kelpie_dst::{DeterministicRng, SimConfig, Simulation};
use kelpie_registry::{
    MemoryRegistry, NodeId, NodeInfo, NodeStatus, PlacementContext, PlacementDecision,
    PlacementStrategy, Registry,
};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::sync::Arc;

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
    ActorId::new("test", format!("actor-{}", n)).unwrap()
}

fn test_node_info(n: u32) -> NodeInfo {
    let mut info = NodeInfo::new(test_node_id(n), test_addr(8080 + n as u16));
    info.status = NodeStatus::Active;
    info
}

/// Create a MemoryRegistry with DST-compatible I/O providers
fn create_registry_with_clock(clock: Arc<dyn TimeProvider>) -> MemoryRegistry {
    // Use DST clock and deterministic RNG for full DST compatibility
    let rng = Arc::new(DeterministicRng::new(42));
    MemoryRegistry::with_providers(clock, rng)
}

/// Register N nodes in the registry
async fn setup_nodes(registry: &MemoryRegistry, count: u32) {
    for i in 0..count {
        let info = test_node_info(i);
        registry.register_node(info).await.unwrap();
    }
}

// =============================================================================
// Production SingleActivation Invariant Tests
// =============================================================================

/// Test concurrent activation: exactly 1 winner using PRODUCTION code
///
/// TLA+ Invariant: At most one node can claim an actor at any time.
#[test]
fn test_production_concurrent_activation_single_winner() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(
        seed = config.seed,
        "Running Production SingleActivation test"
    );

    let result = Simulation::new(config).run(|env| async move {
        // Create production registry with simulated clock
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // Setup nodes
        let num_nodes = 5;
        setup_nodes(&registry, num_nodes).await;

        // Target actor for concurrent claims
        let actor_id = test_actor_id(1);

        // Spawn N concurrent activation attempts for the SAME actor
        let handles: Vec<_> = (0..num_nodes)
            .map(|node_num| {
                let registry = registry.clone();
                let actor_id = actor_id.clone();
                let node_id = test_node_id(node_num);
                kelpie_core::current_runtime()
                    .spawn(async move { registry.try_claim_actor(actor_id, node_id).await })
            })
            .collect();

        // Wait for all attempts to complete
        let results: Vec<_> = join_all(handles)
            .await
            .into_iter()
            .map(|r| r.expect("task panicked"))
            .collect();

        // Count successful claims (PlacementDecision::New means we won)
        let successes: Vec<_> = results
            .iter()
            .enumerate()
            .filter_map(|(i, r)| match r {
                Ok(PlacementDecision::New(_)) => Some(format!("node-{}", i)),
                _ => None,
            })
            .collect();

        // TLA+ INVARIANT: SingleActivation - at most 1 succeeds
        assert!(
            successes.len() <= 1,
            "SingleActivation VIOLATED (production): {} activations succeeded. \
             Winners: {:?}",
            successes.len(),
            successes
        );

        // With correct implementation, exactly 1 should succeed
        assert_eq!(
            successes.len(),
            1,
            "Expected exactly 1 activation, got {}. Results: {:?}",
            successes.len(),
            results
        );

        // Verify the winner is reflected in registry state
        let placement = registry
            .get_placement(&test_actor_id(1))
            .await
            .expect("get_placement should not fail");
        assert!(
            placement.is_some(),
            "Winner should have placement in registry"
        );

        tracing::info!(
            winner = ?successes.first(),
            "Production SingleActivation test passed"
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test high contention with production registry
#[test]
fn test_production_concurrent_activation_high_contention() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(
        seed = config.seed,
        "Running high contention production test"
    );

    let result = Simulation::new(config).run(|env| async move {
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // More nodes for higher contention
        let num_nodes = 20;
        setup_nodes(&registry, num_nodes).await;

        let actor_id = test_actor_id(99);

        let handles: Vec<_> = (0..num_nodes)
            .map(|node_num| {
                let registry = registry.clone();
                let actor_id = actor_id.clone();
                let node_id = test_node_id(node_num);
                kelpie_core::current_runtime()
                    .spawn(async move { registry.try_claim_actor(actor_id, node_id).await })
            })
            .collect();

        let results: Vec<_> = join_all(handles)
            .await
            .into_iter()
            .map(|r| r.expect("task panicked"))
            .collect();

        let successes = results
            .iter()
            .filter(|r| matches!(r, Ok(PlacementDecision::New(_))))
            .count();

        // TLA+ INVARIANT: SingleActivation
        assert!(
            successes <= 1,
            "SingleActivation VIOLATED: {} activations succeeded (expected <= 1)",
            successes
        );

        assert_eq!(
            successes, 1,
            "Expected exactly 1 success, got {}",
            successes
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Determinism Tests
// =============================================================================

/// Test that same seed produces same winner with production code
#[test]
fn test_production_single_activation_deterministic() {
    let seed = 12345_u64;

    let run_test = || {
        let config = SimConfig::new(seed);

        Simulation::new(config).run(|env| async move {
            let registry = Arc::new(create_registry_with_clock(env.clock.clone()));
            let num_nodes = 5;
            setup_nodes(&registry, num_nodes).await;

            let actor_id = test_actor_id(42);

            let handles: Vec<_> = (0..num_nodes)
                .map(|node_num| {
                    let registry = registry.clone();
                    let actor_id = actor_id.clone();
                    let node_id = test_node_id(node_num);
                    kelpie_core::current_runtime().spawn(async move {
                        let result = registry.try_claim_actor(actor_id, node_id.clone()).await;
                        let won = matches!(result, Ok(PlacementDecision::New(_)));
                        (node_id.to_string(), won)
                    })
                })
                .collect();

            let results: Vec<_> = join_all(handles)
                .await
                .into_iter()
                .map(|r| r.expect("task panicked"))
                .collect();

            // Find the winner
            let winner: Option<String> = results
                .iter()
                .find(|(_, won)| *won)
                .map(|(name, _)| name.clone());

            Ok(winner)
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(
        result1, result2,
        "Production determinism violated: winner differs with same seed. \
         Run 1: {:?}, Run 2: {:?}",
        result1, result2
    );
}

// =============================================================================
// Release and Re-activation Tests
// =============================================================================

/// Test that after unregister, a new activation can succeed
#[test]
fn test_production_release_and_reactivation() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // Setup 2 nodes
        setup_nodes(&registry, 2).await;

        let actor_id = test_actor_id(1);

        // Node 0 claims
        let claim1 = registry
            .try_claim_actor(actor_id.clone(), test_node_id(0))
            .await
            .expect("try_claim should not fail");
        assert!(
            matches!(claim1, PlacementDecision::New(_)),
            "First claim should succeed as New"
        );

        // Node 1 cannot claim while node 0 holds
        let claim2 = registry
            .try_claim_actor(actor_id.clone(), test_node_id(1))
            .await
            .expect("try_claim should not fail");
        assert!(
            matches!(claim2, PlacementDecision::Existing(_)),
            "Second claim should return Existing (held by node-0)"
        );

        // Node 0 releases (unregister actor)
        registry
            .unregister_actor(&actor_id)
            .await
            .expect("unregister should not fail");

        // Now node 1 can claim
        let claim3 = registry
            .try_claim_actor(actor_id.clone(), test_node_id(1))
            .await
            .expect("try_claim should not fail");
        assert!(
            matches!(claim3, PlacementDecision::New(_)),
            "Claim after release should succeed as New"
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test concurrent claims during release window
#[test]
fn test_production_concurrent_activation_during_release() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // Setup nodes
        let num_recovery_nodes = 5;
        setup_nodes(&registry, num_recovery_nodes + 1).await;

        let actor_id = test_actor_id(1);

        // Node 0 claims
        let initial = registry
            .try_claim_actor(actor_id.clone(), test_node_id(0))
            .await
            .expect("try_claim should not fail");
        assert!(matches!(initial, PlacementDecision::New(_)));

        // Node 0 releases
        registry
            .unregister_actor(&actor_id)
            .await
            .expect("unregister should not fail");

        // Multiple nodes race to claim the now-free actor
        let handles: Vec<_> = (1..=num_recovery_nodes)
            .map(|node_num| {
                let registry = registry.clone();
                let actor_id = actor_id.clone();
                let node_id = test_node_id(node_num);
                kelpie_core::current_runtime()
                    .spawn(async move { registry.try_claim_actor(actor_id, node_id).await })
            })
            .collect();

        let results: Vec<_> = join_all(handles)
            .await
            .into_iter()
            .map(|r| r.expect("task panicked"))
            .collect();

        let successes = results
            .iter()
            .filter(|r| matches!(r, Ok(PlacementDecision::New(_))))
            .count();

        // TLA+ INVARIANT: Exactly 1 succeeds
        assert_eq!(
            successes, 1,
            "SingleActivation VIOLATED: {} succeeded (expected 1)",
            successes
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Placement Strategy Tests (Production-specific)
// =============================================================================

/// Test placement strategies work correctly under concurrent claims
#[test]
fn test_production_placement_strategies() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // Setup 3 nodes
        setup_nodes(&registry, 3).await;

        // Test different strategies for different actors
        let strategies = vec![
            (test_actor_id(1), PlacementStrategy::LeastLoaded),
            (test_actor_id(2), PlacementStrategy::RoundRobin),
            (test_actor_id(3), PlacementStrategy::Random),
        ];

        for (actor_id, strategy) in strategies {
            let context = PlacementContext::new(actor_id.clone()).with_strategy(strategy);

            let decision = registry
                .select_node_for_placement(context)
                .await
                .expect("select_node should not fail");

            match decision {
                PlacementDecision::New(node_id) => {
                    // Verify we can actually claim it
                    let claim = registry
                        .try_claim_actor(actor_id.clone(), node_id)
                        .await
                        .expect("try_claim should not fail");
                    assert!(
                        matches!(claim, PlacementDecision::New(_)),
                        "Claim on selected node should succeed"
                    );
                }
                PlacementDecision::NoCapacity => {
                    panic!("Should have capacity with empty nodes");
                }
                PlacementDecision::Existing(_) => {
                    panic!("Actor should not exist yet");
                }
            }
        }

        // Verify all 3 actors are placed
        for i in 1..=3 {
            let placement = registry
                .get_placement(&test_actor_id(i))
                .await
                .expect("get_placement should not fail");
            assert!(placement.is_some(), "Actor {} should be placed", i);
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Crash Recovery Tests
// =============================================================================

/// Test single activation with crash and recovery using production code
#[test]
fn test_production_single_activation_with_crash_recovery() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(seed = config.seed, "Running production crash recovery test");

    let result = Simulation::new(config).run(|env| async move {
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // Setup nodes
        setup_nodes(&registry, 4).await;

        let actor_id = test_actor_id(1);

        // Step 1: Node 0 activates
        let claim_a = registry
            .try_claim_actor(actor_id.clone(), test_node_id(0))
            .await
            .expect("try_claim should not fail");
        assert!(
            matches!(claim_a, PlacementDecision::New(_)),
            "Initial activation should succeed"
        );

        // Verify node 0 holds the actor
        let placement = registry
            .get_placement(&actor_id)
            .await
            .expect("get_placement should not fail");
        assert_eq!(placement.unwrap().node_id, test_node_id(0));

        // Step 2: Simulate node 0 crash (release via unregister)
        registry
            .unregister_actor(&actor_id)
            .await
            .expect("unregister should not fail");

        // Step 3: Multiple nodes race to reclaim after crash
        let handles: Vec<_> = (1..=3)
            .map(|node_num| {
                let registry = registry.clone();
                let actor_id = actor_id.clone();
                let node_id = test_node_id(node_num);
                kelpie_core::current_runtime()
                    .spawn(async move { registry.try_claim_actor(actor_id, node_id).await })
            })
            .collect();

        let results: Vec<_> = join_all(handles)
            .await
            .into_iter()
            .map(|r| r.expect("task panicked"))
            .collect();

        // TLA+ INVARIANT: SingleActivation - exactly 1 recovery succeeds
        let successes = results
            .iter()
            .filter(|r| matches!(r, Ok(PlacementDecision::New(_))))
            .count();

        assert_eq!(
            successes, 1,
            "SingleActivation VIOLATED during crash recovery: {} activations succeeded. \
             Expected exactly 1 node to take over after crash.",
            successes
        );

        // Verify the new holder is one of the recovery nodes (not node-0)
        let placement = registry
            .get_placement(&actor_id)
            .await
            .expect("get_placement should not fail");
        let new_holder = placement.unwrap().node_id;
        assert!(
            new_holder != test_node_id(0),
            "Recovery holder should NOT be crashed node-0, got {:?}",
            new_holder
        );

        tracing::info!(
            new_holder = %new_holder,
            "Production SingleActivation held through crash recovery"
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Node Capacity Tests (Production-specific)
// =============================================================================

/// Test that NoCapacity is returned when all nodes are at capacity
#[test]
fn test_production_no_capacity_handling() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let registry = Arc::new(create_registry_with_clock(env.clock.clone()));

        // Create node at capacity
        let mut full_node = test_node_info(0);
        full_node.actor_capacity = 100;
        full_node.actor_count = 100; // At capacity!
        registry
            .register_node(full_node)
            .await
            .expect("register_node should not fail");

        let actor_id = test_actor_id(1);

        // Try to claim - should get NoCapacity since only node is full
        let result = registry
            .try_claim_actor(actor_id.clone(), test_node_id(0))
            .await
            .expect("try_claim should not fail");

        assert!(
            matches!(result, PlacementDecision::NoCapacity),
            "Should return NoCapacity when node is full, got {:?}",
            result
        );

        // Add a node with capacity (use node-1 to avoid duplicate)
        let info1 = test_node_info(1);
        registry
            .register_node(info1)
            .await
            .expect("register_node should not fail");

        // Now claim should succeed on the new node
        let result2 = registry
            .try_claim_actor(actor_id.clone(), test_node_id(1))
            .await
            .expect("try_claim should not fail");

        assert!(
            matches!(result2, PlacementDecision::New(_)),
            "Should succeed on node with capacity"
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Stress Tests
// =============================================================================

/// Stress test: many iterations with random seeds using production code
///
/// Run with: cargo test -p kelpie-dst single_activation_production_stress -- --ignored
#[test]
#[ignore]
fn test_production_single_activation_stress() {
    const NUM_ITERATIONS: usize = 500;
    const NUM_NODES: u32 = 10;

    let mut violations = Vec::new();

    for iteration in 0..NUM_ITERATIONS {
        let seed = 0xCAFE_BEEF_u64.wrapping_add(iteration as u64);
        let config = SimConfig::new(seed);

        let result = Simulation::new(config).run(|env| async move {
            let registry = Arc::new(create_registry_with_clock(env.clock.clone()));
            setup_nodes(&registry, NUM_NODES).await;

            let actor_id = ActorId::new("test", format!("stress-{}", iteration))?;

            let handles: Vec<_> = (0..NUM_NODES)
                .map(|node_num| {
                    let registry = registry.clone();
                    let actor_id = actor_id.clone();
                    let node_id = test_node_id(node_num);
                    kelpie_core::current_runtime()
                        .spawn(async move { registry.try_claim_actor(actor_id, node_id).await })
                })
                .collect();

            let results: Vec<_> = join_all(handles)
                .await
                .into_iter()
                .map(|r| r.expect("task panicked"))
                .collect();

            let successes = results
                .iter()
                .filter(|r| matches!(r, Ok(PlacementDecision::New(_))))
                .count();

            Ok(successes)
        });

        match result {
            Ok(successes) if successes != 1 => {
                violations.push((seed, successes));
            }
            Err(e) => {
                violations.push((seed, 0));
                tracing::error!(seed = seed, error = ?e, "Iteration failed");
            }
            _ => {}
        }

        if (iteration + 1) % 100 == 0 {
            println!(
                "Progress: {}/{} iterations, {} violations",
                iteration + 1,
                NUM_ITERATIONS,
                violations.len()
            );
        }
    }

    if !violations.is_empty() {
        for (seed, count) in &violations {
            println!(
                "VIOLATION: seed={} had {} successes (expected 1)",
                seed, count
            );
        }
        panic!(
            "Production SingleActivation stress test found {} violations in {} iterations",
            violations.len(),
            NUM_ITERATIONS
        );
    }

    println!(
        "Production SingleActivation stress test PASSED: {} iterations, 0 violations",
        NUM_ITERATIONS
    );
}

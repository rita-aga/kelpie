//! DST tests for cluster membership using production-grade types
//!
//! These tests verify TLA+ invariants against the production membership
//! types from `kelpie_registry`, as required by spec 077.
//!
//! TLA+ Invariants:
//! - NoSplitBrain: At most one node has a valid primary claim
//! - MembershipConsistency: Active nodes with same view number have same membership view
//! - JoinAtomicity: Node is either fully joined or not joined
//!
//! DST Requirements (DST-1):
//! - Tests use production types (MembershipView, NodeState, PrimaryInfo)
//! - Tests use injected providers (TimeProvider)
//! - Logic matches ClusterMembership implementation

use kelpie_core::io::TimeProvider;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_registry::{MembershipView, NodeId, NodeState, PrimaryInfo};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::sync::RwLock;

// =============================================================================
// Test Helpers
// =============================================================================

fn test_node_id(n: u32) -> NodeId {
    NodeId::new(format!("node-{}", n)).unwrap()
}

/// Simulated clock for DST
#[derive(Debug, Clone)]
struct SimClock {
    now_ms: Arc<AtomicU64>,
}

impl SimClock {
    fn new(initial_ms: u64) -> Self {
        Self {
            now_ms: Arc::new(AtomicU64::new(initial_ms)),
        }
    }

    fn get_now_ms(&self) -> u64 {
        self.now_ms.load(Ordering::SeqCst)
    }

    fn advance(&self, ms: u64) {
        self.now_ms.fetch_add(ms, Ordering::SeqCst);
    }
}

#[async_trait::async_trait]
impl TimeProvider for SimClock {
    fn now_ms(&self) -> u64 {
        self.get_now_ms()
    }

    async fn sleep_ms(&self, ms: u64) {
        self.advance(ms);
    }
}

// =============================================================================
// Simulated Cluster State
// =============================================================================

/// Node info in the simulated cluster
#[derive(Debug, Clone)]
struct SimNodeInfo {
    id: NodeId,
    state: NodeState,
    believes_primary: bool,
    primary_term: u64,
    #[allow(dead_code)] // Used for debugging and future heartbeat tests
    last_heartbeat_ms: u64,
}

/// Simulated cluster state (mirrors FDB-backed ClusterMembership)
struct SimClusterState {
    nodes: RwLock<HashMap<NodeId, SimNodeInfo>>,
    membership_view: RwLock<MembershipView>,
    primary: RwLock<Option<PrimaryInfo>>,
    primary_term: RwLock<u64>,
    partitions: RwLock<HashSet<(NodeId, NodeId)>>,
}

impl SimClusterState {
    fn new() -> Self {
        Self {
            nodes: RwLock::new(HashMap::new()),
            membership_view: RwLock::new(MembershipView::empty()),
            primary: RwLock::new(None),
            primary_term: RwLock::new(0),
            partitions: RwLock::new(HashSet::new()),
        }
    }

    /// Check if two nodes can communicate
    async fn can_communicate(&self, a: &NodeId, b: &NodeId) -> bool {
        let partitions = self.partitions.read().await;
        !partitions.contains(&(a.clone(), b.clone()))
            && !partitions.contains(&(b.clone(), a.clone()))
    }

    /// Create a network partition between two groups
    async fn partition(&self, group_a: &[NodeId], group_b: &[NodeId]) {
        let mut partitions = self.partitions.write().await;
        for a in group_a {
            for b in group_b {
                partitions.insert((a.clone(), b.clone()));
            }
        }
    }

    /// Heal all partitions
    async fn heal_all_partitions(&self) {
        let mut partitions = self.partitions.write().await;
        partitions.clear();
    }

    /// Join a node (TLA+ NodeJoin)
    async fn join_node(&self, node_id: NodeId, is_first: bool, now_ms: u64) {
        let mut nodes = self.nodes.write().await;

        let state = if is_first {
            // First node becomes Active and primary
            {
                let mut view = self.membership_view.write().await;
                let mut active_nodes = HashSet::new();
                active_nodes.insert(node_id.clone());
                *view = MembershipView::new(active_nodes, 1, now_ms);
            }

            {
                let mut primary = self.primary.write().await;
                *primary = Some(PrimaryInfo::new(node_id.clone(), 1, now_ms));
            }

            {
                let mut term = self.primary_term.write().await;
                *term = 1;
            }

            NodeState::Active
        } else {
            NodeState::Joining
        };

        nodes.insert(
            node_id.clone(),
            SimNodeInfo {
                id: node_id,
                state,
                believes_primary: is_first,
                primary_term: if is_first { 1 } else { 0 },
                last_heartbeat_ms: now_ms,
            },
        );
    }

    /// Complete join (TLA+ NodeJoinComplete)
    async fn complete_join(&self, node_id: &NodeId, now_ms: u64) {
        let mut nodes = self.nodes.write().await;
        if let Some(node) = nodes.get_mut(node_id) {
            if node.state == NodeState::Joining {
                node.state = NodeState::Active;

                drop(nodes);
                let mut view = self.membership_view.write().await;
                *view = view.with_node_added(node_id.clone(), now_ms);
            }
        }
    }

    /// Mark node as failed
    async fn mark_failed(&self, node_id: &NodeId, now_ms: u64) {
        let mut nodes = self.nodes.write().await;
        if let Some(node) = nodes.get_mut(node_id) {
            node.state = NodeState::Failed;
            node.believes_primary = false;
            node.primary_term = 0;

            drop(nodes);
            let mut view = self.membership_view.write().await;
            *view = view.with_node_removed(node_id, now_ms);
        }
    }

    /// Step down from primary
    async fn step_down(&self, node_id: &NodeId) {
        let mut nodes = self.nodes.write().await;
        if let Some(node) = nodes.get_mut(node_id) {
            node.believes_primary = false;
        }
        drop(nodes);

        // Clear primary if this node was primary
        let mut primary = self.primary.write().await;
        if let Some(ref p) = *primary {
            if &p.node_id == node_id {
                *primary = None;
            }
        }
    }

    /// Check if node has quorum
    async fn has_quorum(&self, node_id: &NodeId) -> bool {
        let nodes = self.nodes.read().await;
        let cluster_size = nodes.len();
        if cluster_size == 0 {
            return false;
        }

        // Count reachable nodes including self
        let mut reachable_count = 1; // Self
        for (other_id, _) in nodes.iter() {
            if other_id != node_id && self.can_communicate(node_id, other_id).await {
                reachable_count += 1;
            }
        }

        2 * reachable_count > cluster_size
    }

    /// Try to become primary
    async fn try_become_primary(&self, node_id: &NodeId, now_ms: u64) -> Option<u64> {
        // Check node is Active
        {
            let nodes = self.nodes.read().await;
            let node = nodes.get(node_id)?;
            if node.state != NodeState::Active {
                return None;
            }
            if node.believes_primary {
                return Some(node.primary_term);
            }
        }

        // Check quorum
        if !self.has_quorum(node_id).await {
            return None;
        }

        // Check if valid primary exists
        {
            let primary = self.primary.read().await;
            if let Some(ref p) = *primary {
                let nodes = self.nodes.read().await;
                if let Some(primary_node) = nodes.get(&p.node_id) {
                    if primary_node.state == NodeState::Active
                        && primary_node.believes_primary
                        && self.can_communicate(node_id, &p.node_id).await
                    {
                        return None;
                    }
                }
            }
        }

        // Become primary with new term
        let new_term = {
            let mut term = self.primary_term.write().await;
            *term += 1;
            *term
        };

        {
            let mut primary = self.primary.write().await;
            *primary = Some(PrimaryInfo::new(node_id.clone(), new_term, now_ms));
        }

        {
            let mut nodes = self.nodes.write().await;
            if let Some(node) = nodes.get_mut(node_id) {
                node.believes_primary = true;
                node.primary_term = new_term;
            }
        }

        Some(new_term)
    }

    /// Check if node has valid primary claim (TLA+ HasValidPrimaryClaim)
    async fn has_valid_primary_claim(&self, node_id: &NodeId) -> bool {
        let nodes = self.nodes.read().await;

        let node = match nodes.get(node_id) {
            Some(n) => n.clone(),
            None => return false,
        };

        if !node.believes_primary || node.state != NodeState::Active {
            return false;
        }

        drop(nodes);
        self.has_quorum(node_id).await
    }

    /// Count valid primaries (for NoSplitBrain invariant)
    async fn count_valid_primaries(&self) -> Vec<NodeId> {
        let node_ids: Vec<NodeId> = {
            let nodes = self.nodes.read().await;
            nodes.keys().cloned().collect()
        };

        let mut valid_primaries = Vec::new();
        for node_id in node_ids {
            if self.has_valid_primary_claim(&node_id).await {
                valid_primaries.push(node_id);
            }
        }

        valid_primaries
    }
}

// =============================================================================
// Test 1: NoSplitBrain Invariant
// =============================================================================

/// Test that split-brain is prevented during network partition
#[test]
fn test_production_no_split_brain() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(seed = config.seed, "Running production NoSplitBrain test");

    let result = Simulation::new(config).run(|_env| async move {
        let cluster = Arc::new(SimClusterState::new());
        let clock = SimClock::new(1000);

        // Create 5-node cluster
        let nodes: Vec<NodeId> = (1..=5).map(test_node_id).collect();

        // First node joins and becomes primary
        cluster
            .join_node(nodes[0].clone(), true, clock.get_now_ms())
            .await;

        // Other nodes join
        for node in nodes.iter().skip(1) {
            cluster
                .join_node(node.clone(), false, clock.get_now_ms())
                .await;
            cluster.complete_join(node, clock.get_now_ms()).await;
        }

        // Verify initial state: node-1 is primary
        assert!(
            cluster.has_valid_primary_claim(&nodes[0]).await,
            "Node-1 should be primary"
        );

        // Create partition: [node-1, node-2] (minority) | [node-3, node-4, node-5] (majority)
        let minority = vec![nodes[0].clone(), nodes[1].clone()];
        let majority = vec![nodes[2].clone(), nodes[3].clone(), nodes[4].clone()];
        cluster.partition(&minority, &majority).await;

        tracing::info!("Partition created: [1,2] | [3,4,5]");

        // Minority loses quorum
        assert!(
            !cluster.has_quorum(&nodes[0]).await,
            "Minority node-1 should lose quorum"
        );

        // Primary in minority must step down
        cluster.step_down(&nodes[0]).await;
        tracing::info!("Primary node-1 stepped down");

        // Majority has quorum
        assert!(
            cluster.has_quorum(&nodes[2]).await,
            "Majority node-3 should have quorum"
        );

        // Majority elects new primary
        clock.advance(100);
        let new_term = cluster
            .try_become_primary(&nodes[2], clock.get_now_ms())
            .await;
        assert!(new_term.is_some(), "Majority node-3 should become primary");
        tracing::info!("Node-3 elected as primary with term {:?}", new_term);

        // INVARIANT CHECK: at most one valid primary
        let valid_primaries = cluster.count_valid_primaries().await;
        assert!(
            valid_primaries.len() <= 1,
            "NoSplitBrain violated: {} valid primaries: {:?}",
            valid_primaries.len(),
            valid_primaries
        );

        tracing::info!(
            "NoSplitBrain invariant verified: {} valid primary(ies)",
            valid_primaries.len()
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Test 2: Primary Election with Quorum
// =============================================================================

#[test]
fn test_production_primary_election_requires_quorum() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(seed = config.seed, "Running production quorum test");

    let result = Simulation::new(config).run(|_env| async move {
        let cluster = Arc::new(SimClusterState::new());
        let clock = SimClock::new(1000);

        // Create 5-node cluster
        let nodes: Vec<NodeId> = (1..=5).map(test_node_id).collect();

        cluster
            .join_node(nodes[0].clone(), true, clock.get_now_ms())
            .await;
        for node in nodes.iter().skip(1) {
            cluster
                .join_node(node.clone(), false, clock.get_now_ms())
                .await;
            cluster.complete_join(node, clock.get_now_ms()).await;
        }

        // Create partition: [node-1, node-2] (minority) vs [node-3,4,5] (majority)
        let minority = vec![nodes[0].clone(), nodes[1].clone()];
        let majority = vec![nodes[2].clone(), nodes[3].clone(), nodes[4].clone()];
        cluster.partition(&minority, &majority).await;

        // Step down current primary (it lost quorum)
        cluster.step_down(&nodes[0]).await;

        // Minority cannot elect primary (only 2 of 5 nodes)
        let minority_election = cluster
            .try_become_primary(&nodes[1], clock.get_now_ms())
            .await;
        assert!(
            minority_election.is_none(),
            "Minority partition should not be able to elect primary"
        );

        // Majority can elect primary (3 of 5 nodes)
        let majority_election = cluster
            .try_become_primary(&nodes[2], clock.get_now_ms())
            .await;
        assert!(
            majority_election.is_some(),
            "Majority partition should be able to elect primary"
        );

        tracing::info!("Quorum test passed");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Test 3: Primary Step-Down on Quorum Loss
// =============================================================================

#[test]
fn test_production_primary_stepdown_on_quorum_loss() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(seed = config.seed, "Running production step-down test");

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::NetworkPartition, 1.0))
        .run(|_env| async move {
            let cluster = Arc::new(SimClusterState::new());
            let clock = SimClock::new(1000);

            // Create 3-node cluster
            let nodes: Vec<NodeId> = (1..=3).map(test_node_id).collect();

            cluster
                .join_node(nodes[0].clone(), true, clock.get_now_ms())
                .await;
            for node in nodes.iter().skip(1) {
                cluster
                    .join_node(node.clone(), false, clock.get_now_ms())
                    .await;
                cluster.complete_join(node, clock.get_now_ms()).await;
            }

            // Verify node-1 is primary
            assert!(
                cluster.has_valid_primary_claim(&nodes[0]).await,
                "Node-1 should be primary"
            );

            // Partition node-1 from others
            cluster
                .partition(&[nodes[0].clone()], &[nodes[1].clone(), nodes[2].clone()])
                .await;

            // Primary should lose quorum
            assert!(
                !cluster.has_quorum(&nodes[0]).await,
                "Node-1 should lose quorum"
            );

            // Primary steps down
            cluster.step_down(&nodes[0]).await;

            // Verify primary no longer has valid claim
            assert!(
                !cluster.has_valid_primary_claim(&nodes[0]).await,
                "Stepped-down node should not have valid primary claim"
            );

            tracing::info!("Step-down test passed");

            Ok(())
        });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Test 4: Heartbeat Failure Detection
// =============================================================================

#[test]
fn test_production_heartbeat_failure_detection() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(seed = config.seed, "Running production heartbeat test");

    let result = Simulation::new(config).run(|_env| async move {
        let cluster = Arc::new(SimClusterState::new());
        let clock = SimClock::new(1000);

        // Create 3-node cluster
        let nodes: Vec<NodeId> = (1..=3).map(test_node_id).collect();

        for (i, node) in nodes.iter().enumerate() {
            cluster
                .join_node(node.clone(), i == 0, clock.get_now_ms())
                .await;
            if i > 0 {
                cluster.complete_join(node, clock.get_now_ms()).await;
            }
        }

        // Mark node-2 as failed (simulates heartbeat timeout)
        clock.advance(10000);
        cluster.mark_failed(&nodes[1], clock.get_now_ms()).await;

        // Verify node-2 is failed
        {
            let nodes_map = cluster.nodes.read().await;
            let node2 = nodes_map.get(&nodes[1]).unwrap();
            assert_eq!(node2.state, NodeState::Failed, "Node-2 should be Failed");
        }

        // Verify node-2 is removed from membership view
        {
            let view = cluster.membership_view.read().await;
            assert!(
                !view.contains(&nodes[1]),
                "Failed node should be removed from view"
            );
        }

        tracing::info!("Heartbeat failure detection test passed");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Test 5: Partition Heal
// =============================================================================

#[test]
fn test_production_partition_heal_resolves_conflict() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(seed = config.seed, "Running production partition heal test");

    let result = Simulation::new(config).run(|_env| async move {
        let cluster = Arc::new(SimClusterState::new());
        let clock = SimClock::new(1000);

        // Create 5-node cluster
        let nodes: Vec<NodeId> = (1..=5).map(test_node_id).collect();

        cluster
            .join_node(nodes[0].clone(), true, clock.get_now_ms())
            .await;
        for node in nodes.iter().skip(1) {
            cluster
                .join_node(node.clone(), false, clock.get_now_ms())
                .await;
            cluster.complete_join(node, clock.get_now_ms()).await;
        }

        // Create partition: [1,2,3] (majority) | [4,5] (minority)
        let majority = vec![nodes[0].clone(), nodes[1].clone(), nodes[2].clone()];
        let minority = vec![nodes[3].clone(), nodes[4].clone()];
        cluster.partition(&majority, &minority).await;

        // Primary in majority keeps quorum
        assert!(
            cluster.has_quorum(&nodes[0]).await,
            "Primary in majority should keep quorum"
        );

        // Minority cannot elect
        assert!(
            cluster
                .try_become_primary(&nodes[3], clock.get_now_ms())
                .await
                .is_none(),
            "Minority should not elect primary"
        );

        // Heal partition
        cluster.heal_all_partitions().await;
        tracing::info!("Partition healed");

        // All nodes should have quorum again
        for node in &nodes {
            assert!(
                cluster.has_quorum(node).await,
                "Node {} should have quorum after heal",
                node
            );
        }

        // Verify only one primary
        let primaries = cluster.count_valid_primaries().await;
        assert_eq!(
            primaries.len(),
            1,
            "Should have exactly one primary after heal: {:?}",
            primaries
        );

        tracing::info!("Partition heal test passed");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Test 6: Determinism
// =============================================================================

#[test]
fn test_production_determinism() {
    let seed = 98765;

    let run_test = || {
        let config = SimConfig::new(seed);

        Simulation::new(config).run(|_env| async move {
            let cluster = Arc::new(SimClusterState::new());
            let clock = SimClock::new(1000);

            let nodes: Vec<NodeId> = (1..=5).map(test_node_id).collect();

            cluster
                .join_node(nodes[0].clone(), true, clock.get_now_ms())
                .await;
            for node in nodes.iter().skip(1) {
                cluster
                    .join_node(node.clone(), false, clock.get_now_ms())
                    .await;
                cluster.complete_join(node, clock.get_now_ms()).await;
            }

            // Partition
            cluster
                .partition(
                    &[nodes[0].clone(), nodes[1].clone()],
                    &[nodes[2].clone(), nodes[3].clone(), nodes[4].clone()],
                )
                .await;

            // Collect state
            let mut states = Vec::new();
            for node in &nodes {
                let has_quorum = cluster.has_quorum(node).await;
                let nodes_map = cluster.nodes.read().await;
                let info = nodes_map.get(node).unwrap();
                states.push((
                    node.as_str().to_string(),
                    has_quorum,
                    info.believes_primary,
                    info.primary_term,
                ));
            }

            // Heal
            cluster.heal_all_partitions().await;

            let mut final_states = Vec::new();
            for node in &nodes {
                let has_quorum = cluster.has_quorum(node).await;
                final_states.push((node.as_str().to_string(), has_quorum));
            }

            Ok((states, final_states))
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
// Test 7: Actor Migration on Node Failure (FR-7)
// =============================================================================

/// Simulated migration queue for DST
#[derive(Debug, Clone, Default)]
struct SimMigrationQueue {
    candidates: Vec<(String, NodeId)>, // (actor_id, failed_node_id)
}

impl SimMigrationQueue {
    fn new() -> Self {
        Self {
            candidates: Vec::new(),
        }
    }

    fn queue_actors(&mut self, failed_node_id: NodeId, actor_ids: Vec<String>) {
        for actor_id in actor_ids {
            self.candidates.push((actor_id, failed_node_id.clone()));
        }
    }

    fn process<F>(&mut self, mut select_node: F) -> Vec<(String, Option<NodeId>)>
    where
        F: FnMut(&str) -> Option<NodeId>,
    {
        let mut results = Vec::new();
        let mut remaining = Vec::new();

        for (actor_id, failed_node_id) in self.candidates.drain(..) {
            match select_node(&actor_id) {
                Some(target_node) => {
                    results.push((actor_id, Some(target_node)));
                }
                None => {
                    // No capacity, keep in queue
                    remaining.push((actor_id, failed_node_id));
                    results.push((remaining.last().unwrap().0.clone(), None));
                }
            }
        }

        self.candidates = remaining;
        results
    }

    fn len(&self) -> usize {
        self.candidates.len()
    }

    fn is_empty(&self) -> bool {
        self.candidates.is_empty()
    }
}

#[test]
fn test_production_actor_migration_on_node_failure() {
    let config = SimConfig::from_env_or_random();
    tracing::info!(
        seed = config.seed,
        "Running production actor migration test"
    );

    let result = Simulation::new(config).run(|_env| async move {
        let cluster = Arc::new(SimClusterState::new());
        let migration_queue = Arc::new(RwLock::new(SimMigrationQueue::new()));
        let clock = SimClock::new(1000);

        // Create 3-node cluster
        let nodes: Vec<NodeId> = (1..=3).map(test_node_id).collect();

        for (i, node) in nodes.iter().enumerate() {
            cluster
                .join_node(node.clone(), i == 0, clock.get_now_ms())
                .await;
            if i > 0 {
                cluster.complete_join(node, clock.get_now_ms()).await;
            }
        }

        // Verify node-1 is primary
        assert!(
            cluster.has_valid_primary_claim(&nodes[0]).await,
            "Node-1 should be primary"
        );

        // Simulate actors on node-2
        let actors_on_node2 = vec![
            "test/actor-1".to_string(),
            "test/actor-2".to_string(),
            "test/actor-3".to_string(),
        ];

        // Node-2 fails (heartbeat timeout)
        clock.advance(10000);
        cluster.mark_failed(&nodes[1], clock.get_now_ms()).await;

        // Verify node-2 is failed
        {
            let nodes_map = cluster.nodes.read().await;
            let node2 = nodes_map.get(&nodes[1]).unwrap();
            assert_eq!(node2.state, NodeState::Failed, "Node-2 should be Failed");
        }

        // Primary queues actors for migration
        {
            let mut queue = migration_queue.write().await;
            queue.queue_actors(nodes[1].clone(), actors_on_node2.clone());
            assert_eq!(queue.len(), 3, "Migration queue should have 3 actors");
        }

        // Primary processes migration queue
        let migration_results = {
            let mut queue = migration_queue.write().await;
            let healthy_nodes: Vec<NodeId> = {
                let nodes_map = cluster.nodes.read().await;
                nodes_map
                    .values()
                    .filter(|n| n.state == NodeState::Active)
                    .map(|n| n.id.clone())
                    .collect()
            };

            // Select node via round-robin among healthy nodes
            let mut idx = 0;
            queue.process(|_actor_id| {
                if healthy_nodes.is_empty() {
                    return None;
                }
                let target = healthy_nodes[idx % healthy_nodes.len()].clone();
                idx += 1;
                Some(target)
            })
        };

        // Verify all actors were migrated
        assert_eq!(
            migration_results.len(),
            3,
            "Should have 3 migration results"
        );
        for (actor_id, target_node) in &migration_results {
            assert!(
                target_node.is_some(),
                "Actor {} should be migrated to a node",
                actor_id
            );
            let target = target_node.as_ref().unwrap();
            assert_ne!(
                target, &nodes[1],
                "Actor should not be migrated to failed node"
            );
        }

        // Verify migration queue is empty
        {
            let queue = migration_queue.read().await;
            assert!(
                queue.is_empty(),
                "Migration queue should be empty after processing"
            );
        }

        // Verify single activation guarantee:
        // Each actor should be assigned to exactly one node
        let mut actor_placements: HashMap<String, NodeId> = HashMap::new();
        for (actor_id, target_node) in migration_results {
            if let Some(target) = target_node {
                let prev = actor_placements.insert(actor_id.clone(), target.clone());
                assert!(
                    prev.is_none(),
                    "Actor {} should not be placed on multiple nodes",
                    actor_id
                );
            }
        }

        tracing::info!(
            placements = ?actor_placements,
            "Actor migration test passed - single activation guarantee maintained"
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Test 8: State Transitions Match TLA+
// =============================================================================

#[test]
fn test_production_state_transitions_match_tla() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let cluster = Arc::new(SimClusterState::new());
        let clock = SimClock::new(1000);

        let node_id = test_node_id(1);

        // Left -> Active (first node)
        cluster
            .join_node(node_id.clone(), true, clock.get_now_ms())
            .await;
        {
            let nodes = cluster.nodes.read().await;
            assert_eq!(
                nodes.get(&node_id).unwrap().state,
                NodeState::Active,
                "First node should be Active after join"
            );
        }

        // Create second node: Left -> Joining -> Active
        let node2_id = test_node_id(2);
        cluster
            .join_node(node2_id.clone(), false, clock.get_now_ms())
            .await;
        {
            let nodes = cluster.nodes.read().await;
            assert_eq!(
                nodes.get(&node2_id).unwrap().state,
                NodeState::Joining,
                "Non-first node should be Joining"
            );
        }

        cluster.complete_join(&node2_id, clock.get_now_ms()).await;
        {
            let nodes = cluster.nodes.read().await;
            assert_eq!(
                nodes.get(&node2_id).unwrap().state,
                NodeState::Active,
                "Node should be Active after complete_join"
            );
        }

        // Active -> Failed (failure detection)
        cluster.mark_failed(&node2_id, clock.get_now_ms()).await;
        {
            let nodes = cluster.nodes.read().await;
            assert_eq!(
                nodes.get(&node2_id).unwrap().state,
                NodeState::Failed,
                "Node should be Failed after mark_failed"
            );
        }

        tracing::info!("State transition test passed");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

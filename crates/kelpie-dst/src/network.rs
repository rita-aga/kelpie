//! Simulated network for deterministic testing
//!
//! TigerStyle: Configurable network conditions with fault injection.

use crate::clock::SimClock;
use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use bytes::Bytes;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;
use tokio::sync::RwLock;

/// A network message
#[derive(Debug, Clone)]
pub struct NetworkMessage {
    /// Source node ID
    pub from: String,
    /// Destination node ID
    pub to: String,
    /// Message payload
    pub payload: Bytes,
    /// Time when message should be delivered
    pub deliver_at_ms: u64,
}

/// Simulated network for DST
///
/// Provides configurable network conditions including:
/// - Message delays
/// - Packet loss
/// - Network partitions
/// - Message reordering
#[derive(Debug)]
pub struct SimNetwork {
    /// Pending messages per destination
    messages: Arc<RwLock<HashMap<String, VecDeque<NetworkMessage>>>>,
    /// Bidirectional network partitions (set of (node_a, node_b) pairs)
    /// Messages blocked in both directions
    bidirectional_partitions: Arc<RwLock<HashSet<(String, String)>>>,
    /// One-way network partitions (set of (from, to) pairs)
    /// Messages from `from` to `to` blocked, but `to` to `from` allowed
    one_way_partitions: Arc<RwLock<HashSet<(String, String)>>>,
    /// Simulation clock
    clock: SimClock,
    /// Fault injector
    fault_injector: Arc<FaultInjector>,
    /// RNG for delays
    rng: DeterministicRng,
    /// Base latency in milliseconds
    base_latency_ms: u64,
    /// Latency jitter in milliseconds
    latency_jitter_ms: u64,
}

impl SimNetwork {
    /// Create a new simulated network
    pub fn new(clock: SimClock, rng: DeterministicRng, fault_injector: Arc<FaultInjector>) -> Self {
        Self {
            messages: Arc::new(RwLock::new(HashMap::new())),
            bidirectional_partitions: Arc::new(RwLock::new(HashSet::new())),
            one_way_partitions: Arc::new(RwLock::new(HashSet::new())),
            clock,
            fault_injector,
            rng,
            base_latency_ms: 1,
            latency_jitter_ms: 5,
        }
    }

    /// Set base latency
    pub fn with_latency(mut self, base_ms: u64, jitter_ms: u64) -> Self {
        self.base_latency_ms = base_ms;
        self.latency_jitter_ms = jitter_ms;
        self
    }

    /// Send a message from one node to another
    pub async fn send(&self, from: &str, to: &str, payload: Bytes) -> bool {
        // Check for bidirectional partition
        {
            let partitions = self.bidirectional_partitions.read().await;
            // Normalize to (min, max) for bidirectional lookup
            let (a, b) = if from < to {
                (from.to_string(), to.to_string())
            } else {
                (to.to_string(), from.to_string())
            };
            if partitions.contains(&(a, b)) {
                tracing::debug!(
                    from = from,
                    to = to,
                    "Message dropped: bidirectional partition"
                );
                return false;
            }
        }

        // Check for one-way partition (directional: from -> to)
        {
            let one_way = self.one_way_partitions.read().await;
            if one_way.contains(&(from.to_string(), to.to_string())) {
                tracing::debug!(from = from, to = to, "Message dropped: one-way partition");
                return false;
            }
        }

        // Check for packet loss fault
        if let Some(fault) = self.fault_injector.should_inject("network_send") {
            match fault {
                FaultType::NetworkPacketLoss => {
                    tracing::debug!(from = from, to = to, "Message dropped: packet loss fault");
                    return false;
                }
                FaultType::NetworkPartition => {
                    tracing::debug!(from = from, to = to, "Message dropped: partition fault");
                    return false;
                }
                _ => {}
            }
        }

        // Calculate delivery time with latency
        let latency = self.calculate_latency();
        let deliver_at_ms = self.clock.now_ms() + latency;

        let message = NetworkMessage {
            from: from.to_string(),
            to: to.to_string(),
            payload,
            deliver_at_ms,
        };

        // Queue the message
        let mut messages = self.messages.write().await;
        messages
            .entry(to.to_string())
            .or_default()
            .push_back(message);

        true
    }

    /// Receive messages for a node
    ///
    /// Returns all messages that have arrived (delivery time <= current time)
    pub async fn receive(&self, node_id: &str) -> Vec<NetworkMessage> {
        let current_time = self.clock.now_ms();
        let mut messages = self.messages.write().await;

        let queue = match messages.get_mut(node_id) {
            Some(q) => q,
            None => return Vec::new(),
        };

        // Collect messages ready for delivery
        let mut ready = Vec::new();
        let mut remaining = VecDeque::new();

        while let Some(msg) = queue.pop_front() {
            if msg.deliver_at_ms <= current_time {
                ready.push(msg);
            } else {
                remaining.push_back(msg);
            }
        }

        *queue = remaining;

        // Check for message reordering fault
        if !ready.is_empty() {
            if let Some(FaultType::NetworkMessageReorder) =
                self.fault_injector.should_inject("network_receive")
            {
                self.rng.shuffle(&mut ready);
                tracing::debug!(node_id = node_id, "Messages reordered by fault");
            }
        }

        ready
    }

    /// Create a bidirectional network partition between two nodes
    ///
    /// Messages in BOTH directions are blocked (node_a -> node_b and node_b -> node_a).
    pub async fn partition(&self, node_a: &str, node_b: &str) {
        let mut partitions = self.bidirectional_partitions.write().await;
        // Normalize to (min, max) for consistent storage
        let (a, b) = if node_a < node_b {
            (node_a.to_string(), node_b.to_string())
        } else {
            (node_b.to_string(), node_a.to_string())
        };
        partitions.insert((a, b));
        tracing::info!(
            node_a = node_a,
            node_b = node_b,
            "Bidirectional network partition created"
        );
    }

    /// Create a one-way network partition
    ///
    /// Messages from `from` to `to` are blocked, but messages from `to` to `from` are allowed.
    /// This models asymmetric network failures like:
    /// - Replication lag (writes go through, acks don't)
    /// - One-way network failures
    /// - Partial connectivity
    pub async fn partition_one_way(&self, from: &str, to: &str) {
        assert!(!from.is_empty(), "from node cannot be empty");
        assert!(!to.is_empty(), "to node cannot be empty");
        assert!(from != to, "cannot partition a node from itself");

        let mut partitions = self.one_way_partitions.write().await;
        partitions.insert((from.to_string(), to.to_string()));
        tracing::info!(
            from = from,
            to = to,
            "One-way network partition created (from -> to blocked)"
        );
    }

    /// Heal a bidirectional network partition between two nodes
    pub async fn heal(&self, node_a: &str, node_b: &str) {
        let mut partitions = self.bidirectional_partitions.write().await;
        // Normalize to (min, max) for lookup
        let (a, b) = if node_a < node_b {
            (node_a.to_string(), node_b.to_string())
        } else {
            (node_b.to_string(), node_a.to_string())
        };
        partitions.remove(&(a, b));
        tracing::info!(
            node_a = node_a,
            node_b = node_b,
            "Bidirectional network partition healed"
        );
    }

    /// Heal a one-way network partition
    ///
    /// Only removes the specific directional partition from `from` to `to`.
    pub async fn heal_one_way(&self, from: &str, to: &str) {
        let mut partitions = self.one_way_partitions.write().await;
        partitions.remove(&(from.to_string(), to.to_string()));
        tracing::info!(from = from, to = to, "One-way network partition healed");
    }

    /// Heal all network partitions (both bidirectional and one-way)
    pub async fn heal_all(&self) {
        {
            let mut partitions = self.bidirectional_partitions.write().await;
            partitions.clear();
        }
        {
            let mut partitions = self.one_way_partitions.write().await;
            partitions.clear();
        }
        tracing::info!("All network partitions healed");
    }

    /// Partition two groups of nodes completely
    ///
    /// All nodes in group_a become isolated from all nodes in group_b.
    /// This creates bidirectional partitions between every pair.
    pub async fn partition_group(&self, group_a: &[&str], group_b: &[&str]) {
        for a in group_a {
            for b in group_b {
                self.partition(a, b).await;
            }
        }
        tracing::info!(
            group_a = ?group_a,
            group_b = ?group_b,
            "Network group partition created"
        );
    }

    /// Check if there's a one-way partition from one node to another
    ///
    /// This checks ONLY one-way partitions, not bidirectional ones.
    pub async fn is_one_way_partitioned(&self, from: &str, to: &str) -> bool {
        let partitions = self.one_way_partitions.read().await;
        partitions.contains(&(from.to_string(), to.to_string()))
    }

    /// Check if messages from `from` to `to` are blocked by any partition
    ///
    /// This checks both bidirectional and one-way partitions.
    /// Note: This is directional - `is_partitioned(a, b)` may differ from `is_partitioned(b, a)`
    /// when one-way partitions are in effect.
    pub async fn is_partitioned(&self, from: &str, to: &str) -> bool {
        // Check bidirectional partition
        {
            let partitions = self.bidirectional_partitions.read().await;
            let (a, b) = if from < to {
                (from.to_string(), to.to_string())
            } else {
                (to.to_string(), from.to_string())
            };
            if partitions.contains(&(a, b)) {
                return true;
            }
        }

        // Check one-way partition
        {
            let partitions = self.one_way_partitions.read().await;
            if partitions.contains(&(from.to_string(), to.to_string())) {
                return true;
            }
        }

        false
    }

    /// Get count of pending messages for a node
    pub async fn pending_count(&self, node_id: &str) -> usize {
        let messages = self.messages.read().await;
        messages.get(node_id).map(|q| q.len()).unwrap_or(0)
    }

    /// Clear all pending messages
    pub async fn clear(&self) {
        let mut messages = self.messages.write().await;
        messages.clear();
    }

    /// Calculate latency with jitter
    fn calculate_latency(&self) -> u64 {
        let jitter = if self.latency_jitter_ms > 0 {
            self.rng.next_range(0, self.latency_jitter_ms)
        } else {
            0
        };
        self.base_latency_ms + jitter
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::FaultInjectorBuilder;

    fn create_test_network(clock: SimClock) -> SimNetwork {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        SimNetwork::new(clock, rng, fault_injector).with_latency(0, 0)
    }

    #[tokio::test]
    async fn test_sim_network_basic() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Send message
        let sent = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(sent);

        // Receive message
        let messages = network.receive("node-2").await;
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].payload, Bytes::from("hello"));
    }

    #[tokio::test]
    async fn test_sim_network_bidirectional_partition() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Create bidirectional partition
        network.partition("node-1", "node-2").await;

        // Messages blocked in BOTH directions
        let sent_1_to_2 = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(!sent_1_to_2, "node-1 -> node-2 should be blocked");

        let sent_2_to_1 = network.send("node-2", "node-1", Bytes::from("hello")).await;
        assert!(!sent_2_to_1, "node-2 -> node-1 should be blocked");

        // Heal partition
        network.heal("node-1", "node-2").await;

        // Messages go through in both directions
        let sent = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(sent);

        let sent = network.send("node-2", "node-1", Bytes::from("hello")).await;
        assert!(sent);
    }

    #[tokio::test]
    async fn test_sim_network_one_way_partition_basic() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Create one-way partition: node-1 -> node-2 blocked
        network.partition_one_way("node-1", "node-2").await;

        // node-1 -> node-2 should be BLOCKED
        let sent_1_to_2 = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(!sent_1_to_2, "node-1 -> node-2 should be blocked");

        // node-2 -> node-1 should WORK (asymmetric!)
        let sent_2_to_1 = network.send("node-2", "node-1", Bytes::from("reply")).await;
        assert!(sent_2_to_1, "node-2 -> node-1 should work");

        // Verify message was delivered
        let messages = network.receive("node-1").await;
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].payload, Bytes::from("reply"));
    }

    #[tokio::test]
    async fn test_sim_network_one_way_partition_heal() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Create one-way partition
        network.partition_one_way("node-1", "node-2").await;
        assert!(network.is_partitioned("node-1", "node-2").await);
        assert!(!network.is_partitioned("node-2", "node-1").await);

        // Heal the one-way partition
        network.heal_one_way("node-1", "node-2").await;

        // Both directions should work now
        let sent_1_to_2 = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(sent_1_to_2, "node-1 -> node-2 should work after heal");
    }

    #[tokio::test]
    async fn test_sim_network_one_way_vs_bidirectional_independence() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Create one-way partition for node-1 -> node-2
        network.partition_one_way("node-1", "node-2").await;

        // Create bidirectional partition for node-3 <-> node-4
        network.partition("node-3", "node-4").await;

        // Test one-way behavior
        assert!(
            !network
                .send("node-1", "node-2", Bytes::from("blocked"))
                .await
        );
        assert!(
            network
                .send("node-2", "node-1", Bytes::from("allowed"))
                .await
        );

        // Test bidirectional behavior
        assert!(
            !network
                .send("node-3", "node-4", Bytes::from("blocked"))
                .await
        );
        assert!(
            !network
                .send("node-4", "node-3", Bytes::from("blocked"))
                .await
        );

        // Heal all
        network.heal_all().await;

        // Everything should work
        assert!(network.send("node-1", "node-2", Bytes::from("ok")).await);
        assert!(network.send("node-3", "node-4", Bytes::from("ok")).await);
    }

    #[tokio::test]
    async fn test_sim_network_is_partitioned_directional() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // No partitions initially
        assert!(!network.is_partitioned("node-1", "node-2").await);
        assert!(!network.is_partitioned("node-2", "node-1").await);

        // One-way partition: is_partitioned is directional
        network.partition_one_way("node-1", "node-2").await;
        assert!(
            network.is_partitioned("node-1", "node-2").await,
            "from -> to should be partitioned"
        );
        assert!(
            !network.is_partitioned("node-2", "node-1").await,
            "to -> from should NOT be partitioned"
        );

        // Bidirectional partition: is_partitioned is symmetric
        network.heal_all().await;
        network.partition("node-1", "node-2").await;
        assert!(
            network.is_partitioned("node-1", "node-2").await,
            "bidirectional: a -> b partitioned"
        );
        assert!(
            network.is_partitioned("node-2", "node-1").await,
            "bidirectional: b -> a partitioned"
        );
    }

    #[tokio::test]
    async fn test_sim_network_asymmetric_leader_isolation_scenario() {
        // Scenario: Leader can send heartbeats, but can't receive votes
        // This simulates followers being able to receive from leader but leader can't
        // receive from followers.
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        let leader = "leader";
        let follower1 = "follower-1";
        let follower2 = "follower-2";

        // Followers can't send to leader (leader isolated for incoming)
        network.partition_one_way(follower1, leader).await;
        network.partition_one_way(follower2, leader).await;

        // Leader CAN send heartbeats to followers
        assert!(
            network
                .send(leader, follower1, Bytes::from("heartbeat"))
                .await
        );
        assert!(
            network
                .send(leader, follower2, Bytes::from("heartbeat"))
                .await
        );

        // Followers CANNOT send votes/acks back to leader
        assert!(!network.send(follower1, leader, Bytes::from("vote")).await);
        assert!(!network.send(follower2, leader, Bytes::from("ack")).await);

        // Followers CAN communicate with each other (no partition between them)
        assert!(
            network
                .send(follower1, follower2, Bytes::from("peer-msg"))
                .await
        );
        assert!(
            network
                .send(follower2, follower1, Bytes::from("peer-msg"))
                .await
        );
    }

    #[tokio::test]
    async fn test_sim_network_asymmetric_replication_lag_scenario() {
        // Scenario: Primary can send writes to replica, but replica can't send acks
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        let primary = "primary";
        let replica = "replica";

        // Replica -> Primary blocked (acks can't get through)
        network.partition_one_way(replica, primary).await;

        // Primary CAN send writes to replica
        assert!(network.send(primary, replica, Bytes::from("write-1")).await);
        assert!(network.send(primary, replica, Bytes::from("write-2")).await);

        // Replica CANNOT send acks back
        assert!(!network.send(replica, primary, Bytes::from("ack-1")).await);
        assert!(!network.send(replica, primary, Bytes::from("ack-2")).await);

        // Verify writes were received by replica
        let messages = network.receive(replica).await;
        assert_eq!(messages.len(), 2);
    }

    #[tokio::test]
    async fn test_sim_network_latency() {
        let clock = SimClock::from_millis(0);
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let network = SimNetwork::new(clock.clone(), rng, fault_injector).with_latency(100, 0);

        // Send message
        network.send("node-1", "node-2", Bytes::from("hello")).await;

        // Should not be delivered yet
        let messages = network.receive("node-2").await;
        assert!(messages.is_empty());

        // Advance time
        clock.advance_ms(100);

        // Now should be delivered
        let messages = network.receive("node-2").await;
        assert_eq!(messages.len(), 1);
    }

    #[tokio::test]
    async fn test_sim_network_bidirectional_partition_order_independence() {
        // Verify that partition(a, b) and partition(b, a) have the same effect
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Create partition with reversed order
        network.partition("node-2", "node-1").await;

        // Both directions should be blocked
        assert!(!network.send("node-1", "node-2", Bytes::from("test")).await);
        assert!(!network.send("node-2", "node-1", Bytes::from("test")).await);

        // Heal with reversed order should also work
        network.heal("node-1", "node-2").await;

        assert!(network.send("node-1", "node-2", Bytes::from("test")).await);
        assert!(network.send("node-2", "node-1", Bytes::from("test")).await);
    }

    #[tokio::test]
    async fn test_sim_network_partition_group() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Partition [node-1, node-2] from [node-3, node-4]
        network
            .partition_group(&["node-1", "node-2"], &["node-3", "node-4"])
            .await;

        // Messages within groups should work
        assert!(
            network
                .send("node-1", "node-2", Bytes::from("intra-1"))
                .await
        );
        assert!(
            network
                .send("node-3", "node-4", Bytes::from("intra-2"))
                .await
        );

        // Messages across groups should fail
        assert!(!network.send("node-1", "node-3", Bytes::from("cross")).await);
        assert!(!network.send("node-2", "node-4", Bytes::from("cross")).await);
        assert!(!network.send("node-3", "node-1", Bytes::from("cross")).await);
        assert!(!network.send("node-4", "node-2", Bytes::from("cross")).await);
    }

    #[tokio::test]
    async fn test_sim_network_is_one_way_partitioned() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock);

        // Create one-way partition: node-1 -> node-2 blocked
        network.partition_one_way("node-1", "node-2").await;

        // Check one-way partition detection
        assert!(network.is_one_way_partitioned("node-1", "node-2").await);
        assert!(!network.is_one_way_partitioned("node-2", "node-1").await);

        // Heal one-way partition
        network.heal_one_way("node-1", "node-2").await;
        assert!(!network.is_one_way_partitioned("node-1", "node-2").await);
    }
}

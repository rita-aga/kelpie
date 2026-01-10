//! Simulated network for deterministic testing
//!
//! TigerStyle: Configurable network conditions with fault injection.

use crate::clock::SimClock;
use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use bytes::Bytes;
use std::collections::{HashMap, VecDeque};
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
    /// Network partitions (set of (from, to) pairs that are partitioned)
    partitions: Arc<RwLock<Vec<(String, String)>>>,
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
            partitions: Arc::new(RwLock::new(Vec::new())),
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
        // Check for network partition
        {
            let partitions = self.partitions.read().await;
            if partitions
                .iter()
                .any(|(a, b)| (a == from && b == to) || (a == to && b == from))
            {
                tracing::debug!(from = from, to = to, "Message dropped: network partition");
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

    /// Create a network partition between two nodes
    pub async fn partition(&self, node_a: &str, node_b: &str) {
        let mut partitions = self.partitions.write().await;
        partitions.push((node_a.to_string(), node_b.to_string()));
        tracing::info!(
            node_a = node_a,
            node_b = node_b,
            "Network partition created"
        );
    }

    /// Heal a network partition between two nodes
    pub async fn heal(&self, node_a: &str, node_b: &str) {
        let mut partitions = self.partitions.write().await;
        partitions.retain(|(a, b)| !((a == node_a && b == node_b) || (a == node_b && b == node_a)));
        tracing::info!(node_a = node_a, node_b = node_b, "Network partition healed");
    }

    /// Heal all network partitions
    pub async fn heal_all(&self) {
        let mut partitions = self.partitions.write().await;
        partitions.clear();
        tracing::info!("All network partitions healed");
    }

    /// Check if two nodes are partitioned
    pub async fn is_partitioned(&self, node_a: &str, node_b: &str) -> bool {
        let partitions = self.partitions.read().await;
        partitions
            .iter()
            .any(|(a, b)| (a == node_a && b == node_b) || (a == node_b && b == node_a))
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

    #[tokio::test]
    async fn test_sim_network_basic() {
        let clock = SimClock::from_millis(0);
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let network = SimNetwork::new(clock.clone(), rng, fault_injector).with_latency(0, 0);

        // Send message
        let sent = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(sent);

        // Receive message
        let messages = network.receive("node-2").await;
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].payload, Bytes::from("hello"));
    }

    #[tokio::test]
    async fn test_sim_network_partition() {
        let clock = SimClock::from_millis(0);
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let network = SimNetwork::new(clock, rng, fault_injector).with_latency(0, 0);

        // Create partition
        network.partition("node-1", "node-2").await;

        // Message should be dropped
        let sent = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(!sent);

        // Heal partition
        network.heal("node-1", "node-2").await;

        // Message should go through
        let sent = network.send("node-1", "node-2", Bytes::from("hello")).await;
        assert!(sent);
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
}

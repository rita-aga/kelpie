//! Heartbeat and failure detection
//!
//! TigerStyle: Explicit timeouts, bounded intervals, observable state.

use crate::error::{RegistryError, RegistryResult};
use crate::node::{NodeId, NodeStatus};
use kelpie_core::constants::{HEARTBEAT_INTERVAL_MS, HEARTBEAT_TIMEOUT_MS};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;

/// Minimum heartbeat interval in milliseconds
pub const HEARTBEAT_INTERVAL_MS_MIN: u64 = 100;

/// Maximum heartbeat interval in milliseconds
pub const HEARTBEAT_INTERVAL_MS_MAX: u64 = 60_000;

/// Number of missed heartbeats before suspecting a node
pub const HEARTBEAT_SUSPECT_COUNT: u32 = 2;

/// Number of missed heartbeats before declaring failure
pub const HEARTBEAT_FAILURE_COUNT: u32 = 5;

/// Configuration for the heartbeat system
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HeartbeatConfig {
    /// Interval between heartbeats in milliseconds
    pub interval_ms: u64,
    /// Timeout before node is considered suspect in milliseconds
    pub suspect_timeout_ms: u64,
    /// Timeout before node is considered failed in milliseconds
    pub failure_timeout_ms: u64,
    /// Whether to send heartbeats (false for passive monitoring)
    pub send_heartbeats: bool,
}

impl Default for HeartbeatConfig {
    fn default() -> Self {
        Self {
            interval_ms: HEARTBEAT_INTERVAL_MS,
            suspect_timeout_ms: HEARTBEAT_INTERVAL_MS * HEARTBEAT_SUSPECT_COUNT as u64,
            failure_timeout_ms: HEARTBEAT_TIMEOUT_MS,
            send_heartbeats: true,
        }
    }
}

impl HeartbeatConfig {
    /// Create a new heartbeat configuration
    ///
    /// Values outside bounds are clamped to valid range.
    pub fn new(interval_ms: u64) -> Self {
        let interval_ms = interval_ms.clamp(HEARTBEAT_INTERVAL_MS_MIN, HEARTBEAT_INTERVAL_MS_MAX);

        Self {
            interval_ms,
            suspect_timeout_ms: interval_ms * HEARTBEAT_SUSPECT_COUNT as u64,
            failure_timeout_ms: interval_ms * HEARTBEAT_FAILURE_COUNT as u64,
            send_heartbeats: true,
        }
    }

    /// Create config for testing with short intervals
    #[cfg(test)]
    pub fn for_testing() -> Self {
        Self {
            interval_ms: 100,
            suspect_timeout_ms: 200,
            failure_timeout_ms: 500,
            send_heartbeats: true,
        }
    }
}

/// A heartbeat message
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Heartbeat {
    /// The node sending the heartbeat
    pub node_id: NodeId,
    /// Timestamp when heartbeat was sent (Unix ms)
    pub sent_at_ms: u64,
    /// Current node status
    pub status: NodeStatus,
    /// Number of active actors
    pub actor_count: u64,
    /// Available capacity for actors
    pub available_capacity: u64,
    /// Sequence number for ordering
    pub sequence: u64,
}

impl Heartbeat {
    /// Create a new heartbeat
    pub fn new(
        node_id: NodeId,
        timestamp_ms: u64,
        status: NodeStatus,
        actor_count: u64,
        available_capacity: u64,
        sequence: u64,
    ) -> Self {
        Self {
            node_id,
            sent_at_ms: timestamp_ms,
            status,
            actor_count,
            available_capacity,
            sequence,
        }
    }

    /// Check if this heartbeat is newer than another
    pub fn is_newer_than(&self, other: &Heartbeat) -> bool {
        debug_assert_eq!(self.node_id, other.node_id);
        self.sequence > other.sequence
    }
}

/// State tracked for each node in the heartbeat system
#[derive(Debug, Clone)]
pub struct NodeHeartbeatState {
    /// The node's ID
    pub node_id: NodeId,
    /// Last received heartbeat
    pub last_heartbeat: Option<Heartbeat>,
    /// Last heartbeat receive time (local clock)
    pub last_received_at_ms: u64,
    /// Current detected status
    pub detected_status: NodeStatus,
    /// Number of consecutive missed heartbeats
    pub missed_count: u32,
}

impl NodeHeartbeatState {
    /// Create initial state for a node
    pub fn new(node_id: NodeId, now_ms: u64) -> Self {
        Self {
            node_id,
            last_heartbeat: None,
            last_received_at_ms: now_ms,
            detected_status: NodeStatus::Joining,
            missed_count: 0,
        }
    }

    /// Process a received heartbeat
    pub fn receive_heartbeat(&mut self, heartbeat: Heartbeat, now_ms: u64) {
        debug_assert_eq!(self.node_id, heartbeat.node_id);

        // Only accept newer heartbeats
        if let Some(ref last) = self.last_heartbeat {
            if !heartbeat.is_newer_than(last) {
                return; // Ignore stale heartbeat
            }
        }

        self.last_heartbeat = Some(heartbeat.clone());
        self.last_received_at_ms = now_ms;
        self.missed_count = 0;

        // Update detected status based on received status
        if heartbeat.status.is_healthy() {
            self.detected_status = NodeStatus::Active;
        }
    }

    /// Check for timeout and update status
    ///
    /// Returns the new status if it changed
    pub fn check_timeout(&mut self, now_ms: u64, config: &HeartbeatConfig) -> Option<NodeStatus> {
        let elapsed = now_ms.saturating_sub(self.last_received_at_ms);
        let old_status = self.detected_status;

        if elapsed > config.failure_timeout_ms {
            self.detected_status = NodeStatus::Failed;
            self.missed_count = HEARTBEAT_FAILURE_COUNT;
        } else if elapsed > config.suspect_timeout_ms {
            self.detected_status = NodeStatus::Suspect;
            self.missed_count = (elapsed / config.interval_ms) as u32;
        }

        if self.detected_status != old_status {
            Some(self.detected_status)
        } else {
            None
        }
    }
}

/// The heartbeat tracker maintains state for all known nodes
#[derive(Debug)]
pub struct HeartbeatTracker {
    /// Configuration
    config: HeartbeatConfig,
    /// State for each node
    nodes: HashMap<NodeId, NodeHeartbeatState>,
    /// Sequence number for outgoing heartbeats
    next_sequence: u64,
}

impl HeartbeatTracker {
    /// Create a new heartbeat tracker
    pub fn new(config: HeartbeatConfig) -> Self {
        Self {
            config,
            nodes: HashMap::new(),
            next_sequence: 0,
        }
    }

    /// Get the configuration
    pub fn config(&self) -> &HeartbeatConfig {
        &self.config
    }

    /// Register a new node to track
    pub fn register_node(&mut self, node_id: NodeId, now_ms: u64) {
        self.nodes
            .entry(node_id.clone())
            .or_insert_with(|| NodeHeartbeatState::new(node_id, now_ms));
    }

    /// Unregister a node
    pub fn unregister_node(&mut self, node_id: &NodeId) {
        self.nodes.remove(node_id);
    }

    /// Process a received heartbeat
    pub fn receive_heartbeat(&mut self, heartbeat: Heartbeat, now_ms: u64) -> RegistryResult<()> {
        let state = self
            .nodes
            .get_mut(&heartbeat.node_id)
            .ok_or_else(|| RegistryError::node_not_found(heartbeat.node_id.as_str()))?;

        state.receive_heartbeat(heartbeat, now_ms);
        Ok(())
    }

    /// Check all nodes for timeouts
    ///
    /// Returns a list of (node_id, old_status, new_status) for nodes that changed
    pub fn check_all_timeouts(&mut self, now_ms: u64) -> Vec<(NodeId, NodeStatus, NodeStatus)> {
        let mut changes = Vec::new();

        for (node_id, state) in &mut self.nodes {
            let old_status = state.detected_status;
            if let Some(new_status) = state.check_timeout(now_ms, &self.config) {
                changes.push((node_id.clone(), old_status, new_status));
            }
        }

        changes
    }

    /// Get the next sequence number for outgoing heartbeats
    pub fn next_sequence(&mut self) -> u64 {
        let seq = self.next_sequence;
        self.next_sequence = self.next_sequence.saturating_add(1);
        seq
    }

    /// Get the detected status of a node
    pub fn get_status(&self, node_id: &NodeId) -> Option<NodeStatus> {
        self.nodes.get(node_id).map(|s| s.detected_status)
    }

    /// Get all nodes with a specific status
    pub fn nodes_with_status(&self, status: NodeStatus) -> Vec<NodeId> {
        self.nodes
            .iter()
            .filter(|(_, state)| state.detected_status == status)
            .map(|(id, _)| id.clone())
            .collect()
    }

    /// Get count of active nodes
    pub fn active_node_count(&self) -> usize {
        self.nodes
            .values()
            .filter(|s| s.detected_status == NodeStatus::Active)
            .count()
    }

    /// Get the next heartbeat interval
    pub fn interval(&self) -> Duration {
        Duration::from_millis(self.config.interval_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_node_id(n: u32) -> NodeId {
        NodeId::new(format!("node-{}", n)).unwrap()
    }

    #[test]
    fn test_heartbeat_config_default() {
        let config = HeartbeatConfig::default();
        assert_eq!(config.interval_ms, HEARTBEAT_INTERVAL_MS);
        assert!(config.failure_timeout_ms > config.suspect_timeout_ms);
    }

    #[test]
    fn test_heartbeat_config_bounds() {
        let config = HeartbeatConfig::new(50); // Below minimum
        assert!(config.interval_ms >= HEARTBEAT_INTERVAL_MS_MIN);

        let config = HeartbeatConfig::new(100_000); // Above maximum
        assert!(config.interval_ms <= HEARTBEAT_INTERVAL_MS_MAX);
    }

    #[test]
    fn test_heartbeat_sequence() {
        let hb1 = Heartbeat::new(test_node_id(1), 1000, NodeStatus::Active, 10, 90, 1);
        let hb2 = Heartbeat::new(test_node_id(1), 2000, NodeStatus::Active, 11, 89, 2);

        assert!(hb2.is_newer_than(&hb1));
        assert!(!hb1.is_newer_than(&hb2));
    }

    #[test]
    fn test_node_heartbeat_state_receive() {
        let node_id = test_node_id(1);
        let mut state = NodeHeartbeatState::new(node_id.clone(), 1000);

        let hb = Heartbeat::new(node_id.clone(), 2000, NodeStatus::Active, 10, 90, 1);
        state.receive_heartbeat(hb, 2000);

        assert_eq!(state.detected_status, NodeStatus::Active);
        assert_eq!(state.missed_count, 0);
        assert!(state.last_heartbeat.is_some());
    }

    #[test]
    fn test_node_heartbeat_state_timeout() {
        let config = HeartbeatConfig::for_testing();
        let node_id = test_node_id(1);
        let mut state = NodeHeartbeatState::new(node_id.clone(), 1000);
        state.detected_status = NodeStatus::Active;

        // No timeout yet
        let change = state.check_timeout(1100, &config);
        assert!(change.is_none());
        assert_eq!(state.detected_status, NodeStatus::Active);

        // Suspect timeout
        let change = state.check_timeout(1300, &config);
        assert_eq!(change, Some(NodeStatus::Suspect));

        // Failure timeout
        let change = state.check_timeout(1600, &config);
        assert_eq!(change, Some(NodeStatus::Failed));
    }

    #[test]
    fn test_heartbeat_tracker_register() {
        let config = HeartbeatConfig::for_testing();
        let mut tracker = HeartbeatTracker::new(config);

        tracker.register_node(test_node_id(1), 1000);
        tracker.register_node(test_node_id(2), 1000);

        assert_eq!(tracker.nodes.len(), 2);
    }

    #[test]
    fn test_heartbeat_tracker_receive() {
        let config = HeartbeatConfig::for_testing();
        let mut tracker = HeartbeatTracker::new(config);

        let node_id = test_node_id(1);
        tracker.register_node(node_id.clone(), 1000);

        let hb = Heartbeat::new(node_id.clone(), 2000, NodeStatus::Active, 10, 90, 1);
        tracker.receive_heartbeat(hb, 2000).unwrap();

        assert_eq!(tracker.get_status(&node_id), Some(NodeStatus::Active));
    }

    #[test]
    fn test_heartbeat_tracker_timeout() {
        let config = HeartbeatConfig::for_testing();
        let mut tracker = HeartbeatTracker::new(config);

        let node_id = test_node_id(1);
        tracker.register_node(node_id.clone(), 1000);

        // Receive initial heartbeat
        let hb = Heartbeat::new(node_id.clone(), 1000, NodeStatus::Active, 0, 100, 1);
        tracker.receive_heartbeat(hb, 1000).unwrap();

        // No changes at 1100
        let changes = tracker.check_all_timeouts(1100);
        assert!(changes.is_empty());

        // Suspect at 1300
        let changes = tracker.check_all_timeouts(1300);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].2, NodeStatus::Suspect);

        // Failed at 1600
        let changes = tracker.check_all_timeouts(1600);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].2, NodeStatus::Failed);
    }

    #[test]
    fn test_heartbeat_tracker_nodes_with_status() {
        let config = HeartbeatConfig::for_testing();
        let mut tracker = HeartbeatTracker::new(config);

        for i in 1..=5 {
            let node_id = test_node_id(i);
            tracker.register_node(node_id.clone(), 1000);

            let hb = Heartbeat::new(node_id.clone(), 1000, NodeStatus::Active, 0, 100, 1);
            tracker.receive_heartbeat(hb, 1000).unwrap();
        }

        assert_eq!(tracker.active_node_count(), 5);

        // Time out some nodes
        tracker.check_all_timeouts(1600);

        assert_eq!(tracker.nodes_with_status(NodeStatus::Failed).len(), 5);
        assert_eq!(tracker.active_node_count(), 0);
    }

    #[test]
    fn test_heartbeat_tracker_sequence() {
        let config = HeartbeatConfig::for_testing();
        let mut tracker = HeartbeatTracker::new(config);

        assert_eq!(tracker.next_sequence(), 0);
        assert_eq!(tracker.next_sequence(), 1);
        assert_eq!(tracker.next_sequence(), 2);
    }
}

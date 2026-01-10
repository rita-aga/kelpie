//! Cluster configuration
//!
//! TigerStyle: Explicit configuration with bounded values.

use kelpie_core::constants::RPC_TIMEOUT_MS_DEFAULT;
use kelpie_registry::HeartbeatConfig;
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::time::Duration;

/// Maximum bootstrap retry count
pub const BOOTSTRAP_RETRY_COUNT_MAX: u32 = 10;

/// Bootstrap retry interval in milliseconds
pub const BOOTSTRAP_RETRY_INTERVAL_MS: u64 = 1000;

/// Actor migration batch size
pub const MIGRATION_BATCH_SIZE_DEFAULT: usize = 100;

/// Cluster configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterConfig {
    /// This node's RPC address
    pub rpc_addr: SocketAddr,
    /// Seed nodes to connect to for cluster discovery
    pub seed_nodes: Vec<SocketAddr>,
    /// Heartbeat configuration
    pub heartbeat: HeartbeatConfig,
    /// RPC timeout in milliseconds
    pub rpc_timeout_ms: u64,
    /// Whether to auto-migrate actors on node failure
    pub auto_migrate_on_failure: bool,
    /// Maximum actors to migrate in a single batch
    pub migration_batch_size: usize,
    /// Whether to drain actors before shutdown
    pub drain_on_shutdown: bool,
    /// Drain timeout in milliseconds
    pub drain_timeout_ms: u64,
}

impl Default for ClusterConfig {
    fn default() -> Self {
        Self {
            rpc_addr: "127.0.0.1:9000".parse().unwrap(),
            seed_nodes: Vec::new(),
            heartbeat: HeartbeatConfig::default(),
            rpc_timeout_ms: RPC_TIMEOUT_MS_DEFAULT,
            auto_migrate_on_failure: true,
            migration_batch_size: MIGRATION_BATCH_SIZE_DEFAULT,
            drain_on_shutdown: true,
            drain_timeout_ms: 30_000,
        }
    }
}

impl ClusterConfig {
    /// Create a new cluster configuration
    pub fn new(rpc_addr: SocketAddr) -> Self {
        Self {
            rpc_addr,
            ..Default::default()
        }
    }

    /// Create configuration for single-node deployment
    pub fn single_node(rpc_addr: SocketAddr) -> Self {
        Self {
            rpc_addr,
            seed_nodes: Vec::new(),
            ..Default::default()
        }
    }

    /// Set seed nodes
    pub fn with_seed_nodes(mut self, seeds: Vec<SocketAddr>) -> Self {
        self.seed_nodes = seeds;
        self
    }

    /// Set heartbeat interval
    pub fn with_heartbeat_interval(mut self, interval_ms: u64) -> Self {
        self.heartbeat = HeartbeatConfig::new(interval_ms);
        self
    }

    /// Set RPC timeout
    pub fn with_rpc_timeout(mut self, timeout_ms: u64) -> Self {
        self.rpc_timeout_ms = timeout_ms;
        self
    }

    /// Disable auto-migration
    pub fn without_auto_migrate(mut self) -> Self {
        self.auto_migrate_on_failure = false;
        self
    }

    /// Disable drain on shutdown
    pub fn without_drain(mut self) -> Self {
        self.drain_on_shutdown = false;
        self
    }

    /// Get RPC timeout as Duration
    pub fn rpc_timeout(&self) -> Duration {
        Duration::from_millis(self.rpc_timeout_ms)
    }

    /// Get drain timeout as Duration
    pub fn drain_timeout(&self) -> Duration {
        Duration::from_millis(self.drain_timeout_ms)
    }

    /// Check if this is a single-node configuration
    pub fn is_single_node(&self) -> bool {
        self.seed_nodes.is_empty()
    }

    /// Validate configuration
    pub fn validate(&self) -> Result<(), String> {
        if self.heartbeat.failure_timeout_ms <= self.heartbeat.suspect_timeout_ms {
            return Err("failure timeout must be greater than suspect timeout".into());
        }

        if self.rpc_timeout_ms == 0 {
            return Err("RPC timeout must be positive".into());
        }

        if self.migration_batch_size == 0 {
            return Err("migration batch size must be positive".into());
        }

        Ok(())
    }
}

impl ClusterConfig {
    /// Create configuration for testing with short timeouts
    pub fn for_testing() -> Self {
        Self {
            rpc_addr: "127.0.0.1:0".parse().unwrap(),
            seed_nodes: Vec::new(),
            heartbeat: HeartbeatConfig::new(100), // Short interval for tests
            rpc_timeout_ms: 1000,
            auto_migrate_on_failure: true,
            migration_batch_size: 10,
            drain_on_shutdown: false,
            drain_timeout_ms: 1000,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_default() {
        let config = ClusterConfig::default();
        assert!(config.auto_migrate_on_failure);
        assert!(config.drain_on_shutdown);
        assert!(config.heartbeat.interval_ms > 0);
    }

    #[test]
    fn test_config_single_node() {
        let config = ClusterConfig::single_node("127.0.0.1:9000".parse().unwrap());
        assert!(config.is_single_node());
        assert!(config.seed_nodes.is_empty());
    }

    #[test]
    fn test_config_with_seeds() {
        let seeds: Vec<SocketAddr> = vec![
            "192.168.1.1:9000".parse().unwrap(),
            "192.168.1.2:9000".parse().unwrap(),
        ];

        let config = ClusterConfig::default().with_seed_nodes(seeds.clone());
        assert_eq!(config.seed_nodes.len(), 2);
        assert!(!config.is_single_node());
    }

    #[test]
    fn test_config_validation() {
        let config = ClusterConfig::default();
        assert!(config.validate().is_ok());

        let invalid = ClusterConfig {
            rpc_timeout_ms: 0,
            ..Default::default()
        };
        assert!(invalid.validate().is_err());
    }

    #[test]
    fn test_config_durations() {
        let config = ClusterConfig::default();
        assert!(config.rpc_timeout() > Duration::ZERO);
        assert!(config.drain_timeout() > Duration::ZERO);
    }
}

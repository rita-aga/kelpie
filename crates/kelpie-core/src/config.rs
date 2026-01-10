//! Configuration for Kelpie
//!
//! TigerStyle: Explicit defaults, validation, reasonable limits.

use crate::constants::*;
use crate::error::{Error, Result};
use serde::{Deserialize, Serialize};

/// Main configuration for Kelpie
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct KelpieConfig {
    /// Node configuration
    #[serde(default)]
    pub node: NodeConfig,

    /// Actor runtime configuration
    #[serde(default)]
    pub actor: ActorConfig,

    /// Storage configuration
    #[serde(default)]
    pub storage: StorageConfig,

    /// Cluster configuration
    #[serde(default)]
    pub cluster: ClusterConfig,
}

impl KelpieConfig {
    /// Validate the configuration
    pub fn validate(&self) -> Result<()> {
        self.node.validate()?;
        self.actor.validate()?;
        self.storage.validate()?;
        self.cluster.validate()?;
        Ok(())
    }
}

/// Node configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeConfig {
    /// Node identifier (auto-generated if not specified)
    #[serde(default)]
    pub node_id: Option<String>,

    /// Address to bind for RPC (default: 0.0.0.0:9000)
    #[serde(default = "default_bind_address")]
    pub bind_address: String,

    /// Address advertised to other nodes (default: same as bind_address)
    #[serde(default)]
    pub advertise_address: Option<String>,
}

fn default_bind_address() -> String {
    "0.0.0.0:9000".to_string()
}

impl Default for NodeConfig {
    fn default() -> Self {
        Self {
            node_id: None,
            bind_address: default_bind_address(),
            advertise_address: None,
        }
    }
}

impl NodeConfig {
    fn validate(&self) -> Result<()> {
        // Validate bind address format (basic check)
        if !self.bind_address.contains(':') {
            return Err(Error::InvalidConfiguration {
                field: "node.bind_address".into(),
                reason: "must be in host:port format".into(),
            });
        }
        Ok(())
    }
}

/// Actor runtime configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActorConfig {
    /// Maximum concurrent actors on this node
    #[serde(default = "default_max_actors")]
    pub max_actors_count: usize,

    /// Actor idle timeout before deactivation (milliseconds)
    #[serde(default = "default_idle_timeout_ms")]
    pub idle_timeout_ms: u64,

    /// Maximum invocation timeout (milliseconds)
    #[serde(default = "default_invocation_timeout_ms")]
    pub invocation_timeout_ms: u64,

    /// Maximum mailbox depth per actor
    #[serde(default = "default_mailbox_depth")]
    pub mailbox_depth_max: usize,
}

fn default_max_actors() -> usize {
    100_000
}

fn default_idle_timeout_ms() -> u64 {
    ACTOR_IDLE_TIMEOUT_MS_DEFAULT
}

fn default_invocation_timeout_ms() -> u64 {
    ACTOR_INVOCATION_TIMEOUT_MS_MAX
}

fn default_mailbox_depth() -> usize {
    MAILBOX_DEPTH_MAX
}

impl Default for ActorConfig {
    fn default() -> Self {
        Self {
            max_actors_count: default_max_actors(),
            idle_timeout_ms: default_idle_timeout_ms(),
            invocation_timeout_ms: default_invocation_timeout_ms(),
            mailbox_depth_max: default_mailbox_depth(),
        }
    }
}

impl ActorConfig {
    fn validate(&self) -> Result<()> {
        if self.max_actors_count > ACTOR_CONCURRENT_COUNT_MAX {
            return Err(Error::InvalidConfiguration {
                field: "actor.max_actors_count".into(),
                reason: format!(
                    "{} exceeds limit {}",
                    self.max_actors_count, ACTOR_CONCURRENT_COUNT_MAX
                ),
            });
        }

        if self.idle_timeout_ms > ACTOR_IDLE_TIMEOUT_MS_MAX {
            return Err(Error::InvalidConfiguration {
                field: "actor.idle_timeout_ms".into(),
                reason: format!(
                    "{} exceeds limit {}",
                    self.idle_timeout_ms, ACTOR_IDLE_TIMEOUT_MS_MAX
                ),
            });
        }

        if self.invocation_timeout_ms > ACTOR_INVOCATION_TIMEOUT_MS_MAX {
            return Err(Error::InvalidConfiguration {
                field: "actor.invocation_timeout_ms".into(),
                reason: format!(
                    "{} exceeds limit {}",
                    self.invocation_timeout_ms, ACTOR_INVOCATION_TIMEOUT_MS_MAX
                ),
            });
        }

        Ok(())
    }
}

/// Storage backend configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageConfig {
    /// Storage backend type
    #[serde(default)]
    pub backend: StorageBackend,

    /// FoundationDB cluster file path (for FDB backend)
    #[serde(default)]
    pub fdb_cluster_file: Option<String>,
}

/// Storage backend type
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum StorageBackend {
    /// In-memory storage (for testing)
    #[default]
    Memory,

    /// FoundationDB storage (for production)
    FoundationDb,
}

impl Default for StorageConfig {
    fn default() -> Self {
        Self {
            backend: StorageBackend::Memory,
            fdb_cluster_file: None,
        }
    }
}

impl StorageConfig {
    fn validate(&self) -> Result<()> {
        if matches!(self.backend, StorageBackend::FoundationDb) && self.fdb_cluster_file.is_none() {
            return Err(Error::InvalidConfiguration {
                field: "storage.fdb_cluster_file".into(),
                reason: "required when backend is foundationdb".into(),
            });
        }
        Ok(())
    }
}

/// Cluster configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterConfig {
    /// Seed nodes for cluster discovery
    #[serde(default)]
    pub seed_nodes: Vec<String>,

    /// Heartbeat interval (milliseconds)
    #[serde(default = "default_heartbeat_interval")]
    pub heartbeat_interval_ms: u64,

    /// Heartbeat timeout (milliseconds)
    #[serde(default = "default_heartbeat_timeout")]
    pub heartbeat_timeout_ms: u64,
}

fn default_heartbeat_interval() -> u64 {
    HEARTBEAT_INTERVAL_MS
}

fn default_heartbeat_timeout() -> u64 {
    HEARTBEAT_TIMEOUT_MS
}

impl Default for ClusterConfig {
    fn default() -> Self {
        Self {
            seed_nodes: Vec::new(),
            heartbeat_interval_ms: default_heartbeat_interval(),
            heartbeat_timeout_ms: default_heartbeat_timeout(),
        }
    }
}

impl ClusterConfig {
    fn validate(&self) -> Result<()> {
        if self.heartbeat_timeout_ms <= self.heartbeat_interval_ms {
            return Err(Error::InvalidConfiguration {
                field: "cluster.heartbeat_timeout_ms".into(),
                reason: "must be greater than heartbeat_interval_ms".into(),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config_is_valid() {
        let config = KelpieConfig::default();
        assert!(config.validate().is_ok());
    }

    #[test]
    fn test_invalid_heartbeat_config() {
        let mut config = KelpieConfig::default();
        config.cluster.heartbeat_timeout_ms = 500;
        config.cluster.heartbeat_interval_ms = 1000;
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_fdb_requires_cluster_file() {
        let mut config = KelpieConfig::default();
        config.storage.backend = StorageBackend::FoundationDb;
        config.storage.fdb_cluster_file = None;
        assert!(config.validate().is_err());
    }
}

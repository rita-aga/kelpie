//! Sandbox configuration
//!
//! TigerStyle: Explicit limits with units in names.

use serde::{Deserialize, Serialize};
use std::time::Duration;

/// Default memory limit (256MB)
pub const SANDBOX_MEMORY_BYTES_MAX_DEFAULT: u64 = 256 * 1024 * 1024;

/// Default CPU limit (1 vCPU)
pub const SANDBOX_VCPU_COUNT_DEFAULT: u32 = 1;

/// Default disk size (1GB)
pub const SANDBOX_DISK_BYTES_MAX_DEFAULT: u64 = 1024 * 1024 * 1024;

/// Default execution timeout (30 seconds)
pub const SANDBOX_EXEC_TIMEOUT_MS_DEFAULT: u64 = 30_000;

/// Default idle timeout before reclaim (5 minutes)
pub const SANDBOX_IDLE_TIMEOUT_MS_DEFAULT: u64 = 5 * 60 * 1000;

/// Resource limits for a sandbox
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceLimits {
    /// Maximum memory in bytes
    pub memory_bytes_max: u64,
    /// Number of virtual CPUs
    pub vcpu_count: u32,
    /// Maximum disk size in bytes
    pub disk_bytes_max: u64,
    /// Maximum execution time for a single command
    pub exec_timeout_ms: u64,
    /// Network bandwidth limit in bytes/sec (0 = unlimited)
    pub network_bandwidth_bytes_per_sec: u64,
    /// Whether network access is allowed
    pub network_enabled: bool,
}

impl ResourceLimits {
    /// Create with default limits
    pub fn new() -> Self {
        Self::default()
    }

    /// Create minimal limits (for testing)
    pub fn minimal() -> Self {
        Self {
            memory_bytes_max: 64 * 1024 * 1024, // 64MB
            vcpu_count: 1,
            disk_bytes_max: 100 * 1024 * 1024, // 100MB
            exec_timeout_ms: 10_000,           // 10s
            network_bandwidth_bytes_per_sec: 0,
            network_enabled: false,
        }
    }

    /// Create limits for heavy workloads
    pub fn heavy() -> Self {
        Self {
            memory_bytes_max: 1024 * 1024 * 1024, // 1GB
            vcpu_count: 4,
            disk_bytes_max: 10 * 1024 * 1024 * 1024, // 10GB
            exec_timeout_ms: 300_000,                // 5 minutes
            network_bandwidth_bytes_per_sec: 0,
            network_enabled: true,
        }
    }

    /// Set memory limit
    pub fn with_memory(mut self, bytes: u64) -> Self {
        self.memory_bytes_max = bytes;
        self
    }

    /// Set vCPU count
    pub fn with_vcpus(mut self, count: u32) -> Self {
        self.vcpu_count = count;
        self
    }

    /// Set disk limit
    pub fn with_disk(mut self, bytes: u64) -> Self {
        self.disk_bytes_max = bytes;
        self
    }

    /// Set execution timeout
    pub fn with_exec_timeout(mut self, timeout: Duration) -> Self {
        self.exec_timeout_ms = timeout.as_millis() as u64;
        self
    }

    /// Enable or disable network
    pub fn with_network(mut self, enabled: bool) -> Self {
        self.network_enabled = enabled;
        self
    }
}

impl Default for ResourceLimits {
    fn default() -> Self {
        Self {
            memory_bytes_max: SANDBOX_MEMORY_BYTES_MAX_DEFAULT,
            vcpu_count: SANDBOX_VCPU_COUNT_DEFAULT,
            disk_bytes_max: SANDBOX_DISK_BYTES_MAX_DEFAULT,
            exec_timeout_ms: SANDBOX_EXEC_TIMEOUT_MS_DEFAULT,
            network_bandwidth_bytes_per_sec: 0,
            network_enabled: false,
        }
    }
}

/// Sandbox configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SandboxConfig {
    /// Resource limits
    pub limits: ResourceLimits,
    /// Working directory inside the sandbox
    pub workdir: String,
    /// Environment variables
    pub env: Vec<(String, String)>,
    /// Idle timeout before sandbox is reclaimed
    pub idle_timeout_ms: u64,
    /// Whether to enable debug logging in sandbox
    pub debug: bool,
    /// Base image or rootfs path (implementation-specific)
    pub image: Option<String>,
}

impl SandboxConfig {
    /// Create with default settings
    pub fn new() -> Self {
        Self::default()
    }

    /// Set resource limits
    pub fn with_limits(mut self, limits: ResourceLimits) -> Self {
        self.limits = limits;
        self
    }

    /// Set working directory
    pub fn with_workdir(mut self, workdir: impl Into<String>) -> Self {
        self.workdir = workdir.into();
        self
    }

    /// Add environment variable
    pub fn with_env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.env.push((key.into(), value.into()));
        self
    }

    /// Set idle timeout
    pub fn with_idle_timeout(mut self, timeout: Duration) -> Self {
        self.idle_timeout_ms = timeout.as_millis() as u64;
        self
    }

    /// Set base image
    pub fn with_image(mut self, image: impl Into<String>) -> Self {
        self.image = Some(image.into());
        self
    }

    /// Enable debug mode
    pub fn with_debug(mut self, debug: bool) -> Self {
        self.debug = debug;
        self
    }
}

impl Default for SandboxConfig {
    fn default() -> Self {
        Self {
            limits: ResourceLimits::default(),
            workdir: "/workspace".to_string(),
            env: Vec::new(),
            idle_timeout_ms: SANDBOX_IDLE_TIMEOUT_MS_DEFAULT,
            debug: false,
            image: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resource_limits_default() {
        let limits = ResourceLimits::default();
        assert_eq!(limits.memory_bytes_max, SANDBOX_MEMORY_BYTES_MAX_DEFAULT);
        assert_eq!(limits.vcpu_count, SANDBOX_VCPU_COUNT_DEFAULT);
        assert!(!limits.network_enabled);
    }

    #[test]
    fn test_resource_limits_builder() {
        let limits = ResourceLimits::new()
            .with_memory(512 * 1024 * 1024)
            .with_vcpus(2)
            .with_network(true);

        assert_eq!(limits.memory_bytes_max, 512 * 1024 * 1024);
        assert_eq!(limits.vcpu_count, 2);
        assert!(limits.network_enabled);
    }

    #[test]
    fn test_sandbox_config_default() {
        let config = SandboxConfig::default();
        assert_eq!(config.workdir, "/workspace");
        assert!(config.env.is_empty());
        assert!(!config.debug);
    }

    #[test]
    fn test_sandbox_config_builder() {
        let config = SandboxConfig::new()
            .with_workdir("/home/agent")
            .with_env("PATH", "/usr/bin")
            .with_env("HOME", "/home/agent")
            .with_debug(true);

        assert_eq!(config.workdir, "/home/agent");
        assert_eq!(config.env.len(), 2);
        assert!(config.debug);
    }

    #[test]
    fn test_resource_limits_presets() {
        let minimal = ResourceLimits::minimal();
        let heavy = ResourceLimits::heavy();

        assert!(minimal.memory_bytes_max < heavy.memory_bytes_max);
        assert!(minimal.vcpu_count < heavy.vcpu_count);
    }
}

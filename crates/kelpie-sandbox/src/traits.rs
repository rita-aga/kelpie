//! Sandbox traits and lifecycle abstractions
//!
//! TigerStyle: Explicit state machine with clear transitions.

use crate::config::SandboxConfig;
use crate::error::SandboxResult;
use crate::exec::{ExecOptions, ExecOutput};
use crate::snapshot::Snapshot;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// Sandbox lifecycle states
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SandboxState {
    /// Sandbox is being created
    Creating,
    /// Sandbox is running and ready for commands
    Running,
    /// Sandbox is paused (can be resumed)
    Paused,
    /// Sandbox is stopped (can be started)
    Stopped,
    /// Sandbox failed and cannot be used
    Failed,
    /// Sandbox is being destroyed
    Destroying,
}

impl SandboxState {
    /// Check if sandbox can execute commands in this state
    pub fn can_exec(&self) -> bool {
        matches!(self, Self::Running)
    }

    /// Check if sandbox can be paused in this state
    pub fn can_pause(&self) -> bool {
        matches!(self, Self::Running)
    }

    /// Check if sandbox can be resumed in this state
    pub fn can_resume(&self) -> bool {
        matches!(self, Self::Paused)
    }

    /// Check if sandbox can be stopped in this state
    pub fn can_stop(&self) -> bool {
        matches!(self, Self::Running | Self::Paused)
    }

    /// Check if sandbox can be started in this state
    pub fn can_start(&self) -> bool {
        matches!(self, Self::Stopped)
    }

    /// Check if sandbox can be destroyed in this state
    pub fn can_destroy(&self) -> bool {
        !matches!(self, Self::Destroying)
    }

    /// Check if sandbox can be snapshotted in this state
    pub fn can_snapshot(&self) -> bool {
        matches!(self, Self::Running | Self::Paused)
    }
}

impl std::fmt::Display for SandboxState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Creating => write!(f, "creating"),
            Self::Running => write!(f, "running"),
            Self::Paused => write!(f, "paused"),
            Self::Stopped => write!(f, "stopped"),
            Self::Failed => write!(f, "failed"),
            Self::Destroying => write!(f, "destroying"),
        }
    }
}

/// Core sandbox trait
///
/// Defines the interface for sandbox implementations:
/// - MockSandbox: In-memory for testing
/// - ProcessSandbox: OS process isolation
/// - FirecrackerSandbox: MicroVM isolation
#[async_trait]
pub trait Sandbox: Send + Sync {
    /// Get the sandbox ID
    fn id(&self) -> &str;

    /// Get the current state
    fn state(&self) -> SandboxState;

    /// Get the configuration
    fn config(&self) -> &SandboxConfig;

    /// Start the sandbox
    async fn start(&mut self) -> SandboxResult<()>;

    /// Stop the sandbox
    async fn stop(&mut self) -> SandboxResult<()>;

    /// Pause the sandbox (suspend execution)
    async fn pause(&mut self) -> SandboxResult<()>;

    /// Resume a paused sandbox
    async fn resume(&mut self) -> SandboxResult<()>;

    /// Execute a command in the sandbox
    async fn exec(
        &self,
        command: &str,
        args: &[&str],
        options: ExecOptions,
    ) -> SandboxResult<ExecOutput>;

    /// Execute a command with default options
    async fn exec_simple(&self, command: &str, args: &[&str]) -> SandboxResult<ExecOutput> {
        self.exec(command, args, ExecOptions::default()).await
    }

    /// Create a snapshot of the current state
    async fn snapshot(&self) -> SandboxResult<Snapshot>;

    /// Restore from a snapshot
    async fn restore(&mut self, snapshot: &Snapshot) -> SandboxResult<()>;

    /// Destroy the sandbox and clean up resources
    async fn destroy(&mut self) -> SandboxResult<()>;

    /// Check if the sandbox is healthy
    async fn health_check(&self) -> SandboxResult<bool>;

    /// Get resource usage statistics
    async fn stats(&self) -> SandboxResult<SandboxStats>;
}

/// Resource usage statistics
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SandboxStats {
    /// Memory usage in bytes
    pub memory_bytes_used: u64,
    /// CPU usage percentage (0-100)
    pub cpu_percent: f32,
    /// Disk usage in bytes
    pub disk_bytes_used: u64,
    /// Network bytes received
    pub network_rx_bytes: u64,
    /// Network bytes sent
    pub network_tx_bytes: u64,
    /// Uptime in milliseconds
    pub uptime_ms: u64,
}

/// Factory for creating sandboxes
#[async_trait]
pub trait SandboxFactory: Send + Sync {
    /// The type of sandbox this factory creates
    type Sandbox: Sandbox;

    /// Create a new sandbox with the given configuration
    async fn create(&self, config: SandboxConfig) -> SandboxResult<Self::Sandbox>;

    /// Create a sandbox from a snapshot
    async fn create_from_snapshot(
        &self,
        config: SandboxConfig,
        snapshot: &Snapshot,
    ) -> SandboxResult<Self::Sandbox>;
}

/// Type-erased sandbox for dynamic dispatch
#[allow(dead_code)]
pub type DynSandbox = Arc<dyn Sandbox>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sandbox_state_transitions() {
        assert!(SandboxState::Running.can_exec());
        assert!(!SandboxState::Paused.can_exec());
        assert!(!SandboxState::Stopped.can_exec());

        assert!(SandboxState::Running.can_pause());
        assert!(!SandboxState::Stopped.can_pause());

        assert!(SandboxState::Paused.can_resume());
        assert!(!SandboxState::Running.can_resume());

        assert!(SandboxState::Running.can_stop());
        assert!(SandboxState::Paused.can_stop());
        assert!(!SandboxState::Stopped.can_stop());

        assert!(SandboxState::Stopped.can_start());
        assert!(!SandboxState::Running.can_start());
    }

    #[test]
    fn test_sandbox_state_display() {
        assert_eq!(SandboxState::Running.to_string(), "running");
        assert_eq!(SandboxState::Paused.to_string(), "paused");
        assert_eq!(SandboxState::Failed.to_string(), "failed");
    }

    #[test]
    fn test_sandbox_state_snapshot() {
        assert!(SandboxState::Running.can_snapshot());
        assert!(SandboxState::Paused.can_snapshot());
        assert!(!SandboxState::Stopped.can_snapshot());
        assert!(!SandboxState::Failed.can_snapshot());
    }

    #[test]
    fn test_sandbox_stats_default() {
        let stats = SandboxStats::default();
        assert_eq!(stats.memory_bytes_used, 0);
        assert_eq!(stats.cpu_percent, 0.0);
        assert_eq!(stats.uptime_ms, 0);
    }
}

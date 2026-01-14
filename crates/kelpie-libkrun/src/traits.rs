//! VM instance traits
//!
//! TigerStyle: Async trait with explicit state machine.

use async_trait::async_trait;
use bytes::Bytes;

use crate::config::VmConfig;
use crate::error::LibkrunResult;
use crate::snapshot::VmSnapshot;

/// State of a VM instance
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VmState {
    /// VM is created but not started
    Created,
    /// VM is starting (boot in progress)
    Starting,
    /// VM is running and ready to execute commands
    Running,
    /// VM is paused (memory preserved)
    Paused,
    /// VM has stopped
    Stopped,
    /// VM has crashed
    Crashed,
}

impl std::fmt::Display for VmState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VmState::Created => write!(f, "created"),
            VmState::Starting => write!(f, "starting"),
            VmState::Running => write!(f, "running"),
            VmState::Paused => write!(f, "paused"),
            VmState::Stopped => write!(f, "stopped"),
            VmState::Crashed => write!(f, "crashed"),
        }
    }
}

/// Output from command execution
#[derive(Debug, Clone)]
pub struct ExecOutput {
    /// Exit code from the command
    pub exit_code: i32,
    /// Standard output
    pub stdout: Bytes,
    /// Standard error
    pub stderr: Bytes,
}

impl ExecOutput {
    /// Create a new ExecOutput
    pub fn new(exit_code: i32, stdout: impl Into<Bytes>, stderr: impl Into<Bytes>) -> Self {
        Self {
            exit_code,
            stdout: stdout.into(),
            stderr: stderr.into(),
        }
    }

    /// Check if the command succeeded (exit code 0)
    pub fn success(&self) -> bool {
        self.exit_code == 0
    }

    /// Get stdout as string (lossy UTF-8 conversion)
    pub fn stdout_str(&self) -> String {
        String::from_utf8_lossy(&self.stdout).into_owned()
    }

    /// Get stderr as string (lossy UTF-8 conversion)
    pub fn stderr_str(&self) -> String {
        String::from_utf8_lossy(&self.stderr).into_owned()
    }
}

/// Options for command execution
#[derive(Debug, Clone, Default)]
pub struct ExecOptions {
    /// Timeout in milliseconds (None = default timeout)
    pub timeout_ms: Option<u64>,
    /// Working directory for the command
    pub workdir: Option<String>,
    /// Environment variables for the command
    pub env: Vec<(String, String)>,
    /// Standard input to pass to the command
    pub stdin: Option<Bytes>,
}

impl ExecOptions {
    /// Create new exec options with a timeout
    pub fn with_timeout(timeout_ms: u64) -> Self {
        Self {
            timeout_ms: Some(timeout_ms),
            ..Default::default()
        }
    }
}

/// Trait for VM instance operations
///
/// This trait defines the lifecycle and operations for a VM instance.
/// Implementations can be:
/// - MockVm: For testing without libkrun
/// - LibkrunVm: For actual libkrun integration
#[async_trait]
pub trait VmInstance: Send + Sync {
    /// Get the VM's unique identifier
    fn id(&self) -> &str;

    /// Get the current state of the VM
    fn state(&self) -> VmState;

    /// Get the configuration used to create this VM
    fn config(&self) -> &VmConfig;

    /// Start the VM
    ///
    /// Transitions from Created -> Starting -> Running
    async fn start(&mut self) -> LibkrunResult<()>;

    /// Stop the VM
    ///
    /// Transitions from Running/Paused -> Stopped
    async fn stop(&mut self) -> LibkrunResult<()>;

    /// Pause the VM
    ///
    /// Transitions from Running -> Paused
    async fn pause(&mut self) -> LibkrunResult<()>;

    /// Resume the VM from paused state
    ///
    /// Transitions from Paused -> Running
    async fn resume(&mut self) -> LibkrunResult<()>;

    /// Execute a command in the VM
    ///
    /// Requires VM to be in Running state
    async fn exec(&self, cmd: &str, args: &[&str]) -> LibkrunResult<ExecOutput>;

    /// Execute a command with options
    ///
    /// Requires VM to be in Running state
    async fn exec_with_options(
        &self,
        cmd: &str,
        args: &[&str],
        options: ExecOptions,
    ) -> LibkrunResult<ExecOutput>;

    /// Create a snapshot of the VM state
    ///
    /// Can be called from Running or Paused state
    async fn snapshot(&self) -> LibkrunResult<VmSnapshot>;

    /// Restore VM from a snapshot
    ///
    /// Requires VM to be in Stopped or Created state
    async fn restore(&mut self, snapshot: &VmSnapshot) -> LibkrunResult<()>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vm_state_display() {
        assert_eq!(VmState::Created.to_string(), "created");
        assert_eq!(VmState::Running.to_string(), "running");
        assert_eq!(VmState::Paused.to_string(), "paused");
        assert_eq!(VmState::Stopped.to_string(), "stopped");
        assert_eq!(VmState::Crashed.to_string(), "crashed");
    }

    #[test]
    fn test_exec_output() {
        let output = ExecOutput::new(0, "hello", "");
        assert!(output.success());
        assert_eq!(output.stdout_str(), "hello");
        assert_eq!(output.stderr_str(), "");
    }

    #[test]
    fn test_exec_output_failure() {
        let output = ExecOutput::new(1, "", "error");
        assert!(!output.success());
        assert_eq!(output.stderr_str(), "error");
    }
}

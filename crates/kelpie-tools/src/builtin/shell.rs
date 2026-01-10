//! Shell command execution tool
//!
//! TigerStyle: Sandboxed shell execution with explicit limits.

use crate::error::{ToolError, ToolResult};
use crate::traits::{Tool, ToolCapability, ToolInput, ToolMetadata, ToolOutput, ToolParam};
use async_trait::async_trait;
use kelpie_sandbox::{ExecOptions, MockSandbox, Sandbox, SandboxConfig};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

/// Default shell timeout (60 seconds)
pub const SHELL_TIMEOUT_MS_DEFAULT: u64 = 60_000;

/// Maximum command output size (1MB)
pub const SHELL_OUTPUT_SIZE_BYTES_MAX: u64 = 1024 * 1024;

/// Shell command execution tool
///
/// Executes shell commands in a sandboxed environment.
pub struct ShellTool {
    /// Tool metadata
    metadata: ToolMetadata,
    /// Optional sandbox for execution
    sandbox: Option<Arc<RwLock<MockSandbox>>>,
}

impl ShellTool {
    /// Create a new shell tool
    pub fn new() -> Self {
        let metadata =
            ToolMetadata::new("shell", "Execute shell commands in a sandboxed environment")
                .with_param(ToolParam::string("command", "The shell command to execute"))
                .with_param(
                    ToolParam::string("workdir", "Working directory for command execution")
                        .optional(),
                )
                .with_param(
                    ToolParam::integer("timeout_ms", "Command timeout in milliseconds")
                        .with_default(SHELL_TIMEOUT_MS_DEFAULT as i64),
                )
                .with_capabilities(ToolCapability {
                    requires_network: false,
                    requires_filesystem: true,
                    can_modify_state: true,
                    is_deterministic: false,
                    is_safe: false,
                })
                .with_timeout(Duration::from_millis(SHELL_TIMEOUT_MS_DEFAULT));

        Self {
            metadata,
            sandbox: None,
        }
    }

    /// Create shell tool with a specific sandbox
    pub fn with_sandbox(sandbox: Arc<RwLock<MockSandbox>>) -> Self {
        let mut tool = Self::new();
        tool.sandbox = Some(sandbox);
        tool
    }

    /// Set up a default sandbox if none provided
    async fn get_or_create_sandbox(&self) -> ToolResult<Arc<RwLock<MockSandbox>>> {
        if let Some(sandbox) = &self.sandbox {
            return Ok(Arc::clone(sandbox));
        }

        // Create a new sandbox
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.map_err(|e| ToolError::SandboxError {
            tool: "shell".to_string(),
            reason: e.to_string(),
        })?;

        Ok(Arc::new(RwLock::new(sandbox)))
    }
}

impl Default for ShellTool {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Tool for ShellTool {
    fn metadata(&self) -> &ToolMetadata {
        &self.metadata
    }

    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
        let command = input
            .get_string("command")
            .ok_or_else(|| ToolError::MissingParameter {
                tool: "shell".to_string(),
                param: "command".to_string(),
            })?;

        let workdir = input.get_string("workdir").map(|s| s.to_string());
        let timeout_ms = input
            .get_i64("timeout_ms")
            .unwrap_or(SHELL_TIMEOUT_MS_DEFAULT as i64) as u64;

        let sandbox = self.get_or_create_sandbox().await?;
        let sandbox = sandbox.read().await;

        // Build exec options
        let mut exec_opts = ExecOptions::new()
            .with_timeout(Duration::from_millis(timeout_ms))
            .with_max_output(SHELL_OUTPUT_SIZE_BYTES_MAX);

        if let Some(dir) = workdir {
            exec_opts = exec_opts.with_workdir(dir);
        }

        // Parse command into executable and args
        let parts: Vec<&str> = command.split_whitespace().collect();
        if parts.is_empty() {
            return Err(ToolError::InvalidInput {
                tool: "shell".to_string(),
                reason: "empty command".to_string(),
            });
        }

        let (cmd, args) = (parts[0], &parts[1..]);

        // Execute in sandbox
        let output =
            sandbox
                .exec(cmd, args, exec_opts)
                .await
                .map_err(|e| ToolError::ExecutionFailed {
                    tool: "shell".to_string(),
                    reason: e.to_string(),
                })?;

        if output.is_success() {
            Ok(ToolOutput::success(serde_json::json!({
                "stdout": output.stdout_string(),
                "stderr": output.stderr_string(),
                "exit_code": output.status.code,
                "duration_ms": output.duration_ms,
            }))
            .with_metadata("exit_code", output.status.code))
        } else {
            Ok(ToolOutput::failure(format!(
                "Command exited with code {}: {}",
                output.status.code,
                output.stderr_string()
            ))
            .with_metadata("exit_code", output.status.code)
            .with_metadata("stdout", output.stdout_string())
            .with_metadata("stderr", output.stderr_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_shell_tool_metadata() {
        let tool = ShellTool::new();
        let metadata = tool.metadata();

        assert_eq!(metadata.name, "shell");
        assert!(metadata.get_param("command").is_some());
        assert!(metadata.is_param_required("command"));
    }

    #[tokio::test]
    async fn test_shell_tool_execute_echo() {
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.unwrap();
        let sandbox = Arc::new(RwLock::new(sandbox));

        let tool = ShellTool::with_sandbox(sandbox);
        let input = ToolInput::new("shell").with_param("command", "echo hello");

        let output = tool.execute(input).await.unwrap();
        assert!(output.is_success());
    }

    #[tokio::test]
    async fn test_shell_tool_execute_failure() {
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.unwrap();
        let sandbox = Arc::new(RwLock::new(sandbox));

        let tool = ShellTool::with_sandbox(sandbox);
        let input = ToolInput::new("shell").with_param("command", "false");

        let output = tool.execute(input).await.unwrap();
        assert!(!output.is_success());
    }

    #[tokio::test]
    async fn test_shell_tool_missing_command() {
        let tool = ShellTool::new();
        let input = ToolInput::new("shell"); // No command parameter

        let result = tool.execute(input).await;
        assert!(matches!(result, Err(ToolError::MissingParameter { .. })));
    }

    #[tokio::test]
    async fn test_shell_tool_empty_command() {
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.unwrap();
        let sandbox = Arc::new(RwLock::new(sandbox));

        let tool = ShellTool::with_sandbox(sandbox);
        let input = ToolInput::new("shell").with_param("command", "");

        let result = tool.execute(input).await;
        assert!(matches!(result, Err(ToolError::InvalidInput { .. })));
    }
}

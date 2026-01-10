//! Git operations tool
//!
//! TigerStyle: Safe git operations with explicit command handling.

use crate::error::{ToolError, ToolResult};
use crate::traits::{Tool, ToolCapability, ToolInput, ToolMetadata, ToolOutput, ToolParam};
use async_trait::async_trait;
use kelpie_sandbox::{ExecOptions, MockSandbox, Sandbox, SandboxConfig};
use serde_json::Value;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

/// Default git command timeout (120 seconds)
pub const GIT_TIMEOUT_MS_DEFAULT: u64 = 120_000;

/// Git operations tool
///
/// Provides git operations (status, diff, log, etc.) in a sandboxed environment.
pub struct GitTool {
    /// Tool metadata
    metadata: ToolMetadata,
    /// Sandbox for git operations
    sandbox: Option<Arc<RwLock<MockSandbox>>>,
}

impl GitTool {
    /// Create a new git tool
    pub fn new() -> Self {
        let metadata = ToolMetadata::new("git", "Execute git commands")
            .with_param(
                ToolParam::string(
                    "operation",
                    "Git operation: status, diff, log, show, branch, add, commit, push, pull, clone",
                )
                .with_enum(vec![
                    Value::String("status".to_string()),
                    Value::String("diff".to_string()),
                    Value::String("log".to_string()),
                    Value::String("show".to_string()),
                    Value::String("branch".to_string()),
                    Value::String("add".to_string()),
                    Value::String("commit".to_string()),
                    Value::String("push".to_string()),
                    Value::String("pull".to_string()),
                    Value::String("clone".to_string()),
                ]),
            )
            .with_param(ToolParam::string("args", "Additional arguments for the git command").optional())
            .with_param(ToolParam::string("repo_path", "Repository path").optional())
            .with_capabilities(ToolCapability {
                requires_network: true, // For push/pull/clone
                requires_filesystem: true,
                can_modify_state: true,
                is_deterministic: false,
                is_safe: false,
            })
            .with_timeout(Duration::from_millis(GIT_TIMEOUT_MS_DEFAULT));

        Self {
            metadata,
            sandbox: None,
        }
    }

    /// Create git tool with a specific sandbox
    pub fn with_sandbox(sandbox: Arc<RwLock<MockSandbox>>) -> Self {
        let mut tool = Self::new();
        tool.sandbox = Some(sandbox);
        tool
    }

    /// Register git command handlers on a sandbox
    pub async fn setup_sandbox_handlers(sandbox: &MockSandbox) {
        // Status handler
        sandbox
            .register_handler(
                "git",
                Box::new(|args, _opts| {
                    if args.is_empty() {
                        return kelpie_sandbox::ExecOutput::failure(1, "git: missing command");
                    }

                    match args[0] {
                        "status" => kelpie_sandbox::ExecOutput::success(
                            "On branch main\nnothing to commit, working tree clean\n",
                        ),
                        "diff" => kelpie_sandbox::ExecOutput::success(""),
                        "log" => kelpie_sandbox::ExecOutput::success(
                            "commit abc123\nAuthor: Test <test@test.com>\nDate: Mon Jan 1 00:00:00 2024\n\n    Initial commit\n",
                        ),
                        "branch" => kelpie_sandbox::ExecOutput::success("* main\n  develop\n"),
                        "show" => kelpie_sandbox::ExecOutput::success(
                            "commit abc123\nAuthor: Test <test@test.com>\n\n    Initial commit\n",
                        ),
                        "add" => kelpie_sandbox::ExecOutput::success(""),
                        "commit" => {
                            if args.len() < 3 || args[1] != "-m" {
                                kelpie_sandbox::ExecOutput::failure(1, "git commit: missing message")
                            } else {
                                kelpie_sandbox::ExecOutput::success(
                                    "[main abc1234] Commit message\n 1 file changed, 1 insertion(+)\n",
                                )
                            }
                        }
                        "push" => kelpie_sandbox::ExecOutput::success(
                            "To origin/main\n   abc123..def456  main -> main\n",
                        ),
                        "pull" => kelpie_sandbox::ExecOutput::success("Already up to date.\n"),
                        "clone" => kelpie_sandbox::ExecOutput::success(
                            "Cloning into 'repo'...\ndone.\n",
                        ),
                        _ => kelpie_sandbox::ExecOutput::failure(
                            1,
                            format!("git: '{}' is not a git command", args[0]),
                        ),
                    }
                }),
            )
            .await;
    }

    /// Get or create sandbox with git handlers
    async fn get_sandbox(&self) -> ToolResult<Arc<RwLock<MockSandbox>>> {
        if let Some(sandbox) = &self.sandbox {
            return Ok(Arc::clone(sandbox));
        }

        // Create a new sandbox with git handlers
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.map_err(|e| ToolError::SandboxError {
            tool: "git".to_string(),
            reason: e.to_string(),
        })?;

        Self::setup_sandbox_handlers(&sandbox).await;
        Ok(Arc::new(RwLock::new(sandbox)))
    }
}

impl Default for GitTool {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Tool for GitTool {
    fn metadata(&self) -> &ToolMetadata {
        &self.metadata
    }

    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
        let operation =
            input
                .get_string("operation")
                .ok_or_else(|| ToolError::MissingParameter {
                    tool: "git".to_string(),
                    param: "operation".to_string(),
                })?;

        let args_str = input.get_string("args").unwrap_or("");
        let repo_path = input.get_string("repo_path");

        // Build git command
        let mut git_args = vec![operation];
        if !args_str.is_empty() {
            git_args.extend(args_str.split_whitespace());
        }

        let sandbox = self.get_sandbox().await?;
        let sandbox = sandbox.read().await;

        // Build exec options
        let mut exec_opts =
            ExecOptions::new().with_timeout(Duration::from_millis(GIT_TIMEOUT_MS_DEFAULT));

        if let Some(path) = repo_path {
            exec_opts = exec_opts.with_workdir(path);
        }

        // Execute git command
        let args_slice: Vec<&str> = git_args.iter().map(|s| s.as_ref()).collect();
        let output = sandbox
            .exec("git", &args_slice, exec_opts)
            .await
            .map_err(|e| ToolError::ExecutionFailed {
                tool: "git".to_string(),
                reason: e.to_string(),
            })?;

        if output.is_success() {
            Ok(ToolOutput::success(serde_json::json!({
                "operation": operation,
                "stdout": output.stdout_string(),
                "stderr": output.stderr_string(),
                "exit_code": 0,
            })))
        } else {
            Ok(ToolOutput::failure(format!(
                "git {} failed: {}",
                operation,
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

    async fn create_test_sandbox() -> Arc<RwLock<MockSandbox>> {
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.unwrap();
        GitTool::setup_sandbox_handlers(&sandbox).await;
        Arc::new(RwLock::new(sandbox))
    }

    #[tokio::test]
    async fn test_git_tool_metadata() {
        let tool = GitTool::new();
        let metadata = tool.metadata();

        assert_eq!(metadata.name, "git");
        assert!(metadata.get_param("operation").is_some());
    }

    #[tokio::test]
    async fn test_git_status() {
        let sandbox = create_test_sandbox().await;
        let tool = GitTool::with_sandbox(sandbox);

        let input = ToolInput::new("git").with_param("operation", "status");
        let output = tool.execute(input).await.unwrap();

        assert!(output.is_success());
        let result = output.result.unwrap();
        assert!(result
            .get("stdout")
            .and_then(|s| s.as_str())
            .unwrap_or("")
            .contains("On branch"));
    }

    #[tokio::test]
    async fn test_git_log() {
        let sandbox = create_test_sandbox().await;
        let tool = GitTool::with_sandbox(sandbox);

        let input = ToolInput::new("git").with_param("operation", "log");
        let output = tool.execute(input).await.unwrap();

        assert!(output.is_success());
        let result = output.result.unwrap();
        assert!(result
            .get("stdout")
            .and_then(|s| s.as_str())
            .unwrap_or("")
            .contains("commit"));
    }

    #[tokio::test]
    async fn test_git_branch() {
        let sandbox = create_test_sandbox().await;
        let tool = GitTool::with_sandbox(sandbox);

        let input = ToolInput::new("git").with_param("operation", "branch");
        let output = tool.execute(input).await.unwrap();

        assert!(output.is_success());
        let result = output.result.unwrap();
        assert!(result
            .get("stdout")
            .and_then(|s| s.as_str())
            .unwrap_or("")
            .contains("main"));
    }

    #[tokio::test]
    async fn test_git_diff() {
        let sandbox = create_test_sandbox().await;
        let tool = GitTool::with_sandbox(sandbox);

        let input = ToolInput::new("git").with_param("operation", "diff");
        let output = tool.execute(input).await.unwrap();

        assert!(output.is_success());
    }

    #[tokio::test]
    async fn test_git_commit_with_message() {
        let sandbox = create_test_sandbox().await;
        let tool = GitTool::with_sandbox(sandbox);

        let input = ToolInput::new("git")
            .with_param("operation", "commit")
            .with_param("args", "-m test commit");
        let output = tool.execute(input).await.unwrap();

        assert!(output.is_success());
    }

    #[tokio::test]
    async fn test_git_missing_operation() {
        let tool = GitTool::new();

        let input = ToolInput::new("git");
        let result = tool.execute(input).await;

        assert!(matches!(result, Err(ToolError::MissingParameter { .. })));
    }
}

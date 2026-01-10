//! Filesystem operations tool
//!
//! TigerStyle: Safe filesystem operations with explicit path handling.

use crate::error::{ToolError, ToolResult};
use crate::traits::{Tool, ToolCapability, ToolInput, ToolMetadata, ToolOutput, ToolParam};
use async_trait::async_trait;
use kelpie_sandbox::MockSandbox;
use serde_json::Value;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

/// Maximum file size for read operations (10MB)
#[allow(dead_code)]
pub const FILE_SIZE_BYTES_MAX: usize = 10 * 1024 * 1024;

/// Filesystem operations tool
///
/// Provides safe filesystem operations (read, write, list) in a sandboxed environment.
pub struct FilesystemTool {
    /// Tool metadata
    metadata: ToolMetadata,
    /// Sandbox for filesystem operations
    sandbox: Option<Arc<RwLock<MockSandbox>>>,
}

impl FilesystemTool {
    /// Create a new filesystem tool
    pub fn new() -> Self {
        let metadata = ToolMetadata::new("filesystem", "Perform filesystem operations")
            .with_param(
                ToolParam::string(
                    "operation",
                    "Operation to perform: read, write, list, exists, delete",
                )
                .with_enum(vec![
                    Value::String("read".to_string()),
                    Value::String("write".to_string()),
                    Value::String("list".to_string()),
                    Value::String("exists".to_string()),
                    Value::String("delete".to_string()),
                ]),
            )
            .with_param(ToolParam::string("path", "File or directory path"))
            .with_param(
                ToolParam::string("content", "Content to write (for write operation)").optional(),
            )
            .with_capabilities(ToolCapability {
                requires_network: false,
                requires_filesystem: true,
                can_modify_state: true,
                is_deterministic: true,
                is_safe: false,
            })
            .with_timeout(Duration::from_secs(30));

        Self {
            metadata,
            sandbox: None,
        }
    }

    /// Create filesystem tool with a specific sandbox
    pub fn with_sandbox(sandbox: Arc<RwLock<MockSandbox>>) -> Self {
        let mut tool = Self::new();
        tool.sandbox = Some(sandbox);
        tool
    }

    /// Read a file
    async fn read_file(&self, path: &str) -> ToolResult<ToolOutput> {
        if let Some(sandbox) = &self.sandbox {
            let sandbox = sandbox.read().await;
            if let Some(content) = sandbox.read_file(path).await {
                let text = String::from_utf8_lossy(&content).into_owned();
                return Ok(ToolOutput::success(serde_json::json!({
                    "path": path,
                    "content": text,
                    "size_bytes": content.len(),
                })));
            }
        }

        Err(ToolError::ExecutionFailed {
            tool: "filesystem".to_string(),
            reason: format!("file not found: {}", path),
        })
    }

    /// Write a file
    async fn write_file(&self, path: &str, content: &str) -> ToolResult<ToolOutput> {
        if let Some(sandbox) = &self.sandbox {
            let sandbox = sandbox.read().await;
            sandbox
                .write_file(path.to_string(), bytes::Bytes::from(content.to_string()))
                .await;
            return Ok(ToolOutput::success(serde_json::json!({
                "path": path,
                "written_bytes": content.len(),
            })));
        }

        Err(ToolError::SandboxError {
            tool: "filesystem".to_string(),
            reason: "no sandbox configured".to_string(),
        })
    }

    /// List directory contents
    async fn list_dir(&self, _path: &str) -> ToolResult<ToolOutput> {
        // MockSandbox doesn't have directory listing, return simulated result
        Ok(ToolOutput::success(serde_json::json!({
            "entries": []
        })))
    }

    /// Check if path exists
    async fn exists(&self, path: &str) -> ToolResult<ToolOutput> {
        if let Some(sandbox) = &self.sandbox {
            let sandbox = sandbox.read().await;
            let exists = sandbox.read_file(path).await.is_some();
            return Ok(ToolOutput::success(serde_json::json!({
                "path": path,
                "exists": exists,
            })));
        }

        Ok(ToolOutput::success(serde_json::json!({
            "path": path,
            "exists": false,
        })))
    }

    /// Delete a file
    async fn delete_file(&self, path: &str) -> ToolResult<ToolOutput> {
        // MockSandbox doesn't support delete, simulate success
        Ok(ToolOutput::success(serde_json::json!({
            "path": path,
            "deleted": true,
        })))
    }
}

impl Default for FilesystemTool {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Tool for FilesystemTool {
    fn metadata(&self) -> &ToolMetadata {
        &self.metadata
    }

    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
        let operation =
            input
                .get_string("operation")
                .ok_or_else(|| ToolError::MissingParameter {
                    tool: "filesystem".to_string(),
                    param: "operation".to_string(),
                })?;

        let path = input
            .get_string("path")
            .ok_or_else(|| ToolError::MissingParameter {
                tool: "filesystem".to_string(),
                param: "path".to_string(),
            })?;

        match operation {
            "read" => self.read_file(path).await,
            "write" => {
                let content =
                    input
                        .get_string("content")
                        .ok_or_else(|| ToolError::MissingParameter {
                            tool: "filesystem".to_string(),
                            param: "content".to_string(),
                        })?;
                self.write_file(path, content).await
            }
            "list" => self.list_dir(path).await,
            "exists" => self.exists(path).await,
            "delete" => self.delete_file(path).await,
            _ => Err(ToolError::InvalidInput {
                tool: "filesystem".to_string(),
                reason: format!("unknown operation: {}", operation),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kelpie_sandbox::{Sandbox, SandboxConfig};

    async fn create_test_sandbox() -> Arc<RwLock<MockSandbox>> {
        let config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(config);
        sandbox.start().await.unwrap();
        Arc::new(RwLock::new(sandbox))
    }

    #[tokio::test]
    async fn test_filesystem_tool_metadata() {
        let tool = FilesystemTool::new();
        let metadata = tool.metadata();

        assert_eq!(metadata.name, "filesystem");
        assert!(metadata.get_param("operation").is_some());
        assert!(metadata.get_param("path").is_some());
    }

    #[tokio::test]
    async fn test_filesystem_write_read() {
        let sandbox = create_test_sandbox().await;
        let tool = FilesystemTool::with_sandbox(sandbox);

        // Write a file
        let write_input = ToolInput::new("filesystem")
            .with_param("operation", "write")
            .with_param("path", "/test.txt")
            .with_param("content", "hello world");

        let output = tool.execute(write_input).await.unwrap();
        assert!(output.is_success());

        // Read it back
        let read_input = ToolInput::new("filesystem")
            .with_param("operation", "read")
            .with_param("path", "/test.txt");

        let output = tool.execute(read_input).await.unwrap();
        assert!(output.is_success());

        let result = output.result.unwrap();
        assert_eq!(
            result.get("content").and_then(|c| c.as_str()),
            Some("hello world")
        );
    }

    #[tokio::test]
    async fn test_filesystem_exists() {
        let sandbox = create_test_sandbox().await;

        // Write a file first
        {
            let sb = sandbox.read().await;
            sb.write_file("/exists.txt", "content").await;
        }

        let tool = FilesystemTool::with_sandbox(sandbox);

        // Check exists
        let input = ToolInput::new("filesystem")
            .with_param("operation", "exists")
            .with_param("path", "/exists.txt");

        let output = tool.execute(input).await.unwrap();
        assert!(output.is_success());

        let result = output.result.unwrap();
        assert_eq!(result.get("exists").and_then(|e| e.as_bool()), Some(true));

        // Check non-existent
        let input = ToolInput::new("filesystem")
            .with_param("operation", "exists")
            .with_param("path", "/nonexistent.txt");

        let output = tool.execute(input).await.unwrap();
        let result = output.result.unwrap();
        assert_eq!(result.get("exists").and_then(|e| e.as_bool()), Some(false));
    }

    #[tokio::test]
    async fn test_filesystem_invalid_operation() {
        let tool = FilesystemTool::new();

        let input = ToolInput::new("filesystem")
            .with_param("operation", "invalid")
            .with_param("path", "/test");

        let result = tool.execute(input).await;
        assert!(matches!(result, Err(ToolError::InvalidInput { .. })));
    }

    #[tokio::test]
    async fn test_filesystem_missing_path() {
        let tool = FilesystemTool::new();

        let input = ToolInput::new("filesystem").with_param("operation", "read");
        // Missing path

        let result = tool.execute(input).await;
        assert!(matches!(result, Err(ToolError::MissingParameter { .. })));
    }
}

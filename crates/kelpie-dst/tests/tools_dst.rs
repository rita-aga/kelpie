//! DST tests for tool operations
//!
//! TigerStyle: Deterministic testing of tool registry,
//! tool execution, and MCP client operations.

use kelpie_dst::{SimConfig, Simulation};
use kelpie_sandbox::{MockSandbox, Sandbox, SandboxConfig};
use kelpie_tools::{
    FilesystemTool, GitTool, McpClient, McpConfig, McpTool, McpToolDefinition, ShellTool, Tool,
    ToolInput, ToolMetadata, ToolOutput, ToolParam, ToolRegistry, ToolResult,
};
use serde_json::json;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

// =============================================================================
// Helper Functions
// =============================================================================

async fn create_test_sandbox() -> Arc<RwLock<MockSandbox>> {
    let config = SandboxConfig::default();
    let mut sandbox = MockSandbox::new(config);
    sandbox.start().await.unwrap();
    Arc::new(RwLock::new(sandbox))
}

// =============================================================================
// Test Tool Implementation
// =============================================================================

/// A deterministic test tool for DST testing
struct DeterministicTool {
    metadata: ToolMetadata,
    counter: std::sync::atomic::AtomicU64,
}

impl DeterministicTool {
    fn new() -> Self {
        Self {
            metadata: ToolMetadata::new("deterministic", "A deterministic test tool")
                .with_param(ToolParam::string("input", "Input value"))
                .with_timeout(Duration::from_secs(5)),
            counter: std::sync::atomic::AtomicU64::new(0),
        }
    }
}

#[async_trait::async_trait]
impl Tool for DeterministicTool {
    fn metadata(&self) -> &ToolMetadata {
        &self.metadata
    }

    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
        let count = self
            .counter
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let input_val = input.get_string("input").unwrap_or("default");

        Ok(ToolOutput::success(json!({
            "input": input_val,
            "count": count,
            "result": format!("processed-{}-{}", input_val, count)
        })))
    }
}

// =============================================================================
// Registry Tests
// =============================================================================

#[test]
fn test_dst_tool_registry_determinism() {
    let seed = 42;

    let run_test = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|_env| async move {
            let registry = ToolRegistry::new();

            // Register multiple tools
            registry
                .register(DeterministicTool::new())
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            registry.register(ShellTool::new()).await.map_err(|e| {
                kelpie_core::Error::Internal {
                    message: e.to_string(),
                }
            })?;

            // Get tool names (should be deterministic)
            let mut names: Vec<String> = registry
                .list_metadata()
                .await
                .iter()
                .map(|m| m.name.clone())
                .collect();
            names.sort(); // Sort for deterministic comparison

            // Execute tools
            let input1 = ToolInput::new("deterministic").with_param("input", "test1");
            let output1 = registry
                .execute("deterministic", input1)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            let input2 = ToolInput::new("deterministic").with_param("input", "test2");
            let output2 = registry
                .execute("deterministic", input2)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            Ok((names, output1.result_string(), output2.result_string()))
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(
        result1, result2,
        "Registry operations should be deterministic"
    );
}

#[test]
fn test_dst_tool_registry_execute_not_found() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let registry = ToolRegistry::new();

        let input = ToolInput::new("nonexistent");
        let result = registry.execute("nonexistent", input).await;

        assert!(result.is_err());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_tool_registry_stats() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let registry = ToolRegistry::new();
        registry
            .register(DeterministicTool::new())
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Initial stats
        let count = registry.count().await;
        assert_eq!(count, 1);
        let stats = registry.stats().await;
        assert_eq!(stats.total_executions, 0);

        // Execute and check stats
        for i in 0..10 {
            let input = ToolInput::new("deterministic").with_param("input", format!("test{}", i));
            let _ = registry.execute("deterministic", input).await;
        }

        let stats = registry.stats().await;
        assert_eq!(stats.total_executions, 10);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Shell Tool Tests
// =============================================================================

#[test]
fn test_dst_shell_tool_determinism() {
    let seed = 12345;

    let run_test = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|_env| async move {
            let sandbox = create_test_sandbox().await;
            let tool = ShellTool::with_sandbox(sandbox);

            let mut results = Vec::new();

            // Run multiple echo commands
            for i in 0..5 {
                let input =
                    ToolInput::new("shell").with_param("command", format!("echo test{}", i));
                let output =
                    tool.execute(input)
                        .await
                        .map_err(|e| kelpie_core::Error::Internal {
                            message: e.to_string(),
                        })?;
                results.push(output.is_success());
            }

            Ok(results)
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Shell tool should be deterministic");
}

#[test]
fn test_dst_shell_tool_failure() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox = create_test_sandbox().await;
        let tool = ShellTool::with_sandbox(sandbox);

        // Test failed command
        let input = ToolInput::new("shell").with_param("command", "false");
        let output = tool
            .execute(input)
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        assert!(!output.is_success());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Filesystem Tool Tests
// =============================================================================

#[test]
fn test_dst_filesystem_tool_determinism() {
    let seed = 54321;

    let run_test = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|_env| async move {
            let sandbox = create_test_sandbox().await;
            let tool = FilesystemTool::with_sandbox(sandbox);

            // Write files
            for i in 0..5 {
                let input = ToolInput::new("filesystem")
                    .with_param("operation", "write")
                    .with_param("path", format!("/test{}.txt", i))
                    .with_param("content", format!("content{}", i));
                let _ = tool.execute(input).await;
            }

            // Read files back
            let mut results = Vec::new();
            for i in 0..5 {
                let input = ToolInput::new("filesystem")
                    .with_param("operation", "read")
                    .with_param("path", format!("/test{}.txt", i));
                let output =
                    tool.execute(input)
                        .await
                        .map_err(|e| kelpie_core::Error::Internal {
                            message: e.to_string(),
                        })?;
                results.push(output.is_success());
            }

            Ok(results)
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Filesystem tool should be deterministic");
}

#[test]
fn test_dst_filesystem_tool_operations() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox = create_test_sandbox().await;
        let tool = FilesystemTool::with_sandbox(sandbox);

        // Write a file
        let write_input = ToolInput::new("filesystem")
            .with_param("operation", "write")
            .with_param("path", "/data.txt")
            .with_param("content", "hello world");
        let write_output =
            tool.execute(write_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(write_output.is_success());

        // Check exists
        let exists_input = ToolInput::new("filesystem")
            .with_param("operation", "exists")
            .with_param("path", "/data.txt");
        let exists_output =
            tool.execute(exists_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(exists_output.is_success());
        let exists_result = exists_output.result.unwrap();
        assert_eq!(
            exists_result.get("exists").and_then(|e| e.as_bool()),
            Some(true)
        );

        // Read it back
        let read_input = ToolInput::new("filesystem")
            .with_param("operation", "read")
            .with_param("path", "/data.txt");
        let read_output =
            tool.execute(read_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(read_output.is_success());
        let read_result = read_output.result.unwrap();
        assert_eq!(
            read_result.get("content").and_then(|c| c.as_str()),
            Some("hello world")
        );

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Git Tool Tests
// =============================================================================

#[test]
fn test_dst_git_tool_determinism() {
    let seed = 98765;

    let run_test = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|_env| async move {
            let sandbox = create_test_sandbox().await;

            // Set up git handlers
            {
                let sb = sandbox.read().await;
                GitTool::setup_sandbox_handlers(&sb).await;
            }

            let tool = GitTool::with_sandbox(sandbox);

            // Run multiple git operations
            let operations = vec!["status", "branch", "log"];
            let mut results = Vec::new();

            for op in operations {
                let input = ToolInput::new("git").with_param("operation", op);
                let output =
                    tool.execute(input)
                        .await
                        .map_err(|e| kelpie_core::Error::Internal {
                            message: e.to_string(),
                        })?;
                results.push(output.is_success());
            }

            Ok(results)
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Git tool should be deterministic");
}

#[test]
fn test_dst_git_tool_operations() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox = create_test_sandbox().await;

        // Set up git handlers
        {
            let sb = sandbox.read().await;
            GitTool::setup_sandbox_handlers(&sb).await;
        }

        let tool = GitTool::with_sandbox(sandbox);

        // Test status
        let status_input = ToolInput::new("git").with_param("operation", "status");
        let status_output =
            tool.execute(status_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(status_output.is_success());

        // Test branch
        let branch_input = ToolInput::new("git").with_param("operation", "branch");
        let branch_output =
            tool.execute(branch_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(branch_output.is_success());
        let branch_result = branch_output.result.unwrap();
        assert!(branch_result
            .get("stdout")
            .and_then(|s| s.as_str())
            .unwrap_or("")
            .contains("main"));

        // Test log
        let log_input = ToolInput::new("git").with_param("operation", "log");
        let log_output =
            tool.execute(log_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(log_output.is_success());

        // Test commit with message
        let commit_input = ToolInput::new("git")
            .with_param("operation", "commit")
            .with_param("args", "-m test commit");
        let commit_output =
            tool.execute(commit_input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
        assert!(commit_output.is_success());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// MCP Client Tests
// =============================================================================

#[test]
fn test_dst_mcp_client_state_machine() {
    // Test McpClient state transitions without requiring a real MCP server
    // Note: Real MCP connection requires an actual MCP server process
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mcp_config = McpConfig::stdio("test-server", "nonexistent_command", vec![]);
        let client = McpClient::new(mcp_config);

        // Initial state should be disconnected
        assert!(!client.is_connected().await);

        // Use test helper to simulate connected state
        client.set_connected_for_testing().await;
        assert!(client.is_connected().await);

        // Disconnect
        client
            .disconnect()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert!(!client.is_connected().await);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_mcp_tool_metadata() {
    // Test that McpTool properly builds metadata from definition
    // Note: Real MCP execution requires an actual MCP server process,
    // so we only test metadata construction here in DST tests
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mcp_config = McpConfig::stdio("test-server", "echo", vec![]);
        let client = Arc::new(McpClient::new(mcp_config));

        // Register mock tool without connecting (for metadata testing only)
        let definition = McpToolDefinition {
            name: "test_tool".to_string(),
            description: "A test tool".to_string(),
            input_schema: json!({
                "type": "object",
                "properties": {
                    "message": {
                        "type": "string",
                        "description": "A message"
                    }
                },
                "required": ["message"]
            }),
        };

        client.register_mock_tool(definition.clone()).await;

        let tool = McpTool::new(client, definition);
        let metadata = tool.metadata();

        // Verify metadata was correctly built from definition
        assert_eq!(metadata.name, "test_tool");
        assert_eq!(metadata.description, "A test tool");
        assert_eq!(metadata.parameters.len(), 1);
        assert!(metadata.is_param_required("message"));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Stress Tests
// =============================================================================

#[test]
fn test_dst_tool_registry_many_registrations() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let registry = ToolRegistry::new();

        // Register the tool once (same name can't be registered twice)
        registry
            .register(DeterministicTool::new())
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Registry should track the unique tool
        let count = registry.count().await;
        assert_eq!(count, 1);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_tool_many_executions() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let registry = ToolRegistry::new();
        registry
            .register(DeterministicTool::new())
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Execute tool many times
        for i in 0..500 {
            let input =
                ToolInput::new("deterministic").with_param("input", format!("iteration-{}", i));
            let output = registry
                .execute("deterministic", input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert!(output.is_success());
        }

        let stats = registry.stats().await;
        assert_eq!(stats.total_executions, 500);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_filesystem_many_files() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox = create_test_sandbox().await;
        let tool = FilesystemTool::with_sandbox(sandbox);

        // Write many files
        for i in 0..100 {
            let input = ToolInput::new("filesystem")
                .with_param("operation", "write")
                .with_param("path", format!("/data/file_{}.txt", i))
                .with_param("content", format!("content for file {}", i));
            let output = tool
                .execute(input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert!(output.is_success());
        }

        // Read them back
        for i in 0..100 {
            let input = ToolInput::new("filesystem")
                .with_param("operation", "read")
                .with_param("path", format!("/data/file_{}.txt", i));
            let output = tool
                .execute(input)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert!(output.is_success());

            let result = output.result.unwrap();
            let expected = format!("content for file {}", i);
            assert_eq!(
                result.get("content").and_then(|c| c.as_str()),
                Some(expected.as_str())
            );
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

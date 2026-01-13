//! Unified Tool Registry Implementation
//!
//! TigerStyle: Single registry for all tool types with explicit source tracking.

use crate::llm::ToolDefinition;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Identifies where a tool comes from
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ToolSource {
    /// Built-in Rust tool
    Builtin,
    /// MCP server with server name
    Mcp { server: String },
    /// Custom user-defined tool
    Custom,
}

impl std::fmt::Display for ToolSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToolSource::Builtin => write!(f, "builtin"),
            ToolSource::Mcp { server } => write!(f, "mcp:{}", server),
            ToolSource::Custom => write!(f, "custom"),
        }
    }
}

/// A registered tool with its metadata and source
#[derive(Debug, Clone)]
pub struct RegisteredTool {
    /// Tool definition (for LLM)
    pub definition: ToolDefinition,
    /// Where this tool comes from
    pub source: ToolSource,
    /// Optional description (more detailed than in definition)
    pub description: Option<String>,
}

/// Result of tool execution
#[derive(Debug, Clone)]
pub struct ToolExecutionResult {
    /// Output from the tool
    pub output: String,
    /// Whether execution succeeded
    pub success: bool,
    /// Execution time in milliseconds
    pub duration_ms: u64,
    /// Error message if failed
    pub error: Option<String>,
}

impl ToolExecutionResult {
    /// Create a successful result
    pub fn success(output: impl Into<String>, duration_ms: u64) -> Self {
        Self {
            output: output.into(),
            success: true,
            duration_ms,
            error: None,
        }
    }

    /// Create a failed result
    pub fn failure(error: impl Into<String>, duration_ms: u64) -> Self {
        let error_str = error.into();
        Self {
            output: error_str.clone(),
            success: false,
            duration_ms,
            error: Some(error_str),
        }
    }
}

/// Handler function type for builtin tools
pub type BuiltinToolHandler =
    Arc<dyn Fn(&Value) -> std::pin::Pin<Box<dyn std::future::Future<Output = String> + Send>> + Send + Sync>;

/// Unified tool registry combining all tool sources
pub struct UnifiedToolRegistry {
    /// All registered tools by name
    tools: RwLock<HashMap<String, RegisteredTool>>,
    /// Builtin tool handlers
    builtin_handlers: RwLock<HashMap<String, BuiltinToolHandler>>,
    /// MCP client pool (server_name -> client)
    /// For now, this is a placeholder - will be connected to actual MCP clients
    #[cfg(feature = "dst")]
    sim_mcp_client: RwLock<Option<Arc<kelpie_tools::SimMcpClient>>>,
}

impl UnifiedToolRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self {
            tools: RwLock::new(HashMap::new()),
            builtin_handlers: RwLock::new(HashMap::new()),
            #[cfg(feature = "dst")]
            sim_mcp_client: RwLock::new(None),
        }
    }

    /// Register a builtin tool
    pub async fn register_builtin(
        &self,
        name: impl Into<String>,
        description: impl Into<String>,
        input_schema: Value,
        handler: BuiltinToolHandler,
    ) {
        let name = name.into();
        let description_str = description.into();

        // TigerStyle: Preconditions
        assert!(!name.is_empty(), "tool name cannot be empty");

        let definition = ToolDefinition {
            name: name.clone(),
            description: description_str.clone(),
            input_schema,
        };

        let tool = RegisteredTool {
            definition,
            source: ToolSource::Builtin,
            description: Some(description_str),
        };

        self.tools.write().await.insert(name.clone(), tool);
        self.builtin_handlers.write().await.insert(name, handler);
    }

    /// Register an MCP tool
    pub async fn register_mcp_tool(
        &self,
        name: impl Into<String>,
        description: impl Into<String>,
        input_schema: Value,
        server_name: impl Into<String>,
    ) {
        let name = name.into();
        let description_str = description.into();
        let server = server_name.into();

        // TigerStyle: Preconditions
        assert!(!name.is_empty(), "tool name cannot be empty");
        assert!(!server.is_empty(), "server name cannot be empty");

        let definition = ToolDefinition {
            name: name.clone(),
            description: description_str.clone(),
            input_schema,
        };

        let tool = RegisteredTool {
            definition,
            source: ToolSource::Mcp {
                server: server.clone(),
            },
            description: Some(description_str),
        };

        self.tools.write().await.insert(name, tool);
    }

    /// Set simulated MCP client for DST testing
    #[cfg(feature = "dst")]
    pub async fn set_sim_mcp_client(&self, client: Arc<kelpie_tools::SimMcpClient>) {
        *self.sim_mcp_client.write().await = Some(client);
    }

    /// Get all tool definitions for LLM
    pub async fn get_tool_definitions(&self) -> Vec<ToolDefinition> {
        self.tools
            .read()
            .await
            .values()
            .map(|t| t.definition.clone())
            .collect()
    }

    /// Get a specific tool by name
    pub async fn get_tool(&self, name: &str) -> Option<RegisteredTool> {
        self.tools.read().await.get(name).cloned()
    }

    /// Check if a tool exists
    pub async fn has_tool(&self, name: &str) -> bool {
        self.tools.read().await.contains_key(name)
    }

    /// Get tool source
    pub async fn get_tool_source(&self, name: &str) -> Option<ToolSource> {
        self.tools.read().await.get(name).map(|t| t.source.clone())
    }

    /// List all tool names
    pub async fn list_tools(&self) -> Vec<String> {
        self.tools.read().await.keys().cloned().collect()
    }

    /// Execute a tool by name
    pub async fn execute(&self, name: &str, input: &Value) -> ToolExecutionResult {
        let start = std::time::Instant::now();

        // TigerStyle: Preconditions
        assert!(!name.is_empty(), "tool name cannot be empty");

        // Look up tool
        let tool = match self.tools.read().await.get(name) {
            Some(t) => t.clone(),
            None => {
                return ToolExecutionResult::failure(
                    format!("Tool not found: {}", name),
                    start.elapsed().as_millis() as u64,
                );
            }
        };

        // Route to appropriate handler based on source
        match &tool.source {
            ToolSource::Builtin => self.execute_builtin(name, input, start).await,
            ToolSource::Mcp { server } => self.execute_mcp(name, server, input, start).await,
            ToolSource::Custom => {
                // Custom tools are not yet supported
                ToolExecutionResult::failure(
                    format!("Custom tool execution not yet implemented: {}", name),
                    start.elapsed().as_millis() as u64,
                )
            }
        }
    }

    /// Execute a builtin tool
    async fn execute_builtin(
        &self,
        name: &str,
        input: &Value,
        start: std::time::Instant,
    ) -> ToolExecutionResult {
        let handler = match self.builtin_handlers.read().await.get(name) {
            Some(h) => h.clone(),
            None => {
                return ToolExecutionResult::failure(
                    format!("No handler for builtin tool: {}", name),
                    start.elapsed().as_millis() as u64,
                );
            }
        };

        let output = handler(input).await;
        let duration = start.elapsed().as_millis() as u64;

        // Check if output looks like an error
        let success = !output.starts_with("Error:") && !output.starts_with("Failed:");

        if success {
            ToolExecutionResult::success(output, duration)
        } else {
            ToolExecutionResult::failure(output, duration)
        }
    }

    /// Execute an MCP tool
    async fn execute_mcp(
        &self,
        name: &str,
        _server: &str,
        input: &Value,
        start: std::time::Instant,
    ) -> ToolExecutionResult {
        // Check for simulated MCP client (DST mode)
        #[cfg(feature = "dst")]
        {
            if let Some(client) = self.sim_mcp_client.read().await.as_ref() {
                match client.execute_tool(name, input.clone()).await {
                    Ok(result) => {
                        let output = serde_json::to_string_pretty(&result)
                            .unwrap_or_else(|_| result.to_string());
                        return ToolExecutionResult::success(
                            output,
                            start.elapsed().as_millis() as u64,
                        );
                    }
                    Err(e) => {
                        return ToolExecutionResult::failure(
                            e.to_string(),
                            start.elapsed().as_millis() as u64,
                        );
                    }
                }
            }
        }

        // TODO: Implement real MCP client execution
        // For now, return a placeholder
        ToolExecutionResult::failure(
            format!("MCP tool execution not yet implemented: {}", name),
            start.elapsed().as_millis() as u64,
        )
    }

    /// Unregister a tool
    pub async fn unregister(&self, name: &str) -> bool {
        let removed_tool = self.tools.write().await.remove(name).is_some();
        let removed_handler = self.builtin_handlers.write().await.remove(name).is_some();
        removed_tool || removed_handler
    }

    /// Clear all tools
    pub async fn clear(&self) {
        self.tools.write().await.clear();
        self.builtin_handlers.write().await.clear();
    }

    /// Get statistics about registered tools
    pub async fn stats(&self) -> RegistryStats {
        let tools = self.tools.read().await;
        let mut builtin_count = 0;
        let mut mcp_count = 0;
        let mut custom_count = 0;

        for tool in tools.values() {
            match &tool.source {
                ToolSource::Builtin => builtin_count += 1,
                ToolSource::Mcp { .. } => mcp_count += 1,
                ToolSource::Custom => custom_count += 1,
            }
        }

        RegistryStats {
            total_tools: tools.len(),
            builtin_count,
            mcp_count,
            custom_count,
        }
    }
}

impl Default for UnifiedToolRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics about registered tools
#[derive(Debug, Clone)]
pub struct RegistryStats {
    pub total_tools: usize,
    pub builtin_count: usize,
    pub mcp_count: usize,
    pub custom_count: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[tokio::test]
    async fn test_register_builtin_tool() {
        let registry = UnifiedToolRegistry::new();

        // Create a simple echo handler
        let handler: BuiltinToolHandler = Arc::new(|input| {
            let input = input.clone();
            Box::pin(async move {
                input.get("message").and_then(|v| v.as_str()).unwrap_or("").to_string()
            })
        });

        registry
            .register_builtin(
                "echo",
                "Echo back the input",
                json!({
                    "type": "object",
                    "properties": {
                        "message": { "type": "string" }
                    }
                }),
                handler,
            )
            .await;

        assert!(registry.has_tool("echo").await);
        assert_eq!(
            registry.get_tool_source("echo").await,
            Some(ToolSource::Builtin)
        );
    }

    #[tokio::test]
    async fn test_register_mcp_tool() {
        let registry = UnifiedToolRegistry::new();

        registry
            .register_mcp_tool(
                "external_tool",
                "An external tool",
                json!({"type": "object"}),
                "test-server",
            )
            .await;

        assert!(registry.has_tool("external_tool").await);
        assert_eq!(
            registry.get_tool_source("external_tool").await,
            Some(ToolSource::Mcp {
                server: "test-server".to_string()
            })
        );
    }

    #[tokio::test]
    async fn test_execute_builtin_tool() {
        let registry = UnifiedToolRegistry::new();

        let handler: BuiltinToolHandler = Arc::new(|input| {
            let input = input.clone();
            Box::pin(async move {
                let msg = input
                    .get("message")
                    .and_then(|v| v.as_str())
                    .unwrap_or("no message");
                format!("Echo: {}", msg)
            })
        });

        registry
            .register_builtin("echo", "Echo tool", json!({"type": "object"}), handler)
            .await;

        let result = registry
            .execute("echo", &json!({"message": "hello"}))
            .await;

        assert!(result.success);
        assert_eq!(result.output, "Echo: hello");
    }

    #[tokio::test]
    async fn test_get_tool_definitions() {
        let registry = UnifiedToolRegistry::new();

        let handler: BuiltinToolHandler =
            Arc::new(|_| Box::pin(async move { "result".to_string() }));

        registry
            .register_builtin("tool1", "Tool 1", json!({"type": "object"}), handler.clone())
            .await;

        registry
            .register_builtin("tool2", "Tool 2", json!({"type": "object"}), handler)
            .await;

        let definitions = registry.get_tool_definitions().await;
        assert_eq!(definitions.len(), 2);
    }

    #[tokio::test]
    async fn test_registry_stats() {
        let registry = UnifiedToolRegistry::new();

        let handler: BuiltinToolHandler =
            Arc::new(|_| Box::pin(async move { "result".to_string() }));

        registry
            .register_builtin("builtin1", "Builtin 1", json!({}), handler)
            .await;

        registry
            .register_mcp_tool("mcp1", "MCP 1", json!({}), "server1")
            .await;

        registry
            .register_mcp_tool("mcp2", "MCP 2", json!({}), "server2")
            .await;

        let stats = registry.stats().await;
        assert_eq!(stats.total_tools, 3);
        assert_eq!(stats.builtin_count, 1);
        assert_eq!(stats.mcp_count, 2);
        assert_eq!(stats.custom_count, 0);
    }

    #[tokio::test]
    async fn test_tool_not_found() {
        let registry = UnifiedToolRegistry::new();

        let result = registry.execute("nonexistent", &json!({})).await;

        assert!(!result.success);
        assert!(result.error.is_some());
        assert!(result.error.unwrap().contains("not found"));
    }
}

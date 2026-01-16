//! Simulated MCP client for Deterministic Simulation Testing (DST)
//!
//! TigerStyle: Deterministic MCP operations with fault injection support.

use crate::mcp::McpToolDefinition;
use crate::{ToolError, ToolResult};
use kelpie_dst::fault::{FaultInjector, FaultType};
use kelpie_dst::rng::DeterministicRng;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Simulated MCP server configuration for DST
#[derive(Debug, Clone)]
pub struct SimMcpServerConfig {
    /// Server name
    pub name: String,
    /// Tools this server provides
    pub tools: Vec<McpToolDefinition>,
    /// Whether the server is "online"
    pub online: bool,
}

impl SimMcpServerConfig {
    /// Create a new simulated MCP server config
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            tools: Vec::new(),
            online: true,
        }
    }

    /// Add a tool to this server
    pub fn with_tool(mut self, tool: McpToolDefinition) -> Self {
        self.tools.push(tool);
        self
    }

    /// Set online status
    pub fn online(mut self, online: bool) -> Self {
        self.online = online;
        self
    }
}

/// Simulated MCP client for deterministic testing
///
/// This provides a fully deterministic MCP client that:
/// - Returns predetermined tool definitions
/// - Uses a deterministic RNG for any randomness
/// - Integrates with the DST fault injector
pub struct SimMcpClient {
    /// Server configuration
    servers: HashMap<String, SimMcpServerConfig>,
    /// Cached tool definitions (server_name -> tool_name -> definition)
    tool_cache: HashMap<String, HashMap<String, McpToolDefinition>>,
    /// Map from tool name to server name (for routing)
    tool_to_server: HashMap<String, String>,
    /// Fault injector for simulating failures
    fault_injector: Arc<FaultInjector>,
    /// Deterministic RNG (for future use in randomized tool execution)
    #[allow(dead_code)]
    rng: Arc<RwLock<DeterministicRng>>,
    /// Connection state per server
    connection_state: RwLock<HashMap<String, ConnectionState>>,
}

/// Connection state for a simulated server
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionState {
    Disconnected,
    Connecting,
    Connected,
    Failed,
}

impl SimMcpClient {
    /// Create a new simulated MCP client
    ///
    /// # Arguments
    /// * `fault_injector` - The DST fault injector for simulating failures
    /// * `rng` - Deterministic RNG for reproducible behavior
    pub fn new(fault_injector: Arc<FaultInjector>, rng: DeterministicRng) -> Self {
        Self {
            servers: HashMap::new(),
            tool_cache: HashMap::new(),
            tool_to_server: HashMap::new(),
            fault_injector,
            rng: Arc::new(RwLock::new(rng)),
            connection_state: RwLock::new(HashMap::new()),
        }
    }

    /// Register a simulated MCP server
    pub fn register_server(&mut self, config: SimMcpServerConfig) {
        let server_name = config.name.clone();

        // Build tool cache
        let mut server_tools = HashMap::new();
        for tool in &config.tools {
            server_tools.insert(tool.name.clone(), tool.clone());
            self.tool_to_server
                .insert(tool.name.clone(), server_name.clone());
        }
        self.tool_cache.insert(server_name.clone(), server_tools);

        self.servers.insert(server_name, config);
    }

    /// Connect to a simulated server
    pub async fn connect(&self, server_name: &str) -> ToolResult<()> {
        // TigerStyle: Preconditions
        assert!(!server_name.is_empty(), "server_name cannot be empty");

        let server = self
            .servers
            .get(server_name)
            .ok_or_else(|| ToolError::NotFound {
                name: format!("server:{}", server_name),
            })?;

        // Update state to connecting
        {
            let mut state = self.connection_state.write().await;
            state.insert(server_name.to_string(), ConnectionState::Connecting);
        }

        // Check for server crash fault
        if let Some(fault) = self.fault_injector.should_inject("mcp_connect") {
            match fault {
                FaultType::McpServerCrash => {
                    let mut state = self.connection_state.write().await;
                    state.insert(server_name.to_string(), ConnectionState::Failed);
                    return Err(ToolError::ExecutionFailed {
                        tool: server_name.to_string(),
                        reason: "simulated fault: MCP server crashed".to_string(),
                    });
                }
                FaultType::McpServerSlowStart { delay_ms } => {
                    // In real DST, we'd advance the clock here
                    // For now, just log the delay
                    tracing::debug!(delay_ms, "Simulated slow start");
                }
                FaultType::NetworkPartition => {
                    let mut state = self.connection_state.write().await;
                    state.insert(server_name.to_string(), ConnectionState::Failed);
                    return Err(ToolError::ExecutionFailed {
                        tool: server_name.to_string(),
                        reason: "simulated fault: network partition".to_string(),
                    });
                }
                _ => {}
            }
        }

        // Check if server is configured as online
        if !server.online {
            let mut state = self.connection_state.write().await;
            state.insert(server_name.to_string(), ConnectionState::Failed);
            return Err(ToolError::ExecutionFailed {
                tool: server_name.to_string(),
                reason: "server is offline".to_string(),
            });
        }

        // Success - mark as connected
        {
            let mut state = self.connection_state.write().await;
            state.insert(server_name.to_string(), ConnectionState::Connected);
        }

        Ok(())
    }

    /// Disconnect from a simulated server
    pub async fn disconnect(&self, server_name: &str) {
        let mut state = self.connection_state.write().await;
        state.insert(server_name.to_string(), ConnectionState::Disconnected);
    }

    /// Check if connected to a server
    pub async fn is_connected(&self, server_name: &str) -> bool {
        let state = self.connection_state.read().await;
        matches!(state.get(server_name), Some(ConnectionState::Connected))
    }

    /// Discover tools from a server
    pub async fn discover_tools(&self, server_name: &str) -> ToolResult<Vec<McpToolDefinition>> {
        // Check connection
        if !self.is_connected(server_name).await {
            return Err(ToolError::ExecutionFailed {
                tool: server_name.to_string(),
                reason: "not connected to server".to_string(),
            });
        }

        // Check for network fault during discovery
        if let Some(fault) = self.fault_injector.should_inject("mcp_discover") {
            match fault {
                FaultType::NetworkPartition | FaultType::McpServerCrash => {
                    let mut state = self.connection_state.write().await;
                    state.insert(server_name.to_string(), ConnectionState::Failed);
                    return Err(ToolError::ExecutionFailed {
                        tool: server_name.to_string(),
                        reason: format!("simulated fault: {}", fault.name()),
                    });
                }
                FaultType::NetworkPacketLoss => {
                    return Err(ToolError::ExecutionFailed {
                        tool: server_name.to_string(),
                        reason: "simulated fault: packet loss during discovery".to_string(),
                    });
                }
                _ => {}
            }
        }

        // Return cached tools
        let tools = self
            .tool_cache
            .get(server_name)
            .map(|cache| cache.values().cloned().collect())
            .unwrap_or_default();

        Ok(tools)
    }

    /// Discover all tools from all connected servers
    pub async fn discover_all_tools(&self) -> ToolResult<Vec<McpToolDefinition>> {
        let mut all_tools = Vec::new();

        for server_name in self.servers.keys() {
            if self.is_connected(server_name).await {
                match self.discover_tools(server_name).await {
                    Ok(tools) => all_tools.extend(tools),
                    Err(e) => {
                        tracing::warn!(
                            server = server_name,
                            error = %e,
                            "Failed to discover tools from server"
                        );
                        // Continue with other servers - graceful degradation
                    }
                }
            }
        }

        Ok(all_tools)
    }

    /// Execute a tool
    pub async fn execute_tool(&self, tool_name: &str, arguments: Value) -> ToolResult<Value> {
        // TigerStyle: Preconditions
        assert!(!tool_name.is_empty(), "tool_name cannot be empty");

        // Find which server has this tool
        let server_name =
            self.tool_to_server
                .get(tool_name)
                .ok_or_else(|| ToolError::NotFound {
                    name: tool_name.to_string(),
                })?;

        // Check connection
        if !self.is_connected(server_name).await {
            return Err(ToolError::ExecutionFailed {
                tool: tool_name.to_string(),
                reason: format!("not connected to server '{}'", server_name),
            });
        }

        // Check for tool execution faults
        if let Some(fault) = self.fault_injector.should_inject("mcp_execute") {
            match fault {
                FaultType::McpToolFail => {
                    return Err(ToolError::ExecutionFailed {
                        tool: tool_name.to_string(),
                        reason: "simulated fault: tool execution failed".to_string(),
                    });
                }
                FaultType::McpToolTimeout => {
                    return Err(ToolError::ExecutionTimeout {
                        tool: tool_name.to_string(),
                        timeout_ms: 30000,
                    });
                }
                FaultType::McpServerCrash => {
                    let mut state = self.connection_state.write().await;
                    state.insert(server_name.to_string(), ConnectionState::Failed);
                    return Err(ToolError::ExecutionFailed {
                        tool: tool_name.to_string(),
                        reason: "simulated fault: server crashed during execution".to_string(),
                    });
                }
                FaultType::NetworkDelay { min_ms, max_ms } => {
                    tracing::debug!(min_ms, max_ms, "Simulated network delay");
                    // In real DST, we'd advance the clock
                }
                _ => {}
            }
        }

        // Execute tool - return simulated result based on tool name
        // This is deterministic - same tool + args = same result
        let result = self.simulate_tool_execution(tool_name, &arguments).await;

        Ok(result)
    }

    /// Simulate tool execution with deterministic results
    async fn simulate_tool_execution(&self, tool_name: &str, arguments: &Value) -> Value {
        // Generate deterministic output based on tool name and arguments
        // In practice, tools can be configured with expected responses
        json!({
            "success": true,
            "tool": tool_name,
            "arguments": arguments,
            "result": format!("Simulated result for tool '{}' with args: {}", tool_name, arguments),
            "simulated": true
        })
    }

    /// Get all registered servers
    pub fn servers(&self) -> Vec<&str> {
        self.servers.keys().map(|s| s.as_str()).collect()
    }

    /// Get connection state for a server
    pub async fn connection_state(&self, server_name: &str) -> ConnectionState {
        let state = self.connection_state.read().await;
        state
            .get(server_name)
            .copied()
            .unwrap_or(ConnectionState::Disconnected)
    }
}

/// Builder for creating simulated MCP environments
pub struct SimMcpEnvironment {
    servers: Vec<SimMcpServerConfig>,
}

impl SimMcpEnvironment {
    /// Create a new simulated MCP environment
    pub fn new() -> Self {
        Self {
            servers: Vec::new(),
        }
    }

    /// Add a simulated server
    pub fn with_server(mut self, config: SimMcpServerConfig) -> Self {
        self.servers.push(config);
        self
    }

    /// Build the simulated MCP client
    pub fn build(self, fault_injector: Arc<FaultInjector>, rng: DeterministicRng) -> SimMcpClient {
        let mut client = SimMcpClient::new(fault_injector, rng);
        for server in self.servers {
            client.register_server(server);
        }
        client
    }
}

impl Default for SimMcpEnvironment {
    fn default() -> Self {
        Self::new()
    }
}

/// Create a standard set of simulated MCP tools for testing
pub fn create_test_tools() -> Vec<McpToolDefinition> {
    vec![
        McpToolDefinition {
            name: "test_tool".to_string(),
            description: "A test tool for DST".to_string(),
            input_schema: json!({
                "type": "object",
                "properties": {
                    "input": { "type": "string" }
                },
                "required": ["input"]
            }),
        },
        McpToolDefinition {
            name: "calculator".to_string(),
            description: "Perform basic arithmetic".to_string(),
            input_schema: json!({
                "type": "object",
                "properties": {
                    "operation": { "type": "string", "enum": ["add", "subtract", "multiply", "divide"] },
                    "a": { "type": "number" },
                    "b": { "type": "number" }
                },
                "required": ["operation", "a", "b"]
            }),
        },
        McpToolDefinition {
            name: "file_read".to_string(),
            description: "Read file contents".to_string(),
            input_schema: json!({
                "type": "object",
                "properties": {
                    "path": { "type": "string" }
                },
                "required": ["path"]
            }),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use kelpie_dst::fault::FaultConfig;

    #[tokio::test]
    async fn test_sim_mcp_client_basic() {
        let rng = DeterministicRng::new(42);
        let injector = FaultInjector::new(DeterministicRng::new(42));
        // No faults registered

        let mut client = SimMcpClient::new(Arc::new(injector), rng);

        // Register a server with tools
        let server = SimMcpServerConfig::new("test-server").with_tool(McpToolDefinition {
            name: "echo".to_string(),
            description: "Echo input".to_string(),
            input_schema: json!({"type": "object"}),
        });
        client.register_server(server);

        // Connect
        client.connect("test-server").await.unwrap();
        assert!(client.is_connected("test-server").await);

        // Discover tools
        let tools = client.discover_tools("test-server").await.unwrap();
        assert_eq!(tools.len(), 1);
        assert_eq!(tools[0].name, "echo");

        // Execute tool
        let result = client
            .execute_tool("echo", json!({"message": "hello"}))
            .await
            .unwrap();
        assert!(result.get("success").unwrap().as_bool().unwrap());
    }

    #[tokio::test]
    async fn test_sim_mcp_client_with_faults() {
        let rng = DeterministicRng::new(42);
        let mut injector = FaultInjector::new(DeterministicRng::new(42));
        injector.register(FaultConfig::new(FaultType::McpToolFail, 1.0)); // 100% fault rate

        let mut client = SimMcpClient::new(Arc::new(injector), rng);

        let server = SimMcpServerConfig::new("test-server").with_tool(McpToolDefinition {
            name: "echo".to_string(),
            description: "Echo input".to_string(),
            input_schema: json!({"type": "object"}),
        });
        client.register_server(server);
        client.connect("test-server").await.unwrap();

        // Tool execution should fail due to fault
        let result = client.execute_tool("echo", json!({})).await;
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ToolError::ExecutionFailed { .. }));
    }

    #[tokio::test]
    async fn test_sim_mcp_environment_builder() {
        let rng = DeterministicRng::new(42);
        let injector = Arc::new(FaultInjector::new(DeterministicRng::new(42)));

        let client = SimMcpEnvironment::new()
            .with_server(
                SimMcpServerConfig::new("server-a").with_tool(create_test_tools()[0].clone()),
            )
            .with_server(
                SimMcpServerConfig::new("server-b").with_tool(create_test_tools()[1].clone()),
            )
            .build(injector, rng);

        assert_eq!(client.servers().len(), 2);
    }
}

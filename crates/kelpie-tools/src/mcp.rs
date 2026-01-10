//! MCP (Model Context Protocol) client implementation
//!
//! TigerStyle: Protocol-compliant client with explicit message types.
//!
//! MCP is a protocol for tool discovery and execution between AI models
//! and external tool providers. This module provides a client implementation
//! that can connect to MCP servers and discover/execute tools.

use crate::error::{ToolError, ToolResult};
use crate::traits::{
    ParamType, Tool, ToolCapability, ToolInput, ToolMetadata, ToolOutput, ToolParam,
};
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{debug, info};

/// MCP protocol version
#[allow(dead_code)]
pub const MCP_PROTOCOL_VERSION: &str = "2024-11-05";

/// Default MCP connection timeout
pub const MCP_CONNECTION_TIMEOUT_MS: u64 = 30_000;

/// Default MCP request timeout
pub const MCP_REQUEST_TIMEOUT_MS: u64 = 60_000;

/// MCP server configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpConfig {
    /// Server name
    pub name: String,
    /// Server type (stdio, sse, http)
    pub transport: McpTransport,
    /// Connection timeout in milliseconds
    pub connection_timeout_ms: u64,
    /// Request timeout in milliseconds
    pub request_timeout_ms: u64,
    /// Environment variables for server process
    pub env: HashMap<String, String>,
}

impl McpConfig {
    /// Create configuration for a stdio-based MCP server
    pub fn stdio(name: impl Into<String>, command: impl Into<String>, args: Vec<String>) -> Self {
        Self {
            name: name.into(),
            transport: McpTransport::Stdio {
                command: command.into(),
                args,
            },
            connection_timeout_ms: MCP_CONNECTION_TIMEOUT_MS,
            request_timeout_ms: MCP_REQUEST_TIMEOUT_MS,
            env: HashMap::new(),
        }
    }

    /// Create configuration for an HTTP-based MCP server
    pub fn http(name: impl Into<String>, url: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            transport: McpTransport::Http { url: url.into() },
            connection_timeout_ms: MCP_CONNECTION_TIMEOUT_MS,
            request_timeout_ms: MCP_REQUEST_TIMEOUT_MS,
            env: HashMap::new(),
        }
    }

    /// Add environment variable
    pub fn with_env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.env.insert(key.into(), value.into());
        self
    }

    /// Set connection timeout
    pub fn with_connection_timeout_ms(mut self, timeout: u64) -> Self {
        self.connection_timeout_ms = timeout;
        self
    }

    /// Set request timeout
    pub fn with_request_timeout_ms(mut self, timeout: u64) -> Self {
        self.request_timeout_ms = timeout;
        self
    }
}

/// MCP transport type
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum McpTransport {
    /// stdio transport (spawn subprocess)
    Stdio {
        /// Command to run
        command: String,
        /// Command arguments
        args: Vec<String>,
    },
    /// HTTP transport
    Http {
        /// Server URL
        url: String,
    },
    /// Server-sent events transport
    Sse {
        /// Server URL
        url: String,
    },
}

/// MCP JSON-RPC message types
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum McpMessage {
    /// Request message
    Request(McpRequest),
    /// Response message
    Response(McpResponse),
    /// Notification message
    Notification(McpNotification),
}

/// MCP JSON-RPC request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpRequest {
    /// JSON-RPC version (always "2.0")
    pub jsonrpc: String,
    /// Request ID
    pub id: u64,
    /// Method name
    pub method: String,
    /// Parameters
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
}

#[allow(dead_code)]
impl McpRequest {
    /// Create a new request
    pub fn new(id: u64, method: impl Into<String>) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            id,
            method: method.into(),
            params: None,
        }
    }

    /// Add parameters
    pub fn with_params(mut self, params: impl Into<Value>) -> Self {
        self.params = Some(params.into());
        self
    }
}

/// MCP JSON-RPC response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpResponse {
    /// JSON-RPC version
    pub jsonrpc: String,
    /// Request ID this responds to
    pub id: u64,
    /// Result (on success)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<Value>,
    /// Error (on failure)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<McpError>,
}

/// MCP JSON-RPC error
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpError {
    /// Error code
    pub code: i32,
    /// Error message
    pub message: String,
    /// Additional error data
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

/// MCP JSON-RPC notification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpNotification {
    /// JSON-RPC version
    pub jsonrpc: String,
    /// Method name
    pub method: String,
    /// Parameters
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
}

/// MCP tool definition from server
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpToolDefinition {
    /// Tool name
    pub name: String,
    /// Tool description
    #[serde(default)]
    pub description: String,
    /// Input schema (JSON Schema)
    #[serde(rename = "inputSchema")]
    pub input_schema: Value,
}

/// MCP client for connecting to MCP servers
pub struct McpClient {
    /// Configuration
    config: McpConfig,
    /// Connection state
    state: RwLock<McpClientState>,
    /// Request ID counter
    #[allow(dead_code)]
    request_id: std::sync::atomic::AtomicU64,
    /// Discovered tools
    tools: RwLock<HashMap<String, McpToolDefinition>>,
}

/// Client connection state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum McpClientState {
    /// Not connected
    Disconnected,
    /// Connecting
    Connecting,
    /// Connected and initialized
    Connected,
    /// Connection failed
    Failed,
}

impl McpClient {
    /// Create a new MCP client
    pub fn new(config: McpConfig) -> Self {
        Self {
            config,
            state: RwLock::new(McpClientState::Disconnected),
            request_id: std::sync::atomic::AtomicU64::new(1),
            tools: RwLock::new(HashMap::new()),
        }
    }

    /// Get the server name
    pub fn name(&self) -> &str {
        &self.config.name
    }

    /// Get current connection state
    pub async fn state(&self) -> McpClientState {
        *self.state.read().await
    }

    /// Check if connected
    pub async fn is_connected(&self) -> bool {
        *self.state.read().await == McpClientState::Connected
    }

    /// Connect to the MCP server
    ///
    /// Note: This is a mock implementation. Real implementation would:
    /// - For stdio: spawn subprocess, set up stdin/stdout pipes
    /// - For HTTP: establish HTTP connection
    /// - For SSE: establish SSE connection
    pub async fn connect(&self) -> ToolResult<()> {
        {
            let mut state = self.state.write().await;
            if *state == McpClientState::Connected {
                return Ok(());
            }
            *state = McpClientState::Connecting;
        }

        info!(server = %self.config.name, "Connecting to MCP server");

        // Simulate connection (real implementation would establish actual connection)
        match &self.config.transport {
            McpTransport::Stdio { command, args } => {
                debug!(
                    command = %command,
                    args = ?args,
                    "Would spawn stdio process"
                );
            }
            McpTransport::Http { url } => {
                debug!(url = %url, "Would connect to HTTP endpoint");
            }
            McpTransport::Sse { url } => {
                debug!(url = %url, "Would connect to SSE endpoint");
            }
        }

        // Mark as connected
        {
            let mut state = self.state.write().await;
            *state = McpClientState::Connected;
        }

        info!(server = %self.config.name, "Connected to MCP server");
        Ok(())
    }

    /// Disconnect from the MCP server
    pub async fn disconnect(&self) -> ToolResult<()> {
        let mut state = self.state.write().await;
        *state = McpClientState::Disconnected;

        info!(server = %self.config.name, "Disconnected from MCP server");
        Ok(())
    }

    /// Discover available tools from the server
    pub async fn discover_tools(&self) -> ToolResult<Vec<McpToolDefinition>> {
        if !self.is_connected().await {
            return Err(ToolError::McpConnectionError {
                reason: "not connected".to_string(),
            });
        }

        debug!(server = %self.config.name, "Discovering tools");

        // In a real implementation, this would send:
        // {"jsonrpc": "2.0", "id": 1, "method": "tools/list"}

        // Return cached tools (real implementation would query server)
        let tools = self.tools.read().await;
        Ok(tools.values().cloned().collect())
    }

    /// Register a mock tool definition (for testing)
    pub async fn register_mock_tool(&self, tool: McpToolDefinition) {
        let mut tools = self.tools.write().await;
        tools.insert(tool.name.clone(), tool);
    }

    /// Execute a tool on the MCP server
    pub async fn execute_tool(&self, name: &str, _arguments: Value) -> ToolResult<Value> {
        if !self.is_connected().await {
            return Err(ToolError::McpConnectionError {
                reason: "not connected".to_string(),
            });
        }

        let tools = self.tools.read().await;
        if !tools.contains_key(name) {
            return Err(ToolError::NotFound {
                name: name.to_string(),
            });
        }
        drop(tools);

        debug!(server = %self.config.name, tool = %name, "Executing MCP tool");

        // In a real implementation, this would send:
        // {"jsonrpc": "2.0", "id": N, "method": "tools/call", "params": {"name": "...", "arguments": {...}}}

        // For now, return a mock result
        Ok(serde_json::json!({
            "content": [{
                "type": "text",
                "text": format!("Mock result for tool '{}'", name)
            }]
        }))
    }

    /// Get next request ID
    #[allow(dead_code)]
    fn next_request_id(&self) -> u64 {
        self.request_id
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }
}

/// A tool backed by an MCP server
pub struct McpTool {
    /// MCP client
    client: Arc<McpClient>,
    /// Tool definition
    definition: McpToolDefinition,
    /// Cached metadata
    metadata: ToolMetadata,
}

impl McpTool {
    /// Create a new MCP tool
    pub fn new(client: Arc<McpClient>, definition: McpToolDefinition) -> Self {
        let metadata = Self::build_metadata(&definition);
        Self {
            client,
            definition,
            metadata,
        }
    }

    /// Build tool metadata from MCP definition
    fn build_metadata(definition: &McpToolDefinition) -> ToolMetadata {
        let mut metadata = ToolMetadata::new(&definition.name, &definition.description)
            .with_capabilities(ToolCapability {
                requires_network: true, // MCP tools require network to talk to server
                requires_filesystem: false,
                can_modify_state: true, // Assume MCP tools can modify state
                is_deterministic: false,
                is_safe: false,
            });

        // Parse JSON Schema to extract parameters
        if let Some(properties) = definition
            .input_schema
            .get("properties")
            .and_then(|p| p.as_object())
        {
            let required: Vec<&str> = definition
                .input_schema
                .get("required")
                .and_then(|r| r.as_array())
                .map(|arr| arr.iter().filter_map(|v| v.as_str()).collect::<Vec<_>>())
                .unwrap_or_default();

            for (name, schema) in properties {
                let param_type = schema
                    .get("type")
                    .and_then(|t| t.as_str())
                    .map(|t| match t {
                        "string" => ParamType::String,
                        "integer" => ParamType::Integer,
                        "number" => ParamType::Number,
                        "boolean" => ParamType::Boolean,
                        "array" => ParamType::Array,
                        "object" => ParamType::Object,
                        _ => ParamType::String,
                    })
                    .unwrap_or(ParamType::String);

                let description = schema
                    .get("description")
                    .and_then(|d| d.as_str())
                    .unwrap_or("")
                    .to_string();

                let is_required = required.contains(&name.as_str());

                let mut param = ToolParam {
                    name: name.clone(),
                    param_type,
                    required: is_required,
                    description,
                    default: schema.get("default").cloned(),
                    enum_values: schema.get("enum").and_then(|e| e.as_array()).cloned(),
                };

                if !is_required {
                    param = param.optional();
                }

                metadata = metadata.with_param(param);
            }
        }

        metadata
    }
}

#[async_trait]
impl Tool for McpTool {
    fn metadata(&self) -> &ToolMetadata {
        &self.metadata
    }

    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput> {
        // Convert params to JSON value for MCP call
        let arguments =
            serde_json::to_value(&input.params).map_err(|e| ToolError::InvalidInput {
                tool: self.definition.name.clone(),
                reason: e.to_string(),
            })?;

        // Execute via MCP client
        let result = self
            .client
            .execute_tool(&self.definition.name, arguments)
            .await?;

        // Extract text content from MCP response
        let content = result
            .get("content")
            .and_then(|c| c.as_array())
            .and_then(|arr| arr.first())
            .and_then(|item| item.get("text"))
            .and_then(|t| t.as_str())
            .unwrap_or("");

        Ok(ToolOutput::success(content.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mcp_config_stdio() {
        let config = McpConfig::stdio(
            "test-server",
            "python",
            vec!["-m".to_string(), "mcp".to_string()],
        )
        .with_env("API_KEY", "secret");

        assert_eq!(config.name, "test-server");
        assert!(matches!(config.transport, McpTransport::Stdio { .. }));
        assert!(config.env.contains_key("API_KEY"));
    }

    #[test]
    fn test_mcp_config_http() {
        let config = McpConfig::http("http-server", "http://localhost:8080");

        assert_eq!(config.name, "http-server");
        assert!(matches!(config.transport, McpTransport::Http { .. }));
    }

    #[test]
    fn test_mcp_request() {
        let request =
            McpRequest::new(1, "tools/list").with_params(serde_json::json!({"cursor": null}));

        assert_eq!(request.jsonrpc, "2.0");
        assert_eq!(request.id, 1);
        assert_eq!(request.method, "tools/list");
    }

    #[tokio::test]
    async fn test_mcp_client_connect() {
        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = McpClient::new(config);

        assert_eq!(client.state().await, McpClientState::Disconnected);

        client.connect().await.unwrap();
        assert_eq!(client.state().await, McpClientState::Connected);
    }

    #[tokio::test]
    async fn test_mcp_client_disconnect() {
        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = McpClient::new(config);

        client.connect().await.unwrap();
        client.disconnect().await.unwrap();

        assert_eq!(client.state().await, McpClientState::Disconnected);
    }

    #[tokio::test]
    async fn test_mcp_client_discover_not_connected() {
        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = McpClient::new(config);

        let result = client.discover_tools().await;
        assert!(matches!(result, Err(ToolError::McpConnectionError { .. })));
    }

    #[tokio::test]
    async fn test_mcp_tool_definition() {
        let definition = McpToolDefinition {
            name: "read_file".to_string(),
            description: "Read a file".to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "path": {
                        "type": "string",
                        "description": "File path"
                    }
                },
                "required": ["path"]
            }),
        };

        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = Arc::new(McpClient::new(config));
        let tool = McpTool::new(client, definition);

        let metadata = tool.metadata();
        assert_eq!(metadata.name, "read_file");
        assert_eq!(metadata.parameters.len(), 1);
        assert!(metadata.is_param_required("path"));
    }

    #[tokio::test]
    async fn test_mcp_tool_execute() {
        let definition = McpToolDefinition {
            name: "test_tool".to_string(),
            description: "A test tool".to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {}
            }),
        };

        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = Arc::new(McpClient::new(config));
        client.connect().await.unwrap();
        client.register_mock_tool(definition.clone()).await;

        let tool = McpTool::new(client, definition);
        let input = ToolInput::new("test_tool");
        let output = tool.execute(input).await.unwrap();

        assert!(output.is_success());
    }
}

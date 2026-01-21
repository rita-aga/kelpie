//! MCP (Model Context Protocol) client implementation
//!
//! TigerStyle: Protocol-compliant client with explicit message types.
//!
//! MCP is a protocol for tool discovery and execution between AI models
//! and external tool providers. This module provides a client implementation
//! that can connect to MCP servers via stdio, HTTP, or SSE transports.

use crate::error::{ToolError, ToolResult};
use crate::traits::{
    ParamType, Tool, ToolCapability, ToolInput, ToolMetadata, ToolOutput, ToolParam,
};
use async_trait::async_trait;
use kelpie_core::Runtime;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::process::Stdio;
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};
use tokio::sync::{mpsc, oneshot, RwLock};
use tracing::{debug, error, info, warn};

/// MCP protocol version
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

    /// Create configuration for an SSE-based MCP server
    pub fn sse(name: impl Into<String>, url: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            transport: McpTransport::Sse { url: url.into() },
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

/// MCP JSON-RPC message types (used for parsing mixed message streams)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
#[allow(dead_code)]
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

/// Server capabilities returned during initialization
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ServerCapabilities {
    /// Tools capability
    #[serde(default)]
    pub tools: Option<ToolsCapability>,
    /// Resources capability
    #[serde(default)]
    pub resources: Option<ResourcesCapability>,
    /// Prompts capability
    #[serde(default)]
    pub prompts: Option<PromptsCapability>,
}

/// Tools capability
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ToolsCapability {
    /// Whether tool list can change
    #[serde(rename = "listChanged", default)]
    pub list_changed: bool,
}

/// Resources capability
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ResourcesCapability {
    /// Whether to subscribe to resource changes
    #[serde(default)]
    pub subscribe: bool,
    /// Whether resource list can change
    #[serde(rename = "listChanged", default)]
    pub list_changed: bool,
}

/// Prompts capability
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PromptsCapability {
    /// Whether prompt list can change
    #[serde(rename = "listChanged", default)]
    pub list_changed: bool,
}

/// Initialize result from server
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InitializeResult {
    /// Protocol version
    #[serde(rename = "protocolVersion")]
    pub protocol_version: String,
    /// Server capabilities
    pub capabilities: ServerCapabilities,
    /// Server info
    #[serde(rename = "serverInfo")]
    pub server_info: ServerInfo,
}

/// Server info
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerInfo {
    /// Server name
    pub name: String,
    /// Server version
    #[serde(default)]
    pub version: String,
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

/// Internal transport abstraction
#[async_trait]
trait TransportInner: Send + Sync {
    /// Send a request and wait for response
    async fn request(&self, request: McpRequest, timeout: Duration) -> ToolResult<McpResponse>;

    /// Send a notification (no response expected)
    async fn notify(&self, notification: McpNotification) -> ToolResult<()>;

    /// Close the transport
    async fn close(&self) -> ToolResult<()>;
}

/// Stdio transport - communicates via subprocess stdin/stdout
struct StdioTransport {
    /// Sender for requests
    request_tx: mpsc::Sender<(McpRequest, oneshot::Sender<ToolResult<McpResponse>>)>,
    /// Notification sender
    notify_tx: mpsc::Sender<McpNotification>,
    /// Handle to the child process
    child_handle: RwLock<Option<Child>>,
}

impl StdioTransport {
    /// Create and start a new stdio transport
    async fn new(
        command: &str,
        args: &[String],
        env: &HashMap<String, String>,
        _timeout: Duration,
    ) -> ToolResult<Self> {
        // Spawn the MCP server process
        let mut cmd = Command::new(command);
        cmd.args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true);

        // Set environment variables
        for (k, v) in env {
            cmd.env(k, v);
        }

        let mut child = cmd.spawn().map_err(|e| ToolError::McpConnectionError {
            reason: format!("failed to spawn MCP server '{}': {}", command, e),
        })?;

        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| ToolError::McpConnectionError {
                reason: "failed to get stdin for MCP server".to_string(),
            })?;

        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| ToolError::McpConnectionError {
                reason: "failed to get stdout for MCP server".to_string(),
            })?;

        // Create channels for communication
        let (request_tx, request_rx) =
            mpsc::channel::<(McpRequest, oneshot::Sender<ToolResult<McpResponse>>)>(32);
        let (notify_tx, notify_rx) = mpsc::channel::<McpNotification>(32);
        let (response_tx, response_rx) = mpsc::channel::<McpResponse>(32);

        // Spawn writer task
        let _writer_handle = kelpie_core::current_runtime().spawn(Self::writer_task(stdin, request_rx, notify_rx));

        // Spawn reader task
        let _reader_handle = kelpie_core::current_runtime().spawn(Self::reader_task(stdout, response_tx));

        // Spawn response router task
        let pending: Arc<RwLock<HashMap<u64, oneshot::Sender<ToolResult<McpResponse>>>>> =
            Arc::new(RwLock::new(HashMap::new()));
        let pending_clone = pending.clone();

        kelpie_core::current_runtime().spawn(async move {
            let mut response_rx = response_rx;
            while let Some(response) = response_rx.recv().await {
                let id = response.id;
                if let Some(sender) = pending_clone.write().await.remove(&id) {
                    let _ = sender.send(Ok(response));
                }
            }
        });

        // Store pending map in request channel handler
        // We need to modify the request_tx to register pending requests
        let (real_request_tx, mut real_request_rx) =
            mpsc::channel::<(McpRequest, oneshot::Sender<ToolResult<McpResponse>>)>(32);
        let pending_clone = pending.clone();

        kelpie_core::current_runtime().spawn(async move {
            while let Some((request, response_sender)) = real_request_rx.recv().await {
                let id = request.id;
                pending_clone.write().await.insert(id, response_sender);
                if request_tx
                    .send((request, oneshot::channel().0))
                    .await
                    .is_err()
                {
                    pending_clone.write().await.remove(&id);
                }
            }
        });

        let transport = Self {
            request_tx: real_request_tx,
            notify_tx,
            child_handle: RwLock::new(Some(child)),
        };

        Ok(transport)
    }

    /// Writer task - sends messages to stdin
    async fn writer_task(
        mut stdin: ChildStdin,
        mut request_rx: mpsc::Receiver<(McpRequest, oneshot::Sender<ToolResult<McpResponse>>)>,
        mut notify_rx: mpsc::Receiver<McpNotification>,
    ) {
        loop {
            tokio::select! {
                Some((request, _)) = request_rx.recv() => {
                    let json = match serde_json::to_string(&request) {
                        Ok(j) => j,
                        Err(e) => {
                            error!(error = %e, "Failed to serialize request");
                            continue;
                        }
                    };
                    debug!(id = request.id, method = %request.method, "Sending request");
                    if let Err(e) = stdin.write_all(json.as_bytes()).await {
                        error!(error = %e, "Failed to write to stdin");
                        break;
                    }
                    if let Err(e) = stdin.write_all(b"\n").await {
                        error!(error = %e, "Failed to write newline to stdin");
                        break;
                    }
                    if let Err(e) = stdin.flush().await {
                        error!(error = %e, "Failed to flush stdin");
                        break;
                    }
                }
                Some(notification) = notify_rx.recv() => {
                    let json = match serde_json::to_string(&notification) {
                        Ok(j) => j,
                        Err(e) => {
                            error!(error = %e, "Failed to serialize notification");
                            continue;
                        }
                    };
                    debug!(method = %notification.method, "Sending notification");
                    if let Err(e) = stdin.write_all(json.as_bytes()).await {
                        error!(error = %e, "Failed to write notification to stdin");
                        break;
                    }
                    if let Err(e) = stdin.write_all(b"\n").await {
                        error!(error = %e, "Failed to write newline to stdin");
                        break;
                    }
                    if let Err(e) = stdin.flush().await {
                        error!(error = %e, "Failed to flush stdin");
                        break;
                    }
                }
                else => break,
            }
        }
    }

    /// Reader task - reads messages from stdout
    async fn reader_task(stdout: ChildStdout, response_tx: mpsc::Sender<McpResponse>) {
        let mut reader = BufReader::new(stdout);
        let mut line = String::new();

        loop {
            line.clear();
            match reader.read_line(&mut line).await {
                Ok(0) => {
                    debug!("EOF on stdout");
                    break;
                }
                Ok(_) => {
                    let trimmed = line.trim();
                    if trimmed.is_empty() {
                        continue;
                    }

                    match serde_json::from_str::<McpResponse>(trimmed) {
                        Ok(response) => {
                            debug!(id = response.id, "Received response");
                            if response_tx.send(response).await.is_err() {
                                break;
                            }
                        }
                        Err(e) => {
                            // Try parsing as notification
                            match serde_json::from_str::<McpNotification>(trimmed) {
                                Ok(notification) => {
                                    debug!(method = %notification.method, "Received notification");
                                    // Handle notifications (could add callback here)
                                }
                                Err(_) => {
                                    warn!(error = %e, line = %trimmed, "Failed to parse message");
                                }
                            }
                        }
                    }
                }
                Err(e) => {
                    error!(error = %e, "Failed to read from stdout");
                    break;
                }
            }
        }
    }
}

#[async_trait]
impl TransportInner for StdioTransport {
    async fn request(&self, request: McpRequest, timeout: Duration) -> ToolResult<McpResponse> {
        let (response_tx, response_rx) = oneshot::channel();

        self.request_tx
            .send((request.clone(), response_tx))
            .await
            .map_err(|_| ToolError::McpConnectionError {
                reason: "transport channel closed".to_string(),
            })?;

        match kelpie_core::current_runtime().timeout(timeout, response_rx).await {
            Ok(Ok(result)) => result,
            Ok(Err(_)) => Err(ToolError::McpConnectionError {
                reason: "response channel closed".to_string(),
            }),
            Err(_) => Err(ToolError::ExecutionTimeout {
                tool: request.method,
                timeout_ms: timeout.as_millis() as u64,
            }),
        }
    }

    async fn notify(&self, notification: McpNotification) -> ToolResult<()> {
        self.notify_tx
            .send(notification)
            .await
            .map_err(|_| ToolError::McpConnectionError {
                reason: "notification channel closed".to_string(),
            })
    }

    async fn close(&self) -> ToolResult<()> {
        if let Some(mut child) = self.child_handle.write().await.take() {
            let _ = child.kill().await;
        }
        Ok(())
    }
}

/// HTTP transport - communicates via HTTP POST
struct HttpTransport {
    /// HTTP client
    client: reqwest::Client,
    /// Server URL
    url: String,
}

impl HttpTransport {
    /// Create a new HTTP transport
    fn new(url: &str, timeout: Duration) -> ToolResult<Self> {
        let client = reqwest::Client::builder()
            .timeout(timeout)
            .build()
            .map_err(|e| ToolError::McpConnectionError {
                reason: format!("failed to create HTTP client: {}", e),
            })?;

        Ok(Self {
            client,
            url: url.to_string(),
        })
    }
}

#[async_trait]
impl TransportInner for HttpTransport {
    async fn request(&self, request: McpRequest, timeout: Duration) -> ToolResult<McpResponse> {
        let response = self
            .client
            .post(&self.url)
            .timeout(timeout)
            .json(&request)
            .send()
            .await
            .map_err(|e| ToolError::McpConnectionError {
                reason: format!("HTTP request failed: {}", e),
            })?;

        if !response.status().is_success() {
            return Err(ToolError::McpConnectionError {
                reason: format!("HTTP error: {}", response.status()),
            });
        }

        let mcp_response: McpResponse =
            response
                .json()
                .await
                .map_err(|e| ToolError::McpProtocolError {
                    reason: format!("failed to parse response: {}", e),
                })?;

        Ok(mcp_response)
    }

    async fn notify(&self, notification: McpNotification) -> ToolResult<()> {
        let _ = self
            .client
            .post(&self.url)
            .json(&notification)
            .send()
            .await
            .map_err(|e| ToolError::McpConnectionError {
                reason: format!("HTTP notification failed: {}", e),
            })?;

        Ok(())
    }

    async fn close(&self) -> ToolResult<()> {
        // HTTP is stateless, nothing to close
        Ok(())
    }
}

/// SSE transport - communicates via Server-Sent Events
struct SseTransport {
    /// HTTP client for sending requests
    client: reqwest::Client,
    /// Server URL for requests
    request_url: String,
    /// Pending responses
    pending: Arc<RwLock<HashMap<u64, oneshot::Sender<ToolResult<McpResponse>>>>>,
    /// Shutdown signal (kept to trigger drop-based shutdown)
    #[allow(dead_code)]
    shutdown_tx: Option<mpsc::Sender<()>>,
}

impl SseTransport {
    /// Create a new SSE transport
    async fn new(url: &str, timeout: Duration) -> ToolResult<Self> {
        let client = reqwest::Client::builder()
            .timeout(timeout)
            .build()
            .map_err(|e| ToolError::McpConnectionError {
                reason: format!("failed to create HTTP client: {}", e),
            })?;

        let pending: Arc<RwLock<HashMap<u64, oneshot::Sender<ToolResult<McpResponse>>>>> =
            Arc::new(RwLock::new(HashMap::new()));

        let (shutdown_tx, mut shutdown_rx) = mpsc::channel::<()>(1);

        // Start SSE listener
        let sse_url = format!("{}/sse", url.trim_end_matches('/'));
        let pending_clone = pending.clone();

        kelpie_core::current_runtime().spawn(async move {
            use futures::StreamExt;
            use reqwest_eventsource::{Event, EventSource};

            let mut es = EventSource::get(&sse_url);

            loop {
                tokio::select! {
                    event = es.next() => {
                        match event {
                            Some(Ok(Event::Message(msg))) => {
                                if let Ok(response) = serde_json::from_str::<McpResponse>(&msg.data) {
                                    let id = response.id;
                                    if let Some(sender) = pending_clone.write().await.remove(&id) {
                                        let _ = sender.send(Ok(response));
                                    }
                                }
                            }
                            Some(Ok(Event::Open)) => {
                                debug!("SSE connection opened");
                            }
                            Some(Err(e)) => {
                                error!(error = %e, "SSE error");
                                break;
                            }
                            None => break,
                        }
                    }
                    _ = shutdown_rx.recv() => {
                        debug!("SSE transport shutting down");
                        break;
                    }
                }
            }
        });

        Ok(Self {
            client,
            request_url: url.to_string(),
            pending,
            shutdown_tx: Some(shutdown_tx),
        })
    }
}

#[async_trait]
impl TransportInner for SseTransport {
    async fn request(&self, request: McpRequest, timeout: Duration) -> ToolResult<McpResponse> {
        let (response_tx, response_rx) = oneshot::channel();
        let id = request.id;

        self.pending.write().await.insert(id, response_tx);

        // Send request via HTTP POST
        let result = self
            .client
            .post(&self.request_url)
            .timeout(timeout)
            .json(&request)
            .send()
            .await;

        if let Err(e) = result {
            self.pending.write().await.remove(&id);
            return Err(ToolError::McpConnectionError {
                reason: format!("HTTP request failed: {}", e),
            });
        }

        // Wait for response via SSE
        match kelpie_core::current_runtime().timeout(timeout, response_rx).await {
            Ok(Ok(result)) => result,
            Ok(Err(_)) => {
                self.pending.write().await.remove(&id);
                Err(ToolError::McpConnectionError {
                    reason: "response channel closed".to_string(),
                })
            }
            Err(_) => {
                self.pending.write().await.remove(&id);
                Err(ToolError::ExecutionTimeout {
                    tool: request.method,
                    timeout_ms: timeout.as_millis() as u64,
                })
            }
        }
    }

    async fn notify(&self, notification: McpNotification) -> ToolResult<()> {
        let _ = self
            .client
            .post(&self.request_url)
            .json(&notification)
            .send()
            .await
            .map_err(|e| ToolError::McpConnectionError {
                reason: format!("HTTP notification failed: {}", e),
            })?;

        Ok(())
    }

    async fn close(&self) -> ToolResult<()> {
        // Signal shutdown - this is a bit awkward due to ownership
        // In practice the transport gets dropped
        Ok(())
    }
}

/// MCP client for connecting to MCP servers
pub struct McpClient {
    /// Configuration
    config: McpConfig,
    /// Connection state
    state: RwLock<McpClientState>,
    /// Request ID counter
    request_id: std::sync::atomic::AtomicU64,
    /// Discovered tools
    tools: RwLock<HashMap<String, McpToolDefinition>>,
    /// Active transport
    transport: RwLock<Option<Box<dyn TransportInner>>>,
    /// Server capabilities
    capabilities: RwLock<Option<ServerCapabilities>>,
}

impl McpClient {
    /// Create a new MCP client
    pub fn new(config: McpConfig) -> Self {
        Self {
            config,
            state: RwLock::new(McpClientState::Disconnected),
            request_id: std::sync::atomic::AtomicU64::new(1),
            tools: RwLock::new(HashMap::new()),
            transport: RwLock::new(None),
            capabilities: RwLock::new(None),
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

    /// Get server capabilities
    pub async fn capabilities(&self) -> Option<ServerCapabilities> {
        self.capabilities.read().await.clone()
    }

    /// Connect to the MCP server
    pub async fn connect(&self) -> ToolResult<()> {
        {
            let mut state = self.state.write().await;
            if *state == McpClientState::Connected {
                return Ok(());
            }
            *state = McpClientState::Connecting;
        }

        info!(server = %self.config.name, "Connecting to MCP server");

        let timeout = Duration::from_millis(self.config.connection_timeout_ms);

        // Create transport based on configuration
        let transport: Box<dyn TransportInner> = match &self.config.transport {
            McpTransport::Stdio { command, args } => {
                info!(
                    command = %command,
                    args = ?args,
                    "Spawning stdio MCP server"
                );
                Box::new(StdioTransport::new(command, args, &self.config.env, timeout).await?)
            }
            McpTransport::Http { url } => {
                info!(url = %url, "Connecting to HTTP MCP server");
                Box::new(HttpTransport::new(url, timeout)?)
            }
            McpTransport::Sse { url } => {
                info!(url = %url, "Connecting to SSE MCP server");
                Box::new(SseTransport::new(url, timeout).await?)
            }
        };

        // Store transport
        *self.transport.write().await = Some(transport);

        // Send initialize request
        let init_request =
            McpRequest::new(self.next_request_id(), "initialize").with_params(serde_json::json!({
                "protocolVersion": MCP_PROTOCOL_VERSION,
                "capabilities": {
                    "tools": {}
                },
                "clientInfo": {
                    "name": "kelpie",
                    "version": env!("CARGO_PKG_VERSION")
                }
            }));

        let response = self.send_request(init_request).await?;

        // Parse initialize result
        if let Some(error) = response.error {
            let mut state = self.state.write().await;
            *state = McpClientState::Failed;
            return Err(ToolError::McpProtocolError {
                reason: format!(
                    "initialization failed: {} (code {})",
                    error.message, error.code
                ),
            });
        }

        if let Some(result) = response.result {
            let init_result: InitializeResult =
                serde_json::from_value(result).map_err(|e| ToolError::McpProtocolError {
                    reason: format!("failed to parse initialize result: {}", e),
                })?;

            info!(
                server_name = %init_result.server_info.name,
                server_version = %init_result.server_info.version,
                protocol_version = %init_result.protocol_version,
                "MCP server initialized"
            );

            *self.capabilities.write().await = Some(init_result.capabilities);
        }

        // Send initialized notification
        let initialized = McpNotification {
            jsonrpc: "2.0".to_string(),
            method: "notifications/initialized".to_string(),
            params: None,
        };
        self.send_notification(initialized).await?;

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
        if let Some(transport) = self.transport.write().await.take() {
            transport.close().await?;
        }

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

        // MCP protocol: tools/list with no params (FastMCP doesn't support cursor pagination)
        let request = McpRequest::new(self.next_request_id(), "tools/list");
        let response = self.send_request(request).await?;

        if let Some(error) = response.error {
            return Err(ToolError::McpProtocolError {
                reason: format!("tools/list failed: {} (code {})", error.message, error.code),
            });
        }

        let result = response.result.ok_or_else(|| ToolError::McpProtocolError {
            reason: "tools/list returned no result".to_string(),
        })?;

        #[derive(Deserialize)]
        struct ToolsListResult {
            tools: Vec<McpToolDefinition>,
        }

        let tools_result: ToolsListResult =
            serde_json::from_value(result).map_err(|e| ToolError::McpProtocolError {
                reason: format!("failed to parse tools list: {}", e),
            })?;

        // Cache discovered tools
        {
            let mut tools = self.tools.write().await;
            tools.clear();
            for tool in &tools_result.tools {
                tools.insert(tool.name.clone(), tool.clone());
            }
        }

        info!(
            server = %self.config.name,
            tool_count = tools_result.tools.len(),
            "Discovered tools"
        );

        Ok(tools_result.tools)
    }

    /// Execute a tool on the MCP server
    pub async fn execute_tool(&self, name: &str, arguments: Value) -> ToolResult<Value> {
        if !self.is_connected().await {
            return Err(ToolError::McpConnectionError {
                reason: "not connected".to_string(),
            });
        }

        debug!(server = %self.config.name, tool = %name, "Executing MCP tool");

        let request =
            McpRequest::new(self.next_request_id(), "tools/call").with_params(serde_json::json!({
                "name": name,
                "arguments": arguments
            }));

        let response = self.send_request(request).await?;

        if let Some(error) = response.error {
            return Err(ToolError::ExecutionFailed {
                tool: name.to_string(),
                reason: format!("{} (code {})", error.message, error.code),
            });
        }

        let result = response.result.ok_or_else(|| ToolError::ExecutionFailed {
            tool: name.to_string(),
            reason: "no result returned".to_string(),
        })?;

        Ok(result)
    }

    /// Send a request through the transport
    async fn send_request(&self, request: McpRequest) -> ToolResult<McpResponse> {
        let transport = self.transport.read().await;
        let transport = transport
            .as_ref()
            .ok_or_else(|| ToolError::McpConnectionError {
                reason: "no transport available".to_string(),
            })?;

        let timeout = Duration::from_millis(self.config.request_timeout_ms);
        transport.request(request, timeout).await
    }

    /// Send a notification through the transport
    async fn send_notification(&self, notification: McpNotification) -> ToolResult<()> {
        let transport = self.transport.read().await;
        let transport = transport
            .as_ref()
            .ok_or_else(|| ToolError::McpConnectionError {
                reason: "no transport available".to_string(),
            })?;

        transport.notify(notification).await
    }

    /// Get next request ID
    fn next_request_id(&self) -> u64 {
        self.request_id
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    /// Register a tool definition manually (for testing without server connection)
    pub async fn register_mock_tool(&self, tool: McpToolDefinition) {
        let mut tools = self.tools.write().await;
        tools.insert(tool.name.clone(), tool);
    }

    /// Set client state to connected (for testing without actual connection)
    ///
    /// # Safety
    /// This bypasses the normal initialization flow and should only be used in tests.
    pub async fn set_connected_for_testing(&self) {
        let mut state = self.state.write().await;
        *state = McpClientState::Connected;
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
    fn test_mcp_config_sse() {
        let config = McpConfig::sse("sse-server", "http://localhost:8080");

        assert_eq!(config.name, "sse-server");
        assert!(matches!(config.transport, McpTransport::Sse { .. }));
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
    async fn test_mcp_client_state_transitions() {
        let config = McpConfig::stdio("test", "nonexistent_command_12345", vec![]);
        let client = McpClient::new(config);

        assert_eq!(client.state().await, McpClientState::Disconnected);
        assert!(!client.is_connected().await);
    }

    #[tokio::test]
    async fn test_mcp_client_discover_not_connected() {
        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = McpClient::new(config);

        let result = client.discover_tools().await;
        assert!(matches!(result, Err(ToolError::McpConnectionError { .. })));
    }

    #[tokio::test]
    async fn test_mcp_client_execute_not_connected() {
        let config = McpConfig::stdio("test", "echo", vec![]);
        let client = McpClient::new(config);

        let result = client.execute_tool("test", serde_json::json!({})).await;
        assert!(matches!(result, Err(ToolError::McpConnectionError { .. })));
    }

    #[test]
    fn test_mcp_tool_definition() {
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

    #[test]
    fn test_server_capabilities_deserialization() {
        let json = serde_json::json!({
            "tools": {
                "listChanged": true
            }
        });

        let caps: ServerCapabilities = serde_json::from_value(json).unwrap();
        assert!(caps.tools.is_some());
        assert!(caps.tools.unwrap().list_changed);
    }

    #[test]
    fn test_initialize_result_deserialization() {
        let json = serde_json::json!({
            "protocolVersion": "2024-11-05",
            "capabilities": {
                "tools": {}
            },
            "serverInfo": {
                "name": "test-server",
                "version": "1.0.0"
            }
        });

        let result: InitializeResult = serde_json::from_value(json).unwrap();
        assert_eq!(result.protocol_version, "2024-11-05");
        assert_eq!(result.server_info.name, "test-server");
    }
}

//! MCP Client Example
//!
//! Demonstrates connecting to an MCP server and executing tools.
//!
//! Prerequisites:
//! 1. Python 3 installed
//!
//! Run:
//! ```bash
//! cargo run -p kelpie-tools --example mcp_client
//! ```

use kelpie_tools::mcp::{McpClient, McpConfig};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing for debug output
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("kelpie_tools=debug".parse()?)
                .add_directive("mcp_client=info".parse()?),
        )
        .init();

    println!("MCP Client Example");
    println!("==================");
    println!();

    // Get the path to the test server
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let server_path = format!("{}/examples/mcp_test_server.py", manifest_dir);

    println!("Connecting to MCP server: python3 {}", server_path);
    println!();

    // Create MCP client with stdio transport
    let config = McpConfig::stdio("test-server", "python3", vec![server_path])
        .with_connection_timeout_ms(10_000)
        .with_request_timeout_ms(30_000);

    let client = Arc::new(McpClient::new(config));

    // Connect to the server
    println!("Connecting...");
    client.connect().await?;
    println!("Connected!");
    println!();

    // Get server capabilities
    if let Some(caps) = client.capabilities().await {
        println!("Server capabilities:");
        if caps.tools.is_some() {
            println!("  - Tools: supported");
        }
        if caps.resources.is_some() {
            println!("  - Resources: supported");
        }
        if caps.prompts.is_some() {
            println!("  - Prompts: supported");
        }
        println!();
    }

    // Discover available tools
    println!("Discovering tools...");
    let tools: Vec<kelpie_tools::mcp::McpToolDefinition> = client.discover_tools().await?;
    println!("Found {} tools:", tools.len());
    for tool in &tools {
        println!("  - {}: {}", tool.name, tool.description);
    }
    println!();

    // Execute the echo tool
    println!("Executing 'echo' tool...");
    let result: serde_json::Value = client
        .execute_tool("echo", serde_json::json!({"message": "Hello from Kelpie!"}))
        .await?;
    println!("Result: {}", serde_json::to_string_pretty(&result)?);
    println!();

    // Execute the add tool
    println!("Executing 'add' tool...");
    let result: serde_json::Value = client
        .execute_tool("add", serde_json::json!({"a": 42, "b": 17}))
        .await?;
    println!("Result: {}", serde_json::to_string_pretty(&result)?);
    println!();

    // Execute the read_file tool
    println!("Executing 'read_file' tool...");
    let result: serde_json::Value = client
        .execute_tool("read_file", serde_json::json!({"path": "/etc/hostname"}))
        .await?;
    println!("Result: {}", serde_json::to_string_pretty(&result)?);
    println!();

    // Disconnect
    println!("Disconnecting...");
    client.disconnect().await?;
    println!("Done!");

    Ok(())
}

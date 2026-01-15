//! Messaging Tools for Letta Compatibility
//!
//! TigerStyle: Agent-to-user messaging with dual-mode support.
//!
//! Implements Letta's messaging tools:
//! - send_message: Send a message to the user

use crate::tools::{BuiltinToolHandler, UnifiedToolRegistry};
use serde_json::{json, Value};
use std::sync::Arc;

/// Register messaging tools with the unified registry
pub async fn register_messaging_tools(registry: &UnifiedToolRegistry) {
    register_send_message(registry).await;

    tracing::info!("Registered messaging tools: send_message");
}

/// Register the send_message tool
///
/// This tool allows agents to explicitly send messages to users.
/// In Letta, agents call this tool to communicate with users.
/// In dual-mode, if the agent doesn't call this tool, we fall back
/// to using the LLM's direct response.
async fn register_send_message(registry: &UnifiedToolRegistry) {
    let handler: BuiltinToolHandler = Arc::new(|input: &Value| {
        let input = input.clone();
        Box::pin(async move {
            // Extract message parameter
            let message = match input.get("message").and_then(|v| v.as_str()) {
                Some(m) => m.to_string(),
                None => return "Error: missing required parameter 'message'".to_string(),
            };

            // Validate message is not empty
            if message.trim().is_empty() {
                return "Error: message cannot be empty".to_string();
            }

            // Validate message size (max 100KB)
            const MESSAGE_SIZE_BYTES_MAX: usize = 100 * 1024;
            if message.len() > MESSAGE_SIZE_BYTES_MAX {
                return format!(
                    "Error: message too large ({} bytes, max {} bytes)",
                    message.len(),
                    MESSAGE_SIZE_BYTES_MAX
                );
            }

            // Return success - the actual message content is captured
            // by the agent message handling logic
            format!("Message sent: {}", message)
        })
    });

    registry
        .register_builtin(
            "send_message",
            "Send a message to the user. Use this to communicate your response. You can call this multiple times in a single turn if needed.",
            json!({
                "type": "object",
                "properties": {
                    "message": {
                        "type": "string",
                        "description": "The message content to send to the user"
                    }
                },
                "required": ["message"]
            }),
            handler,
        )
        .await;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tools::registry::UnifiedToolRegistry;

    #[tokio::test]
    async fn test_send_message_success() {
        let registry = UnifiedToolRegistry::new();
        register_messaging_tools(&registry).await;

        let input = json!({
            "message": "Hello, user!"
        });

        let result = registry.execute("send_message", &input).await;
        assert!(result.success);
        assert!(result.output.contains("Message sent"));
    }

    #[tokio::test]
    async fn test_send_message_empty() {
        let registry = UnifiedToolRegistry::new();
        register_messaging_tools(&registry).await;

        let input = json!({
            "message": ""
        });

        let result = registry.execute("send_message", &input).await;
        // Tool executes successfully but returns error message in output
        assert!(result.output.contains("Error: message cannot be empty"));
    }

    #[tokio::test]
    async fn test_send_message_too_large() {
        let registry = UnifiedToolRegistry::new();
        register_messaging_tools(&registry).await;

        // Create message > 100KB
        let large_message = "x".repeat(101 * 1024);
        let input = json!({
            "message": large_message
        });

        let result = registry.execute("send_message", &input).await;
        assert!(result.output.contains("Error: message too large"));
    }

    #[tokio::test]
    async fn test_send_message_missing_parameter() {
        let registry = UnifiedToolRegistry::new();
        register_messaging_tools(&registry).await;

        let input = json!({});

        let result = registry.execute("send_message", &input).await;
        assert!(result.output.contains("Error: missing required parameter"));
    }
}

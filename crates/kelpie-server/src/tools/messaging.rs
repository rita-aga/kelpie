//! Messaging Tools for Letta Compatibility
//!
//! TigerStyle: Agent-to-user messaging with dual-mode support.
//!
//! Implements Letta's messaging tools:
//! - send_message: Send a message to the user
//!
//! Dual-mode operation:
//! - If agent calls send_message("text"), that text is used as the response
//! - If agent doesn't call send_message, LLM's direct response is used
//! - Supports multiple send_message calls per turn (concatenated with newlines)
//!
//! Implementation: AgentActor's extract_send_message_content() handles routing.

use crate::tools::{BuiltinToolHandler, UnifiedToolRegistry};
use serde_json::{json, Value};
use std::sync::Arc;

// =============================================================================
// TigerStyle Constants
// =============================================================================

/// Maximum message size in bytes (100 KiB)
const MESSAGE_SIZE_BYTES_MAX: usize = 100 * 1024;

/// Register messaging tools with the unified registry
pub async fn register_messaging_tools(registry: &UnifiedToolRegistry) {
    register_send_message(registry).await;

    tracing::info!("Registered messaging tools: send_message");
}

/// Register the send_message tool
///
/// This tool allows agents to explicitly send messages to users.
/// In Letta, agents call this tool to communicate with users.
///
/// Dual-mode operation (implemented in AgentActor):
/// - Agent calls send_message("text") -> extract_send_message_content() uses that text
/// - Agent doesn't call send_message -> falls back to direct LLM response
/// - Multiple send_message calls -> concatenated with newlines
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

            // Validate message size (uses module-level constant)
            if message.len() > MESSAGE_SIZE_BYTES_MAX {
                return format!(
                    "Error: message too large ({} bytes, max {} bytes)",
                    message.len(),
                    MESSAGE_SIZE_BYTES_MAX
                );
            }

            // Return confirmation - AgentActor's extract_send_message_content()
            // handles actual message routing to user
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

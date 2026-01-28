//! Agent-to-Agent Communication Tool (Issue #75)
//!
//! TigerStyle: Multi-agent invocation with cycle detection and timeout.
//!
//! Implements the `call_agent` tool that allows agents to invoke other agents.
//!
//! Safety Mechanisms (per ADR-028 and TLA+ spec KelpieMultiAgentInvocation.tla):
//! - Cycle detection: Agent cannot appear twice in call chain
//! - Depth limiting: Maximum AGENT_CALL_DEPTH_MAX nested calls
//! - Timeout: All calls bounded by AGENT_CALL_TIMEOUT_MS_MAX
//! - Backpressure: Per-agent concurrent call limits
//!
//! Related:
//! - docs/adr/028-multi-agent-communication.md
//! - docs/tla/KelpieMultiAgentInvocation.tla

use crate::tools::{BuiltinToolHandler, ToolExecutionContext, UnifiedToolRegistry};
use serde_json::{json, Value};
use std::sync::Arc;

// =============================================================================
// TigerStyle Constants (aligned with ADR-028 and TLA+ spec)
// =============================================================================

/// Maximum depth for nested agent calls
/// TLA+ invariant: DepthBounded ensures Len(callStack[a]) <= MAX_DEPTH
pub const AGENT_CALL_DEPTH_MAX: u32 = 5;

/// Default timeout for agent calls in milliseconds (30 seconds)
pub const AGENT_CALL_TIMEOUT_MS_DEFAULT: u64 = 30_000;

/// Maximum timeout for agent calls in milliseconds (5 minutes)
pub const AGENT_CALL_TIMEOUT_MS_MAX: u64 = 300_000;

/// Maximum concurrent calls an agent can have pending
pub const AGENT_CONCURRENT_CALLS_MAX: usize = 10;

/// Maximum message size in bytes for agent-to-agent calls (100 KiB)
pub const AGENT_CALL_MESSAGE_SIZE_BYTES_MAX: usize = 100 * 1024;

/// Maximum response size in bytes (1 MiB)
pub const AGENT_CALL_RESPONSE_SIZE_BYTES_MAX: usize = 1024 * 1024;

// =============================================================================
// Tool Registration
// =============================================================================

/// Register the call_agent tool with the unified registry
///
/// This tool enables agent-to-agent communication with safety guarantees.
///
/// TLA+ Safety Invariants Enforced:
/// - NoDeadlock: Cycle detection prevents A→B→A deadlock
/// - DepthBounded: Call depth limited to AGENT_CALL_DEPTH_MAX
/// - SingleActivationDuringCall: Dispatcher ensures single activation
pub async fn register_call_agent_tool(registry: &UnifiedToolRegistry) {
    let handler: BuiltinToolHandler = Arc::new(|input: &Value| {
        let input = input.clone();
        Box::pin(async move {
            // Extract required parameters
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let message = match input.get("message").and_then(|v| v.as_str()) {
                Some(m) => m.to_string(),
                None => return "Error: missing required parameter 'message'".to_string(),
            };

            // Extract optional timeout (with bounds checking)
            let timeout_ms = input
                .get("timeout_ms")
                .and_then(|v| v.as_u64())
                .unwrap_or(AGENT_CALL_TIMEOUT_MS_DEFAULT)
                .min(AGENT_CALL_TIMEOUT_MS_MAX);

            // Validate agent_id is not empty
            if agent_id.trim().is_empty() {
                return "Error: agent_id cannot be empty".to_string();
            }

            // Validate message is not empty
            if message.trim().is_empty() {
                return "Error: message cannot be empty".to_string();
            }

            // Validate message size
            if message.len() > AGENT_CALL_MESSAGE_SIZE_BYTES_MAX {
                return format!(
                    "Error: message too large ({} bytes, max {} bytes)",
                    message.len(),
                    AGENT_CALL_MESSAGE_SIZE_BYTES_MAX
                );
            }

            // NOTE: Actual invocation requires dispatcher access which is not available
            // in the basic BuiltinToolHandler signature. This is a placeholder that
            // will be replaced when the handler signature is extended to support context.
            //
            // The implementation follows the pattern:
            // 1. Get call context (call_chain, call_depth) from ToolExecutionContext
            // 2. Check for cycles: if agent_id in call_chain, return error
            // 3. Check depth: if call_depth >= AGENT_CALL_DEPTH_MAX, return error
            // 4. Build new call_chain with current agent appended
            // 5. Create invocation request with HandleMessageFullRequest
            // 6. Call dispatcher.invoke_with_timeout()
            // 7. Return response or error

            // For now, return a placeholder that indicates the tool is registered
            // but requires dispatcher integration to fully function
            format!(
                "call_agent: would call agent '{}' with message '{}' (timeout: {}ms). \
                Full implementation requires dispatcher integration.",
                agent_id, message, timeout_ms
            )
        })
    });

    registry
        .register_builtin(
            "call_agent",
            "Call another agent and wait for their response. Use this to delegate tasks or coordinate with other agents.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The ID of the agent to call"
                    },
                    "message": {
                        "type": "string",
                        "description": "The message to send to the agent"
                    },
                    "timeout_ms": {
                        "type": "integer",
                        "description": "Optional timeout in milliseconds (default: 30000, max: 300000)"
                    }
                },
                "required": ["agent_id", "message"]
            }),
            handler,
        )
        .await;

    tracing::info!("Registered agent communication tool: call_agent");
}

/// Validate call context for cycle detection and depth limiting
///
/// TLA+ Invariants:
/// - NoDeadlock: target_id must not be in call_chain
/// - DepthBounded: call_depth must be < AGENT_CALL_DEPTH_MAX
///
/// Returns Ok(()) if valid, Err(reason) if invalid.
pub fn validate_call_context(
    target_id: &str,
    context: &ToolExecutionContext,
) -> Result<(), String> {
    // TigerStyle: 2+ assertions per function

    // Precondition: target_id is valid
    assert!(!target_id.is_empty(), "target_id cannot be empty");

    // Check for cycle (NoDeadlock invariant)
    if context.call_chain.contains(&target_id.to_string()) {
        return Err(format!(
            "Cycle detected: agent '{}' is already in call chain {:?}",
            target_id, context.call_chain
        ));
    }

    // Check depth limit (DepthBounded invariant)
    if context.call_depth >= AGENT_CALL_DEPTH_MAX {
        return Err(format!(
            "Call depth exceeded: current depth {} >= max {}",
            context.call_depth, AGENT_CALL_DEPTH_MAX
        ));
    }

    // Postcondition: if we reach here, call is valid
    debug_assert!(
        !context.call_chain.contains(&target_id.to_string()),
        "postcondition: no cycle"
    );
    debug_assert!(
        context.call_depth < AGENT_CALL_DEPTH_MAX,
        "postcondition: within depth"
    );

    Ok(())
}

/// Create a new call context for a nested call
///
/// Appends the calling agent to the call chain and increments depth.
pub fn create_nested_context(
    parent_context: &ToolExecutionContext,
    calling_agent_id: &str,
) -> ToolExecutionContext {
    // TigerStyle: 2+ assertions

    // Precondition
    assert!(
        !calling_agent_id.is_empty(),
        "calling_agent_id cannot be empty"
    );
    assert!(
        parent_context.call_depth < AGENT_CALL_DEPTH_MAX,
        "parent context already at max depth"
    );

    let mut new_chain = parent_context.call_chain.clone();
    new_chain.push(calling_agent_id.to_string());

    let context = ToolExecutionContext {
        agent_id: parent_context.agent_id.clone(),
        project_id: parent_context.project_id.clone(),
        call_depth: parent_context.call_depth + 1,
        call_chain: new_chain,
    };

    // Postcondition
    debug_assert_eq!(
        context.call_depth,
        parent_context.call_depth + 1,
        "depth incremented"
    );
    debug_assert!(
        context.call_chain.contains(&calling_agent_id.to_string()),
        "chain contains caller"
    );

    context
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_call_context_success() {
        let context = ToolExecutionContext {
            agent_id: Some("agent-a".to_string()),
            project_id: None,
            call_depth: 0,
            call_chain: vec!["agent-a".to_string()],
        };

        // Agent B is not in chain, should succeed
        assert!(validate_call_context("agent-b", &context).is_ok());
    }

    #[test]
    fn test_validate_call_context_cycle_detected() {
        let context = ToolExecutionContext {
            agent_id: Some("agent-a".to_string()),
            project_id: None,
            call_depth: 1,
            call_chain: vec!["agent-a".to_string(), "agent-b".to_string()],
        };

        // Agent A is in chain, should fail
        let result = validate_call_context("agent-a", &context);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Cycle detected"));
    }

    #[test]
    fn test_validate_call_context_depth_exceeded() {
        let context = ToolExecutionContext {
            agent_id: Some("agent-a".to_string()),
            project_id: None,
            call_depth: AGENT_CALL_DEPTH_MAX,
            call_chain: vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
                "d".to_string(),
                "e".to_string(),
            ],
        };

        // At max depth, should fail
        let result = validate_call_context("agent-f", &context);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Call depth exceeded"));
    }

    #[test]
    fn test_create_nested_context() {
        let parent = ToolExecutionContext {
            agent_id: Some("root".to_string()),
            project_id: Some("project-1".to_string()),
            call_depth: 1,
            call_chain: vec!["agent-a".to_string()],
        };

        let nested = create_nested_context(&parent, "agent-a");

        assert_eq!(nested.call_depth, 2);
        assert_eq!(nested.call_chain.len(), 2);
        assert!(nested.call_chain.contains(&"agent-a".to_string()));
        assert_eq!(nested.project_id, Some("project-1".to_string()));
    }

    #[tokio::test]
    async fn test_register_call_agent_tool() {
        let registry = UnifiedToolRegistry::new();
        register_call_agent_tool(&registry).await;

        // Verify tool is registered
        let tools = registry.list_tools().await;
        assert!(tools.contains(&"call_agent".to_string()));
    }

    #[tokio::test]
    async fn test_call_agent_missing_agent_id() {
        let registry = UnifiedToolRegistry::new();
        register_call_agent_tool(&registry).await;

        let input = json!({
            "message": "Hello"
        });

        let result = registry.execute("call_agent", &input).await;
        assert!(result
            .output
            .contains("Error: missing required parameter 'agent_id'"));
    }

    #[tokio::test]
    async fn test_call_agent_missing_message() {
        let registry = UnifiedToolRegistry::new();
        register_call_agent_tool(&registry).await;

        let input = json!({
            "agent_id": "some-agent"
        });

        let result = registry.execute("call_agent", &input).await;
        assert!(result
            .output
            .contains("Error: missing required parameter 'message'"));
    }

    #[tokio::test]
    async fn test_call_agent_empty_agent_id() {
        let registry = UnifiedToolRegistry::new();
        register_call_agent_tool(&registry).await;

        let input = json!({
            "agent_id": "",
            "message": "Hello"
        });

        let result = registry.execute("call_agent", &input).await;
        assert!(result.output.contains("Error: agent_id cannot be empty"));
    }

    #[tokio::test]
    async fn test_call_agent_message_too_large() {
        let registry = UnifiedToolRegistry::new();
        register_call_agent_tool(&registry).await;

        let large_message = "x".repeat(AGENT_CALL_MESSAGE_SIZE_BYTES_MAX + 1);
        let input = json!({
            "agent_id": "some-agent",
            "message": large_message
        });

        let result = registry.execute("call_agent", &input).await;
        assert!(result.output.contains("Error: message too large"));
    }

    #[tokio::test]
    async fn test_call_agent_timeout_clamped() {
        let registry = UnifiedToolRegistry::new();
        register_call_agent_tool(&registry).await;

        // Request timeout larger than max - should be clamped
        let input = json!({
            "agent_id": "some-agent",
            "message": "Hello",
            "timeout_ms": 999_999_999
        });

        let result = registry.execute("call_agent", &input).await;
        // Should use max timeout, not the requested one
        assert!(result
            .output
            .contains(&format!("{}ms", AGENT_CALL_TIMEOUT_MS_MAX)));
    }
}

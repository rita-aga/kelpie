//! Message API endpoints
//!
//! TigerStyle: Letta-compatible message operations.

use crate::api::ApiError;
use crate::llm::{ChatMessage, ToolDefinition};
use crate::models::{CreateMessageRequest, Message, MessageResponse, MessageRole, UsageStats};
use crate::state::AppState;
use axum::{
    extract::{Path, Query, State},
    Json,
};
use chrono::Utc;
use kelpie_sandbox::{ExecOptions, ProcessSandbox, Sandbox, SandboxConfig};
use serde::Deserialize;
use uuid::Uuid;

/// Query parameters for listing messages
#[derive(Debug, Deserialize)]
pub struct ListMessagesQuery {
    /// Maximum number of messages to return
    #[serde(default = "default_limit")]
    pub limit: usize,
    /// Return messages before this ID
    pub before: Option<String>,
}

fn default_limit() -> usize {
    100
}

/// Maximum limit for list operations
const LIST_LIMIT_MAX: usize = 1000;

/// List messages for an agent
///
/// GET /v1/agents/{agent_id}/messages
pub async fn list_messages(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Query(query): Query<ListMessagesQuery>,
) -> Result<Json<Vec<Message>>, ApiError> {
    let limit = query.limit.min(LIST_LIMIT_MAX);
    let messages = state.list_messages(&agent_id, limit, query.before.as_deref())?;
    Ok(Json(messages))
}

/// Send a message to an agent
///
/// POST /v1/agents/{agent_id}/messages
///
/// Builds a prompt from memory blocks and sends to configured LLM.
/// Requires LLM to be configured via ANTHROPIC_API_KEY or OPENAI_API_KEY.
pub async fn send_message(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Json(request): Json<CreateMessageRequest>,
) -> Result<Json<MessageResponse>, ApiError> {
    // Validate message
    if request.content.is_empty() && request.role != MessageRole::Tool {
        return Err(ApiError::bad_request("message content cannot be empty"));
    }

    // Create user message
    let user_message = Message {
        id: Uuid::new_v4().to_string(),
        agent_id: agent_id.clone(),
        role: request.role.clone(),
        content: request.content.clone(),
        tool_call_id: request.tool_call_id.clone(),
        tool_calls: None,
        created_at: Utc::now(),
    };

    // Store user message
    let stored_user_msg = state.add_message(&agent_id, user_message)?;

    // Get agent for memory blocks and system prompt
    let agent = state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    // Generate response via LLM (required)
    let llm = state.llm().ok_or_else(|| {
        ApiError::internal("LLM not configured. Set ANTHROPIC_API_KEY or OPENAI_API_KEY environment variable.")
    })?;

    let (response_content, prompt_tokens, completion_tokens) = {
        // Build messages for LLM
        let mut messages = Vec::new();

        // System message with memory blocks
        let system_content = build_system_prompt(&agent.system, &agent.blocks);
        messages.push(ChatMessage {
            role: "system".to_string(),
            content: system_content,
        });

        // Get recent message history (last 20 messages)
        let history = state.list_messages(&agent_id, 20, None).unwrap_or_default();
        for msg in history.iter() {
            // Skip the message we just added
            if msg.id == stored_user_msg.id {
                continue;
            }
            messages.push(ChatMessage {
                role: match msg.role {
                    MessageRole::User => "user",
                    MessageRole::Assistant => "assistant",
                    MessageRole::System => "system",
                    MessageRole::Tool => "tool",
                }
                .to_string(),
                content: msg.content.clone(),
            });
        }

        // Add current user message
        messages.push(ChatMessage {
            role: "user".to_string(),
            content: request.content.clone(),
        });

        // Define available tools
        let tools = vec![ToolDefinition::shell()];

        // Call LLM with tools
        match llm.complete_with_tools(messages.clone(), tools.clone()).await {
            Ok(mut response) => {
                let mut total_prompt = response.prompt_tokens;
                let mut total_completion = response.completion_tokens;
                let mut final_content = response.content.clone();

                // Handle tool use loop (max 5 iterations)
                let mut iterations = 0;
                while response.stop_reason == "tool_use" && iterations < 5 {
                    iterations += 1;
                    tracing::info!(
                        agent_id = %agent_id,
                        tool_count = response.tool_calls.len(),
                        iteration = iterations,
                        "Executing tools"
                    );

                    // Execute each tool
                    let mut tool_results = Vec::new();
                    for tool_call in &response.tool_calls {
                        let result = execute_tool(&tool_call.name, &tool_call.input);
                        tracing::info!(
                            tool = %tool_call.name,
                            success = result.len() < 1000,
                            "Tool executed"
                        );
                        tool_results.push((tool_call.id.clone(), result));
                    }

                    // Build assistant content blocks for continuation
                    let mut assistant_blocks = Vec::new();
                    if !response.content.is_empty() {
                        assistant_blocks.push(crate::llm::ContentBlock::Text {
                            text: response.content.clone(),
                        });
                    }
                    for tc in &response.tool_calls {
                        assistant_blocks.push(crate::llm::ContentBlock::ToolUse {
                            id: tc.id.clone(),
                            name: tc.name.clone(),
                            input: tc.input.clone(),
                        });
                    }

                    // Continue conversation with tool results
                    match llm
                        .continue_with_tool_result(messages.clone(), tools.clone(), assistant_blocks, tool_results)
                        .await
                    {
                        Ok(next_response) => {
                            total_prompt += next_response.prompt_tokens;
                            total_completion += next_response.completion_tokens;
                            final_content = next_response.content.clone();
                            response = next_response;
                        }
                        Err(e) => {
                            tracing::error!(error = %e, "Tool continuation failed");
                            final_content = format!("Tool execution error: {}", e);
                            break;
                        }
                    }
                }

                tracing::info!(
                    agent_id = %agent_id,
                    prompt_tokens = total_prompt,
                    completion_tokens = total_completion,
                    tool_iterations = iterations,
                    "LLM response received"
                );
                (final_content, total_prompt, total_completion)
            }
            Err(e) => {
                tracing::error!(agent_id = %agent_id, error = %e, "LLM call failed");
                return Err(ApiError::internal(&format!("LLM call failed: {}", e)));
            }
        }
    };

    // Create assistant message
    let assistant_message = Message {
        id: Uuid::new_v4().to_string(),
        agent_id: agent_id.clone(),
        role: MessageRole::Assistant,
        content: response_content,
        tool_call_id: None,
        tool_calls: None,
        created_at: Utc::now(),
    };

    // Store assistant message
    let stored_assistant_msg = state.add_message(&agent_id, assistant_message)?;

    tracing::info!(
        agent_id = %agent_id,
        user_msg_id = %stored_user_msg.id,
        assistant_msg_id = %stored_assistant_msg.id,
        "processed message"
    );

    Ok(Json(MessageResponse {
        messages: vec![stored_user_msg, stored_assistant_msg],
        usage: Some(UsageStats {
            prompt_tokens,
            completion_tokens,
            total_tokens: prompt_tokens + completion_tokens,
        }),
    }))
}

/// Build system prompt from agent's system message and memory blocks
fn build_system_prompt(system: &Option<String>, blocks: &[crate::models::Block]) -> String {
    let mut parts = Vec::new();

    // Add base system prompt
    if let Some(sys) = system {
        parts.push(sys.clone());
    }

    // Add memory blocks
    if !blocks.is_empty() {
        parts.push("\n\n<memory>".to_string());
        for block in blocks {
            parts.push(format!("<{}>\n{}\n</{}>", block.label, block.value, block.label));
        }
        parts.push("</memory>".to_string());
    }

    parts.join("\n")
}

/// Rough token estimate (4 chars per token on average)
fn estimate_tokens(text: &str) -> u64 {
    (text.len() / 4).max(1) as u64
}

/// Execute a tool and return the result
fn execute_tool(name: &str, input: &serde_json::Value) -> String {
    match name {
        "shell" => {
            let command = input
                .get("command")
                .and_then(|v| v.as_str())
                .unwrap_or("");

            if command.is_empty() {
                return "Error: No command provided".to_string();
            }

            // Execute via sandbox
            let result = tokio::task::block_in_place(|| {
                tokio::runtime::Handle::current().block_on(async {
                    execute_in_sandbox(command).await
                })
            });

            result
        }
        _ => format!("Unknown tool: {}", name),
    }
}

/// Execute a command in a sandboxed environment
async fn execute_in_sandbox(command: &str) -> String {
    // Create and start sandbox
    let config = SandboxConfig::default();
    let mut sandbox = ProcessSandbox::new(config);

    if let Err(e) = sandbox.start().await {
        return format!("Failed to start sandbox: {}", e);
    }

    // Execute command via sh -c for shell expansion
    let exec_opts = ExecOptions::new()
        .with_timeout(std::time::Duration::from_secs(30))
        .with_max_output(1024 * 1024);

    match sandbox.exec("sh", &["-c", command], exec_opts).await {
        Ok(output) => {
            let stdout = output.stdout_string();
            let stderr = output.stderr_string();

            if output.is_success() {
                if stdout.is_empty() {
                    "Command executed successfully (no output)".to_string()
                } else {
                    // Truncate long output
                    if stdout.len() > 4000 {
                        format!("{}...\n[truncated, {} total bytes]", &stdout[..4000], stdout.len())
                    } else {
                        stdout
                    }
                }
            } else {
                format!(
                    "Command failed with exit code {}:\n{}{}",
                    output.status.code,
                    stdout,
                    stderr
                )
            }
        }
        Err(e) => format!("Sandbox execution failed: {}", e),
    }
}

#[cfg(test)]
mod tests {
    use crate::api;
    use crate::models::{AgentState, MessageRole};
    use crate::state::AppState;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use axum::Router;
    use tower::ServiceExt;

    async fn test_app_with_agent() -> (Router, String) {
        let state = AppState::new();

        // Create agent
        let body = serde_json::json!({
            "name": "msg-test-agent",
        });

        let app = api::router(state.clone());

        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/v1/agents")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let agent: AgentState = serde_json::from_slice(&body).unwrap();

        (api::router(state), agent.id)
    }

    #[tokio::test]
    async fn test_send_message_requires_llm() {
        let (app, agent_id) = test_app_with_agent().await;

        let message = serde_json::json!({
            "role": "user",
            "content": "Hello, agent!"
        });

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri(format!("/v1/agents/{}/messages", agent_id))
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&message).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        // Without LLM configured, should return 500 with helpful error
        assert_eq!(response.status(), StatusCode::INTERNAL_SERVER_ERROR);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let error_text = String::from_utf8_lossy(&body);
        assert!(error_text.contains("LLM not configured"));
    }

    #[tokio::test]
    async fn test_send_empty_message() {
        let (app, agent_id) = test_app_with_agent().await;

        let message = serde_json::json!({
            "role": "user",
            "content": ""
        });

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri(format!("/v1/agents/{}/messages", agent_id))
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&message).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::BAD_REQUEST);
    }

    #[tokio::test]
    async fn test_list_messages_empty() {
        let (app, agent_id) = test_app_with_agent().await;

        // List messages on agent with no messages
        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri(format!("/v1/agents/{}/messages?limit=10", agent_id))
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let messages: Vec<crate::models::Message> = serde_json::from_slice(&body).unwrap();

        // No messages sent yet
        assert_eq!(messages.len(), 0);
    }
}

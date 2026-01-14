//! SSE streaming for letta-code compatibility
//!
//! TigerStyle: Implements Letta's SSE streaming protocol.

use crate::api::ApiError;
use axum::{
    extract::{Path, Query, State},
    response::sse::{Event, KeepAlive, Sse},
};
use chrono::Utc;
use futures::stream::{self, Stream, StreamExt};
use kelpie_sandbox::{ExecOptions, ProcessSandbox, Sandbox, SandboxConfig};
use kelpie_server::llm::{ChatMessage, ContentBlock, ToolDefinition};
use kelpie_server::models::{CreateMessageRequest, Message, MessageRole};
use kelpie_server::state::AppState;
use serde::{Deserialize, Serialize};
use std::convert::Infallible;
use std::time::Duration;
use tracing::instrument;
use uuid::Uuid;

/// Query parameters for streaming messages
#[derive(Debug, Deserialize)]
#[allow(dead_code)]
pub struct StreamQuery {
    /// Enable step streaming (default: true for letta-code)
    #[serde(default = "default_true")]
    pub stream_steps: bool,
    /// Enable token streaming (not yet implemented)
    #[serde(default)]
    pub stream_tokens: bool,
}

fn default_true() -> bool {
    true
}

/// Letta SSE message types
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "message_type")]
#[allow(clippy::enum_variant_names)]
#[allow(dead_code)]
enum SseMessage {
    #[serde(rename = "assistant_message")]
    AssistantMessage { id: String, content: String },
    #[serde(rename = "reasoning_message")]
    ReasoningMessage { id: String, reasoning: String },
    #[serde(rename = "tool_call_message")]
    ToolCallMessage { id: String, tool_call: ToolCallInfo },
    #[serde(rename = "tool_return_message")]
    ToolReturnMessage {
        id: String,
        tool_return: String,
        status: String,
    },
    #[serde(rename = "usage_statistics")]
    UsageStatistics {
        completion_tokens: u64,
        prompt_tokens: u64,
        total_tokens: u64,
        step_count: u32,
    },
}

#[derive(Debug, Clone, Serialize)]
struct ToolCallInfo {
    name: String,
    arguments: serde_json::Value,
}

/// SSE event for stop reason (separate because of different structure)
#[derive(Debug, Clone, Serialize)]
struct StopReasonEvent {
    message_type: &'static str,
    stop_reason: String,
}

/// Send a streaming message to an agent
///
/// POST /v1/agents/{agent_id}/messages/stream
#[instrument(skip(state, _query, request), fields(agent_id = %agent_id), level = "info")]
pub async fn send_message_stream(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Query(_query): Query<StreamQuery>,
    axum::Json(request): axum::Json<CreateMessageRequest>,
) -> Result<Sse<impl Stream<Item = Result<Event, Infallible>>>, ApiError> {
    // Extract effective content from various request formats
    let (role, content) = request
        .effective_content()
        .ok_or_else(|| ApiError::bad_request("message content cannot be empty"))?;

    // Verify agent exists and get data we need
    let agent = state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    let llm = state.llm().ok_or_else(|| {
        ApiError::internal(
            "LLM not configured. Set ANTHROPIC_API_KEY or OPENAI_API_KEY environment variable.",
        )
    })?;

    // Clone things we need for the async stream
    let agent_id_clone = agent_id.clone();
    let state_clone = state.clone();
    let llm_clone = llm.clone();
    let agent_clone = agent.clone();

    // Create user message
    let user_message = Message {
        id: Uuid::new_v4().to_string(),
        agent_id: agent_id.clone(),
        message_type: Message::message_type_from_role(&role),
        role: role.clone(),
        content: content.clone(),
        tool_call_id: request.tool_call_id.clone(),
        tool_calls: None,
        created_at: Utc::now(),
    };

    // Store user message
    let _stored_user_msg = state.add_message(&agent_id, user_message)?;

    // Create the SSE stream
    let stream = stream::once(async move {
        let events = generate_response_events(
            &state_clone,
            &agent_id_clone,
            &agent_clone,
            &llm_clone,
            content,
        )
        .await;
        stream::iter(events)
    })
    .flatten();

    Ok(Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("keep-alive"),
    ))
}

/// Generate all SSE events for a response
async fn generate_response_events(
    state: &AppState,
    agent_id: &str,
    agent: &kelpie_server::models::AgentState,
    llm: &crate::llm::LlmClient,
    content: String,
) -> Vec<Result<Event, Infallible>> {
    let mut events = Vec::new();
    let mut total_prompt_tokens = 0u64;
    let mut total_completion_tokens = 0u64;
    let mut step_count = 0u32;

    // Build messages for LLM
    let mut messages = Vec::new();

    // System message with memory blocks
    let system_content = build_system_prompt(&agent.system, &agent.blocks);
    messages.push(ChatMessage {
        role: "system".to_string(),
        content: system_content,
    });

    // Get recent message history
    let history = state.list_messages(agent_id, 20, None).unwrap_or_default();
    for msg in history.iter() {
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
        content: content.clone(),
    });

    // Define available tools
    let tools = vec![ToolDefinition::shell()];

    // Call LLM
    match llm
        .complete_with_tools(messages.clone(), tools.clone())
        .await
    {
        Ok(mut response) => {
            total_prompt_tokens += response.prompt_tokens;
            total_completion_tokens += response.completion_tokens;
            step_count += 1;

            let mut final_content = response.content.clone();
            let mut iterations = 0;

            // Handle tool use loop
            while response.stop_reason == "tool_use" && iterations < 5 {
                iterations += 1;

                // Send tool call events
                for tool_call in &response.tool_calls {
                    let tool_msg = SseMessage::ToolCallMessage {
                        id: Uuid::new_v4().to_string(),
                        tool_call: ToolCallInfo {
                            name: tool_call.name.clone(),
                            arguments: tool_call.input.clone(),
                        },
                    };
                    if let Ok(json) = serde_json::to_string(&tool_msg) {
                        events.push(Ok(Event::default().data(json)));
                    }
                }

                // Execute tools
                let mut tool_results = Vec::new();
                for tool_call in &response.tool_calls {
                    let result = execute_tool(&tool_call.name, &tool_call.input).await;

                    // Send tool return event
                    let return_msg = SseMessage::ToolReturnMessage {
                        id: Uuid::new_v4().to_string(),
                        tool_return: result.clone(),
                        status: "success".to_string(),
                    };
                    if let Ok(json) = serde_json::to_string(&return_msg) {
                        events.push(Ok(Event::default().data(json)));
                    }

                    tool_results.push((tool_call.id.clone(), result));
                }

                // Build assistant content blocks for continuation
                let mut assistant_blocks = Vec::new();
                if !response.content.is_empty() {
                    assistant_blocks.push(ContentBlock::Text {
                        text: response.content.clone(),
                    });
                }
                for tc in &response.tool_calls {
                    assistant_blocks.push(ContentBlock::ToolUse {
                        id: tc.id.clone(),
                        name: tc.name.clone(),
                        input: tc.input.clone(),
                    });
                }

                // Continue conversation with tool results
                match llm
                    .continue_with_tool_result(
                        messages.clone(),
                        tools.clone(),
                        assistant_blocks,
                        tool_results,
                    )
                    .await
                {
                    Ok(next_response) => {
                        total_prompt_tokens += next_response.prompt_tokens;
                        total_completion_tokens += next_response.completion_tokens;
                        step_count += 1;
                        final_content = next_response.content.clone();
                        response = next_response;
                    }
                    Err(e) => {
                        final_content = format!("Tool execution error: {}", e);
                        break;
                    }
                }
            }

            // Send assistant message event
            let assistant_msg = SseMessage::AssistantMessage {
                id: Uuid::new_v4().to_string(),
                content: final_content.clone(),
            };
            if let Ok(json) = serde_json::to_string(&assistant_msg) {
                events.push(Ok(Event::default().data(json)));
            }

            // Store assistant message
            let assistant_message = Message {
                id: Uuid::new_v4().to_string(),
                agent_id: agent_id.to_string(),
                message_type: "assistant_message".to_string(),
                role: MessageRole::Assistant,
                content: final_content,
                tool_call_id: None,
                tool_calls: None,
                created_at: Utc::now(),
            };
            let _ = state.add_message(agent_id, assistant_message);
        }
        Err(e) => {
            // Send error as assistant message
            let error_msg = SseMessage::AssistantMessage {
                id: Uuid::new_v4().to_string(),
                content: format!("Error: {}", e),
            };
            if let Ok(json) = serde_json::to_string(&error_msg) {
                events.push(Ok(Event::default().data(json)));
            }
        }
    }

    // Send stop_reason event
    let stop_event = StopReasonEvent {
        message_type: "stop_reason",
        stop_reason: "end_turn".to_string(),
    };
    if let Ok(json) = serde_json::to_string(&stop_event) {
        events.push(Ok(Event::default().data(json)));
    }

    // Send usage statistics
    let usage_msg = SseMessage::UsageStatistics {
        completion_tokens: total_completion_tokens,
        prompt_tokens: total_prompt_tokens,
        total_tokens: total_prompt_tokens + total_completion_tokens,
        step_count,
    };
    if let Ok(json) = serde_json::to_string(&usage_msg) {
        events.push(Ok(Event::default().data(json)));
    }

    // Send [DONE]
    events.push(Ok(Event::default().data("[DONE]")));

    events
}

/// Build system prompt from agent's system message and memory blocks
fn build_system_prompt(system: &Option<String>, blocks: &[kelpie_server::models::Block]) -> String {
    let mut parts = Vec::new();

    if let Some(sys) = system {
        parts.push(sys.clone());
    }

    if !blocks.is_empty() {
        parts.push("\n\n<memory>".to_string());
        for block in blocks {
            parts.push(format!(
                "<{}>\n{}\n</{}>",
                block.label, block.value, block.label
            ));
        }
        parts.push("</memory>".to_string());
    }

    parts.join("\n")
}

/// Execute a tool and return the result
async fn execute_tool(name: &str, input: &serde_json::Value) -> String {
    match name {
        "shell" => {
            let command = input.get("command").and_then(|v| v.as_str()).unwrap_or("");

            if command.is_empty() {
                return "Error: No command provided".to_string();
            }

            execute_in_sandbox(command).await
        }
        _ => format!("Unknown tool: {}", name),
    }
}

/// Execute a command in a sandboxed environment
async fn execute_in_sandbox(command: &str) -> String {
    let config = SandboxConfig::default();
    let mut sandbox = ProcessSandbox::new(config);

    if let Err(e) = sandbox.start().await {
        return format!("Failed to start sandbox: {}", e);
    }

    let exec_opts = ExecOptions::new()
        .with_timeout(Duration::from_secs(30))
        .with_max_output(1024 * 1024);

    match sandbox.exec("sh", &["-c", command], exec_opts).await {
        Ok(output) => {
            let stdout = output.stdout_string();
            let stderr = output.stderr_string();

            if output.is_success() {
                if stdout.is_empty() {
                    "Command executed successfully (no output)".to_string()
                } else if stdout.len() > 4000 {
                    format!(
                        "{}...\n[truncated, {} total bytes]",
                        &stdout[..4000],
                        stdout.len()
                    )
                } else {
                    stdout
                }
            } else {
                format!(
                    "Command failed with exit code {}:\n{}{}",
                    output.status.code, stdout, stderr
                )
            }
        }
        Err(e) => format!("Sandbox execution failed: {}", e),
    }
}

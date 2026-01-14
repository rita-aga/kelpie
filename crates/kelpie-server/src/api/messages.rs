//! Message API endpoints
//!
//! TigerStyle: Letta-compatible message operations with SSE streaming support.

use crate::api::ApiError;
use axum::{
    extract::{Path, Query, State},
    response::{
        sse::{Event, KeepAlive, Sse},
        IntoResponse, Response,
    },
    Json,
};
use chrono::Utc;
use futures::stream::{self, StreamExt};
use kelpie_server::llm::{ChatMessage, ContentBlock};
use kelpie_server::models::{
    CreateMessageRequest, Message, MessageResponse, MessageRole, UsageStats,
};
use kelpie_server::state::AppState;
use kelpie_server::tools::{parse_pause_signal, ToolSignal, AGENT_LOOP_ITERATIONS_MAX};
use serde::{Deserialize, Serialize};
use std::convert::Infallible;
use std::time::Duration;
use tracing::instrument;
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

/// Query parameters for sending messages (streaming support)
#[derive(Debug, Deserialize, Default)]
#[allow(dead_code)]
pub struct SendMessageQuery {
    /// Enable step streaming (letta-code compatibility)
    #[serde(default)]
    pub stream_steps: bool,
    /// Enable token streaming (not yet implemented)
    #[serde(default)]
    pub stream_tokens: bool,
}

// =============================================================================
// SSE Message Types (Letta-compatible)
// =============================================================================

/// SSE message types for streaming responses
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "message_type")]
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

/// SSE event for stop reason
#[derive(Debug, Clone, Serialize)]
struct StopReasonEvent {
    message_type: &'static str,
    stop_reason: String,
}

/// List messages for an agent
///
/// GET /v1/agents/{agent_id}/messages
#[instrument(skip(state, query), fields(agent_id = %agent_id, limit = query.limit), level = "info")]
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
/// Supports multiple request formats for letta-code compatibility.
/// Supports SSE streaming when stream_steps=true query parameter is set.
#[instrument(skip(state, query, request), fields(agent_id = %agent_id, stream = query.stream_steps), level = "info")]
pub async fn send_message(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Query(query): Query<SendMessageQuery>,
    Json(request): Json<CreateMessageRequest>,
) -> Result<Response, ApiError> {
    // If streaming is requested, delegate to SSE handler
    if query.stream_steps {
        return send_message_streaming(state, agent_id, request).await;
    }

    // Otherwise return JSON response
    send_message_json(state, agent_id, request).await
}

/// Send a message with JSON response (non-streaming)
#[instrument(skip(state, request), fields(agent_id = %agent_id), level = "info")]
async fn send_message_json(
    state: AppState,
    agent_id: String,
    request: CreateMessageRequest,
) -> Result<Response, ApiError> {
    // Extract effective content from various request formats
    let (role, content) = request
        .effective_content()
        .ok_or_else(|| ApiError::bad_request("message content cannot be empty"))?;

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
    let stored_user_msg = state.add_message(&agent_id, user_message)?;

    // Get agent for memory blocks and system prompt
    let agent = state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    // Generate response via LLM (required)
    let llm = state.llm().ok_or_else(|| {
        ApiError::internal(
            "LLM not configured. Set ANTHROPIC_API_KEY or OPENAI_API_KEY environment variable.",
        )
    })?;

    let (response_content, prompt_tokens, completion_tokens, final_stop_reason, pause_info) = {
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
            content: content.clone(),
        });

        // Get available tools from registry, filtered by agent type capabilities
        let capabilities = agent.agent_type.capabilities();
        let all_tools = state.tool_registry().get_tool_definitions().await;
        let tools: Vec<_> = all_tools
            .into_iter()
            .filter(|t| capabilities.allowed_tools.contains(&t.name))
            .collect();

        tracing::debug!(
            agent_id = %agent_id,
            agent_type = ?agent.agent_type,
            tool_count = tools.len(),
            "Filtered tools by agent type capabilities"
        );

        // Call LLM with tools
        match llm
            .complete_with_tools(messages.clone(), tools.clone())
            .await
        {
            Ok(mut response) => {
                let mut total_prompt = response.prompt_tokens;
                let mut total_completion = response.completion_tokens;
                let mut final_content = response.content.clone();

                // Handle tool use loop (max iterations from agent type capabilities)
                let max_iterations = capabilities.max_iterations;
                let mut iterations = 0u32;
                let mut stop_reason = "end_turn".to_string();
                let mut pause_signal: Option<(u64, u64)> = None;

                while response.stop_reason == "tool_use" && iterations < max_iterations {
                    iterations += 1;
                    tracing::info!(
                        agent_id = %agent_id,
                        tool_count = response.tool_calls.len(),
                        iteration = iterations,
                        max_iterations = max_iterations,
                        "Executing tools"
                    );

                    // Execute each tool via registry
                    let mut tool_results = Vec::new();
                    let mut should_break = false;

                    for tool_call in &response.tool_calls {
                        let exec_result = state
                            .tool_registry()
                            .execute(&tool_call.name, &tool_call.input)
                            .await;

                        tracing::info!(
                            tool = %tool_call.name,
                            success = exec_result.success,
                            duration_ms = exec_result.duration_ms,
                            "Tool executed"
                        );

                        // Check for pause_heartbeats signal
                        // Parse from output format: "PAUSE_HEARTBEATS:minutes:pause_until_ms"
                        if let Some((minutes, pause_until_ms)) =
                            parse_pause_signal(&exec_result.output)
                        {
                            // Verify agent type supports heartbeats (defense-in-depth)
                            if !capabilities.supports_heartbeats {
                                tracing::warn!(
                                    agent_id = %agent_id,
                                    agent_type = ?agent.agent_type,
                                    "Agent called pause_heartbeats but type doesn't support heartbeats"
                                );
                            } else {
                                tracing::info!(
                                    agent_id = %agent_id,
                                    pause_minutes = minutes,
                                    pause_until_ms = pause_until_ms,
                                    "Agent requested heartbeat pause"
                                );

                                pause_signal = Some((minutes, pause_until_ms));
                                stop_reason = "pause_heartbeats".to_string();
                                should_break = true;
                            }
                        }

                        // Also check signal field
                        if let ToolSignal::PauseHeartbeats {
                            minutes,
                            pause_until_ms,
                        } = &exec_result.signal
                        {
                            // Verify agent type supports heartbeats (defense-in-depth)
                            if !capabilities.supports_heartbeats {
                                tracing::warn!(
                                    agent_id = %agent_id,
                                    agent_type = ?agent.agent_type,
                                    "Agent called pause_heartbeats but type doesn't support heartbeats (via signal)"
                                );
                            } else {
                                tracing::info!(
                                    agent_id = %agent_id,
                                    pause_minutes = minutes,
                                    pause_until_ms = pause_until_ms,
                                    "Agent requested heartbeat pause (via signal)"
                                );

                                pause_signal = Some((*minutes, *pause_until_ms));
                                stop_reason = "pause_heartbeats".to_string();
                                should_break = true;
                            }
                        }

                        tool_results.push((tool_call.id.clone(), exec_result.output));
                    }

                    // Break the loop if pause was requested
                    if should_break {
                        tracing::info!(
                            agent_id = %agent_id,
                            iteration = iterations,
                            "Breaking agent loop due to pause_heartbeats"
                        );
                        break;
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
                        .continue_with_tool_result(
                            messages.clone(),
                            tools.clone(),
                            assistant_blocks,
                            tool_results,
                        )
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
                    stop_reason = %stop_reason,
                    "LLM response received"
                );

                // If we hit max iterations without pause, set stop_reason
                if iterations >= AGENT_LOOP_ITERATIONS_MAX && stop_reason == "end_turn" {
                    stop_reason = "max_iterations".to_string();
                }

                (
                    final_content,
                    total_prompt,
                    total_completion,
                    stop_reason,
                    pause_signal,
                )
            }
            Err(e) => {
                tracing::error!(agent_id = %agent_id, error = %e, "LLM call failed");
                return Err(ApiError::internal(format!("LLM call failed: {}", e)));
            }
        }
    };

    // Log pause info if present
    if let Some((minutes, pause_until_ms)) = pause_info {
        tracing::info!(
            agent_id = %agent_id,
            pause_minutes = minutes,
            pause_until_ms = pause_until_ms,
            "Agent loop paused via pause_heartbeats"
        );
    }

    // Create assistant message
    let assistant_message = Message {
        id: Uuid::new_v4().to_string(),
        agent_id: agent_id.clone(),
        message_type: "assistant_message".to_string(),
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
        stop_reason = %final_stop_reason,
        "processed message"
    );

    Ok(Json(MessageResponse {
        messages: vec![stored_user_msg, stored_assistant_msg],
        usage: Some(UsageStats {
            prompt_tokens,
            completion_tokens,
            total_tokens: prompt_tokens + completion_tokens,
        }),
        stop_reason: final_stop_reason,
    })
    .into_response())
}

/// Send a message with SSE streaming response
#[instrument(skip(state, request), fields(agent_id = %agent_id), level = "info")]
async fn send_message_streaming(
    state: AppState,
    agent_id: String,
    request: CreateMessageRequest,
) -> Result<Response, ApiError> {
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
        let events = generate_sse_events(
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

    Ok(Sse::new(stream)
        .keep_alive(
            KeepAlive::new()
                .interval(Duration::from_secs(15))
                .text("keep-alive"),
        )
        .into_response())
}

/// Generate all SSE events for a streaming response
#[instrument(skip(state, agent, llm, content), fields(agent_id), level = "debug")]
async fn generate_sse_events(
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
    let mut final_stop_reason = "end_turn".to_string();

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

    // Get available tools from registry
    let tools = state.tool_registry().get_tool_definitions().await;

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
            let mut iterations = 0u32;

            // Handle tool use loop
            while response.stop_reason == "tool_use" && iterations < AGENT_LOOP_ITERATIONS_MAX {
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

                // Execute tools via registry
                let mut tool_results = Vec::new();
                let mut should_break = false;

                for tool_call in &response.tool_calls {
                    let exec_result = state
                        .tool_registry()
                        .execute(&tool_call.name, &tool_call.input)
                        .await;

                    // Check for pause_heartbeats signal
                    if let Some((minutes, pause_until_ms)) = parse_pause_signal(&exec_result.output)
                    {
                        tracing::info!(
                            agent_id = %agent_id,
                            pause_minutes = minutes,
                            pause_until_ms = pause_until_ms,
                            "Agent requested heartbeat pause (streaming)"
                        );
                        final_stop_reason = "pause_heartbeats".to_string();
                        should_break = true;
                    }

                    // Also check signal field
                    if let ToolSignal::PauseHeartbeats {
                        minutes,
                        pause_until_ms,
                    } = &exec_result.signal
                    {
                        tracing::info!(
                            agent_id = %agent_id,
                            pause_minutes = minutes,
                            pause_until_ms = pause_until_ms,
                            "Agent requested heartbeat pause via signal (streaming)"
                        );
                        final_stop_reason = "pause_heartbeats".to_string();
                        should_break = true;
                    }

                    // Send tool return event
                    let return_msg = SseMessage::ToolReturnMessage {
                        id: Uuid::new_v4().to_string(),
                        tool_return: exec_result.output.clone(),
                        status: if exec_result.success {
                            "success".to_string()
                        } else {
                            "error".to_string()
                        },
                    };
                    if let Ok(json) = serde_json::to_string(&return_msg) {
                        events.push(Ok(Event::default().data(json)));
                    }

                    tool_results.push((tool_call.id.clone(), exec_result.output));
                }

                // Break if pause was requested
                if should_break {
                    break;
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

            // Update stop_reason if we hit max iterations
            if iterations >= AGENT_LOOP_ITERATIONS_MAX && final_stop_reason == "end_turn" {
                final_stop_reason = "max_iterations".to_string();
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
        stop_reason: final_stop_reason,
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

    // Add base system prompt
    if let Some(sys) = system {
        parts.push(sys.clone());
    }

    // Add memory blocks
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

/// Rough token estimate (4 chars per token on average)
#[allow(dead_code)]
fn estimate_tokens(text: &str) -> u64 {
    (text.len() / 4).max(1) as u64
}

#[cfg(test)]
mod tests {
    use crate::api;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use axum::Router;
    use kelpie_server::models::AgentState;
    use kelpie_server::state::AppState;
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
        let messages: Vec<kelpie_server::models::Message> = serde_json::from_slice(&body).unwrap();

        // No messages sent yet
        assert_eq!(messages.len(), 0);
    }
}

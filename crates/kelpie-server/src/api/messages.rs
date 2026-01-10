//! Message API endpoints
//!
//! TigerStyle: Letta-compatible message operations.

use crate::api::ApiError;
use crate::models::{CreateMessageRequest, Message, MessageResponse, MessageRole, UsageStats};
use crate::state::AppState;
use axum::{
    extract::{Path, Query, State},
    Json,
};
use chrono::Utc;
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
/// This endpoint currently stores the message and returns a stub response.
/// Full LLM integration will be added when kelpie-agent is connected.
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

    // For now, create a stub assistant response
    // Real LLM integration will come via kelpie-agent
    let assistant_message = Message {
        id: Uuid::new_v4().to_string(),
        agent_id: agent_id.clone(),
        role: MessageRole::Assistant,
        content: generate_stub_response(&request.content),
        tool_call_id: None,
        tool_calls: None,
        created_at: Utc::now(),
    };

    // Store assistant message
    let stored_assistant_msg = state.add_message(&agent_id, assistant_message)?;

    // Calculate usage before moving messages
    let prompt_tokens = estimate_tokens(&stored_user_msg.content);
    let completion_tokens = estimate_tokens(&stored_assistant_msg.content);

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

/// Generate a stub response for testing
/// This will be replaced by actual LLM calls via kelpie-agent
fn generate_stub_response(input: &str) -> String {
    format!(
        "This is a stub response. The Kelpie server received your message: \"{}\". \
         LLM integration is pending via kelpie-agent.",
        if input.len() > 50 {
            format!("{}...", &input[..50])
        } else {
            input.to_string()
        }
    )
}

/// Rough token estimate (4 chars per token on average)
fn estimate_tokens(text: &str) -> u64 {
    (text.len() / 4).max(1) as u64
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
    async fn test_send_message() {
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

        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let response: super::MessageResponse = serde_json::from_slice(&body).unwrap();

        assert_eq!(response.messages.len(), 2);
        assert_eq!(response.messages[0].role, MessageRole::User);
        assert_eq!(response.messages[1].role, MessageRole::Assistant);
        assert!(response.usage.is_some());
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
    async fn test_list_messages() {
        let (app, agent_id) = test_app_with_agent().await;

        // Send a few messages first
        for i in 0..3 {
            let message = serde_json::json!({
                "role": "user",
                "content": format!("Message {}", i)
            });

            let _response = app
                .clone()
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
        }

        // List messages
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

        // 3 user messages + 3 assistant responses = 6 total
        assert_eq!(messages.len(), 6);
    }
}

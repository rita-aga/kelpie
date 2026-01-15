//! Agent API endpoints
//!
//! TigerStyle: Letta-compatible agent CRUD operations.

use crate::api::ApiError;
use axum::{
    extract::{Path, Query, State},
    routing::get,
    Json, Router,
};
use kelpie_server::models::{AgentState, CreateAgentRequest, ListResponse, UpdateAgentRequest};
use kelpie_server::state::AppState;
use serde::Deserialize;
use tracing::instrument;

/// Query parameters for listing agents
#[derive(Debug, Deserialize)]
pub struct ListAgentsQuery {
    /// Maximum number of agents to return
    #[serde(default = "default_limit")]
    pub limit: usize,
    /// Cursor for pagination
    pub cursor: Option<String>,
}

fn default_limit() -> usize {
    50
}

/// Maximum limit for list operations
const LIST_LIMIT_MAX: usize = 100;

/// Create agent routes
pub fn router() -> Router<AppState> {
    Router::new()
        .route("/", get(list_agents).post(create_agent))
        .route(
            "/:agent_id",
            get(get_agent).patch(update_agent).delete(delete_agent),
        )
        // Nested block routes
        .route("/:agent_id/blocks", get(super::blocks::list_blocks))
        .route(
            "/:agent_id/blocks/:block_id",
            get(super::blocks::get_block).patch(super::blocks::update_block),
        )
        // Core memory routes (letta-code compatibility - uses label instead of ID)
        .route(
            "/:agent_id/core-memory/blocks/:label",
            get(super::blocks::get_block_by_label).patch(super::blocks::update_block_by_label),
        )
        // Nested message routes
        .route(
            "/:agent_id/messages",
            get(super::messages::list_messages).post(super::messages::send_message),
        )
        // Streaming message route (letta-code SSE)
        .route(
            "/:agent_id/messages/stream",
            axum::routing::post(super::streaming::send_message_stream),
        )
        // Nested archival routes
        .route(
            "/:agent_id/archival",
            get(super::archival::search_archival).post(super::archival::add_archival),
        )
        .route(
            "/:agent_id/archival/:entry_id",
            get(super::archival::get_archival_entry).delete(super::archival::delete_archival_entry),
        )
}

/// Create a new agent
///
/// POST /v1/agents
#[instrument(skip(state, request), fields(agent_name = %request.name), level = "info")]
async fn create_agent(
    State(state): State<AppState>,
    Json(request): Json<CreateAgentRequest>,
) -> Result<Json<AgentState>, ApiError> {
    // Validate request
    if request.name.is_empty() {
        return Err(ApiError::bad_request("agent name cannot be empty"));
    }

    if request.name.len() > 256 {
        return Err(ApiError::bad_request(
            "agent name too long (max 256 characters)",
        ));
    }

    // Extract block_ids before consuming request
    let block_ids = request.block_ids.clone();

    // Create agent via dual-mode method
    let mut created = state.create_agent_async(request).await?;

    // Look up and attach standalone blocks by ID (letta-code compatibility)
    // Note: This is a temporary workaround until standalone blocks are integrated into the actor model
    for block_id in block_ids {
        if let Ok(Some(block)) = state.get_standalone_block(&block_id) {
            created.blocks.push(block);
        } else {
            tracing::warn!(block_id = %block_id, "standalone block not found, skipping");
        }
    }

    tracing::info!(agent_id = %created.id, name = %created.name, block_count = created.blocks.len(), "created agent");
    Ok(Json(created))
}

/// Get an agent by ID
///
/// GET /v1/agents/{agent_id}
#[instrument(skip(state), fields(agent_id = %agent_id), level = "info")]
async fn get_agent(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
) -> Result<Json<AgentState>, ApiError> {
    let agent = state
        .get_agent_async(&agent_id)
        .await?
        .ok_or_else(|| ApiError::not_found("Agent", &agent_id))?;

    Ok(Json(agent))
}

/// List all agents with pagination
///
/// GET /v1/agents
#[instrument(skip(state, query), fields(limit = query.limit, cursor = ?query.cursor), level = "info")]
async fn list_agents(
    State(state): State<AppState>,
    Query(query): Query<ListAgentsQuery>,
) -> Result<Json<ListResponse<AgentState>>, ApiError> {
    let limit = query.limit.min(LIST_LIMIT_MAX);
    let (items, cursor) = state
        .list_agents_async(limit, query.cursor.as_deref())
        .await?;
    let total = state.agent_count()?;

    Ok(Json(ListResponse {
        items,
        total,
        cursor,
    }))
}

/// Update an agent
///
/// PATCH /v1/agents/{agent_id}
#[instrument(skip(state, request), fields(agent_id = %agent_id), level = "info")]
async fn update_agent(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Json(request): Json<UpdateAgentRequest>,
) -> Result<Json<AgentState>, ApiError> {
    // Validate if name is being updated
    if let Some(ref name) = request.name {
        if name.is_empty() {
            return Err(ApiError::bad_request("agent name cannot be empty"));
        }
        if name.len() > 256 {
            return Err(ApiError::bad_request(
                "agent name too long (max 256 characters)",
            ));
        }
    }

    let update_value = serde_json::to_value(request)
        .map_err(|e| ApiError::bad_request(format!("Invalid update request: {}", e)))?;

    let updated = state.update_agent_async(&agent_id, update_value).await?;

    tracing::info!(agent_id = %updated.id, "updated agent");
    Ok(Json(updated))
}

/// Delete an agent
///
/// DELETE /v1/agents/{agent_id}
#[instrument(skip(state), fields(agent_id = %agent_id), level = "info")]
async fn delete_agent(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
) -> Result<(), ApiError> {
    state.delete_agent_async(&agent_id).await?;
    tracing::info!(agent_id = %agent_id, "deleted agent");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api;
    use async_trait::async_trait;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use kelpie_dst::{DeterministicRng, FaultInjector, SimStorage};
    use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig};
    use kelpie_server::actor::{AgentActor, AgentActorState, LlmClient, LlmMessage, LlmResponse};
    use kelpie_server::service;
    use std::sync::Arc;
    use tower::ServiceExt;

    /// Mock LLM client for testing that returns simple responses
    struct MockLlmClient;

    #[async_trait]
    impl LlmClient for MockLlmClient {
        async fn complete(&self, _messages: Vec<LlmMessage>) -> kelpie_core::Result<LlmResponse> {
            Ok(LlmResponse {
                content: "Test response".to_string(),
                tool_calls: vec![],
            })
        }
    }

    /// Create a test AppState with AgentService for API testing
    async fn test_app() -> Router {
        // Create a minimal AgentService setup for testing
        let llm: Arc<dyn LlmClient> = Arc::new(MockLlmClient);
        let actor = AgentActor::new(llm);
        let factory = Arc::new(CloneFactory::new(actor));

        // Use SimStorage for testing (in-memory KV store)
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(FaultInjector::new(rng.fork()));
        let storage = SimStorage::new(rng.fork(), faults);
        let kv = Arc::new(storage);

        let mut dispatcher = Dispatcher::<AgentActor, AgentActorState>::new(
            factory,
            kv,
            DispatcherConfig::default(),
        );
        let handle = dispatcher.handle();

        tokio::spawn(async move {
            dispatcher.run().await;
        });

        let service = service::AgentService::new(handle.clone());
        let state = AppState::with_agent_service(service, handle);

        api::router(state)
    }

    #[tokio::test]
    async fn test_create_agent() {
        let app = test_app().await;

        let body = serde_json::json!({
            "name": "test-agent",
            "memory_blocks": [{
                "label": "persona",
                "value": "I am a test agent"
            }]
        });

        let response = app
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

        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let agent: AgentState = serde_json::from_slice(&body).unwrap();
        assert_eq!(agent.name, "test-agent");
        assert!(!agent.id.is_empty());
    }

    #[tokio::test]
    async fn test_create_agent_empty_name() {
        let app = test_app().await;

        let body = serde_json::json!({
            "name": "",
        });

        let response = app
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

        assert_eq!(response.status(), StatusCode::BAD_REQUEST);
    }

    #[tokio::test]
    async fn test_get_agent_not_found() {
        let app = test_app().await;

        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri("/v1/agents/nonexistent")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn test_health_check() {
        let app = test_app().await;

        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri("/health")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let health: kelpie_server::models::HealthResponse = serde_json::from_slice(&body).unwrap();
        assert_eq!(health.status, "ok");
    }
}

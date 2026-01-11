//! Agent API endpoints
//!
//! TigerStyle: Letta-compatible agent CRUD operations.

use crate::api::ApiError;
use crate::models::{AgentState, CreateAgentRequest, ListResponse, UpdateAgentRequest};
use crate::state::AppState;
use axum::{
    extract::{Path, Query, State},
    routing::get,
    Json, Router,
};
use serde::Deserialize;

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

    let mut agent = AgentState::from_request(request);

    // Look up and attach standalone blocks by ID (letta-code compatibility)
    for block_id in block_ids {
        if let Ok(Some(block)) = state.get_standalone_block(&block_id) {
            agent.blocks.push(block);
        } else {
            tracing::warn!(block_id = %block_id, "standalone block not found, skipping");
        }
    }

    let created = state.create_agent(agent)?;

    tracing::info!(agent_id = %created.id, name = %created.name, block_count = created.blocks.len(), "created agent");
    Ok(Json(created))
}

/// Get an agent by ID
///
/// GET /v1/agents/{agent_id}
async fn get_agent(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
) -> Result<Json<AgentState>, ApiError> {
    let agent = state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("Agent", &agent_id))?;

    Ok(Json(agent))
}

/// List all agents with pagination
///
/// GET /v1/agents
async fn list_agents(
    State(state): State<AppState>,
    Query(query): Query<ListAgentsQuery>,
) -> Result<Json<ListResponse<AgentState>>, ApiError> {
    let limit = query.limit.min(LIST_LIMIT_MAX);
    let (items, cursor) = state.list_agents(limit, query.cursor.as_deref())?;
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

    let updated = state.update_agent(&agent_id, |agent| {
        agent.apply_update(request);
    })?;

    tracing::info!(agent_id = %updated.id, "updated agent");
    Ok(Json(updated))
}

/// Delete an agent
///
/// DELETE /v1/agents/{agent_id}
async fn delete_agent(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
) -> Result<(), ApiError> {
    state.delete_agent(&agent_id)?;
    tracing::info!(agent_id = %agent_id, "deleted agent");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    async fn test_app() -> Router {
        api::router(AppState::new())
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
        let health: crate::models::HealthResponse = serde_json::from_slice(&body).unwrap();
        assert_eq!(health.status, "ok");
    }
}

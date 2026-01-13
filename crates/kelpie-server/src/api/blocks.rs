//! Memory block API endpoints
//!
//! TigerStyle: Letta-compatible memory block operations.

use crate::api::ApiError;
use kelpie_server::models::{Block, UpdateBlockRequest};
use kelpie_server::state::AppState;
use axum::{
    extract::{Path, State},
    Json,
};
use tracing::instrument;

/// List all blocks for an agent
///
/// GET /v1/agents/{agent_id}/blocks
#[instrument(skip(state), fields(agent_id = %agent_id), level = "info")]
pub async fn list_blocks(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
) -> Result<Json<Vec<Block>>, ApiError> {
    let blocks = state.list_blocks(&agent_id)?;
    Ok(Json(blocks))
}

/// Get a specific block
///
/// GET /v1/agents/{agent_id}/blocks/{block_id}
#[instrument(skip(state), fields(agent_id = %agent_id, block_id = %block_id), level = "info")]
pub async fn get_block(
    State(state): State<AppState>,
    Path((agent_id, block_id)): Path<(String, String)>,
) -> Result<Json<Block>, ApiError> {
    let block = state
        .get_block(&agent_id, &block_id)?
        .ok_or_else(|| ApiError::not_found("Block", &block_id))?;

    Ok(Json(block))
}

/// Update a block
///
/// PATCH /v1/agents/{agent_id}/blocks/{block_id}
#[instrument(skip(state, request), fields(agent_id = %agent_id, block_id = %block_id), level = "info")]
pub async fn update_block(
    State(state): State<AppState>,
    Path((agent_id, block_id)): Path<(String, String)>,
    Json(request): Json<UpdateBlockRequest>,
) -> Result<Json<Block>, ApiError> {
    // Validate value size if provided
    if let Some(ref value) = request.value {
        if let Some(limit) = request.limit {
            if value.len() > limit {
                return Err(ApiError::bad_request(format!(
                    "value exceeds limit ({} > {})",
                    value.len(),
                    limit
                )));
            }
        }
    }

    let updated = state.update_block(&agent_id, &block_id, |block| {
        // Check limit before applying
        if let Some(ref value) = request.value {
            if let Some(limit) = block.limit {
                if value.len() > limit {
                    // Truncate if necessary (could also return error)
                    tracing::warn!(
                        block_id = %block.id,
                        value_len = value.len(),
                        limit,
                        "truncating block value to limit"
                    );
                }
            }
        }
        block.apply_update(request);
    })?;

    tracing::info!(agent_id = %agent_id, block_id = %updated.id, "updated block");
    Ok(Json(updated))
}

// =============================================================================
// Core Memory routes (letta-code compatibility)
// These use block labels instead of block IDs
// =============================================================================

/// Get a block by label
///
/// GET /v1/agents/{agent_id}/core-memory/blocks/{label}
#[instrument(skip(state), fields(agent_id = %agent_id, label = %label), level = "info")]
pub async fn get_block_by_label(
    State(state): State<AppState>,
    Path((agent_id, label)): Path<(String, String)>,
) -> Result<Json<Block>, ApiError> {
    let block = state
        .get_block_by_label(&agent_id, &label)?
        .ok_or_else(|| ApiError::not_found("Block", &label))?;

    Ok(Json(block))
}

/// Update a block by label
///
/// PATCH /v1/agents/{agent_id}/core-memory/blocks/{label}
#[instrument(skip(state, request), fields(agent_id = %agent_id, label = %label), level = "info")]
pub async fn update_block_by_label(
    State(state): State<AppState>,
    Path((agent_id, label)): Path<(String, String)>,
    Json(request): Json<UpdateBlockRequest>,
) -> Result<Json<Block>, ApiError> {
    // Validate value size if provided
    if let Some(ref value) = request.value {
        if let Some(limit) = request.limit {
            if value.len() > limit {
                return Err(ApiError::bad_request(format!(
                    "value exceeds limit ({} > {})",
                    value.len(),
                    limit
                )));
            }
        }
    }

    let updated = state.update_block_by_label(&agent_id, &label, |block| {
        block.apply_update(request);
    })?;

    tracing::info!(agent_id = %agent_id, label = %label, "updated block by label");
    Ok(Json(updated))
}

#[cfg(test)]
mod tests {
    use crate::api;
    use kelpie_server::models::AgentState;
    use kelpie_server::state::AppState;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use axum::Router;
    use tower::ServiceExt;

    async fn test_app_with_agent() -> (Router, String, String) {
        let state = AppState::new();

        // Create agent with a block
        let body = serde_json::json!({
            "name": "block-test-agent",
            "memory_blocks": [{
                "label": "persona",
                "value": "I am a test agent",
                "limit": 1000
            }]
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
        let block_id = agent.blocks[0].id.clone();

        (api::router(state), agent.id, block_id)
    }

    #[tokio::test]
    async fn test_list_blocks() {
        let (app, agent_id, _) = test_app_with_agent().await;

        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri(format!("/v1/agents/{}/blocks", agent_id))
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let blocks: Vec<kelpie_server::models::Block> = serde_json::from_slice(&body).unwrap();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].label, "persona");
    }

    #[tokio::test]
    async fn test_update_block() {
        let (app, agent_id, block_id) = test_app_with_agent().await;

        let update = serde_json::json!({
            "value": "Updated persona value"
        });

        let response = app
            .oneshot(
                Request::builder()
                    .method("PATCH")
                    .uri(format!("/v1/agents/{}/blocks/{}", agent_id, block_id))
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&update).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let block: kelpie_server::models::Block = serde_json::from_slice(&body).unwrap();
        assert_eq!(block.value, "Updated persona value");
    }
}

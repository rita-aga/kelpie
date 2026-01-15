//! Memory block API endpoints
//!
//! TigerStyle: Letta-compatible memory block operations.

use crate::api::ApiError;
use axum::{
    extract::{Path, State},
    Json,
};
use kelpie_server::models::{Block, UpdateBlockRequest};
use kelpie_server::state::AppState;
use tracing::instrument;

/// List all blocks for an agent
///
/// GET /v1/agents/{agent_id}/blocks
#[instrument(skip(state), fields(agent_id = %agent_id), level = "info")]
pub async fn list_blocks(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
) -> Result<Json<Vec<Block>>, ApiError> {
    // Phase 6: Get agent from actor system (or HashMap fallback)
    let agent = state
        .get_agent_async(&agent_id)
        .await?
        .ok_or_else(|| ApiError::not_found("Agent", &agent_id))?;

    Ok(Json(agent.blocks))
}

/// Get a specific block
///
/// GET /v1/agents/{agent_id}/blocks/{block_id}
#[instrument(skip(state), fields(agent_id = %agent_id, block_id = %block_id), level = "info")]
pub async fn get_block(
    State(state): State<AppState>,
    Path((agent_id, block_id)): Path<(String, String)>,
) -> Result<Json<Block>, ApiError> {
    // Phase 6: Get agent from actor system (or HashMap fallback)
    let agent = state
        .get_agent_async(&agent_id)
        .await?
        .ok_or_else(|| ApiError::not_found("Agent", &agent_id))?;

    // Find the block by ID
    let block = agent
        .blocks
        .iter()
        .find(|b| b.id == block_id)
        .cloned()
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
    // Phase 6: Get agent from actor system (or HashMap fallback)
    let agent = state
        .get_agent_async(&agent_id)
        .await?
        .ok_or_else(|| ApiError::not_found("Agent", &agent_id))?;

    // Find the block by ID to get its label
    let block = agent
        .blocks
        .iter()
        .find(|b| b.id == block_id)
        .ok_or_else(|| ApiError::not_found("Block", &block_id))?;

    let label = block.label.clone();

    // Validate value size if provided
    if let Some(ref value) = request.value {
        if let Some(limit) = request.limit.or(block.limit) {
            if value.len() > limit {
                return Err(ApiError::bad_request(format!(
                    "value exceeds limit ({} > {})",
                    value.len(),
                    limit
                )));
            }
        }
    }

    // Update block via AgentService
    if let Some(service) = state.agent_service() {
        // Use value from request, or keep current value
        let new_value = request.value.unwrap_or_else(|| block.value.clone());

        service
            .update_block_by_label(&agent_id, &label, new_value)
            .await
            .map_err(|e| ApiError::internal(format!("Failed to update block: {}", e)))?;

        // Get updated agent to return the updated block
        let updated_agent = state
            .get_agent_async(&agent_id)
            .await?
            .ok_or_else(|| ApiError::internal("Agent not found after update"))?;

        let updated_block = updated_agent
            .blocks
            .iter()
            .find(|b| b.id == block_id)
            .cloned()
            .ok_or_else(|| ApiError::internal("Block not found after update"))?;

        tracing::info!(agent_id = %agent_id, block_id = %block_id, "updated block");
        Ok(Json(updated_block))
    } else {
        // Fallback to HashMap-based update
        #[allow(deprecated)]
        let updated = state.update_block(&agent_id, &block_id, |block| {
            block.apply_update(request);
        })?;

        tracing::info!(agent_id = %agent_id, block_id = %updated.id, "updated block");
        Ok(Json(updated))
    }
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
    use async_trait::async_trait;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use axum::Router;
    use kelpie_dst::{DeterministicRng, FaultInjector, SimStorage};
    use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig};
    use kelpie_server::actor::{AgentActor, AgentActorState, LlmClient, LlmMessage, LlmResponse};
    use kelpie_server::models::AgentState;
    use kelpie_server::service;
    use kelpie_server::state::AppState;
    use std::sync::Arc;
    use tower::ServiceExt;

    /// Mock LLM client for testing
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

    /// Create a test AppState with AgentService
    async fn test_app() -> Router {
        let llm: Arc<dyn LlmClient> = Arc::new(MockLlmClient);
        let actor = AgentActor::new(llm);
        let factory = Arc::new(CloneFactory::new(actor));

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

    async fn test_app_with_agent() -> (Router, String, String) {
        // Create app with AgentService
        let llm: Arc<dyn LlmClient> = Arc::new(MockLlmClient);
        let actor = AgentActor::new(llm);
        let factory = Arc::new(CloneFactory::new(actor));

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

        // Return new router with same state
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

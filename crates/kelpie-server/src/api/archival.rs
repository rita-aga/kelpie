//! Archival memory API endpoints
//!
//! TigerStyle: RESTful archival memory management with semantic search.

use crate::api::ApiError;
use axum::{
    extract::{Path, Query, State},
    Json,
};
use kelpie_server::models::ArchivalEntry;
use kelpie_server::state::AppState;
use serde::{Deserialize, Serialize};
use tracing::instrument;

/// List archival entries response
#[derive(Debug, Serialize)]
pub struct ArchivalListResponse {
    pub items: Vec<ArchivalEntry>,
    pub count: usize,
    pub total: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub next_cursor: Option<String>,
}

/// Query parameters for archival search
#[derive(Debug, Deserialize)]
pub struct ArchivalSearchQuery {
    /// Search query text (for semantic search)
    #[serde(default)]
    pub q: Option<String>,
    /// Maximum number of results to return
    #[serde(default = "default_limit")]
    pub limit: usize,
    /// Cursor for pagination (reserved for future use)
    #[serde(default)]
    #[allow(dead_code)]
    pub cursor: Option<String>,
    /// Cursor for pagination (Letta SDK compatibility - alias for cursor)
    #[serde(default)]
    #[allow(dead_code)]
    pub after: Option<String>,
}

fn default_limit() -> usize {
    50
}

/// Request to add to archival memory
#[derive(Debug, Deserialize)]
pub struct AddArchivalRequest {
    pub content: String,
    #[serde(default)]
    pub metadata: Option<serde_json::Value>,
}

/// Search archival memory
#[instrument(skip(state, query), fields(agent_id = %agent_id, query = ?query.q, limit = query.limit), level = "info")]
pub async fn search_archival(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Query(query): Query<ArchivalSearchQuery>,
) -> Result<Json<ArchivalListResponse>, ApiError> {
    // Verify agent exists
    state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    // Search archival memory
    let entries = state.search_archival(&agent_id, query.q.as_deref(), query.limit)?;

    let count = entries.len();
    Ok(Json(ArchivalListResponse {
        items: entries,
        count,
        total: count, // For now, total equals count since we don't have full pagination
        next_cursor: None,
    }))
}

/// Add entry to archival memory
#[instrument(skip(state, request), fields(agent_id = %agent_id), level = "info")]
pub async fn add_archival(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Json(request): Json<AddArchivalRequest>,
) -> Result<Json<ArchivalEntry>, ApiError> {
    // Verify agent exists
    state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    // Validate content
    if request.content.is_empty() {
        return Err(ApiError::bad_request("Content cannot be empty"));
    }

    if request.content.len() > 100_000 {
        return Err(ApiError::bad_request("Content too long (max 100KB)"));
    }

    // Add to archival memory
    let entry = state.add_archival(&agent_id, request.content, request.metadata)?;

    tracing::info!(agent_id = %agent_id, entry_id = %entry.id, "Added archival entry");

    Ok(Json(entry))
}

/// Get a specific archival entry
#[instrument(skip(state), fields(agent_id = %agent_id, entry_id = %entry_id), level = "info")]
pub async fn get_archival_entry(
    State(state): State<AppState>,
    Path((agent_id, entry_id)): Path<(String, String)>,
) -> Result<Json<ArchivalEntry>, ApiError> {
    // Verify agent exists
    state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    let entry = state
        .get_archival_entry(&agent_id, &entry_id)?
        .ok_or_else(|| ApiError::not_found("archival_entry", &entry_id))?;

    Ok(Json(entry))
}

/// Delete an archival entry
#[instrument(skip(state), fields(agent_id = %agent_id, entry_id = %entry_id), level = "info")]
pub async fn delete_archival_entry(
    State(state): State<AppState>,
    Path((agent_id, entry_id)): Path<(String, String)>,
) -> Result<(), ApiError> {
    // Verify agent exists
    state
        .get_agent(&agent_id)?
        .ok_or_else(|| ApiError::not_found("agent", &agent_id))?;

    state.delete_archival_entry(&agent_id, &entry_id)?;

    tracing::info!(agent_id = %agent_id, entry_id = %entry_id, "Deleted archival entry");

    Ok(())
}

#[cfg(test)]
mod tests {

    use crate::api;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use axum::Router;
    use kelpie_server::state::AppState;
    use tower::ServiceExt;

    async fn test_app_with_agent() -> (Router, String) {
        let state = AppState::new();

        // Create agent
        let body = serde_json::json!({
            "name": "archival-test-agent",
        });

        let app = api::router(state.clone());

        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/v1/agents")
                    .header("Content-Type", "application/json")
                    .body(Body::from(serde_json::to_string(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        let body = axum::body::to_bytes(response.into_body(), 10000)
            .await
            .unwrap();
        let agent: serde_json::Value = serde_json::from_slice(&body).unwrap();
        let agent_id = agent["id"].as_str().unwrap().to_string();

        (api::router(state), agent_id)
    }

    #[tokio::test]
    async fn test_search_archival_empty() {
        let (app, agent_id) = test_app_with_agent().await;

        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri(format!("/v1/agents/{}/archival", agent_id))
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_add_archival() {
        let (app, agent_id) = test_app_with_agent().await;

        let body = serde_json::json!({
            "content": "This is a test archival entry",
        });

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri(format!("/v1/agents/{}/archival", agent_id))
                    .header("Content-Type", "application/json")
                    .body(Body::from(serde_json::to_string(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }
}

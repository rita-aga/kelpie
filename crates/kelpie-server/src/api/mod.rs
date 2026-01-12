//! REST API module
//!
//! TigerStyle: Letta-compatible REST API for agent management.

pub mod agents;
pub mod archival;
pub mod blocks;
pub mod messages;
pub mod standalone_blocks;
pub mod streaming;
pub mod tools;

use crate::models::{ErrorResponse, HealthResponse};
use crate::state::{AppState, StateError};
use axum::{
    extract::State,
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::get,
    Json, Router,
};
use serde::Serialize;
use tower_http::cors::{Any, CorsLayer};
use tower_http::trace::TraceLayer;

/// Create the API router with all routes
pub fn router(state: AppState) -> Router {
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any);

    Router::new()
        // Health check
        .route("/health", get(health_check))
        .route("/v1/health", get(health_check))
        // Metrics endpoint (Prometheus)
        .route("/metrics", get(metrics))
        // Capabilities
        .route("/v1/capabilities", get(capabilities))
        // Agent routes
        .nest("/v1/agents", agents::router())
        // Standalone blocks routes (letta-code compatibility)
        .nest("/v1/blocks", standalone_blocks::router())
        // Tool routes
        .nest("/v1/tools", tools::router())
        .layer(TraceLayer::new_for_http())
        .layer(cors)
        .with_state(state)
}

/// Server capabilities endpoint
async fn capabilities() -> Json<CapabilitiesResponse> {
    Json(CapabilitiesResponse {
        features: vec![
            "agents".to_string(),
            "memory_blocks".to_string(),
            "messages".to_string(),
            "tools".to_string(),
            "archival_memory".to_string(),
            "semantic_search".to_string(),
        ],
        api_version: "v1".to_string(),
        llm_models: vec![
            "anthropic/claude-sonnet-4".to_string(),
            "openai/gpt-4o".to_string(),
        ],
    })
}

/// Server capabilities response
#[derive(Debug, Serialize)]
struct CapabilitiesResponse {
    features: Vec<String>,
    api_version: String,
    llm_models: Vec<String>,
}

/// Health check endpoint
async fn health_check(State(state): State<AppState>) -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "ok".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        uptime_seconds: state.uptime_seconds(),
    })
}

/// Prometheus metrics endpoint
///
/// Returns metrics in Prometheus text format.
/// This is scraped by Prometheus servers for monitoring.
async fn metrics(State(state): State<AppState>) -> Response {
    // For Phase 1, return a simple response
    // In Phase 2, this will scrape from the actual Prometheus registry
    let agent_count = state.agent_count().unwrap_or(0);

    let metrics_text = format!(
        "# HELP kelpie_agents_active_count Current number of active agents\n\
         # TYPE kelpie_agents_active_count gauge\n\
         kelpie_agents_active_count {}\n\
         \n\
         # HELP kelpie_server_uptime_seconds Server uptime in seconds\n\
         # TYPE kelpie_server_uptime_seconds gauge\n\
         kelpie_server_uptime_seconds {}\n",
        agent_count,
        state.uptime_seconds()
    );

    (
        StatusCode::OK,
        [(
            axum::http::header::CONTENT_TYPE,
            "text/plain; version=0.0.4; charset=utf-8",
        )],
        metrics_text,
    )
        .into_response()
}

/// API error type that converts to HTTP responses
pub struct ApiError {
    status: StatusCode,
    body: ErrorResponse,
}

impl ApiError {
    pub fn not_found(resource: &str, id: &str) -> Self {
        Self {
            status: StatusCode::NOT_FOUND,
            body: ErrorResponse::not_found(resource, id),
        }
    }

    pub fn bad_request(message: impl Into<String>) -> Self {
        Self {
            status: StatusCode::BAD_REQUEST,
            body: ErrorResponse::bad_request(message),
        }
    }

    pub fn internal(message: impl Into<String>) -> Self {
        Self {
            status: StatusCode::INTERNAL_SERVER_ERROR,
            body: ErrorResponse::internal(message),
        }
    }

    pub fn conflict(message: impl Into<String>) -> Self {
        Self {
            status: StatusCode::CONFLICT,
            body: ErrorResponse::new("conflict", message),
        }
    }
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        (self.status, Json(self.body)).into_response()
    }
}

impl From<StateError> for ApiError {
    fn from(err: StateError) -> Self {
        match err {
            StateError::NotFound { resource, id } => ApiError::not_found(resource, &id),
            StateError::AlreadyExists { resource, id } => {
                ApiError::conflict(format!("{} with id '{}' already exists", resource, id))
            }
            StateError::LimitExceeded { resource, limit } => {
                ApiError::bad_request(format!("{} limit ({}) exceeded", resource, limit))
            }
            StateError::LockPoisoned => ApiError::internal("internal state error"),
        }
    }
}

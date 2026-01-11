//! Tools API endpoints
//!
//! TigerStyle: RESTful tool management with explicit validation.

use crate::api::ApiError;
use crate::state::{AppState, ToolInfo};
use axum::{
    extract::{Path, State},
    routing::{get, post},
    Json, Router,
};
use serde::{Deserialize, Serialize};

/// Tool definition for API responses
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolResponse {
    pub name: String,
    pub description: String,
    pub input_schema: serde_json::Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

impl From<ToolInfo> for ToolResponse {
    fn from(info: ToolInfo) -> Self {
        Self {
            name: info.name,
            description: info.description,
            input_schema: info.input_schema,
            source: info.source,
        }
    }
}

/// List of tools response
#[derive(Debug, Serialize)]
pub struct ToolListResponse {
    pub items: Vec<ToolResponse>,
    pub count: usize,
}

/// Request to register a tool
#[derive(Debug, Deserialize)]
pub struct RegisterToolRequest {
    pub name: String,
    pub description: String,
    pub input_schema: serde_json::Value,
    #[serde(default)]
    pub source: Option<String>,
}

/// Request to execute a tool
#[derive(Debug, Deserialize)]
pub struct ExecuteToolRequest {
    pub arguments: serde_json::Value,
}

/// Tool execution response
#[derive(Debug, Serialize)]
pub struct ExecuteToolResponse {
    pub success: bool,
    pub output: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Create the tools router
pub fn router() -> Router<AppState> {
    Router::new()
        .route("/", get(list_tools).post(register_tool))
        .route("/{name}", get(get_tool).delete(delete_tool))
        .route("/{name}/execute", post(execute_tool))
}

/// List all available tools
async fn list_tools(State(state): State<AppState>) -> Json<ToolListResponse> {
    let tools = state.list_tools();
    let items: Vec<ToolResponse> = tools.into_iter().map(ToolResponse::from).collect();
    let count = items.len();
    Json(ToolListResponse { items, count })
}

/// Register a new tool
async fn register_tool(
    State(state): State<AppState>,
    Json(request): Json<RegisterToolRequest>,
) -> Result<Json<ToolResponse>, ApiError> {
    // Validate tool name
    if request.name.is_empty() {
        return Err(ApiError::bad_request("Tool name cannot be empty"));
    }

    if request.name.len() > 64 {
        return Err(ApiError::bad_request(
            "Tool name too long (max 64 characters)",
        ));
    }

    // Register the tool
    state.register_tool(
        request.name.clone(),
        request.description.clone(),
        request.input_schema.clone(),
        request.source.clone(),
    )?;

    tracing::info!(name = %request.name, "Registered tool");

    Ok(Json(ToolResponse {
        name: request.name,
        description: request.description,
        input_schema: request.input_schema,
        source: request.source,
    }))
}

/// Get a specific tool
async fn get_tool(
    State(state): State<AppState>,
    Path(name): Path<String>,
) -> Result<Json<ToolResponse>, ApiError> {
    let tool = state
        .get_tool(&name)
        .ok_or_else(|| ApiError::not_found("tool", &name))?;

    Ok(Json(ToolResponse::from(tool)))
}

/// Delete a tool
async fn delete_tool(
    State(state): State<AppState>,
    Path(name): Path<String>,
) -> Result<(), ApiError> {
    state.delete_tool(&name)?;
    tracing::info!(name = %name, "Deleted tool");
    Ok(())
}

/// Execute a tool
async fn execute_tool(
    State(state): State<AppState>,
    Path(name): Path<String>,
    Json(request): Json<ExecuteToolRequest>,
) -> Result<Json<ExecuteToolResponse>, ApiError> {
    let result = state.execute_tool(&name, request.arguments).await;

    match result {
        Ok(output) => Ok(Json(ExecuteToolResponse {
            success: true,
            output,
            error: None,
        })),
        Err(e) => Ok(Json(ExecuteToolResponse {
            success: false,
            output: String::new(),
            error: Some(e.to_string()),
        })),
    }
}

#[cfg(test)]
mod tests {

    use crate::api;
    use crate::state::AppState;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use axum::Router;
    use tower::ServiceExt;

    async fn test_app() -> Router {
        let state = AppState::new();
        api::router(state)
    }

    #[tokio::test]
    async fn test_list_tools() {
        let app = test_app().await;

        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri("/v1/tools")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_register_tool() {
        let app = test_app().await;

        let body = serde_json::json!({
            "name": "test-tool",
            "description": "A test tool",
            "input_schema": {
                "type": "object",
                "properties": {
                    "input": {"type": "string"}
                }
            }
        });

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/v1/tools")
                    .header("Content-Type", "application/json")
                    .body(Body::from(serde_json::to_string(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }
}

//! Kelpie Server
//!
//! Standalone Kelpie server with Letta-compatible REST API.

mod api;
mod llm;
mod models;
mod state;

use axum::extract::Request;
use axum::ServiceExt;
use clap::Parser;
use state::AppState;
use std::net::SocketAddr;
use tower_http::normalize_path::NormalizePath;
use tracing_subscriber::EnvFilter;

/// Kelpie server CLI
#[derive(Parser, Debug)]
#[command(name = "kelpie-server")]
#[command(about = "Kelpie distributed virtual actor server with Letta-compatible API")]
#[command(version)]
struct Cli {
    /// Configuration file path
    #[arg(short, long, default_value = "kelpie.yaml")]
    config: String,

    /// HTTP API bind address
    #[arg(short, long, default_value = "0.0.0.0:8283")]
    bind: String,

    /// Enable verbose logging
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Initialize logging
    let filter = match cli.verbose {
        0 => "info,tower_http=debug",
        1 => "debug",
        _ => "trace",
    };

    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| filter.into()))
        .init();

    tracing::info!("Kelpie server v{}", env!("CARGO_PKG_VERSION"));
    tracing::info!("Config: {}", cli.config);

    // Parse bind address
    let addr: SocketAddr = cli
        .bind
        .parse()
        .map_err(|e| anyhow::anyhow!("Invalid bind address '{}': {}", cli.bind, e))?;

    // Create application state
    let state = AppState::new();

    // Create router
    let app = api::router(state);

    // Start server
    tracing::info!("Starting HTTP server on {}", addr);
    tracing::info!("API endpoints:");
    tracing::info!("  GET  /health                           - Health check");
    tracing::info!("  GET  /metrics                          - Prometheus metrics");
    tracing::info!("  GET  /v1/capabilities                  - Server capabilities");
    tracing::info!("  GET  /v1/agents                        - List agents");
    tracing::info!("  GET  /v1/agents/{{id}}                   - Get agent");
    tracing::info!("  PATCH /v1/agents/{{id}}                  - Update agent");
    tracing::info!("  DELETE /v1/agents/{{id}}                 - Delete agent");
    tracing::info!("  GET  /v1/agents/{{id}}/blocks            - List blocks");
    tracing::info!("  PATCH /v1/agents/{{id}}/blocks/{{bid}}     - Update block");
    tracing::info!("  GET  /v1/agents/{{id}}/messages          - List messages");
    tracing::info!("  POST /v1/agents/{{id}}/messages          - Send message");
    tracing::info!("  GET  /v1/agents/{{id}}/archival          - Search archival memory");
    tracing::info!("  POST /v1/agents/{{id}}/archival          - Add to archival memory");
    tracing::info!("  GET  /v1/tools                         - List tools");
    tracing::info!("  POST /v1/tools                         - Register tool");
    tracing::info!("  POST /v1/tools/{{name}}/execute          - Execute tool");

    let listener = tokio::net::TcpListener::bind(addr).await?;

    // Wrap with NormalizePath to handle trailing slashes (letta-code compatibility)
    let app = NormalizePath::trim_trailing_slash(app);
    axum::serve(listener, ServiceExt::<Request>::into_make_service(app)).await?;

    Ok(())
}

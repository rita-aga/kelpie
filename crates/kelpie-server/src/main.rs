//! Kelpie Server
//!
//! Standalone Kelpie server binary.

use clap::Parser;
use tracing_subscriber::EnvFilter;

/// Kelpie server CLI
#[derive(Parser, Debug)]
#[command(name = "kelpie-server")]
#[command(about = "Kelpie distributed virtual actor server")]
#[command(version)]
struct Cli {
    /// Configuration file path
    #[arg(short, long, default_value = "kelpie.yaml")]
    config: String,

    /// Bind address
    #[arg(short, long, default_value = "0.0.0.0:9000")]
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
        0 => "info",
        1 => "debug",
        _ => "trace",
    };

    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| filter.into()))
        .init();

    tracing::info!("Kelpie server starting...");
    tracing::info!("Config: {}", cli.config);
    tracing::info!("Bind: {}", cli.bind);

    // Server implementation will come in later phases
    tracing::warn!("Server not yet implemented - Phase 0 bootstrap only");

    Ok(())
}

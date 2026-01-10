//! Kelpie CLI
//!
//! Command-line tools for Kelpie.

use clap::{Parser, Subcommand};
use tracing_subscriber::EnvFilter;

/// Kelpie CLI
#[derive(Parser, Debug)]
#[command(name = "kelpie")]
#[command(about = "Kelpie distributed virtual actor system CLI")]
#[command(version)]
struct Cli {
    /// Enable verbose logging
    #[arg(short, long, action = clap::ArgAction::Count, global = true)]
    verbose: u8,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Show cluster status
    Status {
        /// Server address
        #[arg(short, long, default_value = "localhost:9000")]
        server: String,
    },

    /// List actors
    Actors {
        /// Server address
        #[arg(short, long, default_value = "localhost:9000")]
        server: String,

        /// Filter by namespace
        #[arg(short, long)]
        namespace: Option<String>,
    },

    /// Invoke an actor
    Invoke {
        /// Actor ID (namespace:id)
        actor: String,

        /// Operation name
        operation: String,

        /// Payload (JSON)
        #[arg(short, long, default_value = "{}")]
        payload: String,

        /// Server address
        #[arg(short, long, default_value = "localhost:9000")]
        server: String,
    },

    /// Run diagnostics
    Doctor,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Initialize logging
    let filter = match cli.verbose {
        0 => "warn",
        1 => "info",
        2 => "debug",
        _ => "trace",
    };

    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| filter.into()))
        .init();

    match cli.command {
        Commands::Status { server } => {
            println!("Checking status of server: {}", server);
            println!("(Not yet implemented - Phase 0 bootstrap only)");
        }
        Commands::Actors { server, namespace } => {
            println!("Listing actors on server: {}", server);
            if let Some(ns) = namespace {
                println!("  Filtering by namespace: {}", ns);
            }
            println!("(Not yet implemented - Phase 0 bootstrap only)");
        }
        Commands::Invoke {
            actor,
            operation,
            payload,
            server,
        } => {
            println!("Invoking actor {} on server {}", actor, server);
            println!("  Operation: {}", operation);
            println!("  Payload: {}", payload);
            println!("(Not yet implemented - Phase 0 bootstrap only)");
        }
        Commands::Doctor => {
            println!("Running diagnostics...");
            println!();
            println!("Kelpie CLI version: {}", env!("CARGO_PKG_VERSION"));
            println!("Rust version: {}", env!("CARGO_PKG_RUST_VERSION"));
            println!();
            println!("All checks passed!");
        }
    }

    Ok(())
}

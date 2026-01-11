//! Telemetry and observability infrastructure
//!
//! TigerStyle: Explicit telemetry configuration with bounded resource usage.
//!
//! This module provides OpenTelemetry integration for distributed tracing
//! and metrics export. Requires the `otel` feature to be enabled.

#[cfg(feature = "otel")]
use crate::error::Error;
use crate::error::Result;

/// Telemetry configuration
#[derive(Debug, Clone)]
pub struct TelemetryConfig {
    /// Service name for tracing
    pub service_name: String,
    /// OTLP endpoint (e.g., "http://localhost:4317")
    pub otlp_endpoint: Option<String>,
    /// Whether to output traces to stdout
    pub stdout_enabled: bool,
    /// Log level filter
    pub log_level: String,
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            service_name: "kelpie".to_string(),
            otlp_endpoint: None,
            stdout_enabled: true,
            log_level: "info".to_string(),
        }
    }
}

impl TelemetryConfig {
    /// Create a new configuration with the given service name
    pub fn new(service_name: impl Into<String>) -> Self {
        Self {
            service_name: service_name.into(),
            ..Default::default()
        }
    }

    /// Set the OTLP endpoint
    pub fn with_otlp_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.otlp_endpoint = Some(endpoint.into());
        self
    }

    /// Disable stdout tracing
    pub fn without_stdout(mut self) -> Self {
        self.stdout_enabled = false;
        self
    }

    /// Set the log level filter
    pub fn with_log_level(mut self, level: impl Into<String>) -> Self {
        self.log_level = level.into();
        self
    }

    /// Create from environment variables
    ///
    /// Reads:
    /// - `OTEL_SERVICE_NAME`: Service name (default: "kelpie")
    /// - `OTEL_EXPORTER_OTLP_ENDPOINT`: OTLP endpoint
    /// - `RUST_LOG`: Log level filter (default: "info")
    pub fn from_env() -> Self {
        let service_name =
            std::env::var("OTEL_SERVICE_NAME").unwrap_or_else(|_| "kelpie".to_string());

        let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT").ok();

        let log_level = std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string());

        Self {
            service_name,
            otlp_endpoint,
            stdout_enabled: true,
            log_level,
        }
    }
}

/// Initialize telemetry with OpenTelemetry support
///
/// This sets up:
/// - Tracing subscriber with env filter
/// - OTLP exporter (if endpoint configured)
/// - Stdout logging (if enabled)
///
/// # Example
///
/// ```rust,ignore
/// use kelpie_core::telemetry::{init_telemetry, TelemetryConfig};
///
/// let config = TelemetryConfig::new("my-service")
///     .with_otlp_endpoint("http://localhost:4317");
///
/// init_telemetry(config)?;
/// ```
#[cfg(feature = "otel")]
pub fn init_telemetry(config: TelemetryConfig) -> Result<TelemetryGuard> {
    use opentelemetry_otlp::WithExportConfig;
    use opentelemetry_sdk::runtime::Tokio;
    use opentelemetry_sdk::trace::Config;
    use tracing_subscriber::prelude::*;
    use tracing_subscriber::EnvFilter;

    let env_filter =
        EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new(&config.log_level));

    // Build layers
    let fmt_layer = if config.stdout_enabled {
        Some(tracing_subscriber::fmt::layer())
    } else {
        None
    };

    // Add OTLP layer if endpoint configured
    let has_otel = config.otlp_endpoint.is_some();

    if let Some(ref endpoint) = config.otlp_endpoint {
        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(endpoint);

        let trace_config = Config::default().with_resource(opentelemetry_sdk::Resource::new(vec![
            opentelemetry::KeyValue::new("service.name", config.service_name.clone()),
        ]));

        let tracer = opentelemetry_otlp::new_pipeline()
            .tracing()
            .with_exporter(exporter)
            .with_trace_config(trace_config)
            .install_batch(Tokio)
            .map_err(|e| Error::Internal {
                message: format!("failed to initialize OpenTelemetry: {}", e),
            })?;

        let otel_layer = tracing_opentelemetry::layer().with_tracer(tracer);

        tracing_subscriber::registry()
            .with(env_filter)
            .with(fmt_layer)
            .with(otel_layer)
            .try_init()
            .map_err(|e| Error::Internal {
                message: format!("failed to initialize tracing subscriber: {}", e),
            })?;
    } else {
        // No OTLP endpoint - just stdout
        tracing_subscriber::registry()
            .with(env_filter)
            .with(fmt_layer)
            .try_init()
            .map_err(|e| Error::Internal {
                message: format!("failed to initialize tracing subscriber: {}", e),
            })?;
    };

    tracing::info!(
        service = %config.service_name,
        otlp_endpoint = ?config.otlp_endpoint,
        "Telemetry initialized"
    );

    Ok(TelemetryGuard {
        _has_otel: has_otel,
    })
}

/// Guard that shuts down telemetry when dropped
#[cfg(feature = "otel")]
pub struct TelemetryGuard {
    _has_otel: bool,
}

#[cfg(feature = "otel")]
impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        // Shutdown the global tracer provider
        opentelemetry::global::shutdown_tracer_provider();
    }
}

/// Initialize telemetry without OpenTelemetry (fallback when feature not enabled)
#[cfg(not(feature = "otel"))]
pub fn init_telemetry(_config: TelemetryConfig) -> Result<TelemetryGuard> {
    // Without the otel feature, just return a no-op guard
    Ok(TelemetryGuard {})
}

/// No-op guard when otel feature is not enabled
#[cfg(not(feature = "otel"))]
pub struct TelemetryGuard {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_telemetry_config_default() {
        let config = TelemetryConfig::default();
        assert_eq!(config.service_name, "kelpie");
        assert!(config.otlp_endpoint.is_none());
        assert!(config.stdout_enabled);
    }

    #[test]
    fn test_telemetry_config_builder() {
        let config = TelemetryConfig::new("test-service")
            .with_otlp_endpoint("http://localhost:4317")
            .with_log_level("debug")
            .without_stdout();

        assert_eq!(config.service_name, "test-service");
        assert_eq!(
            config.otlp_endpoint,
            Some("http://localhost:4317".to_string())
        );
        assert_eq!(config.log_level, "debug");
        assert!(!config.stdout_enabled);
    }
}

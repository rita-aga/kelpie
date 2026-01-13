//! Metrics collection for Kelpie
//!
//! TigerStyle: Explicit metric names with units, type-safe recording.
//!
//! This module provides high-level functions for recording metrics using
//! OpenTelemetry. Metrics are exported via Prometheus when the `otel` feature is enabled.

#[cfg(feature = "otel")]
use crate::constants::*;
#[cfg(feature = "otel")]
use once_cell::sync::Lazy;
#[cfg(feature = "otel")]
use opentelemetry::metrics::{Counter, Histogram};
#[cfg(feature = "otel")]
use opentelemetry::{global, KeyValue};

// Cached instruments (created once, reused for all recordings)
#[cfg(feature = "otel")]
static AGENTS_ACTIVATED_COUNTER: Lazy<Counter<u64>> = Lazy::new(|| {
    global::meter("kelpie")
        .u64_counter(METRIC_NAME_AGENTS_ACTIVATED_TOTAL)
        .with_description("Total number of agent activations")
        .init()
});

#[cfg(feature = "otel")]
static AGENTS_DEACTIVATED_COUNTER: Lazy<Counter<u64>> = Lazy::new(|| {
    global::meter("kelpie")
        .u64_counter(METRIC_NAME_AGENTS_DEACTIVATED_TOTAL)
        .with_description("Total number of agent deactivations")
        .init()
});

#[cfg(feature = "otel")]
static INVOCATIONS_COUNTER: Lazy<Counter<u64>> = Lazy::new(|| {
    global::meter("kelpie")
        .u64_counter(METRIC_NAME_INVOCATIONS_TOTAL)
        .with_description("Total number of invocations")
        .init()
});

#[cfg(feature = "otel")]
static INVOCATION_DURATION_HISTOGRAM: Lazy<Histogram<f64>> = Lazy::new(|| {
    global::meter("kelpie")
        .f64_histogram(METRIC_NAME_INVOCATION_DURATION_SECONDS)
        .with_description("Invocation duration in seconds")
        .init()
});

#[cfg(feature = "otel")]
static STORAGE_OPERATIONS_COUNTER: Lazy<Counter<u64>> = Lazy::new(|| {
    global::meter("kelpie")
        .u64_counter(METRIC_NAME_STORAGE_OPERATIONS_TOTAL)
        .with_description("Total storage operations")
        .init()
});

#[cfg(feature = "otel")]
static STORAGE_DURATION_HISTOGRAM: Lazy<Histogram<f64>> = Lazy::new(|| {
    global::meter("kelpie")
        .f64_histogram(METRIC_NAME_STORAGE_DURATION_SECONDS)
        .with_description("Storage operation duration in seconds")
        .init()
});

/// Record agent activation
///
/// Increments the activated counter.
#[cfg(feature = "otel")]
pub fn record_agent_activated() {
    AGENTS_ACTIVATED_COUNTER.add(1, &[]);
}

/// Record agent deactivation
///
/// Increments the deactivated counter.
#[cfg(feature = "otel")]
pub fn record_agent_deactivated() {
    AGENTS_DEACTIVATED_COUNTER.add(1, &[]);
}

/// Record an invocation
///
/// # Arguments
/// * `operation` - The operation name (e.g., "execute", "get_state")
/// * `status` - Status: "success" or "error"
/// * `duration_seconds` - Duration in seconds
#[cfg(feature = "otel")]
pub fn record_invocation(operation: &str, status: &str, duration_seconds: f64) {
    INVOCATIONS_COUNTER.add(
        1,
        &[
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("status", status.to_string()),
        ],
    );

    INVOCATION_DURATION_HISTOGRAM.record(
        duration_seconds,
        &[KeyValue::new("operation", operation.to_string())],
    );
}

/// Record storage operation
///
/// # Arguments
/// * `operation` - Operation: "get", "set", "delete", "list"
/// * `status` - Status: "success" or "error"
/// * `duration_seconds` - Duration in seconds
#[cfg(feature = "otel")]
pub fn record_storage_operation(operation: &str, status: &str, duration_seconds: f64) {
    STORAGE_OPERATIONS_COUNTER.add(
        1,
        &[
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("status", status.to_string()),
        ],
    );

    STORAGE_DURATION_HISTOGRAM.record(
        duration_seconds,
        &[KeyValue::new("operation", operation.to_string())],
    );
}

// No-op implementations when otel feature is disabled
#[cfg(not(feature = "otel"))]
pub fn record_agent_activated() {}

#[cfg(not(feature = "otel"))]
pub fn record_agent_deactivated() {}

#[cfg(not(feature = "otel"))]
pub fn record_invocation(_operation: &str, _status: &str, _duration_seconds: f64) {}

#[cfg(not(feature = "otel"))]
pub fn record_storage_operation(_operation: &str, _status: &str, _duration_seconds: f64) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metric_functions_dont_panic() {
        // These should not panic even without the otel feature
        record_agent_activated();
        record_agent_deactivated();
        record_invocation("test", "success", 0.1);
        record_storage_operation("get", "success", 0.05);
    }
}

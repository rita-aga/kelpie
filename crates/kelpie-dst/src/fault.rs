//! Fault injection for deterministic testing
//!
//! TigerStyle: Explicit fault types, probabilistic injection.

use crate::rng::DeterministicRng;
use std::sync::atomic::{AtomicU64, Ordering};

/// Types of faults that can be injected
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FaultType {
    // Storage faults
    /// Storage write operation fails
    StorageWriteFail,
    /// Storage read operation fails
    StorageReadFail,
    /// Storage data is corrupted
    StorageCorruption,
    /// Storage operations are slow
    StorageLatency { min_ms: u64, max_ms: u64 },
    /// Disk is full
    DiskFull,

    // Crash faults
    /// Crash before completing a write
    CrashBeforeWrite,
    /// Crash after completing a write
    CrashAfterWrite,
    /// Crash during a transaction
    CrashDuringTransaction,

    // Network faults
    /// Network partition (node unreachable)
    NetworkPartition,
    /// Network messages are delayed
    NetworkDelay { min_ms: u64, max_ms: u64 },
    /// Network packets are lost
    NetworkPacketLoss,
    /// Network messages arrive out of order
    NetworkMessageReorder,

    // Time faults
    /// Clock skew between nodes
    ClockSkew { delta_ms: i64 },
    /// Clock jumps forward or backward
    ClockJump { delta_ms: i64 },

    // Resource faults
    /// Out of memory
    OutOfMemory,
    /// CPU starvation
    CPUStarvation,

    // MCP (Model Context Protocol) faults
    /// MCP server process crashes
    McpServerCrash,
    /// MCP server takes too long to start
    McpServerSlowStart { delay_ms: u64 },
    /// MCP tool call times out
    McpToolTimeout,
    /// MCP tool execution fails with error
    McpToolFail,
}

impl FaultType {
    /// Get a human-readable name for this fault type
    pub fn name(&self) -> &'static str {
        match self {
            FaultType::StorageWriteFail => "storage_write_fail",
            FaultType::StorageReadFail => "storage_read_fail",
            FaultType::StorageCorruption => "storage_corruption",
            FaultType::StorageLatency { .. } => "storage_latency",
            FaultType::DiskFull => "disk_full",
            FaultType::CrashBeforeWrite => "crash_before_write",
            FaultType::CrashAfterWrite => "crash_after_write",
            FaultType::CrashDuringTransaction => "crash_during_transaction",
            FaultType::NetworkPartition => "network_partition",
            FaultType::NetworkDelay { .. } => "network_delay",
            FaultType::NetworkPacketLoss => "network_packet_loss",
            FaultType::NetworkMessageReorder => "network_message_reorder",
            FaultType::ClockSkew { .. } => "clock_skew",
            FaultType::ClockJump { .. } => "clock_jump",
            FaultType::OutOfMemory => "out_of_memory",
            FaultType::CPUStarvation => "cpu_starvation",
            FaultType::McpServerCrash => "mcp_server_crash",
            FaultType::McpServerSlowStart { .. } => "mcp_server_slow_start",
            FaultType::McpToolTimeout => "mcp_tool_timeout",
            FaultType::McpToolFail => "mcp_tool_fail",
        }
    }
}

/// Configuration for a fault injection rule
#[derive(Debug, Clone)]
pub struct FaultConfig {
    /// The type of fault to inject
    pub fault_type: FaultType,
    /// Probability of injection (0.0 - 1.0)
    pub probability: f64,
    /// Optional filter for operation names
    pub operation_filter: Option<String>,
    /// Only trigger after this many operations
    pub after_operations: u64,
    /// Maximum number of times to trigger
    pub max_triggers: Option<u64>,
    /// Whether this fault is enabled
    pub enabled: bool,
}

impl FaultConfig {
    /// Create a new fault configuration
    pub fn new(fault_type: FaultType, probability: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be in [0, 1]"
        );

        Self {
            fault_type,
            probability,
            operation_filter: None,
            after_operations: 0,
            max_triggers: None,
            enabled: true,
        }
    }

    /// Set an operation filter
    pub fn with_filter(mut self, filter: impl Into<String>) -> Self {
        self.operation_filter = Some(filter.into());
        self
    }

    /// Set the number of operations to wait before triggering
    pub fn after(mut self, operations: u64) -> Self {
        self.after_operations = operations;
        self
    }

    /// Set the maximum number of triggers
    pub fn max_triggers(mut self, max: u64) -> Self {
        self.max_triggers = Some(max);
        self
    }

    /// Disable this fault
    pub fn disabled(mut self) -> Self {
        self.enabled = false;
        self
    }
}

/// Fault injector for deterministic testing
#[derive(Debug)]
pub struct FaultInjector {
    /// Registered fault configurations
    faults: Vec<FaultState>,
    /// RNG for probabilistic injection
    rng: DeterministicRng,
    /// Total operations processed
    operation_count: AtomicU64,
}

/// State for a registered fault
#[derive(Debug)]
struct FaultState {
    config: FaultConfig,
    trigger_count: AtomicU64,
}

impl FaultInjector {
    /// Create a new fault injector with the given RNG
    pub fn new(rng: DeterministicRng) -> Self {
        Self {
            faults: Vec::new(),
            rng,
            operation_count: AtomicU64::new(0),
        }
    }

    /// Register a fault configuration
    pub fn register(&mut self, config: FaultConfig) {
        self.faults.push(FaultState {
            config,
            trigger_count: AtomicU64::new(0),
        });
    }

    /// Check if a fault should be injected for the given operation
    ///
    /// Returns the fault type if injection should occur, None otherwise.
    pub fn should_inject(&self, operation: &str) -> Option<FaultType> {
        let op_count = self.operation_count.fetch_add(1, Ordering::SeqCst);

        for fault_state in &self.faults {
            let config = &fault_state.config;

            // Skip disabled faults
            if !config.enabled {
                continue;
            }

            // Check operation filter
            if let Some(filter) = &config.operation_filter {
                if !operation.contains(filter) {
                    continue;
                }
            }

            // Check operation count threshold
            if op_count < config.after_operations {
                continue;
            }

            // Check max triggers
            let trigger_count = fault_state.trigger_count.load(Ordering::SeqCst);
            if let Some(max) = config.max_triggers {
                if trigger_count >= max {
                    continue;
                }
            }

            // Probabilistic check
            if self.rng.next_bool(config.probability) {
                fault_state.trigger_count.fetch_add(1, Ordering::SeqCst);

                tracing::debug!(
                    fault = config.fault_type.name(),
                    operation = operation,
                    trigger_count = trigger_count + 1,
                    "Injecting fault"
                );

                return Some(config.fault_type.clone());
            }
        }

        None
    }

    /// Get the total number of operations processed
    pub fn operation_count(&self) -> u64 {
        self.operation_count.load(Ordering::SeqCst)
    }

    /// Get statistics for all registered faults
    pub fn stats(&self) -> Vec<FaultStats> {
        self.faults
            .iter()
            .map(|state| FaultStats {
                fault_type: state.config.fault_type.name().to_string(),
                probability: state.config.probability,
                trigger_count: state.trigger_count.load(Ordering::SeqCst),
                enabled: state.config.enabled,
            })
            .collect()
    }

    /// Reset all trigger counts
    pub fn reset(&self) {
        self.operation_count.store(0, Ordering::SeqCst);
        for fault_state in &self.faults {
            fault_state.trigger_count.store(0, Ordering::SeqCst);
        }
    }
}

/// Statistics for a fault configuration
#[derive(Debug, Clone)]
pub struct FaultStats {
    pub fault_type: String,
    pub probability: f64,
    pub trigger_count: u64,
    pub enabled: bool,
}

/// Builder for creating a FaultInjector with multiple faults
pub struct FaultInjectorBuilder {
    rng: DeterministicRng,
    faults: Vec<FaultConfig>,
}

impl FaultInjectorBuilder {
    /// Create a new builder
    pub fn new(rng: DeterministicRng) -> Self {
        Self {
            rng,
            faults: Vec::new(),
        }
    }

    /// Add a fault configuration
    pub fn with_fault(mut self, config: FaultConfig) -> Self {
        self.faults.push(config);
        self
    }

    /// Add storage faults with default probabilities
    pub fn with_storage_faults(self, probability: f64) -> Self {
        self.with_fault(FaultConfig::new(FaultType::StorageWriteFail, probability))
            .with_fault(FaultConfig::new(FaultType::StorageReadFail, probability))
    }

    /// Add network faults with default probabilities
    pub fn with_network_faults(self, probability: f64) -> Self {
        self.with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, probability))
            .with_fault(FaultConfig::new(
                FaultType::NetworkDelay {
                    min_ms: 10,
                    max_ms: 100,
                },
                probability,
            ))
    }

    /// Add crash faults with default probabilities
    pub fn with_crash_faults(self, probability: f64) -> Self {
        self.with_fault(FaultConfig::new(FaultType::CrashAfterWrite, probability))
            .with_fault(FaultConfig::new(
                FaultType::CrashDuringTransaction,
                probability,
            ))
    }

    /// Add MCP (Model Context Protocol) faults with default probabilities
    pub fn with_mcp_faults(self, probability: f64) -> Self {
        self.with_fault(FaultConfig::new(FaultType::McpServerCrash, probability))
            .with_fault(FaultConfig::new(FaultType::McpToolFail, probability))
            .with_fault(FaultConfig::new(
                FaultType::McpToolTimeout,
                probability / 2.0,
            ))
    }

    /// Build the fault injector
    pub fn build(self) -> FaultInjector {
        let mut injector = FaultInjector::new(self.rng);
        for config in self.faults {
            injector.register(config);
        }
        injector
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fault_injection_probability() {
        let rng = DeterministicRng::new(42);
        let mut injector = FaultInjector::new(rng);

        // 100% probability should always inject
        injector.register(FaultConfig::new(FaultType::StorageWriteFail, 1.0));

        for _ in 0..10 {
            assert!(injector.should_inject("write").is_some());
        }
    }

    #[test]
    fn test_fault_injection_zero_probability() {
        let rng = DeterministicRng::new(42);
        let mut injector = FaultInjector::new(rng);

        // 0% probability should never inject
        injector.register(FaultConfig::new(FaultType::StorageWriteFail, 0.0));

        for _ in 0..100 {
            assert!(injector.should_inject("write").is_none());
        }
    }

    #[test]
    fn test_fault_injection_filter() {
        let rng = DeterministicRng::new(42);
        let mut injector = FaultInjector::new(rng);

        // Filter for "write" operations only
        injector.register(FaultConfig::new(FaultType::StorageWriteFail, 1.0).with_filter("write"));

        // Should inject for write
        assert!(injector.should_inject("storage_write").is_some());

        // Should not inject for read
        assert!(injector.should_inject("storage_read").is_none());
    }

    #[test]
    fn test_fault_injection_max_triggers() {
        let rng = DeterministicRng::new(42);
        let mut injector = FaultInjector::new(rng);

        injector.register(FaultConfig::new(FaultType::StorageWriteFail, 1.0).max_triggers(2));

        // First two should trigger
        assert!(injector.should_inject("write").is_some());
        assert!(injector.should_inject("write").is_some());

        // Third should not
        assert!(injector.should_inject("write").is_none());
    }

    #[test]
    fn test_fault_injector_builder() {
        let rng = DeterministicRng::new(42);
        let injector = FaultInjectorBuilder::new(rng)
            .with_storage_faults(0.1)
            .with_network_faults(0.05)
            .build();

        let stats = injector.stats();
        assert_eq!(stats.len(), 4); // 2 storage + 2 network
    }

    #[test]
    fn test_fault_type_names() {
        assert_eq!(FaultType::StorageWriteFail.name(), "storage_write_fail");
        assert_eq!(FaultType::NetworkPartition.name(), "network_partition");
        assert_eq!(FaultType::ClockSkew { delta_ms: 100 }.name(), "clock_skew");
    }
}

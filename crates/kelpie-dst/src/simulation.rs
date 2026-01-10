//! Simulation harness for deterministic testing
//!
//! TigerStyle: Reproducible test execution with explicit configuration.

use crate::clock::SimClock;
use crate::fault::{FaultConfig, FaultInjector, FaultInjectorBuilder};
use crate::network::SimNetwork;
use crate::rng::DeterministicRng;
use crate::storage::SimStorage;
use kelpie_core::{DST_STEPS_COUNT_MAX, DST_TIME_MS_MAX};
use std::future::Future;
use std::sync::Arc;

/// Configuration for a simulation
#[derive(Debug, Clone)]
pub struct SimConfig {
    /// Random seed for reproducibility
    pub seed: u64,
    /// Maximum simulation steps
    pub max_steps: u64,
    /// Maximum simulated time in milliseconds
    pub max_time_ms: u64,
    /// Storage size limit (None = unlimited)
    pub storage_limit_bytes: Option<usize>,
    /// Network base latency in milliseconds
    pub network_latency_ms: u64,
    /// Network latency jitter in milliseconds
    pub network_jitter_ms: u64,
}

impl SimConfig {
    /// Create a new simulation config with the given seed
    pub fn new(seed: u64) -> Self {
        Self {
            seed,
            max_steps: DST_STEPS_COUNT_MAX,
            max_time_ms: DST_TIME_MS_MAX,
            storage_limit_bytes: None,
            network_latency_ms: 1,
            network_jitter_ms: 5,
        }
    }

    /// Create config from DST_SEED environment variable or random
    pub fn from_env_or_random() -> Self {
        let seed = std::env::var("DST_SEED")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(rand::random);

        tracing::info!(seed = seed, "DST seed (set DST_SEED={} to replay)", seed);

        Self::new(seed)
    }

    /// Set maximum simulation steps
    pub fn with_max_steps(mut self, steps: u64) -> Self {
        self.max_steps = steps;
        self
    }

    /// Set maximum simulated time
    pub fn with_max_time_ms(mut self, ms: u64) -> Self {
        self.max_time_ms = ms;
        self
    }

    /// Set storage size limit
    pub fn with_storage_limit(mut self, bytes: usize) -> Self {
        self.storage_limit_bytes = Some(bytes);
        self
    }

    /// Set network latency
    pub fn with_network_latency(mut self, base_ms: u64, jitter_ms: u64) -> Self {
        self.network_latency_ms = base_ms;
        self.network_jitter_ms = jitter_ms;
        self
    }
}

impl Default for SimConfig {
    fn default() -> Self {
        Self::new(0)
    }
}

/// Environment provided to simulation tests
pub struct SimEnvironment {
    /// Deterministic clock
    pub clock: SimClock,
    /// Deterministic RNG
    pub rng: DeterministicRng,
    /// Simulated storage
    pub storage: SimStorage,
    /// Simulated network
    pub network: SimNetwork,
    /// Fault injector
    pub faults: Arc<FaultInjector>,
}

impl SimEnvironment {
    /// Fork the RNG to create an independent stream
    pub fn fork_rng(&self) -> DeterministicRng {
        self.rng.fork()
    }

    /// Advance simulation time
    pub fn advance_time_ms(&self, ms: u64) {
        self.clock.advance_ms(ms);
    }

    /// Get current simulation time in milliseconds
    pub fn now_ms(&self) -> u64 {
        self.clock.now_ms()
    }
}

/// Main simulation harness
pub struct Simulation {
    config: SimConfig,
    fault_configs: Vec<FaultConfig>,
}

impl Simulation {
    /// Create a new simulation with the given config
    pub fn new(config: SimConfig) -> Self {
        Self {
            config,
            fault_configs: Vec::new(),
        }
    }

    /// Add a fault configuration
    pub fn with_fault(mut self, fault: FaultConfig) -> Self {
        self.fault_configs.push(fault);
        self
    }

    /// Add multiple fault configurations
    pub fn with_faults(mut self, faults: Vec<FaultConfig>) -> Self {
        self.fault_configs.extend(faults);
        self
    }

    /// Run the simulation with the given test function
    pub fn run<F, Fut, T>(self, test: F) -> Result<T, SimulationError>
    where
        F: FnOnce(SimEnvironment) -> Fut,
        Fut: Future<Output = Result<T, kelpie_core::Error>>,
    {
        // Build the simulation environment
        let rng = DeterministicRng::new(self.config.seed);
        let clock = SimClock::default();

        // Build fault injector
        let mut fault_builder = FaultInjectorBuilder::new(rng.fork());
        for fault in self.fault_configs {
            fault_builder = fault_builder.with_fault(fault);
        }
        let faults = Arc::new(fault_builder.build());

        // Build storage
        let mut storage = SimStorage::new(rng.fork(), faults.clone());
        if let Some(limit) = self.config.storage_limit_bytes {
            storage = storage.with_size_limit(limit);
        }

        // Build network
        let network = SimNetwork::new(clock.clone(), rng.fork(), faults.clone()).with_latency(
            self.config.network_latency_ms,
            self.config.network_jitter_ms,
        );

        let env = SimEnvironment {
            clock,
            rng,
            storage,
            network,
            faults,
        };

        // Run the test
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|e| SimulationError::RuntimeError(e.to_string()))?;

        runtime.block_on(async { test(env).await.map_err(SimulationError::TestFailed) })
    }

    /// Run the simulation asynchronously (when already in an async context)
    pub async fn run_async<F, Fut, T>(self, test: F) -> Result<T, SimulationError>
    where
        F: FnOnce(SimEnvironment) -> Fut,
        Fut: Future<Output = Result<T, kelpie_core::Error>>,
    {
        let rng = DeterministicRng::new(self.config.seed);
        let clock = SimClock::default();

        let mut fault_builder = FaultInjectorBuilder::new(rng.fork());
        for fault in self.fault_configs {
            fault_builder = fault_builder.with_fault(fault);
        }
        let faults = Arc::new(fault_builder.build());

        let mut storage = SimStorage::new(rng.fork(), faults.clone());
        if let Some(limit) = self.config.storage_limit_bytes {
            storage = storage.with_size_limit(limit);
        }

        let network = SimNetwork::new(clock.clone(), rng.fork(), faults.clone()).with_latency(
            self.config.network_latency_ms,
            self.config.network_jitter_ms,
        );

        let env = SimEnvironment {
            clock,
            rng,
            storage,
            network,
            faults,
        };

        test(env).await.map_err(SimulationError::TestFailed)
    }
}

/// Errors that can occur during simulation
#[derive(Debug)]
pub enum SimulationError {
    /// Test function returned an error
    TestFailed(kelpie_core::Error),
    /// Simulation exceeded maximum steps
    MaxStepsExceeded,
    /// Simulation exceeded maximum time
    MaxTimeExceeded,
    /// Runtime initialization failed
    RuntimeError(String),
}

impl std::fmt::Display for SimulationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SimulationError::TestFailed(e) => write!(f, "Test failed: {}", e),
            SimulationError::MaxStepsExceeded => write!(f, "Maximum simulation steps exceeded"),
            SimulationError::MaxTimeExceeded => write!(f, "Maximum simulation time exceeded"),
            SimulationError::RuntimeError(e) => write!(f, "Runtime error: {}", e),
        }
    }
}

impl std::error::Error for SimulationError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::FaultType;
    use bytes::Bytes;

    #[test]
    fn test_simulation_basic() {
        let config = SimConfig::new(12345);
        let result = Simulation::new(config).run(|env| async move {
            // Write to storage
            env.storage.write(b"key", b"value").await?;

            // Read back
            let value = env.storage.read(b"key").await?;
            assert_eq!(value, Some(Bytes::from("value")));

            Ok(())
        });

        assert!(result.is_ok());
    }

    #[test]
    fn test_simulation_with_faults() {
        let config = SimConfig::new(12345);
        let result = Simulation::new(config)
            .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 1.0))
            .run(|env| async move {
                // This should fail due to fault injection
                env.storage.write(b"key", b"value").await?;
                Ok(())
            });

        assert!(matches!(result, Err(SimulationError::TestFailed(_))));
    }

    #[test]
    fn test_simulation_determinism() {
        // Run the same simulation twice with the same seed
        let seed = 42;

        let run_simulation = || {
            let config = SimConfig::new(seed);
            Simulation::new(config).run(|env| async move {
                let mut values = Vec::new();
                for _ in 0..10 {
                    values.push(env.rng.next_u64());
                }
                Ok(values)
            })
        };

        let result1 = run_simulation().unwrap();
        let result2 = run_simulation().unwrap();

        assert_eq!(result1, result2);
    }

    #[test]
    fn test_simulation_network() {
        let config = SimConfig::new(12345).with_network_latency(0, 0);
        let result = Simulation::new(config).run(|env| async move {
            // Send message
            let sent = env
                .network
                .send("node-1", "node-2", Bytes::from("hello"))
                .await;
            assert!(sent);

            // Receive message
            let messages = env.network.receive("node-2").await;
            assert_eq!(messages.len(), 1);
            assert_eq!(messages[0].payload, Bytes::from("hello"));

            Ok(())
        });

        assert!(result.is_ok());
    }

    #[test]
    fn test_simulation_time_advancement() {
        let config = SimConfig::new(12345);
        let result = Simulation::new(config).run(|env| async move {
            let start = env.now_ms();
            env.advance_time_ms(1000);
            let end = env.now_ms();

            assert_eq!(end - start, 1000);
            Ok(())
        });

        assert!(result.is_ok());
    }
}

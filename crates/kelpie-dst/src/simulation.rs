//! Simulation harness for deterministic testing
//!
//! TigerStyle: Reproducible test execution with explicit configuration.

use crate::clock::SimClock;
use crate::fault::{FaultConfig, FaultInjector, FaultInjectorBuilder};
use crate::network::SimNetwork;
use crate::rng::DeterministicRng;
use crate::sandbox::SimSandboxFactory;
use crate::sandbox_io::SimSandboxIOFactory;
use crate::storage::SimStorage;
use crate::teleport::SimTeleportStorage;
use crate::time::SimTime;
use crate::vm::SimVmFactory;
use kelpie_core::{IoContext, RngProvider, TimeProvider, DST_STEPS_COUNT_MAX, DST_TIME_MS_MAX};
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
    pub clock: Arc<SimClock>,
    /// Deterministic RNG
    pub rng: Arc<DeterministicRng>,
    /// I/O context for DST (unified time/rng abstraction)
    pub io_context: IoContext,
    /// Simulated storage (for actor state)
    pub storage: SimStorage,
    /// Simulated network
    pub network: SimNetwork,
    /// Fault injector (shared across all components)
    pub faults: Arc<FaultInjector>,
    /// Simulated sandbox factory (for creating sandboxes with fault injection)
    /// DEPRECATED: Use sandbox_io_factory for proper DST
    pub sandbox_factory: SimSandboxFactory,
    /// New sandbox factory using `GenericSandbox`<`SimSandboxIO`> for proper DST
    /// This uses the SAME state machine code as production, only I/O differs
    pub sandbox_io_factory: SimSandboxIOFactory,
    /// Simulated teleport storage (for teleport package upload/download)
    pub teleport_storage: SimTeleportStorage,
    /// Simulated VM factory (for VmInstance-based teleport testing)
    pub vm_factory: SimVmFactory,
}

impl SimEnvironment {
    /// Fork the RNG to create an independent stream (wrapped in Arc for sharing)
    pub fn fork_rng(&self) -> Arc<DeterministicRng> {
        Arc::new(self.rng.fork())
    }

    /// Fork the RNG to create an independent stream (raw, not wrapped)
    pub fn fork_rng_raw(&self) -> DeterministicRng {
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

    /// Get time via IoContext (proper DST pattern)
    pub fn time(&self) -> &Arc<dyn TimeProvider> {
        &self.io_context.time
    }

    /// Get RNG via IoContext (proper DST pattern)
    pub fn rng_provider(&self) -> &Arc<dyn RngProvider> {
        &self.io_context.rng
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
        let rng = Arc::new(DeterministicRng::new(self.config.seed));
        let clock = Arc::new(SimClock::default());

        // Build fault injector
        let mut fault_builder = FaultInjectorBuilder::new(rng.fork());
        for fault in self.fault_configs {
            fault_builder = fault_builder.with_fault(fault);
        }
        let faults = Arc::new(fault_builder.build());

        // Build SimTime (auto-advancing time provider for DST)
        let sim_time = Arc::new(SimTime::new(clock.clone()));

        // Build IoContext (unified time/rng for DST)
        let io_context = IoContext {
            time: sim_time as Arc<dyn TimeProvider>,
            rng: rng.clone() as Arc<dyn RngProvider>,
        };

        // Build storage
        let mut storage = SimStorage::new(rng.fork(), faults.clone());
        if let Some(limit) = self.config.storage_limit_bytes {
            storage = storage.with_size_limit(limit);
        }

        // Build network
        let network = SimNetwork::new((*clock).clone(), rng.fork(), faults.clone()).with_latency(
            self.config.network_latency_ms,
            self.config.network_jitter_ms,
        );

        // Build old sandbox factory (deprecated)
        let sandbox_factory = SimSandboxFactory::new(rng.fork(), faults.clone());

        // Build new sandbox IO factory (proper DST - same state machine as production)
        let sandbox_io_factory =
            SimSandboxIOFactory::new(rng.clone(), faults.clone(), clock.clone());

        // Build teleport storage
        let teleport_storage = SimTeleportStorage::new(rng.fork(), faults.clone());
        let vm_factory = SimVmFactory::new(rng.clone(), faults.clone(), clock.clone());

        let env = SimEnvironment {
            clock,
            rng,
            io_context,
            storage,
            network,
            faults,
            sandbox_factory,
            sandbox_io_factory,
            teleport_storage,
            vm_factory,
        };

        // Run the test
        // TigerStyle: Explicit runtime selection for deterministic testing
        #[cfg(not(madsim))]
        {
            // Production: Create tokio runtime for execution
            let runtime = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .map_err(|e| SimulationError::RuntimeError(e.to_string()))?;

            runtime.block_on(async { test(env).await.map_err(SimulationError::TestFailed) })
        }

        #[cfg(madsim)]
        {
            // DST: Use madsim's existing runtime context (no new runtime needed)
            // When #[madsim::test] is used, madsim already controls the execution context
            madsim::runtime::Handle::current()
                .block_on(async { test(env).await.map_err(SimulationError::TestFailed) })
        }
    }

    /// Run the simulation asynchronously (when already in an async context)
    pub async fn run_async<F, Fut, T>(self, test: F) -> Result<T, SimulationError>
    where
        F: FnOnce(SimEnvironment) -> Fut,
        Fut: Future<Output = Result<T, kelpie_core::Error>>,
    {
        let rng = Arc::new(DeterministicRng::new(self.config.seed));
        let clock = Arc::new(SimClock::default());

        let mut fault_builder = FaultInjectorBuilder::new(rng.fork());
        for fault in self.fault_configs {
            fault_builder = fault_builder.with_fault(fault);
        }
        let faults = Arc::new(fault_builder.build());

        // Build SimTime (auto-advancing time provider for DST)
        let sim_time = Arc::new(SimTime::new(clock.clone()));

        // Build IoContext (unified time/rng for DST)
        let io_context = IoContext {
            time: sim_time as Arc<dyn TimeProvider>,
            rng: rng.clone() as Arc<dyn RngProvider>,
        };

        let mut storage = SimStorage::new(rng.fork(), faults.clone());
        if let Some(limit) = self.config.storage_limit_bytes {
            storage = storage.with_size_limit(limit);
        }

        let network = SimNetwork::new((*clock).clone(), rng.fork(), faults.clone()).with_latency(
            self.config.network_latency_ms,
            self.config.network_jitter_ms,
        );

        // Build old sandbox factory (deprecated)
        let sandbox_factory = SimSandboxFactory::new(rng.fork(), faults.clone());

        // Build new sandbox IO factory (proper DST - same state machine as production)
        let sandbox_io_factory =
            SimSandboxIOFactory::new(rng.clone(), faults.clone(), clock.clone());

        // Build teleport storage
        let teleport_storage = SimTeleportStorage::new(rng.fork(), faults.clone());
        let vm_factory = SimVmFactory::new(rng.clone(), faults.clone(), clock.clone());

        let env = SimEnvironment {
            clock,
            rng,
            io_context,
            storage,
            network,
            faults,
            sandbox_factory,
            sandbox_io_factory,
            teleport_storage,
            vm_factory,
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

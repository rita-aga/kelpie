//! Simulated sandbox for deterministic testing
//!
//! TigerStyle: Sandbox simulation with fault injection for DST.
//!
//! This module provides a simulated sandbox that:
//! - Implements the kelpie_sandbox::Sandbox trait
//! - Injects faults based on FaultInjector configuration
//! - Uses deterministic RNG for reproducible behavior
//! - Tracks all operations for verification

use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_sandbox::{
    ExecOptions, ExecOutput, Sandbox, SandboxConfig, SandboxError, SandboxFactory, SandboxResult,
    SandboxState, SandboxStats, Snapshot,
};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::sync::RwLock;

/// Maximum sandbox ID length in bytes
const SANDBOX_ID_LENGTH_BYTES_MAX: usize = 128;

/// Maximum file path length in bytes
const FILE_PATH_LENGTH_BYTES_MAX: usize = 4096;

/// Maximum snapshot size in bytes (for fault injection)
const SNAPSHOT_SIZE_BYTES_DEFAULT_MAX: u64 = 1024 * 1024 * 1024; // 1GB

/// Simulated sandbox with fault injection
///
/// This sandbox implementation is designed for deterministic simulation testing.
/// It injects faults based on the provided FaultInjector and uses deterministic
/// RNG for all random behavior.
pub struct SimSandbox {
    /// Sandbox ID
    id: String,
    /// Configuration
    config: SandboxConfig,
    /// Current state
    state: RwLock<SandboxState>,
    /// Simulated filesystem
    filesystem: RwLock<HashMap<String, Bytes>>,
    /// Simulated environment variables
    env: RwLock<HashMap<String, String>>,
    /// Deterministic RNG for this sandbox
    rng: RwLock<DeterministicRng>,
    /// Fault injector (shared)
    faults: Arc<FaultInjector>,
    /// Simulated start time (in simulation milliseconds)
    start_time_ms: AtomicU64,
    /// Simulated memory usage
    memory_used: AtomicU64,
    /// Operation counter for debugging
    operation_count: AtomicU64,
    /// Maximum snapshot size (for SnapshotTooLarge fault)
    max_snapshot_bytes: u64,
}

impl SimSandbox {
    /// Create a new simulated sandbox
    ///
    /// # Arguments
    /// * `id` - Unique sandbox identifier
    /// * `config` - Sandbox configuration
    /// * `rng` - Deterministic RNG for this sandbox
    /// * `faults` - Shared fault injector
    pub fn new(
        id: impl Into<String>,
        config: SandboxConfig,
        rng: DeterministicRng,
        faults: Arc<FaultInjector>,
    ) -> Self {
        let id = id.into();
        assert!(
            id.len() <= SANDBOX_ID_LENGTH_BYTES_MAX,
            "sandbox ID too long"
        );

        // Initialize environment from config
        let mut env = HashMap::new();
        for (k, v) in &config.env {
            env.insert(k.clone(), v.clone());
        }

        Self {
            id,
            config,
            state: RwLock::new(SandboxState::Stopped),
            filesystem: RwLock::new(HashMap::new()),
            env: RwLock::new(env),
            rng: RwLock::new(rng),
            faults,
            start_time_ms: AtomicU64::new(0),
            memory_used: AtomicU64::new(0),
            operation_count: AtomicU64::new(0),
            max_snapshot_bytes: SNAPSHOT_SIZE_BYTES_DEFAULT_MAX,
        }
    }

    /// Set the maximum snapshot size (for testing SnapshotTooLarge fault)
    pub fn with_max_snapshot_bytes(mut self, max_bytes: u64) -> Self {
        self.max_snapshot_bytes = max_bytes;
        self
    }

    /// Check for fault injection and return error if fault should be injected
    fn check_fault(&self, operation: &str) -> Option<FaultType> {
        self.operation_count.fetch_add(1, Ordering::SeqCst);
        self.faults.should_inject(operation)
    }

    /// Convert a FaultType to a SandboxError
    fn fault_to_error(&self, fault: FaultType) -> SandboxError {
        match fault {
            FaultType::SandboxBootFail => SandboxError::Internal {
                message: format!("Sandbox {} boot failed (DST fault injection)", self.id),
            },
            FaultType::SandboxCrash => SandboxError::Internal {
                message: format!("Sandbox {} crashed (DST fault injection)", self.id),
            },
            FaultType::SandboxPauseFail => SandboxError::Internal {
                message: format!("Sandbox {} pause failed (DST fault injection)", self.id),
            },
            FaultType::SandboxResumeFail => SandboxError::Internal {
                message: format!("Sandbox {} resume failed (DST fault injection)", self.id),
            },
            FaultType::SandboxExecFail => SandboxError::ExecFailed {
                command: "unknown".to_string(),
                reason: format!(
                    "Simulated exec failure in sandbox {} (DST fault injection)",
                    self.id
                ),
            },
            FaultType::SandboxExecTimeout { timeout_ms } => SandboxError::ExecTimeout {
                command: "unknown".to_string(),
                timeout_ms,
            },
            FaultType::SnapshotCreateFail => SandboxError::SnapshotFailed {
                sandbox_id: self.id.clone(),
                reason: "Simulated snapshot creation failure (DST fault injection)".to_string(),
            },
            FaultType::SnapshotCorruption => SandboxError::SnapshotFailed {
                sandbox_id: self.id.clone(),
                reason: "Simulated snapshot corruption (DST fault injection)".to_string(),
            },
            FaultType::SnapshotRestoreFail => SandboxError::RestoreFailed {
                sandbox_id: self.id.clone(),
                reason: "Simulated restore failure (DST fault injection)".to_string(),
            },
            FaultType::SnapshotTooLarge { max_bytes } => SandboxError::SnapshotFailed {
                sandbox_id: self.id.clone(),
                reason: format!(
                    "Snapshot too large: exceeds {} bytes (DST fault injection)",
                    max_bytes
                ),
            },
            _ => SandboxError::Internal {
                message: format!("Unexpected fault type: {:?}", fault),
            },
        }
    }

    /// Write a file to the simulated filesystem
    pub async fn write_file(&self, path: impl Into<String>, content: impl Into<Bytes>) {
        let path = path.into();
        assert!(
            path.len() <= FILE_PATH_LENGTH_BYTES_MAX,
            "file path too long"
        );

        let mut fs = self.filesystem.write().await;
        fs.insert(path, content.into());
    }

    /// Read a file from the simulated filesystem
    pub async fn read_file(&self, path: &str) -> Option<Bytes> {
        let fs = self.filesystem.read().await;
        fs.get(path).cloned()
    }

    /// Set an environment variable
    pub async fn set_env(&self, key: impl Into<String>, value: impl Into<String>) {
        let mut env = self.env.write().await;
        env.insert(key.into(), value.into());
    }

    /// Get an environment variable
    pub async fn get_env(&self, key: &str) -> Option<String> {
        let env = self.env.read().await;
        env.get(key).cloned()
    }

    /// Simulate memory usage
    pub fn set_memory_used(&self, bytes: u64) {
        self.memory_used.store(bytes, Ordering::SeqCst);
    }

    /// Get the operation count (for debugging)
    pub fn operation_count(&self) -> u64 {
        self.operation_count.load(Ordering::SeqCst)
    }

    /// Default command handler that echoes arguments
    fn default_handler(command: &str, args: &[&str], _options: &ExecOptions) -> ExecOutput {
        match command {
            "echo" => ExecOutput::success(format!("{}\n", args.join(" "))),
            "cat" => {
                if args.is_empty() {
                    ExecOutput::failure(1, "cat: missing operand")
                } else {
                    ExecOutput::success(format!("contents of {}\n", args[0]))
                }
            }
            "ls" => ExecOutput::success("file1.txt\nfile2.txt\n"),
            "pwd" => ExecOutput::success("/workspace\n"),
            "true" => ExecOutput::success(""),
            "false" => ExecOutput::failure(1, ""),
            "sleep" => ExecOutput::success(""),
            "touch" => ExecOutput::success(""),
            _ => ExecOutput::failure(127, format!("{}: command not found\n", command)),
        }
    }
}

#[async_trait]
impl Sandbox for SimSandbox {
    fn id(&self) -> &str {
        &self.id
    }

    fn state(&self) -> SandboxState {
        futures::executor::block_on(async { *self.state.read().await })
    }

    fn config(&self) -> &SandboxConfig {
        &self.config
    }

    async fn start(&mut self) -> SandboxResult<()> {
        // Check for boot failure fault
        if let Some(fault) = self.check_fault("sandbox_start") {
            if matches!(fault, FaultType::SandboxBootFail) {
                return Err(self.fault_to_error(fault));
            }
        }

        let mut state = self.state.write().await;

        if !state.can_start() && *state != SandboxState::Creating {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.to_string(),
                expected: "stopped or creating".to_string(),
            });
        }

        *state = SandboxState::Running;
        // Use a deterministic start time (could be from SimClock)
        self.start_time_ms.store(1000, Ordering::SeqCst);

        tracing::debug!(sandbox_id = %self.id, "SimSandbox started");
        Ok(())
    }

    async fn stop(&mut self) -> SandboxResult<()> {
        // Check for crash fault during stop
        if let Some(fault) = self.check_fault("sandbox_stop") {
            if matches!(fault, FaultType::SandboxCrash) {
                let mut state = self.state.write().await;
                *state = SandboxState::Failed;
                return Err(self.fault_to_error(fault));
            }
        }

        let mut state = self.state.write().await;

        if !state.can_stop() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.to_string(),
                expected: "running or paused".to_string(),
            });
        }

        *state = SandboxState::Stopped;
        tracing::debug!(sandbox_id = %self.id, "SimSandbox stopped");
        Ok(())
    }

    async fn pause(&mut self) -> SandboxResult<()> {
        // Check for pause failure fault
        if let Some(fault) = self.check_fault("sandbox_pause") {
            if matches!(fault, FaultType::SandboxPauseFail) {
                return Err(self.fault_to_error(fault));
            }
        }

        let mut state = self.state.write().await;

        if !state.can_pause() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.to_string(),
                expected: "running".to_string(),
            });
        }

        *state = SandboxState::Paused;
        tracing::debug!(sandbox_id = %self.id, "SimSandbox paused");
        Ok(())
    }

    async fn resume(&mut self) -> SandboxResult<()> {
        // Check for resume failure fault
        if let Some(fault) = self.check_fault("sandbox_resume") {
            if matches!(fault, FaultType::SandboxResumeFail) {
                return Err(self.fault_to_error(fault));
            }
        }

        let mut state = self.state.write().await;

        if !state.can_resume() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.to_string(),
                expected: "paused".to_string(),
            });
        }

        *state = SandboxState::Running;
        tracing::debug!(sandbox_id = %self.id, "SimSandbox resumed");
        Ok(())
    }

    async fn exec(
        &self,
        command: &str,
        args: &[&str],
        options: ExecOptions,
    ) -> SandboxResult<ExecOutput> {
        // Check for exec failure or timeout fault
        if let Some(fault) = self.check_fault("sandbox_exec") {
            match &fault {
                FaultType::SandboxExecFail | FaultType::SandboxExecTimeout { .. } => {
                    return Err(self.fault_to_error(fault));
                }
                FaultType::SandboxCrash => {
                    // Crash during exec - mark as failed
                    let mut state = self.state.write().await;
                    *state = SandboxState::Failed;
                    return Err(self.fault_to_error(fault));
                }
                _ => {}
            }
        }

        let state = self.state.read().await;

        if !state.can_exec() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.to_string(),
                expected: "running".to_string(),
            });
        }
        drop(state);

        // Use default handler
        Ok(Self::default_handler(command, args, &options))
    }

    async fn snapshot(&self) -> SandboxResult<Snapshot> {
        // Check for snapshot creation failure
        // NOTE: SnapshotCorruption is NOT checked here - it only affects restore
        // Corruption happens during storage/transfer, not during creation
        if let Some(fault) = self.check_fault("sandbox_snapshot") {
            match &fault {
                FaultType::SnapshotCreateFail => {
                    return Err(self.fault_to_error(fault));
                }
                FaultType::SnapshotTooLarge { .. } => {
                    return Err(self.fault_to_error(fault));
                }
                _ => {}
            }
        }

        let state = self.state.read().await;

        if !state.can_snapshot() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.to_string(),
                expected: "running or paused".to_string(),
            });
        }
        drop(state);

        // Serialize filesystem and env
        let fs = self.filesystem.read().await;
        let env = self.env.read().await;

        let fs_data = serde_json::to_vec(&*fs).map_err(|e| SandboxError::SnapshotFailed {
            sandbox_id: self.id.clone(),
            reason: e.to_string(),
        })?;

        // Check snapshot size
        let snapshot_size = fs_data.len() as u64;
        if snapshot_size > self.max_snapshot_bytes {
            return Err(SandboxError::SnapshotFailed {
                sandbox_id: self.id.clone(),
                reason: format!(
                    "Snapshot too large: {} bytes exceeds max {} bytes",
                    snapshot_size, self.max_snapshot_bytes
                ),
            });
        }

        // SimSandbox creates Suspend snapshots (memory-only, same-host)
        let snapshot = Snapshot::suspend(&self.id)
            .with_memory(Bytes::from(fs_data))
            .with_env_state(env.iter().map(|(k, v)| (k.clone(), v.clone())).collect());

        tracing::debug!(
            sandbox_id = %self.id,
            snapshot_id = %snapshot.id(),
            size_bytes = snapshot_size,
            "SimSandbox snapshot created"
        );

        Ok(snapshot)
    }

    async fn restore(&mut self, snapshot: &Snapshot) -> SandboxResult<()> {
        // Check for restore failure fault
        if let Some(fault) = self.check_fault("sandbox_restore") {
            match &fault {
                FaultType::SnapshotRestoreFail | FaultType::SnapshotCorruption => {
                    return Err(self.fault_to_error(fault));
                }
                _ => {}
            }
        }

        // Restore filesystem
        if let Some(memory) = &snapshot.memory {
            let fs: HashMap<String, Bytes> =
                serde_json::from_slice(memory).map_err(|e| SandboxError::RestoreFailed {
                    sandbox_id: self.id.clone(),
                    reason: e.to_string(),
                })?;

            let mut current_fs = self.filesystem.write().await;
            *current_fs = fs;
        }

        // Restore environment
        if let Some(env_state) = &snapshot.env_state {
            let mut env = self.env.write().await;
            env.clear();
            for (k, v) in env_state {
                env.insert(k.clone(), v.clone());
            }
        }

        tracing::debug!(
            sandbox_id = %self.id,
            snapshot_id = %snapshot.id(),
            "SimSandbox restored from snapshot"
        );

        Ok(())
    }

    async fn destroy(&mut self) -> SandboxResult<()> {
        let mut state = self.state.write().await;
        *state = SandboxState::Destroying;

        // Clear all state
        self.filesystem.write().await.clear();
        self.env.write().await.clear();

        tracing::debug!(sandbox_id = %self.id, "SimSandbox destroyed");
        Ok(())
    }

    async fn health_check(&self) -> SandboxResult<bool> {
        let state = self.state.read().await;
        Ok(*state == SandboxState::Running)
    }

    async fn stats(&self) -> SandboxResult<SandboxStats> {
        let start_time = self.start_time_ms.load(Ordering::SeqCst);
        // Use a deterministic uptime calculation
        let uptime = if start_time > 0 { 1000 } else { 0 };

        Ok(SandboxStats {
            memory_bytes_used: self.memory_used.load(Ordering::SeqCst),
            cpu_percent: 0.0,
            disk_bytes_used: 0,
            network_rx_bytes: 0,
            network_tx_bytes: 0,
            uptime_ms: uptime,
        })
    }
}

/// Factory for creating SimSandbox instances
pub struct SimSandboxFactory {
    /// Deterministic RNG for sandbox ID generation
    rng: RwLock<DeterministicRng>,
    /// Shared fault injector
    faults: Arc<FaultInjector>,
    /// Counter for deterministic ID generation
    counter: AtomicU64,
    /// ID prefix
    prefix: String,
}

impl Clone for SimSandboxFactory {
    fn clone(&self) -> Self {
        // Clone needs to be synchronous, so we use blocking read
        // This is safe in tests where Clone is used
        let rng = futures::executor::block_on(self.rng.read()).fork();
        Self {
            rng: RwLock::new(rng),
            faults: self.faults.clone(),
            counter: AtomicU64::new(self.counter.load(Ordering::SeqCst)),
            prefix: self.prefix.clone(),
        }
    }
}

impl SimSandboxFactory {
    /// Create a new SimSandboxFactory
    pub fn new(rng: DeterministicRng, faults: Arc<FaultInjector>) -> Self {
        Self {
            rng: RwLock::new(rng),
            faults,
            counter: AtomicU64::new(0),
            prefix: "sim-sandbox".to_string(),
        }
    }

    /// Set the ID prefix
    pub fn with_prefix(mut self, prefix: impl Into<String>) -> Self {
        self.prefix = prefix.into();
        self
    }
}

#[async_trait]
impl SandboxFactory for SimSandboxFactory {
    type Sandbox = SimSandbox;

    async fn create(&self, config: SandboxConfig) -> SandboxResult<SimSandbox> {
        let id = self.counter.fetch_add(1, Ordering::SeqCst);
        let sandbox_id = format!("{}-{}", self.prefix, id);

        let rng = {
            let rng = self.rng.write().await;
            rng.fork()
        };

        // Return sandbox in Stopped state - caller must call start()
        // This allows testing the full lifecycle including start failures
        let sandbox = SimSandbox::new(sandbox_id, config, rng, self.faults.clone());
        Ok(sandbox)
    }

    async fn create_from_snapshot(
        &self,
        config: SandboxConfig,
        snapshot: &Snapshot,
    ) -> SandboxResult<SimSandbox> {
        let id = self.counter.fetch_add(1, Ordering::SeqCst);
        let sandbox_id = format!("{}-{}", self.prefix, id);

        let rng = {
            let rng = self.rng.write().await;
            rng.fork()
        };

        let mut sandbox = SimSandbox::new(sandbox_id, config, rng, self.faults.clone());
        sandbox.restore(snapshot).await?;
        // Return sandbox in Stopped state - caller must call start()
        Ok(sandbox)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::{FaultConfig, FaultInjectorBuilder};

    fn create_test_faults(rng: DeterministicRng) -> Arc<FaultInjector> {
        Arc::new(FaultInjectorBuilder::new(rng).build())
    }

    fn create_test_faults_with_sandbox_faults(
        rng: DeterministicRng,
        probability: f64,
    ) -> Arc<FaultInjector> {
        Arc::new(
            FaultInjectorBuilder::new(rng)
                .with_sandbox_faults(probability)
                .build(),
        )
    }

    #[tokio::test]
    async fn test_sim_sandbox_lifecycle() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let config = SandboxConfig::default();
        let mut sandbox = SimSandbox::new("test-1", config, rng, faults);

        assert_eq!(sandbox.state(), SandboxState::Stopped);

        sandbox.start().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Running);

        sandbox.pause().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Paused);

        sandbox.resume().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Running);

        sandbox.stop().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Stopped);
    }

    #[tokio::test]
    async fn test_sim_sandbox_exec() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let config = SandboxConfig::default();
        let mut sandbox = SimSandbox::new("test-1", config, rng, faults);

        sandbox.start().await.unwrap();

        let output = sandbox
            .exec_simple("echo", &["hello", "world"])
            .await
            .unwrap();
        assert!(output.is_success());
        assert_eq!(output.stdout_string(), "hello world\n");
    }

    #[tokio::test]
    async fn test_sim_sandbox_snapshot_restore() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let config = SandboxConfig::default();
        let mut sandbox = SimSandbox::new("test-1", config.clone(), rng.fork(), faults.clone());

        sandbox.start().await.unwrap();
        sandbox.write_file("/test.txt", "hello").await;
        sandbox.set_env("MY_VAR", "my_value").await;

        let snapshot = sandbox.snapshot().await.unwrap();

        let mut sandbox2 = SimSandbox::new("test-2", config, rng.fork(), faults);
        sandbox2.restore(&snapshot).await.unwrap();
        sandbox2.start().await.unwrap();

        let content = sandbox2.read_file("/test.txt").await.unwrap();
        assert_eq!(content.as_ref(), b"hello");

        let env_value = sandbox2.get_env("MY_VAR").await.unwrap();
        assert_eq!(env_value, "my_value");
    }

    #[tokio::test]
    async fn test_sim_sandbox_with_boot_fault() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 1.0))
                .build(),
        );
        let config = SandboxConfig::default();
        let mut sandbox = SimSandbox::new("test-1", config, rng, faults);

        let result = sandbox.start().await;
        assert!(result.is_err());
        assert!(matches!(result, Err(SandboxError::Internal { .. })));
    }

    #[tokio::test]
    async fn test_sim_sandbox_with_snapshot_fault() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 1.0))
                .build(),
        );
        let config = SandboxConfig::default();
        let mut sandbox = SimSandbox::new("test-1", config, rng, faults);

        sandbox.start().await.unwrap();

        let result = sandbox.snapshot().await;
        assert!(result.is_err());
        assert!(matches!(result, Err(SandboxError::SnapshotFailed { .. })));
    }

    #[tokio::test]
    async fn test_sim_sandbox_factory() {
        let rng = DeterministicRng::new(42);
        let faults = create_test_faults(rng.fork());
        let factory = SimSandboxFactory::new(rng, faults);

        let mut sandbox1 = factory.create(SandboxConfig::default()).await.unwrap();
        let mut sandbox2 = factory.create(SandboxConfig::default()).await.unwrap();

        assert_eq!(sandbox1.id(), "sim-sandbox-0");
        assert_eq!(sandbox2.id(), "sim-sandbox-1");
        // Factory returns sandbox in Stopped state - caller must start()
        assert_eq!(sandbox1.state(), SandboxState::Stopped);
        assert_eq!(sandbox2.state(), SandboxState::Stopped);

        // Start them manually
        sandbox1.start().await.unwrap();
        sandbox2.start().await.unwrap();
        assert_eq!(sandbox1.state(), SandboxState::Running);
        assert_eq!(sandbox2.state(), SandboxState::Running);
    }

    #[tokio::test]
    async fn test_sim_sandbox_determinism() {
        let run_test = |seed: u64| async move {
            let rng = DeterministicRng::new(seed);
            let faults = create_test_faults_with_sandbox_faults(rng.fork(), 0.3);
            let factory = SimSandboxFactory::new(rng, faults).with_prefix("det-test");

            let mut results = Vec::new();

            for _ in 0..5 {
                let result = factory.create(SandboxConfig::default()).await;
                results.push(result.is_ok());
            }

            results
        };

        let results1 = run_test(12345).await;
        let results2 = run_test(12345).await;

        assert_eq!(results1, results2, "Results should be deterministic");
    }
}

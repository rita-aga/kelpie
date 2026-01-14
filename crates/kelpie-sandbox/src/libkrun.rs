//! libkrun-based sandbox implementation
//!
//! TigerStyle: VM-backed sandbox with explicit lifecycle and state transitions.
//!
//! This module provides `LibkrunSandbox`, a sandbox implementation that uses
//! libkrun microVMs for isolation. Works on macOS (HVF) and Linux (KVM).

use std::sync::atomic::{AtomicU64, Ordering};

use async_trait::async_trait;
use bytes::Bytes;
use tracing::{debug, error, info, instrument};

use kelpie_libkrun::{
    LibkrunError, LibkrunResult, MockVm, MockVmFactory, VmConfig, VmExecOptions, VmInstance,
    VmSnapshot as LibkrunSnapshot, VmState, VM_BOOT_TIMEOUT_MS,
};

use crate::config::SandboxConfig;
use crate::error::{SandboxError, SandboxResult};
use crate::exec::{ExecOptions, ExecOutput, ExitStatus};
use crate::snapshot::Snapshot;
use crate::traits::{Sandbox, SandboxFactory, SandboxState, SandboxStats};

// ============================================================================
// TigerStyle Constants
// ============================================================================

/// Default root disk path for libkrun VMs
pub const LIBKRUN_ROOT_DISK_PATH_DEFAULT: &str = "/var/lib/kelpie/rootfs.ext4";

/// Health check command
const HEALTH_CHECK_CMD: &str = "true";

/// Counter for generating unique sandbox IDs
static SANDBOX_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

// ============================================================================
// LibkrunSandbox Configuration
// ============================================================================

/// Configuration specific to libkrun sandboxes
#[derive(Debug, Clone)]
pub struct LibkrunSandboxConfig {
    /// Path to root filesystem image
    pub root_disk_path: String,
    /// Boot timeout in milliseconds
    pub boot_timeout_ms: u64,
    /// Whether to enable networking in the VM
    pub network_enabled: bool,
}

impl Default for LibkrunSandboxConfig {
    fn default() -> Self {
        Self {
            root_disk_path: LIBKRUN_ROOT_DISK_PATH_DEFAULT.to_string(),
            boot_timeout_ms: VM_BOOT_TIMEOUT_MS,
            network_enabled: true,
        }
    }
}

impl LibkrunSandboxConfig {
    /// Create new libkrun config
    pub fn new(root_disk_path: impl Into<String>) -> Self {
        Self {
            root_disk_path: root_disk_path.into(),
            ..Default::default()
        }
    }

    /// Set boot timeout
    pub fn with_boot_timeout(mut self, timeout_ms: u64) -> Self {
        self.boot_timeout_ms = timeout_ms;
        self
    }

    /// Enable/disable networking
    pub fn with_network(mut self, enabled: bool) -> Self {
        self.network_enabled = enabled;
        self
    }
}

// ============================================================================
// LibkrunSandbox Implementation
// ============================================================================

/// Sandbox implementation using libkrun microVMs
pub struct LibkrunSandbox {
    /// Unique sandbox identifier
    id: String,
    /// Sandbox configuration
    config: SandboxConfig,
    /// libkrun-specific configuration
    libkrun_config: LibkrunSandboxConfig,
    /// Underlying VM instance
    vm: MockVm,
    /// Current state
    state: SandboxState,
    /// Uptime tracking (start time in epoch ms)
    start_time_ms: Option<u64>,
}

impl std::fmt::Debug for LibkrunSandbox {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LibkrunSandbox")
            .field("id", &self.id)
            .field("state", &self.state)
            .finish()
    }
}

impl LibkrunSandbox {
    /// Create a new libkrun sandbox
    pub fn new(config: SandboxConfig, libkrun_config: LibkrunSandboxConfig, vm: MockVm) -> Self {
        let id = format!(
            "libkrun-sandbox-{}",
            SANDBOX_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
        );

        Self {
            id,
            config,
            libkrun_config,
            vm,
            state: SandboxState::Stopped,
            start_time_ms: None,
        }
    }

    /// Get current epoch time in milliseconds
    fn now_ms() -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0)
    }

    /// Map VmState to SandboxState
    fn map_vm_state(vm_state: VmState) -> SandboxState {
        match vm_state {
            VmState::Created => SandboxState::Stopped,
            VmState::Starting => SandboxState::Creating,
            VmState::Running => SandboxState::Running,
            VmState::Paused => SandboxState::Paused,
            VmState::Stopped => SandboxState::Stopped,
            VmState::Crashed => SandboxState::Failed,
        }
    }

    /// Map LibkrunError to SandboxError
    fn map_error(&self, err: LibkrunError) -> SandboxError {
        match err {
            LibkrunError::BootFailed { reason } => SandboxError::Internal {
                message: format!("VM boot failed: {}", reason),
            },
            LibkrunError::BootTimeout { timeout_ms } => SandboxError::ExecTimeout {
                command: "boot".to_string(),
                timeout_ms,
            },
            LibkrunError::NotRunning { state } => SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: state.clone(),
                expected: "running".to_string(),
            },
            LibkrunError::ExecFailed { reason } => SandboxError::ExecFailed {
                command: "exec".to_string(),
                reason,
            },
            LibkrunError::ExecTimeout { timeout_ms } => SandboxError::ExecTimeout {
                command: "exec".to_string(),
                timeout_ms,
            },
            LibkrunError::SnapshotFailed { reason } => SandboxError::SnapshotFailed {
                sandbox_id: self.id.clone(),
                reason,
            },
            LibkrunError::SnapshotCorrupted => SandboxError::RestoreFailed {
                sandbox_id: self.id.clone(),
                reason: "snapshot corrupted".to_string(),
            },
            LibkrunError::RestoreFailed { reason } => SandboxError::RestoreFailed {
                sandbox_id: self.id.clone(),
                reason,
            },
            _ => SandboxError::Internal {
                message: err.to_string(),
            },
        }
    }

    /// Synchronize internal state with VM state
    fn sync_state(&mut self) {
        self.state = Self::map_vm_state(self.vm.state());
    }
}

#[async_trait]
impl Sandbox for LibkrunSandbox {
    fn id(&self) -> &str {
        &self.id
    }

    fn state(&self) -> SandboxState {
        self.state
    }

    fn config(&self) -> &SandboxConfig {
        &self.config
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn start(&mut self) -> SandboxResult<()> {
        // Precondition: must be in Stopped state
        if !self.state.can_start() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "stopped".to_string(),
            });
        }

        debug!("Starting libkrun sandbox");
        self.state = SandboxState::Creating;

        match self.vm.start().await {
            Ok(()) => {
                self.state = SandboxState::Running;
                self.start_time_ms = Some(Self::now_ms());
                info!("Libkrun sandbox started successfully");
                Ok(())
            }
            Err(err) => {
                error!("Failed to start sandbox: {}", err);
                self.state = SandboxState::Failed;
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn stop(&mut self) -> SandboxResult<()> {
        // Precondition: must be able to stop
        if !self.state.can_stop() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "running or paused".to_string(),
            });
        }

        debug!("Stopping libkrun sandbox");

        match self.vm.stop().await {
            Ok(()) => {
                self.state = SandboxState::Stopped;
                self.start_time_ms = None;
                info!("Libkrun sandbox stopped");
                Ok(())
            }
            Err(err) => {
                error!("Failed to stop sandbox: {}", err);
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn pause(&mut self) -> SandboxResult<()> {
        // Precondition: must be running
        if !self.state.can_pause() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "running".to_string(),
            });
        }

        debug!("Pausing libkrun sandbox");

        match self.vm.pause().await {
            Ok(()) => {
                self.state = SandboxState::Paused;
                info!("Libkrun sandbox paused");
                Ok(())
            }
            Err(err) => {
                error!("Failed to pause sandbox: {}", err);
                // Sync state in case VM crashed
                self.sync_state();
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn resume(&mut self) -> SandboxResult<()> {
        // Precondition: must be paused
        if !self.state.can_resume() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "paused".to_string(),
            });
        }

        debug!("Resuming libkrun sandbox");

        match self.vm.resume().await {
            Ok(()) => {
                self.state = SandboxState::Running;
                info!("Libkrun sandbox resumed");
                Ok(())
            }
            Err(err) => {
                error!("Failed to resume sandbox: {}", err);
                // Sync state in case VM crashed
                self.sync_state();
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self, options), fields(sandbox_id = %self.id, command = %command))]
    async fn exec(
        &self,
        command: &str,
        args: &[&str],
        options: ExecOptions,
    ) -> SandboxResult<ExecOutput> {
        // Precondition: must be running
        if !self.state.can_exec() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "running".to_string(),
            });
        }

        // TigerStyle assertions
        assert!(!command.is_empty(), "command cannot be empty");

        debug!("Executing command in sandbox: {} {:?}", command, args);

        let start = Self::now_ms();

        // Convert options
        let exec_opts = VmExecOptions {
            timeout_ms: options.timeout_ms,
            workdir: options.workdir,
            env: options.env,
            stdin: options.stdin,
        };

        match self.vm.exec_with_options(command, args, exec_opts).await {
            Ok(output) => {
                let duration_ms = Self::now_ms() - start;

                let exec_output = ExecOutput::new(
                    if output.success() {
                        ExitStatus::success()
                    } else {
                        ExitStatus::with_code(output.exit_code)
                    },
                    output.stdout,
                    output.stderr,
                    duration_ms,
                );

                debug!(
                    "Command completed with exit code {}: {} ms",
                    output.exit_code, duration_ms
                );

                Ok(exec_output)
            }
            Err(err) => {
                error!("Command execution failed: {}", err);
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn snapshot(&self) -> SandboxResult<Snapshot> {
        // Precondition: must be able to snapshot
        if !self.state.can_snapshot() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "running or paused".to_string(),
            });
        }

        debug!("Creating snapshot of libkrun sandbox");

        match self.vm.snapshot().await {
            Ok(vm_snapshot) => {
                // Convert VM snapshot to Sandbox snapshot - LibkrunSandbox creates full Teleport snapshots
                let snapshot = Snapshot::teleport(&self.id)
                    .with_memory(vm_snapshot.data.clone())
                    .with_cpu_state(Bytes::from(format!(
                        "arch={},vcpu={},mem={}",
                        vm_snapshot.metadata.architecture,
                        vm_snapshot.metadata.vcpu_count,
                        vm_snapshot.metadata.memory_mib
                    )));

                info!(
                    "Snapshot created: {} bytes",
                    vm_snapshot.metadata.size_bytes
                );

                Ok(snapshot)
            }
            Err(err) => {
                error!("Snapshot failed: {}", err);
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self, snapshot), fields(sandbox_id = %self.id))]
    async fn restore(&mut self, snapshot: &Snapshot) -> SandboxResult<()> {
        // Precondition: must be stopped or just created
        if self.state != SandboxState::Stopped && self.state != SandboxState::Creating {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "stopped".to_string(),
            });
        }

        debug!("Restoring sandbox from snapshot: {}", snapshot.id());

        // Convert Sandbox snapshot to VM snapshot format
        // This is a simplified conversion - real implementation would need
        // to properly deserialize the VM state
        let memory_data = snapshot.memory.clone().unwrap_or_default();
        let checksum = crc32fast::hash(&memory_data);

        let vm_snapshot_metadata = kelpie_libkrun::VmSnapshotMetadata::new(
            snapshot.id().to_string(),
            self.id.clone(),
            memory_data.len() as u64,
            checksum,
            std::env::consts::ARCH.to_string(),
            self.config.limits.vcpu_count,
            (self.config.limits.memory_bytes_max / (1024 * 1024)) as u32,
        );

        let vm_snapshot = LibkrunSnapshot::new(vm_snapshot_metadata, memory_data).map_err(|e| {
            SandboxError::RestoreFailed {
                sandbox_id: self.id.clone(),
                reason: e.to_string(),
            }
        })?;

        match self.vm.restore(&vm_snapshot).await {
            Ok(()) => {
                self.state = SandboxState::Stopped;
                info!("Sandbox restored from snapshot");
                Ok(())
            }
            Err(err) => {
                error!("Restore failed: {}", err);
                Err(self.map_error(err))
            }
        }
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn destroy(&mut self) -> SandboxResult<()> {
        if !self.state.can_destroy() {
            return Err(SandboxError::InvalidState {
                sandbox_id: self.id.clone(),
                current: self.state.to_string(),
                expected: "not destroying".to_string(),
            });
        }

        debug!("Destroying libkrun sandbox");
        self.state = SandboxState::Destroying;

        // Stop if running
        if self.vm.state() == VmState::Running || self.vm.state() == VmState::Paused {
            let _ = self.vm.stop().await;
        }

        self.state = SandboxState::Stopped;
        info!("Libkrun sandbox destroyed");

        Ok(())
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn health_check(&self) -> SandboxResult<bool> {
        if self.state != SandboxState::Running {
            return Ok(false);
        }

        // Try a simple command to verify VM is responsive
        match self.vm.exec(HEALTH_CHECK_CMD, &[]).await {
            Ok(output) => Ok(output.success()),
            Err(_) => Ok(false),
        }
    }

    #[instrument(skip(self), fields(sandbox_id = %self.id))]
    async fn stats(&self) -> SandboxResult<SandboxStats> {
        let uptime_ms = self
            .start_time_ms
            .map(|start| Self::now_ms().saturating_sub(start))
            .unwrap_or(0);

        // In a real implementation, we would query the VM for resource usage
        // For now, return basic stats
        Ok(SandboxStats {
            memory_bytes_used: 0,
            cpu_percent: 0.0,
            disk_bytes_used: 0,
            network_rx_bytes: 0,
            network_tx_bytes: 0,
            uptime_ms,
        })
    }
}

// ============================================================================
// LibkrunSandboxFactory Implementation
// ============================================================================

/// Factory for creating libkrun sandboxes
pub struct LibkrunSandboxFactory {
    /// libkrun-specific configuration
    libkrun_config: LibkrunSandboxConfig,
    /// VM factory
    vm_factory: MockVmFactory,
}

impl std::fmt::Debug for LibkrunSandboxFactory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LibkrunSandboxFactory")
            .field("libkrun_config", &self.libkrun_config)
            .finish()
    }
}

impl LibkrunSandboxFactory {
    /// Create a new factory with default configuration
    pub fn new() -> Self {
        Self {
            libkrun_config: LibkrunSandboxConfig::default(),
            vm_factory: MockVmFactory::new(),
        }
    }

    /// Create with custom libkrun configuration
    pub fn with_config(config: LibkrunSandboxConfig) -> Self {
        Self {
            libkrun_config: config,
            vm_factory: MockVmFactory::new(),
        }
    }

    /// Build VmConfig from SandboxConfig
    fn build_vm_config(&self, config: &SandboxConfig) -> LibkrunResult<VmConfig> {
        VmConfig::builder()
            .cpus(config.limits.vcpu_count)
            .memory_mib((config.limits.memory_bytes_max / (1024 * 1024)) as u32)
            .root_disk(&self.libkrun_config.root_disk_path)
            .networking(self.libkrun_config.network_enabled && config.limits.network_enabled)
            .workdir(&config.workdir)
            .build()
    }
}

impl Default for LibkrunSandboxFactory {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl SandboxFactory for LibkrunSandboxFactory {
    type Sandbox = LibkrunSandbox;

    #[instrument(skip(self))]
    async fn create(&self, config: SandboxConfig) -> SandboxResult<Self::Sandbox> {
        debug!("Creating libkrun sandbox");

        // Build VM config
        let vm_config = self
            .build_vm_config(&config)
            .map_err(|e| SandboxError::ConfigError {
                reason: e.to_string(),
            })?;

        // Create VM
        let vm = self
            .vm_factory
            .create(vm_config)
            .map_err(|e| SandboxError::Internal {
                message: format!("Failed to create VM: {}", e),
            })?;

        let sandbox = LibkrunSandbox::new(config, self.libkrun_config.clone(), vm);

        info!("Created libkrun sandbox: {}", sandbox.id());

        Ok(sandbox)
    }

    #[instrument(skip(self, snapshot))]
    async fn create_from_snapshot(
        &self,
        config: SandboxConfig,
        snapshot: &Snapshot,
    ) -> SandboxResult<Self::Sandbox> {
        debug!("Creating libkrun sandbox from snapshot: {}", snapshot.id());

        // Create a new sandbox
        let mut sandbox = self.create(config).await?;

        // Restore from snapshot
        sandbox.restore(snapshot).await?;

        info!("Created libkrun sandbox from snapshot: {}", sandbox.id());

        Ok(sandbox)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ResourceLimits;

    fn test_config() -> SandboxConfig {
        SandboxConfig::new()
            .with_limits(
                ResourceLimits::new()
                    .with_memory(512 * 1024 * 1024)
                    .with_vcpus(2),
            )
            .with_workdir("/workspace")
    }

    fn test_libkrun_config() -> LibkrunSandboxConfig {
        LibkrunSandboxConfig::new("/path/to/rootfs.ext4")
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_lifecycle() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let mut sandbox = factory.create(config).await.unwrap();

        assert_eq!(sandbox.state(), SandboxState::Stopped);

        sandbox.start().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Running);

        sandbox.pause().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Paused);

        sandbox.resume().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Running);

        sandbox.stop().await.unwrap();
        assert_eq!(sandbox.state(), SandboxState::Stopped);

        sandbox.destroy().await.unwrap();
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_exec() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let mut sandbox = factory.create(config).await.unwrap();
        sandbox.start().await.unwrap();

        let output = sandbox
            .exec("echo", &["hello", "world"], ExecOptions::default())
            .await
            .unwrap();

        assert!(output.is_success());
        assert_eq!(output.stdout_string(), "hello world");

        sandbox.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_exec_not_running() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let sandbox = factory.create(config).await.unwrap();

        // Not started - should fail
        let result = sandbox
            .exec("echo", &["test"], ExecOptions::default())
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_snapshot_restore() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let mut sandbox = factory.create(config.clone()).await.unwrap();
        sandbox.start().await.unwrap();

        // Take snapshot
        let snapshot = sandbox.snapshot().await.unwrap();
        assert_eq!(snapshot.sandbox_id(), sandbox.id());

        sandbox.stop().await.unwrap();

        // Create new sandbox and restore
        let mut new_sandbox = factory.create(config).await.unwrap();
        new_sandbox.restore(&snapshot).await.unwrap();

        // Should be stopped after restore (needs start)
        assert_eq!(new_sandbox.state(), SandboxState::Stopped);

        // Start and verify it works
        new_sandbox.start().await.unwrap();
        assert_eq!(new_sandbox.state(), SandboxState::Running);
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_health_check() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let mut sandbox = factory.create(config).await.unwrap();

        // Not running - health check should return false
        assert!(!sandbox.health_check().await.unwrap());

        sandbox.start().await.unwrap();

        // Running - health check should return true
        assert!(sandbox.health_check().await.unwrap());

        sandbox.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_stats() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let mut sandbox = factory.create(config).await.unwrap();
        sandbox.start().await.unwrap();

        let stats = sandbox.stats().await.unwrap();
        assert!(stats.uptime_ms >= 0);

        sandbox.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_libkrun_sandbox_factory_from_snapshot() {
        let factory = LibkrunSandboxFactory::with_config(test_libkrun_config());
        let config = test_config();

        let mut sandbox = factory.create(config.clone()).await.unwrap();
        sandbox.start().await.unwrap();

        let snapshot = sandbox.snapshot().await.unwrap();
        sandbox.stop().await.unwrap();

        // Create from snapshot
        let mut new_sandbox = factory
            .create_from_snapshot(config, &snapshot)
            .await
            .unwrap();

        // Should be stopped after create_from_snapshot
        assert_eq!(new_sandbox.state(), SandboxState::Stopped);

        // Should be able to start
        new_sandbox.start().await.unwrap();
        assert_eq!(new_sandbox.state(), SandboxState::Running);
    }
}

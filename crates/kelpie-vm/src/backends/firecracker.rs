//! Firecracker VM backend for Kelpie
//!
//! TigerStyle: Explicit configuration mapping and snapshot encoding.

use crate::{
    ExecOptions as VmExecOptions, ExecOutput as VmExecOutput, VmConfig, VmError, VmFactory,
    VmInstance, VmResult, VmSnapshot, VmSnapshotMetadata, VmState,
};
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::teleport::VmSnapshotBlob;
pub use kelpie_sandbox::FirecrackerConfig;
use kelpie_sandbox::{
    ExecOptions as SandboxExecOptions, ExecOutput as SandboxExecOutput, FirecrackerSandbox,
    ResourceLimits, SandboxConfig, SandboxError,
};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use tokio::sync::Mutex as AsyncMutex;
use tracing::info;
use uuid::Uuid;

/// Firecracker VM factory
#[derive(Debug, Clone)]
pub struct FirecrackerVmFactory {
    base_config: FirecrackerConfig,
}

impl FirecrackerVmFactory {
    /// Create a new factory with a base Firecracker configuration
    pub fn new(base_config: FirecrackerConfig) -> Self {
        Self { base_config }
    }

    /// Create a Firecracker VM instance
    pub async fn create_vm(&self, config: VmConfig) -> VmResult<FirecrackerVm> {
        FirecrackerVm::new(config, &self.base_config).await
    }
}

impl Default for FirecrackerVmFactory {
    fn default() -> Self {
        Self::new(FirecrackerConfig::default())
    }
}

/// Firecracker VM instance backed by kelpie-sandbox
pub struct FirecrackerVm {
    id: String,
    config: VmConfig,
    sandbox: AsyncMutex<FirecrackerSandbox>,
    state: Mutex<VmState>,
    snapshot_dir: PathBuf,
}

impl FirecrackerVm {
    async fn new(config: VmConfig, base_config: &FirecrackerConfig) -> VmResult<Self> {
        if !cfg!(target_os = "linux") {
            return Err(VmError::CreateFailed {
                reason: "Firecracker backend requires Linux".to_string(),
            });
        }

        config.validate()?;

        let kernel_path =
            config
                .kernel_image_path
                .clone()
                .ok_or_else(|| VmError::ConfigInvalid {
                    reason: "kernel_image_path is required for Firecracker".to_string(),
                })?;

        let rootfs_path = config.root_disk_path.clone();

        if !Path::new(&kernel_path).exists() {
            return Err(VmError::ConfigInvalid {
                reason: format!("kernel image not found: {}", kernel_path),
            });
        }
        if !Path::new(&rootfs_path).exists() {
            return Err(VmError::RootDiskNotFound { path: rootfs_path });
        }

        let mut fc_config = base_config.clone();
        fc_config.kernel_image = PathBuf::from(kernel_path);
        fc_config.rootfs_image = PathBuf::from(&config.root_disk_path);
        if let Some(args) = &config.kernel_args {
            fc_config.kernel_args = args.clone();
        }

        fc_config.validate().map_err(|err| map_sandbox_error(err))?;

        let limits = ResourceLimits::default()
            .with_vcpus(config.vcpu_count)
            .with_memory((config.memory_mib as u64) * 1024 * 1024)
            .with_network(config.networking_enabled);

        let mut sandbox_config = SandboxConfig::default().with_limits(limits);
        if let Some(workdir) = &config.workdir {
            sandbox_config = sandbox_config.with_workdir(workdir.clone());
        }
        for (key, value) in &config.env_vars {
            sandbox_config = sandbox_config.with_env(key.clone(), value.clone());
        }
        sandbox_config = sandbox_config.with_image(config.root_disk_path.clone());

        let sandbox = FirecrackerSandbox::new(sandbox_config, fc_config.clone())
            .await
            .map_err(map_sandbox_error)?;

        Ok(Self {
            id: format!("fc-{}", Uuid::new_v4()),
            config,
            sandbox: AsyncMutex::new(sandbox),
            state: Mutex::new(VmState::Created),
            snapshot_dir: fc_config.snapshot_dir,
        })
    }

    fn set_state(&self, next: VmState) {
        if let Ok(mut state) = self.state.lock() {
            *state = next;
        }
    }

    fn snapshot_paths(base_path: &Path) -> (PathBuf, PathBuf) {
        (
            base_path.with_extension("state"),
            base_path.with_extension("mem"),
        )
    }

    async fn read_snapshot_blob(&self, base_path: &Path) -> VmResult<Bytes> {
        let (state_path, mem_path) = Self::snapshot_paths(base_path);
        let state_bytes =
            tokio::fs::read(&state_path)
                .await
                .map_err(|e| VmError::SnapshotFailed {
                    reason: format!("failed reading snapshot state: {}", e),
                })?;
        let mem_bytes = tokio::fs::read(&mem_path)
            .await
            .map_err(|e| VmError::SnapshotFailed {
                reason: format!("failed reading snapshot memory: {}", e),
            })?;

        self.cleanup_snapshot_files(&state_path, &mem_path).await;

        Ok(VmSnapshotBlob::encode(
            Bytes::new(),
            Bytes::from(state_bytes),
            Bytes::from(mem_bytes),
        ))
    }

    async fn write_snapshot_blob(&self, snapshot: &VmSnapshot) -> VmResult<PathBuf> {
        let decoded =
            VmSnapshotBlob::decode(&snapshot.data).map_err(|err| VmError::RestoreFailed {
                reason: format!("failed to decode snapshot blob: {}", err),
            })?;

        let snapshot_id = format!("restore-{}", snapshot.metadata.snapshot_id);
        let base_path = self.snapshot_dir.join(snapshot_id);
        tokio::fs::create_dir_all(&self.snapshot_dir)
            .await
            .map_err(|e| VmError::RestoreFailed {
                reason: format!("failed to create snapshot dir: {}", e),
            })?;

        let (state_path, mem_path) = Self::snapshot_paths(&base_path);
        tokio::fs::write(&state_path, &decoded.snapshot_bytes)
            .await
            .map_err(|e| VmError::RestoreFailed {
                reason: format!("failed to write snapshot state: {}", e),
            })?;
        tokio::fs::write(&mem_path, &decoded.memory_bytes)
            .await
            .map_err(|e| VmError::RestoreFailed {
                reason: format!("failed to write snapshot memory: {}", e),
            })?;

        Ok(base_path)
    }

    async fn cleanup_snapshot_files(&self, state_path: &Path, mem_path: &Path) {
        let _ = tokio::fs::remove_file(state_path).await;
        let _ = tokio::fs::remove_file(mem_path).await;
    }
}

#[async_trait]
impl VmFactory for FirecrackerVmFactory {
    async fn create(&self, config: VmConfig) -> VmResult<Box<dyn VmInstance>> {
        let vm = self.create_vm(config).await?;
        Ok(Box::new(vm))
    }
}

#[async_trait]
impl VmInstance for FirecrackerVm {
    fn id(&self) -> &str {
        &self.id
    }

    fn state(&self) -> VmState {
        match self.state.lock() {
            Ok(state) => *state,
            Err(_) => VmState::Crashed,
        }
    }

    fn config(&self) -> &VmConfig {
        &self.config
    }

    async fn start(&mut self) -> VmResult<()> {
        let current = self.state();
        if matches!(
            current,
            VmState::Running | VmState::Starting | VmState::Paused
        ) {
            return Err(VmError::AlreadyRunning);
        }

        self.set_state(VmState::Starting);
        let mut sandbox = self.sandbox.lock().await;
        match sandbox.start().await.map_err(map_sandbox_error) {
            Ok(()) => {
                self.set_state(VmState::Running);
                Ok(())
            }
            Err(err) => {
                self.set_state(VmState::Crashed);
                Err(err)
            }
        }
    }

    async fn stop(&mut self) -> VmResult<()> {
        let current = self.state();
        if !matches!(current, VmState::Running | VmState::Paused) {
            return Err(VmError::NotRunning {
                state: current.to_string(),
            });
        }

        let mut sandbox = self.sandbox.lock().await;
        match sandbox.stop().await.map_err(map_sandbox_error) {
            Ok(()) => {
                self.set_state(VmState::Stopped);
                Ok(())
            }
            Err(err) => {
                self.set_state(VmState::Crashed);
                Err(err)
            }
        }
    }

    async fn pause(&mut self) -> VmResult<()> {
        let current = self.state();
        if current != VmState::Running {
            return Err(VmError::PauseFailed {
                reason: format!("cannot pause from state {}", current),
            });
        }

        let mut sandbox = self.sandbox.lock().await;
        match sandbox.pause().await.map_err(map_sandbox_error) {
            Ok(()) => {
                self.set_state(VmState::Paused);
                Ok(())
            }
            Err(err) => {
                self.set_state(VmState::Crashed);
                Err(err)
            }
        }
    }

    async fn resume(&mut self) -> VmResult<()> {
        let current = self.state();
        if current != VmState::Paused {
            return Err(VmError::ResumeFailed {
                reason: format!("cannot resume from state {}", current),
            });
        }

        let mut sandbox = self.sandbox.lock().await;
        match sandbox.resume().await.map_err(map_sandbox_error) {
            Ok(()) => {
                self.set_state(VmState::Running);
                Ok(())
            }
            Err(err) => {
                self.set_state(VmState::Crashed);
                Err(err)
            }
        }
    }

    async fn exec(&self, cmd: &str, args: &[&str]) -> VmResult<VmExecOutput> {
        self.exec_with_options(cmd, args, VmExecOptions::default())
            .await
    }

    async fn exec_with_options(
        &self,
        cmd: &str,
        args: &[&str],
        options: VmExecOptions,
    ) -> VmResult<VmExecOutput> {
        let current = self.state();
        if current != VmState::Running {
            return Err(VmError::NotRunning {
                state: current.to_string(),
            });
        }

        let sandbox_options = to_sandbox_exec_options(options);
        let sandbox = self.sandbox.lock().await;
        let output = sandbox
            .exec(cmd, args, sandbox_options)
            .await
            .map_err(map_sandbox_error)?;

        Ok(map_exec_output(output))
    }

    async fn snapshot(&self) -> VmResult<VmSnapshot> {
        let current = self.state();
        if !matches!(current, VmState::Running | VmState::Paused) {
            return Err(VmError::SnapshotFailed {
                reason: format!("cannot snapshot from state {}", current),
            });
        }

        let sandbox = self.sandbox.lock().await;
        let snapshot = sandbox.snapshot().await.map_err(map_sandbox_error)?;
        let disk_ref = snapshot
            .disk_reference
            .as_ref()
            .ok_or_else(|| VmError::SnapshotFailed {
                reason: "snapshot missing disk reference".to_string(),
            })?;
        let base_path = PathBuf::from(disk_ref);
        drop(sandbox);

        let snapshot_blob = self.read_snapshot_blob(&base_path).await?;
        let checksum = crc32fast::hash(&snapshot_blob);
        let size_bytes = snapshot_blob.len() as u64;
        let metadata = VmSnapshotMetadata::new(
            snapshot.id().to_string(),
            self.id.clone(),
            size_bytes,
            checksum,
            std::env::consts::ARCH.to_string(),
            self.config.vcpu_count,
            self.config.memory_mib,
        );
        let vm_snapshot = VmSnapshot::new(metadata, snapshot_blob)?;
        info!(vm_id = %self.id, snapshot_id = %snapshot.id(), "Firecracker snapshot captured");
        Ok(vm_snapshot)
    }

    async fn restore(&mut self, snapshot: &VmSnapshot) -> VmResult<()> {
        if !snapshot.verify_checksum() {
            return Err(VmError::SnapshotCorrupted);
        }

        let base_path = self.write_snapshot_blob(snapshot).await?;
        let sandbox_snapshot = kelpie_sandbox::Snapshot::teleport(self.id.clone())
            .with_disk_reference(base_path.to_string_lossy().to_string());

        self.set_state(VmState::Starting);
        let mut sandbox = self.sandbox.lock().await;
        let result = sandbox.restore(&sandbox_snapshot).await;
        let (state_path, mem_path) = Self::snapshot_paths(&base_path);
        self.cleanup_snapshot_files(&state_path, &mem_path).await;

        match result {
            Ok(()) => {
                self.set_state(VmState::Running);
                Ok(())
            }
            Err(err) => {
                self.set_state(VmState::Crashed);
                Err(map_sandbox_error(err))
            }
        }
    }
}

fn to_sandbox_exec_options(options: VmExecOptions) -> SandboxExecOptions {
    let mut sandbox_options = SandboxExecOptions::default();
    sandbox_options.timeout_ms = options.timeout_ms;
    sandbox_options.workdir = options.workdir;
    sandbox_options.env = options.env;
    sandbox_options.stdin = options.stdin;
    sandbox_options
}

fn map_exec_output(output: SandboxExecOutput) -> VmExecOutput {
    VmExecOutput::new(output.status.code, output.stdout, output.stderr)
}

fn map_sandbox_error(err: SandboxError) -> VmError {
    match err {
        SandboxError::ConfigError { reason } => VmError::ConfigInvalid { reason },
        SandboxError::InvalidState { current, .. } => VmError::NotRunning { state: current },
        SandboxError::ExecFailed { reason, .. } => VmError::ExecFailed { reason },
        SandboxError::ExecTimeout { timeout_ms, .. } => VmError::ExecTimeout { timeout_ms },
        SandboxError::SnapshotFailed { reason, .. } => VmError::SnapshotFailed { reason },
        SandboxError::RestoreFailed { reason } => VmError::RestoreFailed { reason },
        SandboxError::IoError { reason } => VmError::Internal { reason },
        SandboxError::Internal { message } => VmError::Internal { reason: message },
        other => VmError::Internal {
            reason: other.to_string(),
        },
    }
}

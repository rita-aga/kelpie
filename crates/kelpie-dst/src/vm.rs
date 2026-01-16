//! Simulated VM implementation for deterministic testing
//!
//! TigerStyle: Deterministic VM state machine with explicit fault injection.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use async_trait::async_trait;
use bytes::Bytes;
use tokio::sync::RwLock;

use crate::clock::SimClock;
use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use kelpie_vm::{
    VmConfig, VmError, VmExecOptions as ExecOptions, VmExecOutput as ExecOutput, VmFactory,
    VmInstance, VmResult, VmSnapshot, VmSnapshotMetadata, VmState, VM_EXEC_TIMEOUT_MS_DEFAULT,
    VM_SNAPSHOT_SIZE_BYTES_MAX,
};

/// Simulated VM instance with deterministic behavior
pub struct SimVm {
    id: String,
    config: VmConfig,
    state: VmState,
    faults: Arc<FaultInjector>,
    clock: Arc<SimClock>,
    memory: Arc<RwLock<Bytes>>,
    architecture: String,
    exec_counter: AtomicU64,
    snapshot_counter: AtomicU64,
}

impl SimVm {
    /// Create a new simulated VM
    pub fn new(
        id: String,
        config: VmConfig,
        faults: Arc<FaultInjector>,
        clock: Arc<SimClock>,
        architecture: String,
    ) -> VmResult<Self> {
        config.validate()?;

        Ok(Self {
            id,
            config,
            state: VmState::Created,
            faults,
            clock,
            memory: Arc::new(RwLock::new(Bytes::new())),
            architecture: Self::normalize_architecture(&architecture),
            exec_counter: AtomicU64::new(0),
            snapshot_counter: AtomicU64::new(0),
        })
    }

    fn check_fault(&self, operation: &str) -> Option<FaultType> {
        self.faults.should_inject(operation)
    }

    fn normalize_architecture(arch: &str) -> String {
        match arch {
            "arm64" => "aarch64".to_string(),
            "aarch64" => "aarch64".to_string(),
            "x86_64" => "x86_64".to_string(),
            other => other.to_string(),
        }
    }

    async fn build_snapshot(&self, corrupt_checksum: bool) -> VmResult<VmSnapshot> {
        assert!(self.config.vcpu_count > 0, "vcpu_count must be positive");
        assert!(self.config.memory_mib > 0, "memory_mib must be positive");

        let data = { self.memory.read().await.clone() };
        let size_bytes = data.len() as u64;
        let checksum = if corrupt_checksum {
            crc32fast::hash(&data).wrapping_add(1)
        } else {
            crc32fast::hash(&data)
        };
        let snapshot_id = format!(
            "sim-snap-{}",
            self.snapshot_counter.fetch_add(1, Ordering::SeqCst)
        );

        let metadata = VmSnapshotMetadata {
            snapshot_id,
            vm_id: self.id.clone(),
            created_at_ms: self.clock.now_ms(),
            size_bytes,
            checksum,
            architecture: self.architecture.clone(),
            vcpu_count: self.config.vcpu_count,
            memory_mib: self.config.memory_mib,
            is_full_snapshot: true,
        };

        VmSnapshot::new(metadata, data)
    }
}

#[async_trait]
impl VmInstance for SimVm {
    fn id(&self) -> &str {
        &self.id
    }

    fn state(&self) -> VmState {
        self.state
    }

    fn config(&self) -> &VmConfig {
        &self.config
    }

    async fn start(&mut self) -> VmResult<()> {
        assert!(!self.id.is_empty(), "vm id must not be empty");
        assert!(self.config.vcpu_count > 0, "vcpu_count must be positive");

        if self.state != VmState::Created && self.state != VmState::Stopped {
            if self.state == VmState::Running {
                return Err(VmError::AlreadyRunning);
            }
            return Err(VmError::CreateFailed {
                reason: format!("cannot start from state {:?}", self.state),
            });
        }

        if let Some(fault) = self.check_fault("vm_start") {
            match fault {
                FaultType::SandboxBootFail => {
                    self.state = VmState::Crashed;
                    return Err(VmError::BootFailed {
                        reason: "simulated boot failure".to_string(),
                    });
                }
                FaultType::SandboxCrash => {
                    self.state = VmState::Crashed;
                    return Err(VmError::Crashed {
                        reason: "simulated crash during start".to_string(),
                    });
                }
                _ => {}
            }
        }

        self.state = VmState::Running;
        assert_eq!(self.state, VmState::Running);

        Ok(())
    }

    async fn stop(&mut self) -> VmResult<()> {
        assert!(!self.id.is_empty());
        assert!(self.config.memory_mib > 0, "memory_mib must be positive");

        if self.state != VmState::Running && self.state != VmState::Paused {
            return Err(VmError::CreateFailed {
                reason: format!("cannot stop from state {:?}", self.state),
            });
        }

        self.state = VmState::Stopped;
        assert_eq!(self.state, VmState::Stopped);

        Ok(())
    }

    async fn pause(&mut self) -> VmResult<()> {
        assert!(!self.id.is_empty());
        assert!(self.config.vcpu_count > 0, "vcpu_count must be positive");

        if self.state != VmState::Running {
            return Err(VmError::NotRunning {
                state: self.state.to_string(),
            });
        }

        if let Some(fault) = self.check_fault("vm_pause") {
            if matches!(fault, FaultType::SandboxPauseFail) {
                return Err(VmError::PauseFailed {
                    reason: "simulated pause failure".to_string(),
                });
            }
        }

        self.state = VmState::Paused;
        assert_eq!(self.state, VmState::Paused);

        Ok(())
    }

    async fn resume(&mut self) -> VmResult<()> {
        assert!(!self.id.is_empty());
        assert!(self.config.vcpu_count > 0, "vcpu_count must be positive");

        if self.state != VmState::Paused {
            return Err(VmError::ResumeFailed {
                reason: format!("cannot resume from state {:?}", self.state),
            });
        }

        if let Some(fault) = self.check_fault("vm_resume") {
            if matches!(fault, FaultType::SandboxResumeFail) {
                return Err(VmError::ResumeFailed {
                    reason: "simulated resume failure".to_string(),
                });
            }
        }

        self.state = VmState::Running;
        assert_eq!(self.state, VmState::Running);

        Ok(())
    }

    async fn exec(&self, cmd: &str, args: &[&str]) -> VmResult<ExecOutput> {
        self.exec_with_options(cmd, args, ExecOptions::default())
            .await
    }

    async fn exec_with_options(
        &self,
        cmd: &str,
        args: &[&str],
        options: ExecOptions,
    ) -> VmResult<ExecOutput> {
        assert!(!cmd.is_empty());
        assert!(self.config.vcpu_count > 0, "vcpu_count must be positive");

        if self.state != VmState::Running {
            return Err(VmError::NotRunning {
                state: self.state.to_string(),
            });
        }

        if let Some(fault) = self.check_fault("vm_exec") {
            match fault {
                FaultType::SandboxExecFail => {
                    return Err(VmError::ExecFailed {
                        reason: "simulated exec failure".to_string(),
                    });
                }
                FaultType::SandboxExecTimeout { timeout_ms } => {
                    return Err(VmError::ExecTimeout { timeout_ms });
                }
                _ => {}
            }
        }

        let exec_id = self.exec_counter.fetch_add(1, Ordering::SeqCst);
        let stdout = format!("sim:{}:{}:{}", exec_id, cmd, args.join(" "));
        let stderr = String::new();

        let mut memory = self.memory.write().await;
        *memory = Bytes::from(stdout.clone());
        drop(memory);

        let timeout_ms = options.timeout_ms.unwrap_or(VM_EXEC_TIMEOUT_MS_DEFAULT);
        assert!(timeout_ms > 0, "timeout must be positive");

        Ok(ExecOutput::new(0, stdout, stderr))
    }

    async fn snapshot(&self) -> VmResult<VmSnapshot> {
        assert!(!self.id.is_empty());
        assert!(VM_SNAPSHOT_SIZE_BYTES_MAX > 0);

        if self.state != VmState::Running && self.state != VmState::Paused {
            return Err(VmError::SnapshotFailed {
                reason: format!("cannot snapshot from state {:?}", self.state),
            });
        }

        if let Some(fault) = self.check_fault("vm_snapshot") {
            match fault {
                FaultType::SnapshotCreateFail => {
                    return Err(VmError::SnapshotFailed {
                        reason: "simulated snapshot failure".to_string(),
                    });
                }
                FaultType::SnapshotTooLarge { max_bytes } => {
                    let size_bytes = max_bytes.saturating_add(1);
                    return Err(VmError::SnapshotTooLarge {
                        size_bytes,
                        max_bytes,
                    });
                }
                FaultType::SnapshotCorruption => {
                    return self.build_snapshot(true).await;
                }
                _ => {}
            }
        }

        let snapshot = self.build_snapshot(false).await?;
        let size_bytes = snapshot.size_bytes();
        if size_bytes > VM_SNAPSHOT_SIZE_BYTES_MAX {
            return Err(VmError::SnapshotTooLarge {
                size_bytes,
                max_bytes: VM_SNAPSHOT_SIZE_BYTES_MAX,
            });
        }

        Ok(snapshot)
    }

    async fn restore(&mut self, snapshot: &VmSnapshot) -> VmResult<()> {
        assert!(!self.id.is_empty());
        assert!(snapshot.metadata.size_bytes == snapshot.data.len() as u64);

        if self.state != VmState::Created && self.state != VmState::Stopped {
            return Err(VmError::RestoreFailed {
                reason: format!("cannot restore to state {:?}", self.state),
            });
        }

        if let Some(fault) = self.check_fault("vm_restore") {
            match fault {
                FaultType::SnapshotRestoreFail => {
                    return Err(VmError::RestoreFailed {
                        reason: "simulated restore failure".to_string(),
                    });
                }
                FaultType::SnapshotCorruption => {
                    return Err(VmError::SnapshotCorrupted);
                }
                _ => {}
            }
        }

        if !snapshot.verify_checksum() {
            return Err(VmError::SnapshotCorrupted);
        }

        let arch = Self::normalize_architecture(&self.architecture);
        if !snapshot.metadata.is_compatible_with(&arch) {
            return Err(VmError::RestoreFailed {
                reason: format!(
                    "architecture mismatch: snapshot is {} but VM is {}",
                    snapshot.metadata.architecture, arch
                ),
            });
        }

        let mut memory = self.memory.write().await;
        *memory = snapshot.data.clone();
        drop(memory);

        self.state = VmState::Stopped;
        assert_eq!(self.state, VmState::Stopped);

        Ok(())
    }
}

/// Factory for creating simulated VMs
pub struct SimVmFactory {
    faults: Arc<FaultInjector>,
    clock: Arc<SimClock>,
    id_counter: AtomicU64,
    architecture: String,
}

impl SimVmFactory {
    /// Create a new simulated VM factory
    pub fn new(
        _rng: Arc<DeterministicRng>,
        faults: Arc<FaultInjector>,
        clock: Arc<SimClock>,
    ) -> Self {
        Self {
            faults,
            clock,
            id_counter: AtomicU64::new(1),
            architecture: "aarch64".to_string(),
        }
    }

    /// Override the architecture used for snapshots
    pub fn with_architecture(mut self, arch: impl Into<String>) -> Self {
        let arch = arch.into();
        self.architecture = SimVm::normalize_architecture(&arch);
        self
    }

    /// Create a new simulated VM
    pub async fn create_vm(&self, config: VmConfig) -> VmResult<SimVm> {
        let id = format!("sim-vm-{}", self.id_counter.fetch_add(1, Ordering::SeqCst));
        SimVm::new(
            id,
            config,
            self.faults.clone(),
            self.clock.clone(),
            self.architecture.clone(),
        )
    }

    /// Create a new simulated VM and restore from snapshot
    pub async fn create_vm_from_snapshot(
        &self,
        config: VmConfig,
        snapshot: &VmSnapshot,
    ) -> VmResult<SimVm> {
        let mut vm = self.create_vm(config).await?;
        vm.restore(snapshot).await?;
        Ok(vm)
    }
}

#[async_trait]
impl VmFactory for SimVmFactory {
    async fn create(&self, config: VmConfig) -> VmResult<Box<dyn VmInstance>> {
        let vm = self.create_vm(config).await?;
        Ok(Box::new(vm))
    }
}

//! Apple Virtualization.framework backend
//!
//! TigerStyle: Explicit lifecycle, snapshot handling, and vsock exec.

use async_trait::async_trait;
use bytes::Bytes;
use libc::{c_char, c_int};
use serde_json::Value;
use std::ffi::{CStr, CString};
use std::mem::ManuallyDrop;
use std::os::unix::io::FromRawFd;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::UnixStream;
use tracing::info;
use uuid::Uuid;

use crate::error::{VmError, VmResult};
use crate::snapshot::{VmSnapshot, VmSnapshotMetadata};
use crate::traits::{
    ExecOptions as VmExecOptions, ExecOutput as VmExecOutput, VmFactory, VmInstance, VmState,
};
use crate::{VmConfig, VM_EXEC_TIMEOUT_MS_DEFAULT};
use kelpie_core::Runtime;

#[repr(C)]
struct KelpieVzVmHandle {
    _private: [u8; 0],
}

#[link(name = "kelpie_vz_bridge", kind = "static")]
extern "C" {
    fn kelpie_vz_is_supported() -> bool;
    fn kelpie_vz_vm_create(
        id: *const c_char,
        kernel_path: *const c_char,
        initrd_path: *const c_char,
        rootfs_path: *const c_char,
        boot_args: *const c_char,
        rootfs_readonly: bool,
        vcpu_count: u32,
        memory_mib: u64,
        error_out: *mut *mut c_char,
    ) -> *mut KelpieVzVmHandle;
    fn kelpie_vz_vm_free(vm: *mut KelpieVzVmHandle);
    fn kelpie_vz_vm_start(vm: *mut KelpieVzVmHandle, error_out: *mut *mut c_char) -> c_int;
    fn kelpie_vz_vm_stop(vm: *mut KelpieVzVmHandle, error_out: *mut *mut c_char) -> c_int;
    fn kelpie_vz_vm_pause(vm: *mut KelpieVzVmHandle, error_out: *mut *mut c_char) -> c_int;
    fn kelpie_vz_vm_resume(vm: *mut KelpieVzVmHandle, error_out: *mut *mut c_char) -> c_int;
    fn kelpie_vz_vm_save_state(
        vm: *mut KelpieVzVmHandle,
        path: *const c_char,
        error_out: *mut *mut c_char,
    ) -> c_int;
    fn kelpie_vz_vm_restore_state(
        vm: *mut KelpieVzVmHandle,
        path: *const c_char,
        error_out: *mut *mut c_char,
    ) -> c_int;
    fn kelpie_vz_vm_connect_vsock(
        vm: *mut KelpieVzVmHandle,
        port: u32,
        error_out: *mut *mut c_char,
    ) -> c_int;
    fn kelpie_vz_vm_close_vsock(
        vm: *mut KelpieVzVmHandle,
        fd: c_int,
        error_out: *mut *mut c_char,
    ) -> c_int;
    fn kelpie_vz_string_free(string: *mut c_char);
}

/// Default vsock port for Kelpie guest agent (matches guest agent default)
pub const VZ_VSOCK_PORT_DEFAULT: u32 = 9001;

/// VZ backend configuration
#[derive(Debug, Clone)]
pub struct VzConfig {
    /// Port for guest agent vsock connection
    pub vsock_port: u32,
    /// Directory for snapshot files
    pub snapshot_dir: PathBuf,
}

impl Default for VzConfig {
    fn default() -> Self {
        Self {
            vsock_port: VZ_VSOCK_PORT_DEFAULT,
            snapshot_dir: std::env::temp_dir().join("kelpie-vz-snapshots"),
        }
    }
}

/// Factory for creating VZ virtual machines
#[derive(Debug, Clone)]
pub struct VzVmFactory {
    config: VzConfig,
}

impl VzVmFactory {
    /// Create a new factory
    pub fn new(config: VzConfig) -> Self {
        Self { config }
    }

    /// Create a new VZ VM
    pub async fn create_vm(&self, config: VmConfig) -> VmResult<VzVm> {
        VzVm::new(config, self.config.clone())
    }
}

impl Default for VzVmFactory {
    fn default() -> Self {
        Self::new(VzConfig::default())
    }
}

/// VZ virtual machine implementation
#[derive(Debug)]
pub struct VzVm {
    id: String,
    config: VmConfig,
    state: Mutex<VmState>,
    handle: *mut KelpieVzVmHandle,
    vz_config: VzConfig,
}

unsafe impl Send for VzVm {}
unsafe impl Sync for VzVm {}

impl VzVm {
    fn new(config: VmConfig, vz_config: VzConfig) -> VmResult<Self> {
        if !cfg!(target_os = "macos") {
            return Err(VmError::CreateFailed {
                reason: "Apple VZ backend requires macOS".to_string(),
            });
        }

        if !unsafe { kelpie_vz_is_supported() } {
            return Err(VmError::CreateFailed {
                reason: "Virtualization.framework is not supported on this host".to_string(),
            });
        }

        config.validate()?;
        let kernel_path =
            config
                .kernel_image_path
                .clone()
                .ok_or_else(|| VmError::ConfigInvalid {
                    reason: "kernel_image_path is required for VZ".to_string(),
                })?;

        let id = format!("vz-{}", Uuid::new_v4());
        let id_c = CString::new(id.clone()).map_err(|e| VmError::ConfigInvalid {
            reason: format!("invalid vm id: {}", e),
        })?;
        let kernel_c = CString::new(kernel_path).map_err(|e| VmError::ConfigInvalid {
            reason: format!("invalid kernel path: {}", e),
        })?;
        let rootfs_c =
            CString::new(config.root_disk_path.clone()).map_err(|e| VmError::ConfigInvalid {
                reason: format!("invalid rootfs path: {}", e),
            })?;
        let initrd_c = match config.initrd_path.as_ref() {
            Some(path) => Some(
                CString::new(path.clone()).map_err(|e| VmError::ConfigInvalid {
                    reason: format!("invalid initrd path: {}", e),
                })?,
            ),
            None => None,
        };
        let boot_args = config.kernel_args.clone().unwrap_or_default();
        let boot_args_c = CString::new(boot_args).map_err(|e| VmError::ConfigInvalid {
            reason: format!("invalid boot args: {}", e),
        })?;

        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let handle = unsafe {
            kelpie_vz_vm_create(
                id_c.as_ptr(),
                kernel_c.as_ptr(),
                initrd_c
                    .as_ref()
                    .map(|c| c.as_ptr())
                    .unwrap_or(std::ptr::null()),
                rootfs_c.as_ptr(),
                boot_args_c.as_ptr(),
                config.root_disk_readonly,
                config.vcpu_count,
                config.memory_mib as u64,
                &mut error_ptr,
            )
        };

        if handle.is_null() {
            return Err(VmError::CreateFailed {
                reason: take_error("vz create", error_ptr),
            });
        }

        Ok(Self {
            id,
            config,
            state: Mutex::new(VmState::Created),
            handle,
            vz_config,
        })
    }

    fn set_state(&self, next: VmState) {
        if let Ok(mut state) = self.state.lock() {
            *state = next;
        }
    }

    fn snapshot_path(&self, snapshot_id: &str) -> PathBuf {
        self.vz_config
            .snapshot_dir
            .join(format!("{}.vzstate", snapshot_id))
    }

    async fn save_state_to_path(&self, path: &Path) -> VmResult<()> {
        tokio::fs::create_dir_all(&self.vz_config.snapshot_dir)
            .await
            .map_err(|e| VmError::SnapshotFailed {
                reason: format!("failed to create snapshot dir: {}", e),
            })?;

        let path_c = CString::new(path.to_string_lossy().to_string()).map_err(|e| {
            VmError::SnapshotFailed {
                reason: format!("invalid snapshot path: {}", e),
            }
        })?;

        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result =
            unsafe { kelpie_vz_vm_save_state(self.handle, path_c.as_ptr(), &mut error_ptr) };
        if result != 0 {
            return Err(VmError::SnapshotFailed {
                reason: take_error("vz save", error_ptr),
            });
        }

        Ok(())
    }

    async fn restore_state_from_path(&self, path: &Path) -> VmResult<()> {
        let path_c = CString::new(path.to_string_lossy().to_string()).map_err(|e| {
            VmError::RestoreFailed {
                reason: format!("invalid snapshot path: {}", e),
            }
        })?;

        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result =
            unsafe { kelpie_vz_vm_restore_state(self.handle, path_c.as_ptr(), &mut error_ptr) };
        if result != 0 {
            return Err(VmError::RestoreFailed {
                reason: take_error("vz restore", error_ptr),
            });
        }

        Ok(())
    }

    async fn exec_via_vsock(
        &self,
        cmd: &str,
        args: &[&str],
        options: VmExecOptions,
    ) -> VmResult<VmExecOutput> {
        let fd = {
            let mut error_ptr: *mut c_char = std::ptr::null_mut();
            let fd = unsafe {
                kelpie_vz_vm_connect_vsock(self.handle, self.vz_config.vsock_port, &mut error_ptr)
            };
            if fd < 0 {
                return Err(VmError::ExecFailed {
                    reason: take_error("vz vsock connect", error_ptr),
                });
            }
            fd
        };

        let stream = unsafe { std::os::unix::net::UnixStream::from_raw_fd(fd) };
        stream
            .set_nonblocking(true)
            .map_err(|e| VmError::ExecFailed {
                reason: format!("failed to set vsock nonblocking: {}", e),
            })?;
        let stream = UnixStream::from_std(stream).map_err(|e| VmError::ExecFailed {
            reason: format!("failed to wrap vsock stream: {}", e),
        })?;
        let mut stream = ManuallyDrop::new(stream);
        let _guard = VzVsockGuard::new(self.handle, fd);

        let request = serde_json::json!({
            "type": "exec",
            "command": cmd,
            "args": args,
            "env": options.env,
            "cwd": options.workdir,
            "timeout_ms": options.timeout_ms,
        });
        let request_bytes = serde_json::to_vec(&request).map_err(|e| VmError::ExecFailed {
            reason: format!("failed to serialize exec request: {}", e),
        })?;
        let len_bytes = (request_bytes.len() as u32).to_be_bytes();
        stream
            .write_all(&len_bytes)
            .await
            .map_err(|e| VmError::ExecFailed {
                reason: format!("failed to write exec length: {}", e),
            })?;
        stream
            .write_all(&request_bytes)
            .await
            .map_err(|e| VmError::ExecFailed {
                reason: format!("failed to write exec request: {}", e),
            })?;

        let mut len_buf = [0u8; 4];
        stream
            .read_exact(&mut len_buf)
            .await
            .map_err(|e| VmError::ExecFailed {
                reason: format!("failed to read response length: {}", e),
            })?;
        let response_len = u32::from_be_bytes(len_buf) as usize;
        let mut response_buf = vec![0u8; response_len];
        stream
            .read_exact(&mut response_buf)
            .await
            .map_err(|e| VmError::ExecFailed {
                reason: format!("failed to read response: {}", e),
            })?;

        let response: Value =
            serde_json::from_slice(&response_buf).map_err(|e| VmError::ExecFailed {
                reason: format!("failed to parse exec response: {}", e),
            })?;

        let exit_code = response
            .get("exit_code")
            .and_then(|v| v.as_i64())
            .unwrap_or(-1) as i32;
        let stdout = response
            .get("stdout")
            .and_then(|v| v.as_str())
            .map(|value| value.as_bytes().to_vec())
            .unwrap_or_default();
        let stderr = response
            .get("stderr")
            .and_then(|v| v.as_str())
            .map(|value| value.as_bytes().to_vec())
            .unwrap_or_default();

        Ok(VmExecOutput::new(exit_code, stdout, stderr))
    }
}

impl Drop for VzVm {
    fn drop(&mut self) {
        unsafe {
            kelpie_vz_vm_free(self.handle);
        }
    }
}

#[async_trait]
impl VmFactory for VzVmFactory {
    async fn create(&self, config: VmConfig) -> VmResult<Box<dyn VmInstance>> {
        let vm = self.create_vm(config).await?;
        Ok(Box::new(vm))
    }
}

#[async_trait]
impl VmInstance for VzVm {
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
        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result = unsafe { kelpie_vz_vm_start(self.handle, &mut error_ptr) };
        if result != 0 {
            self.set_state(VmState::Crashed);
            return Err(VmError::BootFailed {
                reason: take_error("vz start", error_ptr),
            });
        }

        self.set_state(VmState::Running);
        Ok(())
    }

    async fn stop(&mut self) -> VmResult<()> {
        let current = self.state();
        if !matches!(current, VmState::Running | VmState::Paused) {
            return Err(VmError::NotRunning {
                state: current.to_string(),
            });
        }

        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result = unsafe { kelpie_vz_vm_stop(self.handle, &mut error_ptr) };
        if result != 0 {
            self.set_state(VmState::Crashed);
            return Err(VmError::Crashed {
                reason: take_error("vz stop", error_ptr),
            });
        }

        self.set_state(VmState::Stopped);
        Ok(())
    }

    async fn pause(&mut self) -> VmResult<()> {
        let current = self.state();
        if current != VmState::Running {
            return Err(VmError::PauseFailed {
                reason: format!("cannot pause from state {}", current),
            });
        }

        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result = unsafe { kelpie_vz_vm_pause(self.handle, &mut error_ptr) };
        if result != 0 {
            return Err(VmError::PauseFailed {
                reason: take_error("vz pause", error_ptr),
            });
        }

        self.set_state(VmState::Paused);
        Ok(())
    }

    async fn resume(&mut self) -> VmResult<()> {
        let current = self.state();
        if current != VmState::Paused {
            return Err(VmError::ResumeFailed {
                reason: format!("cannot resume from state {}", current),
            });
        }

        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result = unsafe { kelpie_vz_vm_resume(self.handle, &mut error_ptr) };
        if result != 0 {
            return Err(VmError::ResumeFailed {
                reason: take_error("vz resume", error_ptr),
            });
        }

        self.set_state(VmState::Running);
        Ok(())
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

        let timeout_ms = options.timeout_ms.unwrap_or(VM_EXEC_TIMEOUT_MS_DEFAULT);
        if timeout_ms == 0 {
            return Err(VmError::ExecTimeout { timeout_ms });
        }

        let result = kelpie_core::current_runtime()
            .timeout(
                std::time::Duration::from_millis(timeout_ms),
                self.exec_via_vsock(cmd, args, options),
            )
            .await;

        match result {
            Ok(result) => result,
            Err(_) => Err(VmError::ExecTimeout { timeout_ms }),
        }
    }

    async fn snapshot(&self) -> VmResult<VmSnapshot> {
        let current = self.state();
        if !matches!(current, VmState::Running | VmState::Paused) {
            return Err(VmError::SnapshotFailed {
                reason: format!("cannot snapshot from state {}", current),
            });
        }

        let should_resume = current == VmState::Running;
        if should_resume {
            self.pause_internal().await?;
        }

        let snapshot_id = format!("vz-snap-{}", Uuid::new_v4());
        let path = self.snapshot_path(&snapshot_id);
        self.save_state_to_path(&path).await?;
        let data = tokio::fs::read(&path)
            .await
            .map_err(|e| VmError::SnapshotFailed {
                reason: format!("failed to read snapshot file: {}", e),
            })?;
        let _ = tokio::fs::remove_file(&path).await;

        if should_resume {
            self.resume_internal().await?;
        }

        let checksum = crc32fast::hash(&data);
        let metadata = VmSnapshotMetadata::new(
            snapshot_id,
            self.id.clone(),
            data.len() as u64,
            checksum,
            std::env::consts::ARCH.to_string(),
            self.config.vcpu_count,
            self.config.memory_mib,
        );

        VmSnapshot::new(metadata, Bytes::from(data))
    }

    async fn restore(&mut self, snapshot: &VmSnapshot) -> VmResult<()> {
        if !snapshot.verify_checksum() {
            return Err(VmError::SnapshotCorrupted);
        }

        let current = self.state();
        if !matches!(current, VmState::Created | VmState::Stopped) {
            return Err(VmError::RestoreFailed {
                reason: format!("cannot restore from state {}", current),
            });
        }

        tokio::fs::create_dir_all(&self.vz_config.snapshot_dir)
            .await
            .map_err(|e| VmError::RestoreFailed {
                reason: format!("failed to create snapshot dir: {}", e),
            })?;
        let snapshot_id = format!("vz-restore-{}", snapshot.metadata.snapshot_id);
        let path = self.snapshot_path(&snapshot_id);
        tokio::fs::write(&path, snapshot.data.clone())
            .await
            .map_err(|e| VmError::RestoreFailed {
                reason: format!("failed to write snapshot file: {}", e),
            })?;

        self.restore_state_from_path(&path).await?;
        let _ = tokio::fs::remove_file(&path).await;

        self.set_state(VmState::Paused);
        self.resume().await?;

        info!(vm_id = %self.id, snapshot_id = %snapshot.metadata.snapshot_id, "VZ snapshot restored");
        Ok(())
    }
}

impl VzVm {
    async fn pause_internal(&self) -> VmResult<()> {
        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result = unsafe { kelpie_vz_vm_pause(self.handle, &mut error_ptr) };
        if result != 0 {
            return Err(VmError::PauseFailed {
                reason: take_error("vz pause", error_ptr),
            });
        }
        self.set_state(VmState::Paused);
        Ok(())
    }

    async fn resume_internal(&self) -> VmResult<()> {
        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        let result = unsafe { kelpie_vz_vm_resume(self.handle, &mut error_ptr) };
        if result != 0 {
            return Err(VmError::ResumeFailed {
                reason: take_error("vz resume", error_ptr),
            });
        }
        self.set_state(VmState::Running);
        Ok(())
    }
}

fn take_error(context: &str, error_ptr: *mut c_char) -> String {
    if error_ptr.is_null() {
        return format!("{} failed", context);
    }

    let message = unsafe {
        let cstr = CStr::from_ptr(error_ptr);
        let msg = cstr.to_string_lossy().to_string();
        kelpie_vz_string_free(error_ptr as *mut c_char);
        msg
    };
    format!("{}: {}", context, message)
}

struct VzVsockGuard {
    handle: *mut KelpieVzVmHandle,
    fd: c_int,
}

unsafe impl Send for VzVsockGuard {}

impl VzVsockGuard {
    fn new(handle: *mut KelpieVzVmHandle, fd: c_int) -> Self {
        Self { handle, fd }
    }
}

impl Drop for VzVsockGuard {
    fn drop(&mut self) {
        let mut error_ptr: *mut c_char = std::ptr::null_mut();
        unsafe {
            let _ = kelpie_vz_vm_close_vsock(self.handle, self.fd, &mut error_ptr);
            if !error_ptr.is_null() {
                kelpie_vz_string_free(error_ptr);
            }
        }
    }
}

# Task: Phase 5.9 - Teleport Implementation with Dual Backend Architecture

**Created:** 2026-01-15 12:13:24
**State:** IN_PROGRESS

---

## Vision Alignment

**Vision files read:**
- `CLAUDE.md` (Project-specific guidance)
- Previous: `.progress/015_20260115_101730_libkrun-dst-integration.md`

**Relevant constraints/guidance:**
- **TigerStyle safety principles** - Explicit constants, assertions, no silent failures
- **No placeholders in production** - Real implementations only
- **Platform-specific optimization** - Use native APIs when available
- **Developer experience** - Local Mac development must work seamlessly

---

## Task Description

Implement true VM teleportation (snapshot/restore) using platform-native hypervisors with full VM memory state preservation. This replaces the previous libkrun-based approach after research revealed better alternatives.

### Current State

**Teleport Infrastructure (✅ Complete):**
- ✅ `TeleportPackage` struct with 3 snapshot kinds (Suspend/Teleport/Checkpoint)
- ✅ `TeleportStorage` trait for S3/local storage
- ✅ Architecture validation (ARM64 vs x86_64)
- ✅ Base image version validation
- ✅ LocalTeleportStorage implementation

**VM Backends (⚠️ Mixed Status):**
- ✅ MockVm with working snapshot/restore (DST testing)
- ✅ Apple VZ backend implemented with ObjC bridge (builds; real VM validation pending)
- ✅ Firecracker backend implemented (Linux-only; validation pending)
- ✅ libkrun removed (consolidated into kelpie-vm)

**Key Discovery (Phase 5.7 Research):**
After extensive research, we discovered:
1. **libkrun has NO snapshot/restore API** (checked C header, docs, source)
2. **Apple Virtualization.framework HAS snapshot API** (`saveMachineStateTo()` since macOS 14 Sonoma)
3. **Firecracker HAS production-ready snapshot API** (powers AWS Lambda)
4. **Cross-architecture VM snapshot is IMPOSSIBLE** (ARM64 memory ↔ x86_64 memory incompatible)
5. **AWS Graviton (ARM64) is fully available** (Graviton2/3/4/5 across 28+ regions)

---

## Goal

Implement true VM teleportation with dual backend architecture:

### Primary Goal: Same-Architecture Teleport
- **Mac ARM64 → AWS Graviton ARM64** (full VM memory snapshot)
- **Linux x86_64 → AWS x86_64** (full VM memory snapshot)
- Sub-second resume time (Firecracker: ~125ms, Apple Vz: ~200-500ms)

### Secondary Goal: Cross-Architecture Migration
- **Mac ARM64 → AWS x86_64** (Checkpoint-only: agent state, no VM memory)
- **Linux x86_64 → AWS ARM64** (Checkpoint-only)
- Requires VM restart (2-5 seconds)

### Tertiary Goal: Clean Up libkrun
- Document actual capabilities (no snapshot support)
- Update README to remove misleading snapshot documentation
- Clarify role as "DST testing only" or deprecate in favor of native backends
- Remove snapshot/restore from LibkrunVm trait implementation (return clear "unsupported" errors)

---

## Options & Decisions

### Decision 1: Backend Strategy - Single vs Dual vs Triple

**Context:** Should we use one hypervisor everywhere or platform-specific backends?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: libkrun everywhere | Fork libkrun, add snapshot API, use on Mac/Linux | Single codebase | 4-6 weeks, maintenance burden, fighting library design intent |
| B: Firecracker everywhere | Use Firecracker on Mac via nested Linux VM | Production-proven snapshots | Mac nested VM is slow (10-30% overhead), complex setup |
| C: Dual native backends | Apple Vz on Mac, Firecracker on Linux/AWS | Zero maintenance, native performance | Two implementations to maintain |
| D: Triple (current + native) | Keep MockVm for DST, add Vz + Firecracker | Best testing + production | Most code to maintain |

**Decision:** Option D - Triple Backend (MockVm + Apple Vz + Firecracker)

**Reasoning:**
1. **Native APIs are mature** - Apple Vz since macOS 14, Firecracker powers AWS Lambda
2. **Zero maintenance burden** - No forks, no upstream tracking
3. **Optimal performance** - Native hypervisors (no nested virtualization)
4. **Clear separation** - MockVm for testing, native for production
5. **Platform-appropriate** - Mac devs get Mac-native UX, Linux devs get Linux-native UX

**Trade-offs accepted:**
- Three implementations instead of one (acceptable - trait abstracts differences)
- Can't test Firecracker on Mac locally (acceptable - most Mac devs won't need to)
- Cross-platform snapshot testing requires CI (acceptable - rare edge case)

---

### Decision 2: libkrun Role - Keep, Deprecate, or Remove

**Context:** What to do with the libkrun implementation we just completed?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Keep for Checkpoint-only | Use libkrun for Checkpoint (agent state) migration only | Leverages existing work | Confusing to have 3 production backends |
| B: DST testing only | Keep for MockVm replacement in DST, not production | Clear role separation | Wasted effort on FFI implementation |
| C: Deprecate entirely | Remove from production paths, mark deprecated | Simple architecture | Need to remove recent work |
| D: Fork and add snapshot | Continue with Option B from earlier | We already started FFI | 4-6 weeks more work, goes against native API benefits |

**Decision:** Option B - DST Testing Only (with future removal)

**Reasoning:**
1. **MockVm is sufficient for DST** - Simpler, no system dependencies
2. **Native backends are superior** - Apple Vz and Firecracker have proven snapshot APIs
3. **Clear role** - libkrun becomes "real VM testing harness" for DST edge cases
4. **Graceful deprecation** - Keep code for now, remove when native backends are stable
5. **Honest about limitations** - Update docs to reflect "no snapshot support"

**Trade-offs accepted:**
- Recent FFI work becomes testing-only (acceptable - it validates our understanding)
- Three codepaths initially (acceptable - removes libkrun after Phase 5.10 complete)

---

### Decision 3: Implementation Order - Parallel vs Sequential

**Context:** Should we implement Apple Vz and Firecracker in parallel or one at a time?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Apple Vz first | Mac backend, then Firecracker | Mac devs unblocked faster | Linux/AWS delayed |
| B: Firecracker first | Linux/AWS backend, then Apple Vz | Production ready faster | Mac devs blocked longer |
| C: Parallel | Both at once (requires two people or long timeline) | Both ready together | Higher complexity, potential design drift |

**Decision:** Option A - Apple Vz First, Then Firecracker

**Reasoning:**
1. **Mac is primary dev platform** - Most team on Apple Silicon
2. **Apple Vz is simpler** - Single Swift/Objective-C API, no HTTP layer
3. **Learn patterns first** - Vz implementation informs Firecracker design
4. **Incremental validation** - Test snapshot format with one backend before adding second
5. **Firecracker can copy patterns** - Vz establishes trait implementation approach

**Trade-offs accepted:**
- Linux/AWS teleport delayed by 2-3 weeks (acceptable - Mac devs more numerous)
- Sequential timeline (~5 weeks total vs ~3.5 weeks parallel)

---

## Implementation Phases

### Phase 1: libkrun Cleanup & Documentation (1-2 days)

**Goal:** Make libkrun's limitations explicit and document actual status

**Tasks:**
- [ ] Update `crates/kelpie-libkrun/README.md`:
  - Remove "PARTIALLY IMPLEMENTED" status
  - Change to "TESTING ONLY - No Snapshot Support"
  - Add section: "Why Not libkrun for Production?"
  - Document that Apple Vz and Firecracker are production backends
  - Keep MockVm as recommended for most testing
- [ ] Update `crates/kelpie-libkrun/src/ffi.rs`:
  - Keep current implementation (it's correct for what libkrun offers)
  - Update `snapshot()` and `restore()` error messages to be more explicit
  - Change from "deferred to Phase X" to "libkrun does not support this feature"
- [ ] Update `crates/kelpie-libkrun/Cargo.toml`:
  - Update feature docs to clarify "testing/validation only"
- [ ] Create `DEPRECATION_NOTICE.md`:
  - Timeline: Remove after Phase 5.10 (native backends stable)
  - Migration path: Use MockVm for DST, Apple Vz/Firecracker for production
- [ ] Update main `CLAUDE.md`:
  - Add section on hypervisor backends
  - Document when to use which backend

**Acceptance:**
- Documentation is honest about libkrun limitations
- No misleading claims about snapshot support
- Clear migration path documented

---

### Phase 2: Apple Virtualization.framework Backend (2-3 weeks)

**Goal:** Implement VzVm backend with snapshot/restore for macOS

#### Phase 2.1: Project Setup & C Bridge (2-3 days)

**Tasks:**
- [ ] Create `crates/kelpie-vz/` crate:
  ```toml
  [package]
  name = "kelpie-vz"
  description = "Apple Virtualization.framework backend for Kelpie"

  [dependencies]
  kelpie-libkrun = { path = "../kelpie-libkrun" } # for traits
  objc = "0.2"
  cocoa = "0.25"
  core-foundation = "0.9"

  [build-dependencies]
  cc = "1.0"
  ```
- [ ] Research existing Rust bindings:
  - Study [vfkit](https://github.com/crc-org/vfkit) (Go, but shows API patterns)
  - Study [Lima's VZ driver](https://github.com/lima-vm/lima/tree/master/pkg/vz) (Go)
  - Check for existing Rust crates (vz-rs, etc.)
- [ ] Create C bridge layer (`src/vz_bridge.c`):
  - Wrap Objective-C Virtualization.framework APIs
  - Expose C functions callable from Rust
  - Handle memory management (CFRetain/CFRelease)
- [ ] Create Rust FFI bindings (`src/ffi.rs`):
  - Extern C declarations
  - Safe Rust wrappers
  - SAFETY comments for all unsafe blocks

**Acceptance:**
- Can create VZVirtualMachine from Rust
- Can call basic lifecycle methods (start, stop, pause)
- No memory leaks (verify with Instruments.app)

---

#### Phase 2.2: Core VM Lifecycle (3-4 days)

**Tasks:**
- [ ] Implement `VzVm` struct:
  ```rust
  pub struct VzVm {
      id: String,
      config: VmConfig,
      state: VmState,
      vz_vm: *mut VZVirtualMachine, // Objective-C pointer
      architecture: Architecture,
  }
  ```
- [ ] Implement `VmInstance` trait for `VzVm`:
  - `new()` - Create VM configuration
  - `start()` - Boot VM
  - `stop()` - Shutdown VM
  - `pause()` - Call VZVirtualMachine.pause()
  - `resume()` - Call VZVirtualMachine.resume()
  - `state()` - Map VZVirtualMachine.state to VmState enum
- [ ] Configure VM:
  - CPU count (VZVirtualMachineConfiguration.cpuCount)
  - Memory size (VZVirtualMachineConfiguration.memorySize)
  - Boot loader (VZLinuxBootLoader with kernel/initramfs)
  - Root disk (VZVirtioBlockDeviceConfiguration)
  - Console (VZVirtioConsoleDeviceConfiguration)
- [ ] Add assertions (TigerStyle):
  - Preconditions: state checks, parameter validation
  - Postconditions: verify state transitions
  - At least 2 per function

**Acceptance:**
- Can boot Linux VM on Mac
- VM starts and stops cleanly
- State machine transitions work correctly
- No panics or crashes

---

#### Phase 2.3: Snapshot/Restore Implementation (3-4 days)

**Tasks:**
- [ ] Implement `snapshot()`:
  ```rust
  async fn snapshot(&self) -> LibkrunResult<VmSnapshot> {
      // Call VZVirtualMachine.saveMachineStateTo(url:completionHandler:)
      let snapshot_path = format!("/tmp/kelpie-snapshot-{}.vz", self.id);
      self.vz_vm.saveMachineStateTo(url: snapshot_path)?;

      // Read snapshot file
      let snapshot_data = tokio::fs::read(&snapshot_path).await?;

      // Create VmSnapshot with metadata
      let metadata = VmSnapshotMetadata {
          vm_id: self.id.clone(),
          architecture: Architecture::Arm64,
          base_image_version: "1.0.2".to_string(),
          created_at_ms: current_time_ms(),
          size_bytes: snapshot_data.len() as u64,
      };

      Ok(VmSnapshot::new(metadata, snapshot_data))
  }
  ```
- [ ] Implement `restore()`:
  ```rust
  async fn restore(&mut self, snapshot: &VmSnapshot) -> LibkrunResult<()> {
      // Verify architecture
      if snapshot.metadata().architecture != Architecture::Arm64 {
          return Err(LibkrunError::RestoreFailed {
              reason: "architecture mismatch".into()
          });
      }

      // Write snapshot to temp file
      let snapshot_path = format!("/tmp/kelpie-restore-{}.vz", self.id);
      tokio::fs::write(&snapshot_path, snapshot.data()).await?;

      // Call VZVirtualMachine.restoreMachineStateFrom(url:completionHandler:)
      self.vz_vm.restoreMachineStateFrom(url: snapshot_path)?;

      Ok(())
  }
  ```
- [ ] Handle VirtIO GPU limitation:
  - Document that GUI Linux VMs don't support snapshot (as of macOS 14)
  - Verify headless Linux works (our use case)
- [ ] Add error handling:
  - Map VZ errors to LibkrunError
  - Handle file I/O errors
  - Handle async completion handlers

**Acceptance:**
- Can snapshot running VM
- Can restore from snapshot
- VM continues execution after restore
- Works with headless Linux (kelpie-base image)

---

#### Phase 2.4: Guest Agent Integration (2-3 days)

**Tasks:**
- [ ] Configure virtio-vsock device:
  ```rust
  let vsock_device = VZVirtioSocketDeviceConfiguration::new();
  vsock_device.setDestinationPort(9001);
  vm_config.addSocketDevice(vsock_device);
  ```
- [ ] Implement `exec()` method:
  - Connect to vsock port 9001
  - Send JSON-RPC command to guest agent
  - Read response with timeout
  - Parse stdout/stderr/exit_code
- [ ] Test with kelpie-base image:
  - Boot VM with guest agent
  - Verify agent responds to health check
  - Execute test commands
- [ ] Add timeout handling:
  - Use `tokio::time::timeout`
  - Return `ExecTimeout` error on timeout

**Acceptance:**
- Can execute commands in VM
- Guest agent responds correctly
- Timeouts work as expected
- Error messages are clear

---

#### Phase 2.5: Testing & Validation (2-3 days)

**Tasks:**
- [ ] Create unit tests:
  - VM creation
  - State transitions
  - Snapshot/restore roundtrip
  - Error handling
- [ ] Create integration tests:
  - Full lifecycle (create → start → exec → snapshot → restore → exec)
  - Verify data persistence across snapshots
  - Test failure scenarios
- [ ] Manual testing:
  - Boot VM
  - Run commands
  - Snapshot
  - Kill process
  - Restore snapshot
  - Verify VM state matches pre-snapshot
- [ ] Performance testing:
  - Measure snapshot creation time
  - Measure restore time
  - Measure snapshot size
  - Compare with Firecracker benchmarks

**Acceptance:**
- All tests pass
- Snapshot/restore works reliably
- Performance meets expectations (< 500ms restore)
- No memory leaks or crashes

---

### Phase 3: Firecracker Backend (2-3 weeks)

**Goal:** Implement FirecrackerVm backend for Linux/AWS

#### Phase 3.1: Project Setup (1-2 days)

**Tasks:**
- [ ] Create `crates/kelpie-firecracker/` crate:
  ```toml
  [package]
  name = "kelpie-firecracker"
  description = "Firecracker microVM backend for Kelpie"

  [dependencies]
  kelpie-libkrun = { path = "../kelpie-libkrun" }
  hyper = "1.0"
  tokio = { version = "1", features = ["full"] }
  serde = { version = "1", features = ["derive"] }
  serde_json = "1"
  ```
- [ ] Study Firecracker API:
  - Read [HTTP API spec](https://github.com/firecracker-microvm/firecracker/blob/main/src/api_server/swagger/firecracker.yaml)
  - Read [snapshot documentation](https://github.com/firecracker-microvm/firecracker/blob/main/docs/snapshotting/snapshot-support.md)
  - Review [getting started guide](https://github.com/firecracker-microvm/firecracker/blob/main/docs/getting-started.md)
- [ ] Install Firecracker on Linux dev machine:
  ```bash
  # Download latest release
  curl -LOJ https://github.com/firecracker-microvm/firecracker/releases/download/v1.8.0/firecracker-v1.8.0-x86_64.tgz
  tar -xzf firecracker-v1.8.0-x86_64.tgz
  sudo mv firecracker-v1.8.0-x86_64 /usr/local/bin/firecracker
  ```
- [ ] Create HTTP client for Firecracker API:
  ```rust
  struct FirecrackerClient {
      socket_path: PathBuf,
      client: hyper::Client<UnixConnector>,
  }
  ```

**Acceptance:**
- Can start Firecracker process
- Can communicate with API socket
- Can create basic VM

---

#### Phase 3.2: Core VM Lifecycle (3-4 days)

**Tasks:**
- [ ] Implement `FirecrackerVm` struct:
  ```rust
  pub struct FirecrackerVm {
      id: String,
      config: VmConfig,
      state: VmState,
      firecracker_pid: Option<u32>,
      api_socket: PathBuf,
      client: FirecrackerClient,
      architecture: Architecture,
  }
  ```
- [ ] Implement `VmInstance` trait:
  - `new()` - Start Firecracker process with API socket
  - `start()` - Configure VM via PUT /machine-config, PUT /boot-source, PUT /actions (InstanceStart)
  - `stop()` - Send CtrlAltDelete action
  - `pause()` - Send Pause action
  - `resume()` - Send Resume action
- [ ] Configure VM via API:
  ```rust
  // PUT /machine-config
  client.put("/machine-config").json(&json!({
      "vcpu_count": config.vcpu_count,
      "mem_size_mib": config.memory_mib,
  })).send().await?;

  // PUT /boot-source
  client.put("/boot-source").json(&json!({
      "kernel_image_path": "/path/to/vmlinux",
      "boot_args": "console=ttyS0 reboot=k panic=1",
  })).send().await?;

  // PUT /drives/rootfs
  client.put("/drives/rootfs").json(&json!({
      "drive_id": "rootfs",
      "path_on_host": config.root_disk_path,
      "is_root_device": true,
      "is_read_only": false,
  })).send().await?;
  ```
- [ ] Handle Firecracker process lifecycle:
  - Start firecracker with --api-sock
  - Monitor process health
  - Clean up on Drop

**Acceptance:**
- Can boot Linux VM via Firecracker
- VM starts and stops cleanly
- API communication works reliably
- Process cleanup works on Drop

---

#### Phase 3.3: Snapshot/Restore Implementation (3-4 days)

**Tasks:**
- [ ] Implement `snapshot()`:
  ```rust
  async fn snapshot(&self) -> LibkrunResult<VmSnapshot> {
      // Pause VM first
      self.client.patch("/vm").json(&json!({
          "state": "Paused"
      })).send().await?;

      // Create snapshot via PUT /snapshot/create
      let snapshot_path = format!("/tmp/kelpie-snapshot-{}.snap", self.id);
      let mem_path = format!("/tmp/kelpie-memory-{}.mem", self.id);

      self.client.put("/snapshot/create").json(&json!({
          "snapshot_type": "Full",
          "snapshot_path": snapshot_path,
          "mem_file_path": mem_path,
      })).send().await?;

      // Read snapshot files
      let snapshot_data = tokio::fs::read(&snapshot_path).await?;
      let memory_data = tokio::fs::read(&mem_path).await?;

      // Combine into single VmSnapshot
      let mut combined = Vec::new();
      combined.extend_from_slice(&(snapshot_data.len() as u64).to_le_bytes());
      combined.extend_from_slice(&snapshot_data);
      combined.extend_from_slice(&memory_data);

      let metadata = VmSnapshotMetadata { /* ... */ };
      Ok(VmSnapshot::new(metadata, Bytes::from(combined)))
  }
  ```
- [ ] Implement `restore()`:
  ```rust
  async fn restore(&mut self, snapshot: &VmSnapshot) -> LibkrunResult<()> {
      // Extract snapshot and memory files
      let data = snapshot.data();
      let snapshot_len = u64::from_le_bytes(data[0..8].try_into().unwrap()) as usize;
      let snapshot_data = &data[8..8 + snapshot_len];
      let memory_data = &data[8 + snapshot_len..];

      // Write to temp files
      let snapshot_path = format!("/tmp/kelpie-restore-{}.snap", self.id);
      let mem_path = format!("/tmp/kelpie-restore-{}.mem", self.id);
      tokio::fs::write(&snapshot_path, snapshot_data).await?;
      tokio::fs::write(&mem_path, memory_data).await?;

      // Load snapshot via PUT /snapshot/load
      self.client.put("/snapshot/load").json(&json!({
          "snapshot_path": snapshot_path,
          "mem_backend": {
              "backend_path": mem_path,
              "backend_type": "File",
          },
          "enable_diff_snapshots": false,
          "resume_vm": true,
      })).send().await?;

      Ok(())
  }
  ```
- [ ] Handle diff snapshots:
  - Document that we use full snapshots (not diff)
  - Consider diff snapshots for optimization later
- [ ] Add error handling:
  - Map Firecracker API errors to LibkrunError
  - Handle HTTP communication failures
  - Handle file I/O errors

**Acceptance:**
- Can snapshot running VM
- Can restore from snapshot
- VM resumes execution correctly
- Snapshot files are portable (can move between hosts)

---

#### Phase 3.4: Guest Agent Integration (2-3 days)

**Tasks:**
- [ ] Configure virtio-vsock device:
  ```rust
  // PUT /vsock
  client.put("/vsock").json(&json!({
      "guest_cid": 3,
      "uds_path": format!("/tmp/firecracker-{}.vsock", self.id),
  })).send().await?;
  ```
- [ ] Implement `exec()` using vsock:
  - Connect to Unix socket
  - Send guest agent command
  - Read response
  - Parse output
- [ ] Reuse guest agent protocol from Phase 2.4 (same protocol, different transport)

**Acceptance:**
- Can execute commands in VM
- Guest agent communication works
- Same protocol works on both Apple Vz and Firecracker

---

#### Phase 3.5: Testing & Validation (2-3 days)

**Tasks:**
- [ ] Same testing approach as Phase 2.5
- [ ] Cross-platform testing:
  - Test on x86_64 Linux
  - Test on ARM64 Linux (AWS Graviton instance)
  - Verify snapshots are portable (x86_64 host A → x86_64 host B)
- [ ] Performance benchmarks:
  - Snapshot creation time (target: < 100ms)
  - Restore time (target: < 125ms, per Firecracker docs)
  - Compare with Apple Vz performance

**Acceptance:**
- All tests pass
- Performance meets Firecracker benchmarks
- Snapshots are portable across hosts
- Works on both x86_64 and ARM64

---

### Phase 4: Teleport Integration (1 week)

**Goal:** Wire up backends to TeleportStorage and implement end-to-end migration

#### Phase 4.1: Backend Selection (2 days)

**Tasks:**
- [ ] Create `VmBackend` enum:
  ```rust
  pub enum VmBackend {
      #[cfg(target_os = "macos")]
      AppleVirtualization(VzVm),

      #[cfg(target_os = "linux")]
      Firecracker(FirecrackerVm),

      Mock(MockVm), // For testing
  }

  impl VmInstance for VmBackend {
      // Delegate to inner implementation
  }
  ```
- [ ] Create backend factory:
  ```rust
  pub struct VmFactory;

  impl VmFactory {
      pub fn create(config: VmConfig) -> Result<Box<dyn VmInstance>> {
          #[cfg(target_os = "macos")]
          return Ok(Box::new(VmBackend::AppleVirtualization(
              VzVm::new(config)?
          )));

          #[cfg(target_os = "linux")]
          return Ok(Box::new(VmBackend::Firecracker(
              FirecrackerVm::new(config)?
          )));

          #[cfg(test)]
          return Ok(Box::new(VmBackend::Mock(
              MockVm::new(config)?
          )));
      }
  }
  ```
- [ ] Add feature flags:
  ```toml
  [features]
  default = []
  apple-vz = ["kelpie-vz"]
  firecracker = ["kelpie-firecracker"]
  ```

**Acceptance:**
- Correct backend selected at compile time
- Factory works on Mac and Linux
- Tests use MockVm automatically

---

#### Phase 4.2: Teleport API Implementation (3 days)

**Tasks:**
- [ ] Implement teleport upload:
  ```rust
  pub async fn teleport_to_storage(
      vm: &dyn VmInstance,
      storage: &dyn TeleportStorage,
      kind: SnapshotKind,
  ) -> Result<String> {
      // Create snapshot
      let snapshot = vm.snapshot().await?;

      // Create teleport package
      let package = TeleportPackage::new(
          uuid::Uuid::new_v4().to_string(),
          vm.id(),
          storage.host_arch(),
          kind,
      )
      .with_vm_memory(snapshot.data())
      .with_vm_cpu_state(Bytes::new()) // Included in Apple Vz snapshot
      .with_agent_state(Bytes::new()) // TODO: extract from VM
      .with_base_image_version("1.0.2");

      // Upload to storage
      storage.upload(package).await
  }
  ```
- [ ] Implement teleport restore:
  ```rust
  pub async fn teleport_from_storage(
      storage: &dyn TeleportStorage,
      package_id: &str,
  ) -> Result<Box<dyn VmInstance>> {
      // Download package
      let package = storage.download_for_restore(
          package_id,
          Architecture::current(),
      ).await?;

      // Verify kind
      if !package.is_full_teleport() {
          return Err(Error::InvalidTeleportKind);
      }

      // Create VM
      let config = VmConfig::from_package(&package)?;
      let mut vm = VmFactory::create(config)?;

      // Restore from snapshot
      let snapshot = VmSnapshot::from_package(&package)?;
      vm.restore(&snapshot).await?;

      Ok(vm)
  }
  ```
- [ ] Add checkpoint-only migration:
  ```rust
  pub async fn checkpoint_to_storage(
      agent_state: AgentState,
      storage: &dyn TeleportStorage,
  ) -> Result<String> {
      let package = TeleportPackage::new(
          uuid::Uuid::new_v4().to_string(),
          agent_state.id(),
          Architecture::current(),
          SnapshotKind::Checkpoint,
      )
      .with_agent_state(agent_state.serialize()?)
      .with_env_vars(agent_state.env_vars())
      .with_workspace_ref(agent_state.workspace_ref());

      storage.upload(package).await
  }
  ```

**Acceptance:**
- Can upload teleport package to storage
- Can restore from teleport package
- Checkpoint-only migration works cross-architecture
- Full teleport works same-architecture

---

#### Phase 4.3: End-to-End Testing (2 days)

**Tasks:**
- [ ] Test Mac → AWS ARM64 teleport:
  - Start VM on Mac with Apple Vz
  - Run agent with state
  - Snapshot and upload to S3
  - Spin up AWS Graviton instance
  - Download snapshot
  - Restore with Firecracker
  - Verify agent continues from same state
- [ ] Test Linux x86_64 → AWS x86_64 teleport:
  - Same flow with Firecracker on both ends
- [ ] Test cross-architecture checkpoint:
  - Mac ARM64 → AWS x86_64 (agent state only)
  - Verify agent restarts correctly
  - Verify no memory state corruption
- [ ] Performance testing:
  - Measure total teleport time (snapshot + upload + download + restore)
  - Target: < 5 seconds for 512MB VM
  - Snapshot: < 500ms
  - S3 upload: ~2-3s (depends on bandwidth)
  - S3 download: ~1-2s
  - Restore: < 500ms

**Acceptance:**
- End-to-end teleport works Mac → AWS
- End-to-end teleport works Linux → AWS
- Cross-architecture checkpoint works
- Performance meets targets
- No data loss or corruption

---

### Phase 5: Documentation & Cleanup (2-3 days)

**Goal:** Complete documentation and deprecate libkrun

**Tasks:**
- [ ] Update main README:
  - Add teleport capabilities section
  - Document supported architectures
  - Add Mac/Linux developer quickstart
- [ ] Create teleport documentation:
  - `docs/teleport/architecture.md` - How it works
  - `docs/teleport/quickstart.md` - Getting started
  - `docs/teleport/cross-architecture.md` - Checkpoint vs full teleport
  - `docs/teleport/troubleshooting.md` - Common issues
- [ ] Update API documentation:
  - Document VmBackend enum
  - Document teleport_to_storage() / teleport_from_storage()
  - Document when to use Checkpoint vs Teleport
- [ ] Create migration guide from libkrun:
  - How to switch from LibkrunVm to VmFactory
  - Breaking changes
  - Timeline for removal
- [ ] Update CLAUDE.md:
  - Add teleport implementation status
  - Document hypervisor backend choices
- [ ] Remove/deprecate libkrun:
  - Add deprecation warnings to LibkrunVm
  - Update tests to use MockVm or native backends
  - Schedule removal for Phase 5.11

**Acceptance:**
- Documentation is complete and accurate
- Migration path is clear
- Examples work on both Mac and Linux
- libkrun deprecation is announced

---

## Success Criteria

### Functional Requirements
- ✅ Can snapshot running VM on Mac (Apple Vz)
- ✅ Can snapshot running VM on Linux (Firecracker)
- ✅ Can restore VM from snapshot (same architecture)
- ✅ Can teleport Mac ARM64 → AWS Graviton ARM64
- ✅ Can teleport Linux x86_64 → AWS x86_64
- ✅ Can checkpoint agent state cross-architecture
- ✅ VM resumes execution after restore
- ✅ Agent state preserved across teleport

### Performance Requirements
- ✅ Snapshot creation: < 500ms (Apple Vz), < 100ms (Firecracker)
- ✅ Restore time: < 500ms (Apple Vz), < 125ms (Firecracker)
- ✅ Total teleport time: < 5 seconds (including S3 transfer)
- ✅ Snapshot size: ~memory_size (minimal overhead)

### Quality Requirements
- ✅ No memory leaks (verified with instruments/valgrind)
- ✅ No panics or crashes
- ✅ All tests pass (unit, integration, end-to-end)
- ✅ TigerStyle compliance (assertions, SAFETY comments, error handling)
- ✅ Documentation complete and accurate

### Developer Experience
- ✅ Mac developers can snapshot/restore locally
- ✅ Linux developers can snapshot/restore locally
- ✅ Clear error messages when cross-architecture attempted
- ✅ Simple API (VmFactory, teleport_to_storage)
- ✅ Works with existing DST harness (MockVm)

---

## Timeline

| Phase | Duration | Dependencies |
|-------|----------|--------------|
| Phase 1: libkrun Cleanup | 1-2 days | None |
| Phase 2: Apple Vz Backend | 2-3 weeks | Phase 1 |
| Phase 3: Firecracker Backend | 2-3 weeks | Phase 2 (can overlap partially) |
| Phase 4: Teleport Integration | 1 week | Phase 2 + 3 |
| Phase 5: Documentation | 2-3 days | Phase 4 |

**Total: 6-8 weeks**

**Milestones:**
- Week 1: libkrun cleanup + Apple Vz setup
- Week 3: Apple Vz snapshot/restore working
- Week 5: Firecracker snapshot/restore working
- Week 7: End-to-end teleport working Mac → AWS
- Week 8: Documentation complete, libkrun deprecated

---

## Risks & Mitigations

### Risk 1: Apple Vz API Changes
**Probability:** Low
**Impact:** High
**Mitigation:** Target macOS 14+ (Sonoma), which has stable API. Test on multiple macOS versions.

### Risk 2: Firecracker Snapshot Format Changes
**Probability:** Low
**Impact:** Medium
**Mitigation:** Use stable Firecracker release (v1.8+). Version snapshots with metadata.

### Risk 3: Cross-Platform Snapshot Incompatibility
**Probability:** Medium (different Firecracker versions)
**Impact:** High
**Mitigation:** Include Firecracker version in snapshot metadata. Validate on restore.

### Risk 4: Performance Not Meeting Targets
**Probability:** Low
**Impact:** Medium
**Mitigation:** Both frameworks have proven performance in production. Benchmark early.

### Risk 5: Guest Agent Protocol Incompatibility
**Probability:** Low
**Impact:** Medium
**Mitigation:** Design protocol in Phase 2.4, reuse in Phase 3.4. Same protocol, different transport.

---

## Open Questions

1. **Snapshot versioning:** How do we handle incompatible snapshot format changes?
   - Proposal: Include format version in VmSnapshotMetadata, reject incompatible versions

2. **S3 vs local storage:** Should we default to S3 or local for development?
   - Proposal: LocalTeleportStorage for dev, S3TeleportStorage for prod (configurable)

3. **Diff snapshots:** Should we support Firecracker's diff snapshots?
   - Proposal: Phase 5.10 optimization (full snapshots sufficient for now)

4. **Cross-region teleport:** How do we handle AWS region selection?
   - Proposal: TeleportStorage configured with region, user specifies target region

5. **Snapshot encryption:** Do we need encrypted snapshots?
   - Proposal: S3 server-side encryption sufficient for Phase 5.9, client-side encryption in Phase 5.11

---

## Instance Log

| Time | Instance | Phase | Status | Notes |
|------|----------|-------|--------|-------|
| 2026-01-15 12:13 | Claude-001 | Planning | In Progress | Creating plan document |

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 12:13 | Use dual backend (Apple Vz + Firecracker) | Native APIs, zero maintenance, optimal performance | Two implementations to maintain vs one |
| 12:15 | Deprecate libkrun | No snapshot API, native backends superior | Recent FFI work becomes testing-only |
| 12:17 | Apple Vz first, Firecracker second | Mac is primary dev platform, learn patterns first | Sequential timeline ~5 weeks vs ~3.5 parallel |
| 12:20 | Keep MockVm for DST | Simple, no dependencies, sufficient for testing | Three implementations during transition |

---

## What to Try

### Works Now
- ✅ `kelpie-vm` builds with `vz` feature on macOS
- ✅ Deterministic simulation coverage for VM exec/teleport (DST)
- ✅ Firecracker snapshot metadata blob guards in DST

### Doesn't Work Yet
- Real VZ snapshot/restore validation on macOS (needs VM boot + exec + snapshot cycle)
- Firecracker boot/exec/snapshot validation on Linux
- Cross-host teleport (Mac ↔ AWS, Linux ↔ AWS)

### Known Limitations
- **libkrun has no snapshot support** - This is a library limitation, not fixable without forking
- **Cross-architecture VM snapshot impossible** - CPU architecture incompatibility, use Checkpoint instead
- **Apple Vz doesn't support GUI Linux snapshots** - VirtIO GPU limitation, headless works fine
- **Firecracker requires Linux** - Cannot run on macOS natively (nested VM is slow)
- **Snapshot format is hypervisor-specific** - Cannot restore Apple Vz snapshot with Firecracker

---

## Progress Update (2026-01-15)

- Unified VM backends into `crates/kelpie-vm` with `firecracker`/`vz` features; removed libkrun and legacy backend crates.
- Added deterministic simulation tests in `crates/kelpie-dst/tests` and verified `vm_exec_dst` and `vm_teleport_dst` pass.
- Implemented initial Apple VZ Objective-C bridge and Rust backend; fixing build errors from type naming and VZ boot loader init.
- Confirmed `cargo test -p kelpie-vm --features vz` passes after VZ bridge fixes.
- Added `VmBackendFactory::for_host` to select VZ on macOS, Firecracker on Linux, or Mock as fallback.
- Removed unused RNG warning in SimSandbox by using deterministic start-time jitter.
- Added DST coverage for Firecracker snapshot metadata roundtrip and teleport blob version guard.
- Converted VZ bridge record to ADR (`docs/adr/016-vz-objc-bridge.md`).
- Migrated remaining EDRs into ADRs (017-020) and removed the `docs/edr` directory.

---

## Plan Audit (2026-01-15)

**Completed**
- Consolidated VM crates into `kelpie-vm` and removed libkrun/firecracker/vm-backends legacy crates.
- Apple VZ backend implemented with ObjC bridge (build/test on macOS).
- DST deterministic simulations for VM exec/teleport + Firecracker snapshot metadata/versioning.

**Pending**
- Validate VZ backend on a real VM (boot, exec, snapshot/restore) on macOS.
- Validate Firecracker backend on Linux (boot, exec, snapshot/restore).
- End-to-end teleport tests across hosts once Linux/AWS are available.

---

## References

- [Apple Virtualization.framework Documentation](https://developer.apple.com/documentation/virtualization)
- [Apple saveMachineStateTo API](https://developer.apple.com/documentation/virtualization/vzvirtualmachine/savemachinestateto(url:completionhandler:))
- [WWDC 2023: VM State Saving](https://developer.apple.com/videos/play/wwdc2023/10007/)
- [Firecracker GitHub](https://github.com/firecracker-microvm/firecracker)
- [Firecracker Snapshot Documentation](https://github.com/firecracker-microvm/firecracker/blob/main/docs/snapshotting/snapshot-support.md)
- [Firecracker HTTP API Spec](https://github.com/firecracker-microvm/firecracker/blob/main/src/api_server/swagger/firecracker.yaml)
- [AWS Graviton](https://aws.amazon.com/ec2/graviton/)
- [vfkit (Apple Vz in Go)](https://github.com/crc-org/vfkit)
- [Lima VZ Driver](https://github.com/lima-vm/lima/tree/master/pkg/vz)

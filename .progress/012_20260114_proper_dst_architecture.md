# Task: Implement Proper DST Architecture

**Created:** 2026-01-14
**State:** PHASE 1-5 COMPLETE ✅
**Priority:** CRITICAL - Current "DST" is just mock testing
**Updated:** 2026-01-14 - Core DST infrastructure complete

## Problem Statement

Current architecture has **completely separate code paths** for production and testing:

```
Production:                      Testing/DST:
┌────────────────────┐           ┌────────────────────┐
│ LibkrunSandbox     │           │ SimSandbox         │
│ (real VM code)     │           │ (HashMap mock)     │
└────────────────────┘           └────────────────────┘
        ↓                                ↓
   Real libkrun                    In-memory fake
   Real disk I/O                   No real I/O
   Wall clock                      Hardcoded time
```

**This means DST tests don't test the actual production code.**

## What True DST Requires

FoundationDB-style DST runs the **same code** in both modes:

```
┌─────────────────────────────────────────────────────┐
│         Business Logic (SAME CODE)                  │
│    Agent, Service, Handler, Dispatcher              │
└──────────────────────┬──────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────┐
│              I/O Abstraction Layer                  │
│  IoContext { sandbox, storage, time, network }      │
└──────────────────────┬──────────────────────────────┘
                       │
          ┌────────────┴────────────┐
          │                         │
    ┌─────▼─────┐            ┌─────▼─────┐
    │ Production│            │    DST    │
    │ - Libkrun │            │ - SimIO   │
    │ - FDB     │            │ - Faults  │
    │ - HTTP    │            │ - SimClk  │
    │ - Wall Clk│            │ - Determ  │
    └───────────┘            └───────────┘
```

## Design: IoContext Abstraction

### Core Traits (in kelpie-core)

```rust
/// Time provider - abstracts wall clock vs simulated time
#[async_trait]
pub trait TimeProvider: Send + Sync {
    fn now_ms(&self) -> u64;
    async fn sleep_ms(&self, ms: u64);
}

/// Random number generator - abstracts std RNG vs deterministic RNG
pub trait RngProvider: Send + Sync {
    fn next_u64(&self) -> u64;
    fn next_f64(&self) -> f64;
    fn gen_uuid(&self) -> String;
}
```

### Sandbox I/O Abstraction (in kelpie-sandbox)

```rust
/// Low-level sandbox I/O operations
#[async_trait]
pub trait SandboxIO: Send + Sync {
    async fn boot_vm(&mut self, config: &VmConfig) -> SandboxResult<()>;
    async fn shutdown_vm(&mut self) -> SandboxResult<()>;
    async fn exec_in_vm(&self, cmd: &str, args: &[&str], opts: &ExecOptions)
        -> SandboxResult<ExecOutput>;
    async fn capture_snapshot(&self) -> SandboxResult<SnapshotData>;
    async fn restore_snapshot(&mut self, data: &SnapshotData) -> SandboxResult<()>;
    async fn read_file(&self, path: &str) -> SandboxResult<Bytes>;
    async fn write_file(&self, path: &str, content: &[u8]) -> SandboxResult<()>;
}

/// Sandbox implementation - SAME CODE for prod and DST
pub struct Sandbox<IO: SandboxIO> {
    id: String,
    config: SandboxConfig,
    state: SandboxState,
    io: IO,
    time: Arc<dyn TimeProvider>,
}

impl<IO: SandboxIO> Sandbox<IO> {
    pub async fn start(&mut self) -> SandboxResult<()> {
        // State validation (SAME in both modes)
        if self.state != SandboxState::Stopped {
            return Err(SandboxError::InvalidState { ... });
        }

        // I/O operation (delegated to IO impl)
        self.io.boot_vm(&self.config.into()).await?;

        // State transition (SAME in both modes)
        self.state = SandboxState::Running;
        Ok(())
    }

    pub async fn exec(&self, cmd: &str, args: &[&str], opts: ExecOptions)
        -> SandboxResult<ExecOutput>
    {
        // State validation (SAME)
        if self.state != SandboxState::Running {
            return Err(SandboxError::InvalidState { ... });
        }

        // I/O operation (delegated)
        let output = self.io.exec_in_vm(cmd, args, &opts).await?;

        // Result processing (SAME)
        Ok(output)
    }
}
```

### Production I/O Implementation

```rust
/// Production sandbox I/O using libkrun
pub struct LibkrunSandboxIO {
    vm: Option<VmInstance>,
    config: LibkrunConfig,
}

#[async_trait]
impl SandboxIO for LibkrunSandboxIO {
    async fn boot_vm(&mut self, config: &VmConfig) -> SandboxResult<()> {
        // Real libkrun VM boot
        let vm = kelpie_libkrun::create_vm(config).await?;
        vm.start().await?;
        self.vm = Some(vm);
        Ok(())
    }

    async fn exec_in_vm(&self, cmd: &str, args: &[&str], opts: &ExecOptions)
        -> SandboxResult<ExecOutput>
    {
        // Real command execution in VM
        let vm = self.vm.as_ref().ok_or(SandboxError::NotRunning)?;
        let result = vm.exec_with_options(cmd, args, opts.into()).await?;
        Ok(result.into())
    }
}
```

### DST I/O Implementation

```rust
/// DST sandbox I/O with fault injection
pub struct SimSandboxIO {
    filesystem: HashMap<String, Bytes>,
    env: HashMap<String, String>,
    running: bool,
    rng: Arc<DeterministicRng>,
    faults: Arc<FaultInjector>,
    time: Arc<SimClock>,
}

#[async_trait]
impl SandboxIO for SimSandboxIO {
    async fn boot_vm(&mut self, _config: &VmConfig) -> SandboxResult<()> {
        // Check for boot fault
        if let Some(FaultType::SandboxBootFail) = self.faults.should_inject("sandbox_boot") {
            return Err(SandboxError::BootFailed {
                reason: "injected fault".into()
            });
        }

        // Simulated boot (instant, deterministic)
        self.running = true;
        Ok(())
    }

    async fn exec_in_vm(&self, cmd: &str, args: &[&str], opts: &ExecOptions)
        -> SandboxResult<ExecOutput>
    {
        // Check for exec fault
        if let Some(fault) = self.faults.should_inject("sandbox_exec") {
            match fault {
                FaultType::SandboxExecFail => {
                    return Err(SandboxError::ExecFailed { ... });
                }
                FaultType::SandboxExecTimeout { timeout_ms } => {
                    self.time.sleep_ms(timeout_ms).await;
                    return Err(SandboxError::Timeout { ... });
                }
                _ => {}
            }
        }

        // Simulated execution (deterministic output)
        Ok(ExecOutput {
            status: ExitStatus::success(),
            stdout: Bytes::from(format!("simulated: {} {:?}", cmd, args)),
            stderr: Bytes::new(),
            duration_ms: 1,
            ..Default::default()
        })
    }
}
```

### Storage I/O Abstraction

```rust
/// Storage I/O trait
#[async_trait]
pub trait StorageIO: Send + Sync {
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>>;
    async fn put(&self, key: &[u8], value: &[u8]) -> Result<()>;
    async fn delete(&self, key: &[u8]) -> Result<()>;
    async fn scan(&self, prefix: &[u8]) -> Result<Vec<(Bytes, Bytes)>>;
}

/// Production: FoundationDB
pub struct FdbStorageIO { /* ... */ }

/// DST: In-memory with faults
pub struct SimStorageIO {
    data: Arc<RwLock<HashMap<Bytes, Bytes>>>,
    faults: Arc<FaultInjector>,
    rng: Arc<DeterministicRng>,
}
```

## Implementation Phases

### Phase 1: Core Abstractions (kelpie-core) ✅ COMPLETE
- [x] Add `TimeProvider` trait (`crates/kelpie-core/src/io.rs`)
- [x] Add `RngProvider` trait (`crates/kelpie-core/src/io.rs`)
- [x] Add `WallClockTime` production impl
- [x] Add `StdRngProvider` production impl
- [x] Add `IoContext` bundling time and rng
- [x] Export in lib.rs

### Phase 2: Sandbox I/O Abstraction (kelpie-sandbox) ✅ COMPLETE
- [x] Define `SandboxIO` trait (`crates/kelpie-sandbox/src/io.rs`)
- [x] Create generic `GenericSandbox<IO: SandboxIO>` struct
- [x] Move state machine logic to GenericSandbox
- [x] State validation, lifecycle management shared between modes
- [x] Export in lib.rs
- [x] Tests pass

### Phase 3: DST Sandbox I/O (kelpie-dst) ✅ COMPLETE
- [x] Create `SimSandboxIO` implementing `SandboxIO` trait (`crates/kelpie-dst/src/sandbox_io.rs`)
- [x] Integrate fault injection into SimSandboxIO
- [x] Use SimClock for all time operations
- [x] Create `SimSandboxIOFactory` for creating sandboxes
- [x] All 5 sandbox_io tests pass
- [x] Existing SimSandbox deprecated but kept for backward compat

### Phase 4: Wire IoContext Through Simulation ✅ COMPLETE
- [x] Updated `SimEnvironment` to include `IoContext`
- [x] Updated `SimEnvironment` to use `Arc<SimClock>` and `Arc<DeterministicRng>`
- [x] Added `sandbox_io_factory` (new proper DST factory)
- [x] Added `time()` and `rng_provider()` methods for IoContext access
- [x] Updated `SimAgentEnv` to use Arc types
- [x] All 70+ DST tests pass

### Phase 5: Verification ✅ COMPLETE
- [x] All kelpie-core tests pass
- [x] All kelpie-sandbox tests pass
- [x] All kelpie-dst tests pass (70+ tests)
- [x] `GenericSandbox<SimSandboxIO>` uses SAME state machine code
- [x] Fault injection works through `SimSandboxIO`
- [x] Determinism verified

### Phase 6: Storage I/O (DEFERRED)
Storage already has clean abstraction via `ActorKV` trait:
- `MemoryKV` - for testing
- `SimStorage` - for DST with fault injection
- `FdbKV` - for production (feature-gated)
No additional refactoring needed at this time.

### Phase 7: Production Integration (FUTURE)
- [ ] Create `LibkrunSandboxIO` implementing `SandboxIO`
- [ ] Wire production code to use `GenericSandbox<LibkrunSandboxIO>`
- [ ] Update kelpie-server to use unified architecture
- [ ] Full end-to-end DST of production paths

## What to Try Now

### Works Now ✅
- **Create sandboxes with proper DST architecture:**
  ```rust
  let factory = SimSandboxIOFactory::new(rng, faults, clock);
  let mut sandbox = factory.create(SandboxConfig::default()).await?;
  sandbox.start().await?;
  sandbox.exec_simple("echo", &["hello"]).await?;
  ```
- **Access unified IoContext in SimEnvironment:**
  ```rust
  Simulation::new(config).run_async(|env| async move {
      let time = env.time();  // Arc<dyn TimeProvider>
      let rng = env.rng_provider();  // Arc<dyn RngProvider>
      // Use env.sandbox_io_factory for proper DST sandboxes
      Ok(())
  })
  ```
- **Run all DST tests:**
  ```bash
  cargo test -p kelpie-dst  # 70+ tests pass
  ```

### Doesn't Work Yet
- **kelpie-server compilation**: Has pre-existing LLM client issues unrelated to DST refactor
- **Production LibkrunSandboxIO**: Not yet created - still needs `impl SandboxIO for LibkrunSandbox`

### Known Limitations
- Old `SimSandbox` kept for backward compatibility (deprecated)
- Storage uses existing `ActorKV` trait (good enough, deferred full refactor)
- Full production integration pending (Phase 7)

## Success Criteria

1. **Single codebase**: `Sandbox<IO>` used in both production and DST
2. **Shared logic**: State machine, validation, etc. runs in both modes
3. **I/O separation**: Only I/O differs between modes
4. **Fault injection at boundary**: Faults injected in SimSandboxIO, not in Sandbox
5. **Deterministic time**: All time from TimeProvider, never wall clock
6. **Reproducible**: Same seed produces identical behavior
7. **Test coverage**: DST tests exercise production code paths

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-14 | Generic `Sandbox<IO>` over trait objects | Better type safety, inlining | More complex types |
| 2026-01-14 | IoContext bundle over individual injection | Simpler API, atomic swap | Slightly less flexible |
| 2026-01-14 | Start with Sandbox refactor | Most complex, establishes pattern | Larger initial effort |

## References

- FoundationDB Testing: https://www.foundationdb.org/files/fdb-paper.pdf
- TigerBeetle Simulation: https://github.com/tigerbeetle/tigerbeetle
- Current SimSandbox (to be replaced): `crates/kelpie-dst/src/sandbox.rs`
- Current LibkrunSandbox: `crates/kelpie-sandbox/src/libkrun.rs`

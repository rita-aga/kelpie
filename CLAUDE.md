# CLAUDE.md - Kelpie Development Guide

This document provides guidance for AI assistants (and human developers) contributing to Kelpie.

## Project Overview

Kelpie is a distributed virtual actor system with linearizability guarantees, designed for AI agent orchestration and general stateful distributed systems. Built with DST-first (Deterministic Simulation Testing) and TigerStyle engineering principles.

## Quick Commands

```bash
# Build the entire workspace
cargo build

# Run all tests
cargo test

# Run tests with DST seed for reproduction
DST_SEED=12345 cargo test -p kelpie-dst

# Run specific crate tests
cargo test -p kelpie-core
cargo test -p kelpie-dst

# Format code
cargo fmt

# Run clippy
cargo clippy --all-targets --all-features

# Run benchmarks
cargo bench -p kelpie-runtime
```

## Architecture

```
kelpie/
├── crates/
│   ├── kelpie-core/      # Core types, errors, constants
│   ├── kelpie-runtime/   # Actor runtime and dispatcher
│   ├── kelpie-registry/  # Actor placement and discovery
│   ├── kelpie-storage/   # Per-actor KV storage
│   ├── kelpie-wasm/      # WASM actor runtime
│   ├── kelpie-cluster/   # Cluster coordination
│   ├── kelpie-agent/     # AI agent abstractions
│   ├── kelpie-dst/       # Deterministic Simulation Testing
│   ├── kelpie-server/    # Standalone server binary
│   └── kelpie-cli/       # CLI tools
├── docs/adr/             # Architecture Decision Records
└── tests/                # Integration tests
```

## TigerStyle Engineering Principles

Kelpie follows TigerBeetle's TigerStyle: **Safety > Performance > DX**

### 1. Explicit Constants with Units

All limits are named constants with units in the name:

```rust
// Good - unit in name, explicit limit
pub const ACTOR_INVOCATION_TIMEOUT_MS_MAX: u64 = 30_000;
pub const ACTOR_STATE_SIZE_BYTES_MAX: usize = 10 * 1024 * 1024;

// Bad - unclear units, magic number
pub const TIMEOUT: u64 = 30000;
const MAX_SIZE: usize = 10485760;
```

### 2. Big-Endian Naming

Name identifiers from big to small concept:

```rust
// Good - big to small
actor_id_length_bytes_max
network_latency_ms_base
storage_write_batch_size

// Bad - small to big
max_actor_id_length
base_latency_ms
batch_size_storage_write
```

### 3. Assertions (2+ per Function)

Every non-trivial function should have at least 2 assertions:

```rust
pub fn set_timeout(&mut self, timeout_ms: u64) {
    // Precondition
    assert!(timeout_ms > 0, "timeout must be positive");
    assert!(timeout_ms <= TIMEOUT_MS_MAX, "timeout exceeds maximum");

    self.timeout_ms = timeout_ms;

    // Postcondition
    assert!(self.timeout_ms > 0);
}
```

### 4. Prefer u64 Over usize for Sizes

Use fixed-width integers for portability:

```rust
// Good - portable across platforms
pub fn size_bytes(&self) -> u64;
pub fn item_count(&self) -> u64;

// Bad - varies by platform
pub fn size_bytes(&self) -> usize;
```

### 5. No Silent Truncation

Avoid implicit conversions that could truncate:

```rust
// Good - explicit conversion with assertion
let size: u64 = data.len() as u64;
assert!(size <= u32::MAX as u64, "size too large for u32");
let size_u32: u32 = size as u32;

// Bad - silent truncation
let size: u32 = data.len() as u32;
```

### 6. Explicit Error Handling

No unwrap() in production code (only tests):

```rust
// Good - explicit error handling
let value = self.storage.get(key)?;
let config = Config::load().map_err(|e| Error::ConfigInvalid { reason: e.to_string() })?;

// Bad - panics in production
let value = self.storage.get(key).unwrap();
```

### 7. Debug Assertions for Expensive Checks

Use `debug_assert!` for checks that are too expensive for release:

```rust
pub fn insert(&mut self, key: &[u8], value: &[u8]) {
    // Cheap check - always run
    assert!(key.len() <= KEY_LENGTH_BYTES_MAX);

    // Expensive check - debug only
    debug_assert!(self.validate_key_uniqueness(key));

    // ...
}
```

## DST (Deterministic Simulation Testing)

### Core Principles

1. **All randomness flows from a single seed** - set `DST_SEED` to reproduce
2. **Simulated time** - `SimClock` replaces wall clock
3. **Explicit fault injection** - 16+ fault types with configurable probability
4. **Deterministic network** - `SimNetwork` with partitions, delays, reordering

### Running DST Tests

```bash
# Run with random seed (logged for reproduction)
cargo test -p kelpie-dst

# Reproduce specific run
DST_SEED=12345 cargo test -p kelpie-dst

# Stress test (longer, more iterations)
cargo test -p kelpie-dst stress --release -- --ignored
```

### Writing DST Tests

```rust
use kelpie_dst::{Simulation, SimConfig, FaultConfig, FaultType};

#[test]
fn test_actor_under_faults() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.05))
        .run(|env| async move {
            // Test logic using env.storage, env.network, env.clock
            env.storage.write(b"key", b"value").await?;

            // Advance simulated time
            env.advance_time_ms(1000);

            // Verify invariants
            let value = env.storage.read(b"key").await?;
            assert_eq!(value, Some(Bytes::from("value")));

            Ok(())
        });

    assert!(result.is_ok());
}
```

### Fault Types

| Category | Fault Types |
|----------|-------------|
| Storage | `StorageWriteFail`, `StorageReadFail`, `StorageCorruption`, `StorageLatency`, `DiskFull` |
| Crash | `CrashBeforeWrite`, `CrashAfterWrite`, `CrashDuringTransaction` |
| Network | `NetworkPartition`, `NetworkDelay`, `NetworkPacketLoss`, `NetworkMessageReorder` |
| Time | `ClockSkew`, `ClockJump` |
| Resource | `OutOfMemory`, `CPUStarvation` |

## Code Style

### Module Organization

```rust
//! Module-level documentation with TigerStyle note
//!
//! TigerStyle: Brief description of the module's invariants.

// Imports grouped by: std, external crates, internal crates, local modules
use std::collections::HashMap;
use std::sync::Arc;

use bytes::Bytes;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use kelpie_core::{ActorId, Error, Result};

use crate::internal_module;
```

### Struct Layout

```rust
/// Brief description
///
/// Longer description if needed.
#[derive(Debug, Clone)]
pub struct ActorContext<S> {
    // Public fields at top with documentation
    /// The actor's unique identifier
    pub id: ActorId,
    /// The actor's state
    pub state: S,

    // Private fields below
    kv: Box<dyn ActorKV>,
    runtime: ActorRuntime,
}
```

### Function Signatures

```rust
/// Brief description of what the function does.
///
/// # Arguments
/// * `key` - The key to look up
///
/// # Returns
/// The value if found, None otherwise
///
/// # Errors
/// Returns `Error::StorageReadFailed` if the storage operation fails
pub async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> {
    // Preconditions
    assert!(!key.is_empty(), "key cannot be empty");
    assert!(key.len() <= KEY_LENGTH_BYTES_MAX);

    // Implementation...
}
```

## Testing Guidelines

### Test Naming

```rust
#[test]
fn test_actor_id_valid() { }           // Positive case
#[test]
fn test_actor_id_too_long() { }        // Edge case
#[test]
fn test_actor_id_invalid_chars() { }   // Error case
```

### Property-Based Testing

Use proptest for invariant testing:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_actor_id_roundtrip(namespace in "[a-z]{1,10}", id in "[a-z0-9]{1,10}") {
        let actor_id = ActorId::new(&namespace, &id).unwrap();
        let serialized = serde_json::to_string(&actor_id).unwrap();
        let deserialized: ActorId = serde_json::from_str(&serialized).unwrap();
        assert_eq!(actor_id, deserialized);
    }
}
```

### DST Test Coverage

Every critical path must have DST coverage:
- [ ] Actor activation/deactivation
- [ ] State persistence and recovery
- [ ] Cross-actor invocation
- [ ] Failure detection and recovery
- [ ] Migration correctness

## Error Handling

### Error Types (kelpie-core)

```rust
#[derive(Error, Debug)]
pub enum Error {
    #[error("actor not found: {id}")]
    ActorNotFound { id: String },

    #[error("storage read failed for key '{key}': {reason}")]
    StorageReadFailed { key: String, reason: String },

    // ...
}
```

### Result Type

```rust
// All fallible operations return kelpie_core::Result
pub type Result<T> = std::result::Result<T, Error>;
```

### Retriable Errors

```rust
impl Error {
    /// Whether this error is retriable
    pub fn is_retriable(&self) -> bool {
        matches!(self,
            Error::StorageReadFailed { .. } |
            Error::NetworkTimeout { .. } |
            Error::TransactionConflict
        )
    }
}
```

## Performance Guidelines

### Allocation

- Prefer stack allocation for small, fixed-size data
- Use `Bytes` for byte buffers (zero-copy slicing)
- Pool allocations for hot paths

### Async

- Use `tokio` runtime with `current_thread` flavor for DST
- Avoid blocking operations in async contexts
- Use channels for cross-task communication

### Benchmarking

```bash
# Run all benchmarks
cargo bench

# Run specific benchmark
cargo bench -p kelpie-runtime -- single_actor
```

## Documentation

### ADRs (Architecture Decision Records)

All significant architectural decisions are documented in `docs/adr/`:

- `001-virtual-actor-model.md` - Why virtual actors
- `002-foundationdb-integration.md` - Storage layer design
- `003-wasm-actor-runtime.md` - WASM support
- `004-linearizability-guarantees.md` - Consistency model
- `005-dst-framework.md` - Testing approach

### Code Documentation

- All public items must have doc comments
- Include examples for complex APIs
- Document invariants and safety requirements

## Commit Policy: Only Working Software

**Never commit broken code.** Every commit must represent working software.

### Pre-Commit Verification

Before every commit, you MUST verify the code works:

```bash
# Required before EVERY commit
cargo test           # All tests must pass
cargo clippy         # No warnings allowed
cargo fmt --check    # Code must be formatted
```

### Why This Matters

- Every commit is a potential rollback point
- Broken commits make `git bisect` useless
- CI should never be the first place code is tested
- Other developers should be able to checkout any commit

### Commit Checklist

Before running `git commit`:

1. **Run `cargo test`** - All tests must pass (currently 74+ tests)
2. **Run `cargo clippy`** - Fix any warnings
3. **Run `cargo fmt`** - Code must be formatted
4. **Review changes** - `git diff` to verify what's being committed
5. **Write clear message** - Describe what and why, not how

### If Tests Fail

Do NOT commit. Instead:
1. Fix the failing tests
2. If the fix is complex, consider `git stash` to save work
3. Never use `--no-verify` to skip pre-commit hooks
4. Never commit with `// TODO: fix this test` comments

## Contributing

1. Create a branch from `main`
2. Make changes following this guide
3. **Run `cargo test` and ensure ALL tests pass**
4. **Run `cargo clippy` and fix ALL warnings**
5. Run `cargo fmt` to format code
6. Update documentation as needed
7. Create PR with clear description

## References

- [TigerStyle](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md)
- [NOLA - Go Virtual Actors](https://github.com/richardartoul/nola)
- [FoundationDB Testing](https://www.foundationdb.org/files/fdb-paper.pdf)
- [Stateright - Rust Model Checker](https://github.com/stateright/stateright)

# TLA+ to DST Test Mapping

This document tracks the mapping between TLA+ specifications and their corresponding DST (Deterministic Simulation Testing) implementations.

## Overview

Each TLA+ invariant is implemented as a Rust struct in `crates/kelpie-dst/src/invariants.rs` and verified in DST tests. This ensures that the formal properties defined in TLA+ are actively checked at runtime during testing.

## Invariant Status Legend

- ✅ **Verified**: Invariant is implemented and actively checked in DST tests
- 🔄 **Partial**: Implementation exists but not yet integrated into all relevant tests
- ❌ **TODO**: Invariant defined in TLA+ but not yet implemented in Rust

## KelpieSingleActivation.tla

Core single activation guarantee for virtual actors.

| TLA+ Invariant | Rust Implementation | DST Tests | Status | Notes |
|----------------|---------------------|-----------|--------|-------|
| **SingleActivation** | `invariants::SingleActivation` | `single_activation_dst.rs::test_concurrent_activation_*` | ✅ Verified | At most 1 node Active per actor |
| **ConsistentHolder** | `invariants::ConsistentHolder` | `single_activation_dst.rs::test_consistent_holder_invariant` | ✅ Verified | Active node matches FDB holder |
| **TypeOK** | Enforced by Rust type system | N/A (compile-time) | ✅ Verified | Type safety guaranteed by Rust |

### Test Coverage

```rust
// Single activation tests with explicit invariant verification
test_concurrent_activation_single_winner()
test_concurrent_activation_high_contention()
test_single_activation_with_network_partition()
test_single_activation_with_crash_recovery()
test_consistent_holder_invariant()
```

**Verification Method**: Tests build `SystemState` from protocol state and call `InvariantChecker::verify_all()` with `SingleActivation` and `ConsistentHolder` invariants.

**Fault Injection Coverage**:
- Storage write failures (20% probability)
- Transaction crash faults (30% probability)
- Network delays (10-100ms latency)
- Network partitions (guaranteed)

## KelpieLinearizability.tla

Linearization points for client-visible operations.

| TLA+ Invariant | Rust Implementation | DST Tests | Status | Notes |
|----------------|---------------------|-----------|--------|-------|
| **ReadYourWrites** | `invariants::ReadYourWrites` | `actor_lifecycle_dst.rs` (planned) | 🔄 Partial | Client sees own claim in subsequent read |
| **MonotonicReads** | `invariants::MonotonicReads` | `actor_lifecycle_dst.rs` (planned) | 🔄 Partial | Reads don't regress without release |
| **DispatchConsistency** | TODO | N/A | ❌ TODO | Dispatch succeeds iff actor owned |
| **SequentialPerActor** | TODO | N/A | ❌ TODO | Operations on same actor are ordered |

### Test Coverage (Planned)

```rust
// Linearizability tests (to be added)
test_read_your_writes_invariant()
test_monotonic_reads_invariant()
test_dispatch_consistency()
```

**Implementation Status**: Invariant structs implemented with unit tests. Integration into DST tests pending.

## KelpieRegistry.tla

Actor placement and discovery.

| TLA+ Invariant | Rust Implementation | DST Tests | Status | Notes |
|----------------|---------------------|-----------|--------|-------|
| **PlacementConsistency** | `invariants::PlacementConsistency` | `cluster_dst.rs` (partial) | 🔄 Partial | No placement on failed nodes |
| **UniqueActivation** | Verified via SingleActivation | `single_activation_dst.rs` | ✅ Verified | One activation per actor |

### Test Coverage

```rust
// Cluster tests
test_cluster_node_failure()  // Should verify PlacementConsistency
```

**Next Steps**: Add explicit `PlacementConsistency` checks to cluster DST tests.

## KelpieLease.tla

Lease-based actor ownership.

| TLA+ Invariant | Rust Implementation | DST Tests | Status | Notes |
|----------------|---------------------|-----------|--------|-------|
| **LeaseUniqueness** | `invariants::LeaseUniqueness` | `lease_dst.rs` | ✅ Verified | At most 1 node believes it holds lease |
| **LeaseValidity** | TODO | N/A | ❌ TODO | Valid lease implies FDB holder match |

### Test Coverage

```rust
// Lease tests
test_lease_expiry()
test_lease_renewal()
test_concurrent_lease_claims()
```

**Verification Method**: Tests populate `SystemState` with lease beliefs and current time, then verify `LeaseUniqueness`.

## KelpieWAL.tla

Write-Ahead Log durability and atomicity.

| TLA+ Invariant | Rust Implementation | DST Tests | Status | Notes |
|----------------|---------------------|-----------|--------|-------|
| **Durability** | `invariants::Durability` | `storage_dst.rs` (planned) | 🔄 Partial | Completed WAL → visible in storage |
| **AtomicVisibility** | `invariants::AtomicVisibility` | `storage_dst.rs` (planned) | 🔄 Partial | Operations are all-or-nothing |
| **Idempotency** | TODO | N/A | ❌ TODO | Duplicate requests have same effect |

### Test Coverage (Planned)

```rust
// WAL tests (to be added)
test_wal_durability()
test_wal_atomic_visibility()
test_wal_idempotency()
```

## KelpieTeleport.tla

Actor migration and state transfer.

| TLA+ Invariant | Rust Implementation | DST Tests | Status | Notes |
|----------------|---------------------|-----------|--------|-------|
| **StateConsistency** | TODO | N/A | ❌ TODO | State preserved across teleport |
| **SingleActivationDuringTeleport** | Verified via SingleActivation | `teleport_service_dst.rs` | ✅ Verified | No dual activation during migration |

### Test Coverage

```rust
// Teleport tests
test_teleport_concurrent_messages()  // Verifies SingleActivation during migration
```

## Verification Infrastructure

### InvariantChecker

The `InvariantChecker` from `kelpie-dst/src/invariants.rs` provides:

```rust
let checker = InvariantChecker::new()
    .with_invariant(SingleActivation)
    .with_invariant(ConsistentHolder)
    .with_invariant(LeaseUniqueness);

// Fail-fast: stop at first violation
checker.verify_all(&system_state)?;

// Collect all violations for debugging
let violations = checker.verify_all_collect(&system_state);
```

### Standard Invariants

The `with_standard_invariants()` method adds all core Kelpie invariants:

```rust
let checker = InvariantChecker::new().with_standard_invariants();
// Includes: SingleActivation, ConsistentHolder, PlacementConsistency,
//           LeaseUniqueness, Durability, AtomicVisibility
```

### SystemState Construction

DST tests build `SystemState` by:

1. Extracting distributed system state (node states, FDB holder, leases, etc.)
2. Populating `SystemState` using builder methods
3. Passing to `InvariantChecker`

Example:

```rust
let mut system_state = SystemState::new()
    .with_time(current_time)
    .with_node(NodeInfo::new("node-1").with_actor_state("actor-1", NodeState::Active))
    .with_fdb_holder("actor-1", Some("node-1".to_string()));

checker.verify_all(&system_state)?;
```

## Testing Strategy

### Unit Tests (Fast, ~5s)

Each invariant has unit tests in `invariants.rs`:

```bash
cargo test -p kelpie-dst invariants
```

### Integration Tests (Moderate, ~30s)

DST tests verify invariants under various conditions:

```bash
cargo test -p kelpie-dst --test single_activation_dst
cargo test -p kelpie-dst --test lease_dst
```

### Stress Tests (Slow, ~5min)

Long-running tests with random seeds:

```bash
cargo test -p kelpie-dst single_activation_stress -- --ignored
cargo test -p kelpie-dst --release  # Faster stress tests
```

## Fault Injection Coverage

Invariants are tested under:

| Fault Type | Coverage | Affected Invariants |
|------------|----------|---------------------|
| **StorageWriteFail** | 10-20% | SingleActivation, Durability |
| **CrashDuringTransaction** | 10-30% | ConsistentHolder, AtomicVisibility |
| **NetworkPartition** | Guaranteed (100%) | SingleActivation |
| **StorageLatency** | 50% (10-100ms) | SingleActivation, LeaseUniqueness |
| **ClockSkew** | 20% (±50ms) | LeaseUniqueness |

## Adding New Invariants

To add a new TLA+ invariant to DST:

1. **Define in TLA+**: Document the invariant in the appropriate `.tla` file
2. **Implement in Rust**: Add to `invariants.rs` with `Invariant` trait
3. **Add Unit Tests**: Test the invariant logic in isolation
4. **Integrate in DST**: Update relevant `*_dst.rs` tests to build `SystemState` and verify
5. **Update This Document**: Add entry to mapping table with status

### Example: Adding a new invariant

```rust
// 1. Define struct in invariants.rs
pub struct MyNewInvariant;

impl Invariant for MyNewInvariant {
    fn name(&self) -> &'static str {
        "MyNewInvariant"
    }

    fn tla_source(&self) -> &'static str {
        "docs/tla/KelpieMySpec.tla"
    }

    fn check(&self, state: &SystemState) -> Result<(), InvariantViolation> {
        // Check logic here
        Ok(())
    }
}

// 2. Add unit tests
#[cfg(test)]
mod tests {
    #[test]
    fn test_my_new_invariant_passes() { /* ... */ }
}

// 3. Use in DST tests
#[test]
fn test_my_feature() {
    let result = Simulation::new(config).run(|_env| async move {
        // ... test logic ...

        let system_state = build_system_state();
        MyNewInvariant.check(&system_state)?;

        Ok(())
    });
}
```

## References

- TLA+ Specs: `docs/tla/*.tla`
- Invariant Implementations: `crates/kelpie-dst/src/invariants.rs`
- DST Tests: `crates/kelpie-dst/tests/*_dst.rs`
- Liveness Properties: `crates/kelpie-dst/src/liveness.rs`

## Verification Workflow

```
┌─────────────────────────────────────────────────────────────┐
│  TLA+ Specification                                         │
│  ├── Define invariants (TypeOK, SingleActivation, etc.)    │
│  └── Model check with TLC                                   │
└──────────────────┬──────────────────────────────────────────┘
                   │
                   │ Translate
                   ▼
┌─────────────────────────────────────────────────────────────┐
│  Rust Invariant Implementation                              │
│  ├── Implement `Invariant` trait                            │
│  ├── Add unit tests                                         │
│  └── Export from invariants.rs                              │
└──────────────────┬──────────────────────────────────────────┘
                   │
                   │ Integrate
                   ▼
┌─────────────────────────────────────────────────────────────┐
│  DST Tests                                                  │
│  ├── Run distributed simulation                             │
│  ├── Extract SystemState                                    │
│  ├── Call InvariantChecker::verify_all()                   │
│  └── Assert no violations                                   │
└─────────────────────────────────────────────────────────────┘
```

## Known Limitations

1. **Operation History**: Linearizability invariants (ReadYourWrites, MonotonicReads) require operation history tracking. Currently implemented as standalone invariant structs but not yet integrated into `SystemState`.

2. **Time-Dependent Invariants**: Lease expiry and time-based properties require careful time provider injection in DST.

3. **Cross-Crate Invariants**: Some invariants span multiple crates (e.g., kelpie-storage, kelpie-cluster). Integration tests may be needed.

## Future Work

- [ ] Integrate ReadYourWrites/MonotonicReads into actor lifecycle DST tests
- [ ] Add DispatchConsistency invariant and tests
- [ ] Add WAL idempotency invariant
- [ ] Create InvariantCheckingSimulation harness (automatic checking after each step)
- [ ] Add operation history tracking to SystemState
- [ ] Model check linearizability with Elle or Jepsen-style checker
- [ ] Cross-crate invariant integration tests

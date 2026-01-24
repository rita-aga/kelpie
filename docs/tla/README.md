# Kelpie TLA+ Specifications

This directory contains TLA+ specifications for formally verifying Kelpie's distributed actor system.

## Overview

TLA+ is a formal specification language for describing concurrent and distributed systems. These specs verify critical safety and liveness properties of Kelpie actors.

## Prerequisites

Download TLA+ tools:
```bash
curl -L -o ~/tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
```

Requires Java 11+.

## Specifications

### KelpieLease.tla

Models the lease-based actor ownership protocol from ADR-004, verifying:
- **G2.2 (Atomic Lease Operations)**: Lease acquisition/renewal via atomic CAS
- **G4.2 (Single Activation)**: At most one node holds a valid lease per actor

#### State Variables
- `leases`: Ground truth - actual lease holder and expiry per actor
- `clock`: Global wall clock time
- `nodeBeliefs`: What each node believes it owns (can diverge from ground truth in buggy version)

#### Actions
| Action | Description | Precondition |
|--------|-------------|--------------|
| `AcquireLeaseSafe` | Atomic CAS lease acquisition | No valid lease exists |
| `AcquireLeaseNoCheck` | Buggy: claim without checking | Node doesn't already believe it has lease |
| `RenewLeaseSafe` | Extend lease duration | Current holder only |
| `TickClock` | Advance time, expire stale beliefs | clock < MaxClock |
| `ReleaseLease` | Voluntary deactivation | Node holds lease |

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type constraints on all variables | - |
| `LeaseUniqueness` | At most one node believes it holds a valid lease | ADR-004 G4.2 |
| `RenewalRequiresOwnership` | Only lease holder can renew | ADR-002 G2.2 |
| `LeaseValidityBounds` | Lease expiry within configured bounds | - |
| `BeliefConsistency` | Node beliefs match ground truth (safe only) | - |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualLeaseResolution` | Eventually a lease is granted or expires |

#### TLC Results
- **Safe version**: PASS (679 distinct states, 3171 generated, depth 9)
- **Buggy version**: FAIL - LeaseUniqueness violated in 5 states

#### Counterexample (Buggy Version)
```
State 1: Initial - no leases
State 2: n1 acquires lease (holder=n1, n1 believes it has it)
State 3: n2 acquires WITHOUT CHECK (holder=n2, but BOTH n1 and n2 believe they have it!)
```

This demonstrates why FDB's atomic transactions are essential - without CAS semantics, race conditions allow dual activation.

---

### KelpieActorLifecycle.tla

Models the lifecycle of a Kelpie virtual actor, verifying:
- **G1.3 (Lifecycle Ordering)**: No invoke without activate, no deactivate during invoke
- **G1.5 (Idle Timeout)**: Actors deactivate after idle timeout

#### State Variables
- `state`: Actor lifecycle state (`Inactive`, `Activating`, `Active`, `Deactivating`)
- `pending`: Number of pending invocations (0..MAX_PENDING)
- `idleTicks`: Ticks since last activity (for idle timeout tracking)

#### Actions
| Action | Description | Precondition |
|--------|-------------|--------------|
| `Activate` | Start activation | state = Inactive |
| `CompleteActivation` | Finish activation | state = Activating |
| `StartInvoke` | Begin invocation | state = Active (safe) or any state (buggy) |
| `CompleteInvoke` | Finish invocation | pending > 0 |
| `IdleTick` | Advance idle timer | state = Active, pending = 0 |
| `StartDeactivate` | Begin deactivation | state = Active, pending = 0, idleTicks >= IDLE_TIMEOUT |
| `CompleteDeactivate` | Finish deactivation | state = Deactivating |

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type constraints on all variables | - |
| `LifecycleOrdering` | Invocations only when Active | ADR-001 G1.3 |
| `GracefulDeactivation` | No pending invocations when deactivating | ADR-001 G1.3 |
| `IdleTimeoutRespected` | Deactivation only after timeout | ADR-001 G1.5 |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualActivation` | Activation always completes |
| `EventualDeactivation` | Idle actors eventually deactivate (not checked - busy actors shouldn't deactivate) |
| `EventualInvocationCompletion` | Invocations eventually complete (not checked - model allows infinite invocations) |

#### TLC Results
- **Safe version**: PASS (19 states generated, 11 distinct states, depth 8)
- **Buggy version**: FAIL - LifecycleOrdering violated

#### Counterexample (Buggy Version)
```
State 1: /\ pending = 0 /\ state = "Inactive" /\ idleTicks = 0
State 2: /\ pending = 1 /\ state = "Inactive" /\ idleTicks = 0
```

#### Configuration Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `MAX_PENDING` | 2 | Maximum concurrent invocations |
| `IDLE_TIMEOUT` | 3 | Ticks before idle deactivation |
| `BUGGY` | FALSE | Enable buggy behavior for testing |

#### Mapping to Rust Implementation

| TLA+ Concept | Rust Implementation |
|--------------|---------------------|
| `state` variable | `ActivationState` enum in `activation.rs` |
| `pending` variable | `pending_counts` in `dispatcher.rs` |
| `idleTicks` | `idle_time()` from `ActivationStats` |
| `StartInvoke` | `DispatcherHandle::invoke()` |
| `process_invocation` assertion | `assert!(self.state == ActivationState::Active)` |
| `should_deactivate()` | Check in `should_deactivate()` method |

---

### KelpieMigration.tla

Models Kelpie's 3-phase actor migration protocol:

```
PREPARE → TRANSFER → COMPLETE
```

**Reference Implementation:** `crates/kelpie-cluster/src/handler.rs`

#### Safety Invariants

| Invariant | Description |
|-----------|-------------|
| `MigrationAtomicity` | Complete migration transfers full state |
| `NoStateLoss` | Actor state is never lost during migration |
| `SingleActivationDuringMigration` | At most one active instance during migration |
| `MigrationRollback` | Failed migration leaves actor recoverable |

#### Liveness Properties

| Property | Description |
|----------|-------------|
| `EventualMigrationCompletion` | Started migrations eventually complete or fail |
| `EventualRecovery` | Actors with pending recovery eventually recover |

#### TLC Results
- **Safe version**: PASS (59 distinct states)
- **Buggy version**: FAIL - MigrationAtomicity violated

---

## Running TLC Model Checker

### Safe Configurations (should pass)
```bash
cd docs/tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieLease.cfg KelpieLease.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle.cfg KelpieActorLifecycle.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieMigration.cfg KelpieMigration.tla
```

### Buggy Configurations (should fail)
```bash
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieLease_Buggy.cfg KelpieLease.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle_Buggy.cfg KelpieActorLifecycle.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieMigration_Buggy.cfg KelpieMigration.tla
```

## Adding New Specs

1. Create `.tla` file with specification
2. Create `.cfg` configuration file (Safe and Buggy)
3. Add documentation to this README
4. Run TLC to verify
5. Add test scripts if needed

## References

- [ADR-001: Virtual Actor Model](../adr/001-virtual-actor-model.md)
- [ADR-002: FoundationDB Integration](../adr/002-foundationdb-integration.md)
- [ADR-004: Linearizability Guarantees](../adr/004-linearizability-guarantees.md)
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [TLC Model Checker](https://lamport.azurewebsites.net/tla/tools.html)
- [Learn TLA+](https://learntla.com/)

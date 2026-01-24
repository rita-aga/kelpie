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

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type constraints on all variables | - |
| `LeaseUniqueness` | At most one node believes it holds a valid lease | ADR-004 G4.2 |
| `RenewalRequiresOwnership` | Only lease holder can renew | ADR-002 G2.2 |

#### TLC Results
- **Safe version**: PASS (679 distinct states, 3171 generated, depth 9)
- **Buggy version**: FAIL - LeaseUniqueness violated in 5 states

---

### KelpieActorLifecycle.tla

Models the lifecycle of a Kelpie virtual actor, verifying:
- **G1.3 (Lifecycle Ordering)**: No invoke without activate, no deactivate during invoke
- **G1.5 (Idle Timeout)**: Actors deactivate after idle timeout

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type constraints on all variables | - |
| `LifecycleOrdering` | Invocations only when Active | ADR-001 G1.3 |
| `GracefulDeactivation` | No pending invocations when deactivating | ADR-001 G1.3 |
| `IdleTimeoutRespected` | Deactivation only after timeout | ADR-001 G1.5 |

#### TLC Results
- **Safe version**: PASS (19 states generated, 11 distinct states, depth 8)
- **Buggy version**: FAIL - LifecycleOrdering violated

---

### KelpieMigration.tla

Models Kelpie's 3-phase actor migration protocol:

```
PREPARE → TRANSFER → COMPLETE
```

#### Safety Invariants

| Invariant | Description |
|-----------|-------------|
| `MigrationAtomicity` | Complete migration transfers full state |
| `NoStateLoss` | Actor state is never lost during migration |
| `SingleActivationDuringMigration` | At most one active instance during migration |
| `MigrationRollback` | Failed migration leaves actor recoverable |

#### TLC Results
- **Safe version**: PASS (59 distinct states)
- **Buggy version**: FAIL - MigrationAtomicity violated

---

### KelpieActorState.tla

Models the actor state management and transaction semantics from ADR-008.

#### Safety Invariants

| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type invariant for all variables | - |
| `RollbackCorrectness` | After rollback, memory equals pre-invocation snapshot | ADR-008 G8.2 |
| `BufferEmptyWhenIdle` | Transaction buffer empty when not running | - |

#### TLC Results
- **Safe version**: PASS (136 generated, 60 distinct states)
- **Buggy version**: FAIL - RollbackCorrectness violated

---

### KelpieFDBTransaction.tla

Models FoundationDB transaction semantics that Kelpie relies on for correctness:
- **G2.4 (Conflict Detection)**: Read-write conflicts are detected and cause transaction abort
- **G4.1 (Atomic Operations)**: Transaction writes are all-or-nothing

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type correctness of all state variables | - |
| `SerializableIsolation` | Committed transactions respect serial order | ADR-004 G4.1 |
| `ConflictDetection` | Read-write conflicts properly detected | ADR-002 G2.4 |
| `AtomicCommit` | Writes are all-or-nothing | ADR-002 G2.4 |

#### TLC Results
- **Safe version**: PASS (56,193 distinct states, 308,867 generated, depth 13)
- **Buggy version**: FAIL - SerializableIsolation violated at depth 7

---

### KelpieTeleport.tla

Models teleport state consistency for VM snapshot operations from ADR-020:
- **G20.1 (Snapshot Consistency)**: Restored state equals pre-snapshot state
- **G20.2 (Architecture Validation)**: Teleport requires same architecture

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeInvariant` | All variables have correct types | - |
| `SnapshotConsistency` | Restored state equals pre-snapshot state | ADR-020 G20.1 |
| `ArchitectureValidation` | Teleport/Suspend require same architecture | ADR-020 G20.2 |

#### TLC Results
- **Safe version**: PASS (1,508 distinct states, 4,840 generated)
- **Buggy version**: FAIL - ArchitectureValidation violated at depth 4

---

### KelpieSingleActivation.tla

Models the single-activation guarantee with explicit FDB transaction semantics:
- **G4.2 (Single Activation)**: At most one node can have an actor active at any time

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | All variables have valid types | - |
| `SingleActivation` | At most one node active at any time | ADR-004 G4.2 |
| `ConsistentHolder` | FDB holder matches node state | - |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualActivation` | Every claim eventually resolves (active or rejected) |

#### TLC Results
- **Safe version**: PASS (714 distinct states, 1429 generated, depth 27)

---

### KelpieRegistry.tla

Models the actor registry with node lifecycle and cache coherence:
- Node states: Active → Suspect → Failed
- Actor placement and discovery
- Cache invalidation

#### Safety Invariants
| Invariant | Description |
|-----------|-------------|
| `TypeOK` | All variables have correct types |
| `SingleActivation` | An actor is placed on at most one node at any time |
| `PlacementConsistency` | Authoritative placements never point to Failed nodes |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualFailureDetection` | Dead nodes are eventually detected and marked Failed |
| `EventualCacheInvalidation` | Stale cache entries on alive nodes are eventually corrected |

#### TLC Results
- **Safe version**: PASS (6,174 distinct states, 22,845 generated, depth 19)

---

## Running TLC Model Checker

### Safe Configurations (should pass)
```bash
cd docs/tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieLease.cfg KelpieLease.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle.cfg KelpieActorLifecycle.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieMigration.cfg KelpieMigration.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorState.cfg KelpieActorState.tla
java -XX:+UseParallelGC -Xmx4g -jar ~/tla2tools.jar -deadlock -config KelpieFDBTransaction.cfg KelpieFDBTransaction.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieTeleport.cfg KelpieTeleport.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieSingleActivation.cfg KelpieSingleActivation.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieRegistry.cfg KelpieRegistry.tla
```

### Buggy Configurations (should fail)
```bash
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieLease_Buggy.cfg KelpieLease.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle_Buggy.cfg KelpieActorLifecycle.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieMigration_Buggy.cfg KelpieMigration.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorState_Buggy.cfg KelpieActorState.tla
java -XX:+UseParallelGC -Xmx4g -jar ~/tla2tools.jar -deadlock -config KelpieFDBTransaction_Buggy.cfg KelpieFDBTransaction.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieTeleport_Buggy.cfg KelpieTeleport.tla
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
- [ADR-008: Transaction API](../adr/008-transaction-api.md)
- [ADR-020: Consolidated VM Crate](../adr/020-consolidated-vm-crate.md)
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [TLC Model Checker](https://lamport.azurewebsites.net/tla/tools.html)
- [Learn TLA+](https://learntla.com/)
- [FoundationDB Paper](https://www.foundationdb.org/files/fdb-paper.pdf)

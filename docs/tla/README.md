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

Models the lease-based actor ownership protocol from ADR-004.

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type constraints on all variables | - |
| `LeaseUniqueness` | At most one node believes it holds a valid lease | ADR-004 G4.2 |
| `RenewalRequiresOwnership` | Only lease holder can renew | ADR-002 G2.2 |

#### TLC Results
- **Safe version**: PASS (679 distinct states)
- **Buggy version**: FAIL - LeaseUniqueness violated

---

### KelpieActorLifecycle.tla

Models the lifecycle of a Kelpie virtual actor.

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type constraints on all variables | - |
| `LifecycleOrdering` | Invocations only when Active | ADR-001 G1.3 |
| `GracefulDeactivation` | No pending invocations when deactivating | ADR-001 G1.3 |

#### TLC Results
- **Safe version**: PASS (11 distinct states)
- **Buggy version**: FAIL - LifecycleOrdering violated

---

### KelpieMigration.tla

Models Kelpie's 3-phase actor migration protocol.

#### Safety Invariants
| Invariant | Description |
|-----------|-------------|
| `MigrationAtomicity` | Complete migration transfers full state |
| `NoStateLoss` | Actor state is never lost during migration |
| `SingleActivationDuringMigration` | At most one active instance during migration |

#### TLC Results
- **Safe version**: PASS (59 distinct states)
- **Buggy version**: FAIL - MigrationAtomicity violated

---

### KelpieActorState.tla

Models the actor state management and transaction semantics.

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type invariant for all variables | - |
| `RollbackCorrectness` | After rollback, memory equals pre-invocation snapshot | ADR-008 G8.2 |

#### TLC Results
- **Safe version**: PASS (60 distinct states)
- **Buggy version**: FAIL - RollbackCorrectness violated

---

### KelpieFDBTransaction.tla

Models FoundationDB transaction semantics.

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `SerializableIsolation` | Committed transactions respect serial order | ADR-004 G4.1 |
| `ConflictDetection` | Read-write conflicts properly detected | ADR-002 G2.4 |
| `AtomicCommit` | Writes are all-or-nothing | ADR-002 G2.4 |

#### TLC Results
- **Safe version**: PASS (56,193 distinct states, 308,867 generated)
- **Buggy version**: FAIL - SerializableIsolation violated

---

### KelpieTeleport.tla

Models teleport state consistency for VM snapshot operations.

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `SnapshotConsistency` | Restored state equals pre-snapshot state | ADR-020 G20.1 |
| `ArchitectureValidation` | Teleport/Suspend require same architecture | ADR-020 G20.2 |

#### TLC Results
- **Safe version**: PASS (1,508 distinct states)
- **Buggy version**: FAIL - ArchitectureValidation violated

---

### KelpieSingleActivation.tla

Models the single-activation guarantee with FDB transaction semantics.

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `SingleActivation` | At most one node active at any time | ADR-004 G4.2 |
| `ConsistentHolder` | FDB holder matches node state | - |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualActivation` | Every claim eventually resolves |

#### TLC Results
- **Safe version**: PASS (714 distinct states, depth 27)

---

### KelpieRegistry.tla

Models the actor registry with node lifecycle and cache coherence.

#### Safety Invariants
| Invariant | Description |
|-----------|-------------|
| `SingleActivation` | An actor is placed on at most one node |
| `PlacementConsistency` | Placements never point to Failed nodes |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualFailureDetection` | Dead nodes eventually detected |
| `EventualCacheInvalidation` | Stale cache entries eventually corrected |

#### TLC Results
- **Safe version**: PASS (6,174 distinct states, 22,845 generated)

---

### KelpieWAL.tla

Models the Write-Ahead Log for operation durability and atomicity.

#### Safety Invariants
| Invariant | Description |
|-----------|-------------|
| `TypeOK` | Type invariant |
| `Durability` | Completed entries remain completed |
| `Idempotency` | No duplicate entries for same client+key |
| `AtomicVisibility` | Operations fully visible or not at all |

#### Liveness Properties
| Property | Description |
|----------|-------------|
| `EventualRecovery` | After crash, system eventually recovers |
| `EventualCompletion` | Pending entries eventually complete or fail |
| `NoStarvation` | No client's operations indefinitely blocked |
| `ProgressUnderCrash` | System can always recover from crashes |

#### TLC Results
- **Safe version**: PASS (70,713 states, 1 client)
- **Concurrent version**: PASS (2,548,321 states, 2 clients)

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
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieWAL.cfg KelpieWAL.tla
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

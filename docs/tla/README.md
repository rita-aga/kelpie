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
- **TLC Results**: PASS (679 distinct states) / FAIL LeaseUniqueness (buggy)

### KelpieActorLifecycle.tla
Models the lifecycle of a Kelpie virtual actor.
- **TLC Results**: PASS (11 distinct states) / FAIL LifecycleOrdering (buggy)

### KelpieMigration.tla
Models Kelpie's 3-phase actor migration protocol.
- **TLC Results**: PASS (59 distinct states) / FAIL MigrationAtomicity (buggy)

### KelpieActorState.tla
Models actor state management and transaction semantics.
- **TLC Results**: PASS (60 distinct states) / FAIL RollbackCorrectness (buggy)

### KelpieFDBTransaction.tla
Models FoundationDB transaction semantics.
- **TLC Results**: PASS (56,193 distinct states) / FAIL SerializableIsolation (buggy)

### KelpieTeleport.tla
Models teleport state consistency for VM snapshot operations.
- **TLC Results**: PASS (1,508 distinct states) / FAIL ArchitectureValidation (buggy)

### KelpieSingleActivation.tla
Models the single-activation guarantee with FDB transaction semantics.
- **TLC Results**: PASS (714 distinct states, depth 27)

### KelpieRegistry.tla
Models the actor registry with node lifecycle and cache coherence.
- **TLC Results**: PASS (6,174 distinct states, 22,845 generated)

### KelpieWAL.tla
Models the Write-Ahead Log for operation durability and atomicity.
- **TLC Results**: PASS (70,713 states single client / 2,548,321 states concurrent)

### KelpieClusterMembership.tla
Models cluster membership protocol with:
- Node states: Joining, Active, Leaving, Failed, Left
- Heartbeat-based failure detection
- Network partitions
- Primary election with terms (Raft-style)

#### Safety Invariants
| Invariant | Description |
|-----------|-------------|
| `TypeOK` | Type safety - all variables have expected types |
| `JoinAtomicity` | Node is either fully joined or not joined |
| `NoSplitBrain` | At most one node has valid primary claim |

#### TLC Results
- **Safe version**: PASS - All invariants hold
- **Buggy version**: FAIL - NoSplitBrain violated

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
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieClusterMembership.cfg KelpieClusterMembership.tla
```

### Buggy Configurations (should fail)
```bash
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieLease_Buggy.cfg KelpieLease.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle_Buggy.cfg KelpieActorLifecycle.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieMigration_Buggy.cfg KelpieMigration.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorState_Buggy.cfg KelpieActorState.tla
java -XX:+UseParallelGC -Xmx4g -jar ~/tla2tools.jar -deadlock -config KelpieFDBTransaction_Buggy.cfg KelpieFDBTransaction.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieTeleport_Buggy.cfg KelpieTeleport.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieClusterMembership_Buggy.cfg KelpieClusterMembership.tla
```

## References

- [ADR-001: Virtual Actor Model](../adr/001-virtual-actor-model.md)
- [ADR-002: FoundationDB Integration](../adr/002-foundationdb-integration.md)
- [ADR-004: Linearizability Guarantees](../adr/004-linearizability-guarantees.md)
- [ADR-008: Transaction API](../adr/008-transaction-api.md)
- [ADR-020: Consolidated VM Crate](../adr/020-consolidated-vm-crate.md)
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [TLC Model Checker](https://lamport.azurewebsites.net/tla/tools.html)

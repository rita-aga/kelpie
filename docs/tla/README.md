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

#### TLC Results
- **Safe version**: PASS (679 distinct states)
- **Buggy version**: FAIL - LeaseUniqueness violated

---

### KelpieActorLifecycle.tla

Models the lifecycle of a Kelpie virtual actor, verifying:
- **G1.3 (Lifecycle Ordering)**: No invoke without activate, no deactivate during invoke
- **G1.5 (Idle Timeout)**: Actors deactivate after idle timeout

#### TLC Results
- **Safe version**: PASS (11 distinct states)
- **Buggy version**: FAIL - LifecycleOrdering violated

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
- [Learn TLA+](https://learntla.com/)

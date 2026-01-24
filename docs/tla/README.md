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

#### State Variables
- `state`: Actor lifecycle state (`Inactive`, `Activating`, `Active`, `Deactivating`)
- `pending`: Number of pending invocations (0..MAX_PENDING)
- `idleTicks`: Ticks since last activity (for idle timeout tracking)

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

### KelpieActorState.tla

Models the actor state management and transaction semantics from ADR-008.

#### Safety Invariants

| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type invariant for all variables | - |
| `RollbackCorrectness` | After rollback, memory equals pre-invocation snapshot | ADR-008 G8.2 |
| `BufferEmptyWhenIdle` | Transaction buffer empty when not running | - |

#### Liveness Properties

| Property | Description |
|----------|-------------|
| `EventualCommitOrRollback` | Every invocation eventually completes |

#### TLC Results
- **Safe version**: PASS (136 generated, 60 distinct states)
- **Buggy version**: FAIL - RollbackCorrectness violated

---

### KelpieFDBTransaction.tla

Models FoundationDB transaction semantics that Kelpie relies on for correctness:
- **G2.4 (Conflict Detection)**: Read-write conflicts are detected and cause transaction abort
- **G4.1 (Atomic Operations)**: Transaction writes are all-or-nothing

#### State Variables
- `kvStore`: Global key-value store (committed values)
- `txnState`: Transaction state (IDLE, RUNNING, COMMITTED, ABORTED)
- `readSet`: Keys read by each transaction
- `writeBuffer`: Buffered writes per transaction
- `readSnapshot`: Snapshot of kvStore at transaction start
- `commitOrder`: Sequence of committed transactions

#### Safety Invariants
| Invariant | Description | ADR Reference |
|-----------|-------------|---------------|
| `TypeOK` | Type correctness of all state variables | - |
| `SerializableIsolation` | Committed transactions respect serial order | ADR-004 G4.1 |
| `ConflictDetection` | Read-write conflicts properly detected | ADR-002 G2.4 |
| `AtomicCommit` | Writes are all-or-nothing | ADR-002 G2.4 |
| `ReadYourWrites` | Transactions see their own uncommitted writes | - |

#### Liveness Properties

| Property | Description |
|----------|-------------|
| `EventualTermination` | Every running transaction eventually commits or aborts |

#### TLC Results
- **Safe version**: PASS (56,193 distinct states, 308,867 generated, depth 13)
- **Buggy version**: FAIL - SerializableIsolation violated at depth 7

#### Counterexample (Buggy Version)
```
State 1: Txn1 reads k1 (sees initial value v0)
State 2: Txn2 writes k1 = v1
State 3: Txn2 commits (k1 becomes v1)
State 4: Txn1 commits WITHOUT detecting conflict
=> SerializableIsolation VIOLATED: Txn1 read stale value
```

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
```

### Buggy Configurations (should fail)
```bash
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieLease_Buggy.cfg KelpieLease.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle_Buggy.cfg KelpieActorLifecycle.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieMigration_Buggy.cfg KelpieMigration.tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorState_Buggy.cfg KelpieActorState.tla
java -XX:+UseParallelGC -Xmx4g -jar ~/tla2tools.jar -deadlock -config KelpieFDBTransaction_Buggy.cfg KelpieFDBTransaction.tla
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
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [TLC Model Checker](https://lamport.azurewebsites.net/tla/tools.html)
- [Learn TLA+](https://learntla.com/)
- [FoundationDB Paper](https://www.foundationdb.org/files/fdb-paper.pdf)

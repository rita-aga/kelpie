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

## Running Model Checker

### Safe Configuration (should pass)
```bash
cd docs/tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle.cfg KelpieActorLifecycle.tla
```

Expected output:
```
Model checking completed. No error has been found.
19 states generated, 11 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 8.
```

### Buggy Configuration (should fail LifecycleOrdering)
```bash
cd docs/tla
java -XX:+UseParallelGC -jar ~/tla2tools.jar -deadlock -config KelpieActorLifecycle_Buggy.cfg KelpieActorLifecycle.tla
```

Expected output:
```
Error: Invariant LifecycleOrdering is violated.
State 1: /\ pending = 0 /\ state = "Inactive" /\ idleTicks = 0
State 2: /\ pending = 1 /\ state = "Inactive" /\ idleTicks = 0
```

## Configuration Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `MAX_PENDING` | 2 | Maximum concurrent invocations |
| `IDLE_TIMEOUT` | 3 | Ticks before idle deactivation |
| `BUGGY` | FALSE | Enable buggy behavior for testing |

## Mapping to Rust Implementation

| TLA+ Concept | Rust Implementation |
|--------------|---------------------|
| `state` variable | `ActivationState` enum in `activation.rs` |
| `pending` variable | `pending_counts` in `dispatcher.rs` |
| `idleTicks` | `idle_time()` from `ActivationStats` |
| `StartInvoke` | `DispatcherHandle::invoke()` |
| `process_invocation` assertion | `assert!(self.state == ActivationState::Active)` |
| `should_deactivate()` | Check in `should_deactivate()` method |

## Adding New Specs

1. Create `.tla` file with specification
2. Create `.cfg` configuration file
3. Add documentation to this README
4. Run TLC to verify
5. Add test scripts if needed

## References

- [ADR-001: Virtual Actor Model](../adr/001-virtual-actor-model.md)
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [TLC Model Checker](https://lamport.azurewebsites.net/tla/tools.html)
- [Learn TLA+](https://learntla.com/)

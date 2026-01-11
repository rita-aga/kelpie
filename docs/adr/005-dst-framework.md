# ADR-005: DST Framework

## Status

Accepted

## Date

2025-01-10

## Implementation Status

| Component | Status | Location |
|-----------|--------|----------|
| SimClock | ✅ Complete | `kelpie-dst/src/clock.rs` |
| SimRng (ChaCha20) | ✅ Complete | `kelpie-dst/src/rng.rs` |
| FaultInjector | ✅ Complete | `kelpie-dst/src/faults.rs` |
| SimStorage | ✅ Complete | `kelpie-dst/src/storage.rs` |
| SimNetwork | ✅ Complete | `kelpie-dst/src/network.rs` |
| Simulation harness | ✅ Complete | `kelpie-dst/src/lib.rs` |
| 16+ fault types | ✅ Complete | All categories implemented |
| DST_SEED replay | ✅ Complete | Via environment variable |
| Stateright integration | 🚧 Scaffolded | Basic structure only |

**Test Coverage**: 49+ DST tests across storage, network, time, and fault injection scenarios.

## Context

Distributed systems are notoriously difficult to test. Traditional testing approaches fail to catch:
- Race conditions that occur rarely
- Failures that only manifest under specific timing
- Bugs that appear only during network partitions
- State corruption from crash-recovery sequences

FoundationDB demonstrated that **Deterministic Simulation Testing (DST)** can find bugs that would otherwise escape to production.

## Decision

Kelpie adopts **DST-first** development, where all critical paths are testable under simulation with fault injection.

### Core Principles

1. **Single Source of Randomness**: All randomness flows from a single seed
2. **Simulated Time**: No wall-clock dependencies
3. **Simulated I/O**: Storage and network are abstracted
4. **Explicit Faults**: Failures are injected, not waited for
5. **Deterministic Replay**: Any failure can be reproduced

### DST Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    DST Test Harness                          │
│                                                              │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                  Simulation                          │   │
│  │  ┌───────────┐  ┌───────────┐  ┌───────────────┐   │   │
│  │  │ SimClock  │  │ SimRng    │  │ FaultInjector │   │   │
│  │  │ (det.time)│  │ (ChaCha20)│  │ (16+ types)   │   │   │
│  │  └───────────┘  └───────────┘  └───────────────┘   │   │
│  │                                                      │   │
│  │  ┌───────────────────────────────────────────────┐  │   │
│  │  │              SimEnvironment                    │  │   │
│  │  │  ┌───────────┐         ┌───────────────────┐  │  │   │
│  │  │  │ SimStorage│         │    SimNetwork     │  │  │   │
│  │  │  │ (memory)  │         │ (delays,partitions)│  │  │   │
│  │  │  └───────────┘         └───────────────────┘  │  │   │
│  │  └───────────────────────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                              │
│  seed = DST_SEED env var or random                          │
│  Replay: DST_SEED=12345 cargo test                          │
└─────────────────────────────────────────────────────────────┘
```

### Fault Types (16+)

| Category | Fault Type | Description |
|----------|------------|-------------|
| **Storage** | `StorageWriteFail` | Write operation fails |
| | `StorageReadFail` | Read operation fails |
| | `StorageCorruption` | Returns corrupted data |
| | `StorageLatency` | Adds configurable delay |
| | `DiskFull` | Writes fail with ENOSPC |
| **Crash** | `CrashBeforeWrite` | Crash before write completes |
| | `CrashAfterWrite` | Crash after write, before ack |
| | `CrashDuringTransaction` | Partial transaction |
| **Network** | `NetworkPartition` | Node unreachable |
| | `NetworkDelay` | Adds latency to messages |
| | `NetworkPacketLoss` | Messages dropped |
| | `NetworkMessageReorder` | Out-of-order delivery |
| **Time** | `ClockSkew` | Nodes have different times |
| | `ClockJump` | Time jumps forward/backward |
| **Resource** | `OutOfMemory` | Allocations fail |
| | `CPUStarvation` | Delays from load |

### Usage Pattern

```rust
use kelpie_dst::{Simulation, SimConfig, FaultConfig, FaultType};

#[test]
fn test_actor_survives_storage_faults() {
    // Get seed from env or generate random (always logged)
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config)
        // 10% chance of storage write failure
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        // 5% chance of network packet loss
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.05))
        .run(|env| async move {
            // Test logic here
            // env.storage - SimStorage
            // env.network - SimNetwork
            // env.clock - SimClock
            // env.rng - DeterministicRng

            // Verify invariants hold under faults
            Ok(())
        });

    assert!(result.is_ok());
}
```

### Stateright Integration

For formal verification of critical invariants:

```rust
use stateright::Model;

#[derive(Clone, Debug, Hash)]
struct KelpieModel {
    actors: BTreeMap<ActorId, ActorState>,
    nodes: BTreeMap<NodeId, NodeState>,
    network: NetworkState,
}

impl Model for KelpieModel {
    type State = Self;
    type Action = KelpieAction;

    fn properties(&self) -> Vec<Property<Self>> {
        vec![
            Property::always("single_activation", |_, state| {
                // Verify no actor is activated on multiple nodes
                for (actor_id, _) in &state.actors {
                    let activations: Vec<_> = state.nodes.values()
                        .filter(|n| n.active_actors.contains(actor_id))
                        .collect();
                    if activations.len() > 1 {
                        return false;
                    }
                }
                true
            }),
            Property::always("linearizable", |_, state| {
                // Verify operation history is linearizable
                is_linearizable(&state.history)
            }),
        ]
    }
}
```

### Test Categories

| Category | Description | Example |
|----------|-------------|---------|
| **Unit** | Single component | `test_sim_clock_advance` |
| **Integration** | Multiple components | `test_actor_invocation` |
| **Chaos** | Random faults | `test_actor_under_chaos` |
| **Stress** | Long-running | `test_1m_operations` |
| **Stateright** | Model checking | `test_single_activation_property` |

## Consequences

### Positive

- **Confidence**: Find bugs before production
- **Reproducibility**: Every bug can be replayed
- **Speed**: Run millions of scenarios in minutes
- **Coverage**: Test failure modes impossible to trigger otherwise
- **Debugging**: Deterministic execution aids debugging

### Negative

- **Abstraction Cost**: Real I/O must be abstracted
- **Development Overhead**: DST-compatible code requires discipline
- **Not 100% Coverage**: Some bugs only manifest with real hardware
- **Learning Curve**: Developers must understand DST principles

### Neutral

- Different from traditional integration testing
- Requires maintaining sim and real implementations

## DST Invariants to Verify

1. **Single Activation**: At most one instance of an actor exists
2. **Linearizability**: Operations appear sequential
3. **Durability**: Committed state survives crashes
4. **No Lost Messages**: Acknowledged invocations complete
5. **Consistent Migration**: State preserved during migration
6. **Heartbeat Accuracy**: Failed nodes detected within timeout
7. **Transaction Atomicity**: All-or-nothing operations

## References

- [FoundationDB Testing](https://www.foundationdb.org/files/fdb-paper.pdf) (Section 6)
- [TigerBeetle Testing](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md)
- [Jepsen](https://jepsen.io/)
- [Stateright](https://github.com/stateright/stateright)
- [Antithesis](https://antithesis.com/)

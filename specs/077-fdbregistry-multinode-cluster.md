# Feature: FdbRegistry Multi-Node Cluster Membership

> Issue #77 - Implements distributed cluster membership via FoundationDB for multi-node Kelpie deployments.

## Overview

Enable Kelpie to operate as a multi-node cluster with automatic failover, split-brain prevention, and consistent actor placement. Uses FoundationDB as the coordination layer, leveraging FDB's linearizable transactions and consensus guarantees.

## User Stories

- As a platform operator, I want Kelpie nodes to automatically discover each other so that I don't need manual cluster configuration
- As a platform operator, I want automatic failover when a node dies so that actor availability is maintained
- As a platform operator, I want split-brain prevention so that actors never have dual activation during network partitions

## TLA+ Specification Reference

**Spec:** `docs/tla/KelpieClusterMembership.tla`

### State Machine

```
Left ──join──> Joining ──complete──> Active ──leave──> Leaving ──complete──> Left
                                        │                                      ▲
                                        │ failure detected                     │
                                        ▼                                      │
                                     Failed ──recover─────────────────────────┘
```

### Invariants to Verify

| ID | Invariant | TLA+ Name | Description |
|----|-----------|-----------|-------------|
| INV-1 | NoSplitBrain | `NoSplitBrain` | At most one node has a valid primary claim |
| INV-2 | MembershipConsistency | `MembershipConsistency` | Active nodes with same view number have same membership view |
| INV-3 | JoinAtomicity | `JoinAtomicity` | Node is either fully joined (Active + non-empty view) or not joined |
| INV-4 | LeaveDetection | `LeaveDetectionWeak` | Left nodes are not in any active node's membership view |

### Liveness Properties

| ID | Property | TLA+ Name | Description |
|----|----------|-----------|-------------|
| LIV-1 | Convergence | `EventualMembershipConvergence` | If network heals and nodes stable, all active nodes eventually have same view |

## Functional Requirements

### FR-1: Node State Machine

Implement the TLA+ node state machine with states: Left, Joining, Active, Leaving, Failed.

**Acceptance Criteria:**
- [ ] `NodeState` enum matches TLA+ exactly (Left, Joining, Active, Leaving, Failed)
- [ ] State transitions match TLA+ actions (NodeJoin, NodeJoinComplete, NodeLeave, NodeLeaveComplete, MarkNodeFailed, NodeRecover)
- [ ] Invalid state transitions are rejected with assertion failures
- [ ] DST test: `test_node_state_machine_matches_tla` verifies all valid/invalid transitions
- [ ] DST test runs against REAL `FdbRegistry`, not mock

### FR-2: Primary Election

Implement Raft-style primary election with monotonically increasing terms.

**Acceptance Criteria:**
- [ ] `PrimaryInfo` struct with node_id, term, elected_at_ms
- [ ] Only Active nodes can become primary
- [ ] Election requires reaching majority of ALL nodes (not just view)
- [ ] Higher term always wins
- [ ] Primary term stored in FDB, incremented atomically
- [ ] DST test: `test_primary_election_requires_quorum` - node in minority partition cannot become primary
- [ ] DST test: `test_no_split_brain_under_partition` - at most one valid primary during any partition scenario
- [ ] DST test runs against REAL implementation

### FR-3: Primary Step-Down

Primary must step down when it loses quorum.

**Acceptance Criteria:**
- [ ] Primary continuously monitors reachability to majority
- [ ] If FDB transaction fails due to partition, primary steps down
- [ ] Step-down clears `believesPrimary` in FDB transaction
- [ ] DST test: `test_primary_stepdown_on_quorum_loss` - primary in minority partition steps down
- [ ] DST test: Inject NetworkPartition fault, verify step-down within timeout
- [ ] DST test runs against REAL implementation

### FR-4: Heartbeat-Based Failure Detection

Detect node failures via heartbeat timeout.

**Acceptance Criteria:**
- [ ] Heartbeats written to FDB with timestamp
- [ ] If no heartbeat for `MAX_HEARTBEAT_MISS * HEARTBEAT_INTERVAL_MS`, mark Suspect
- [ ] If still no heartbeat, transition to Failed
- [ ] DST test: `test_failure_detection_on_heartbeat_timeout`
- [ ] DST test: Inject clock advancement, verify failure detection
- [ ] DST test: Uses SimClock for deterministic timing
- [ ] DST test runs against REAL implementation

### FR-5: Membership View Synchronization

Active nodes synchronize their membership views.

**Acceptance Criteria:**
- [ ] `MembershipView` struct with active_nodes and view_number
- [ ] View stored in FDB, updated atomically on membership change
- [ ] Higher view number takes precedence
- [ ] View merge ensures both communicating nodes are included
- [ ] FDB watches notify nodes of view changes
- [ ] DST test: `test_membership_view_convergence` - after partition heal, all nodes have same view
- [ ] DST test runs against REAL implementation

### FR-6: Partition Handling

Handle network partitions safely with CP semantics.

**Acceptance Criteria:**
- [ ] Minority partition cannot elect primary (quorum not reachable)
- [ ] Minority partition operations fail (unavailable)
- [ ] Majority partition continues serving
- [ ] On partition heal, stale primary steps down atomically
- [ ] DST test: `test_minority_partition_unavailable` - operations fail in minority
- [ ] DST test: `test_partition_heal_resolves_conflict` - split-brain resolved on heal
- [ ] DST test: Uses SimNetwork for deterministic partitions
- [ ] DST test runs against REAL implementation

### FR-7: Actor Migration on Node Failure

Trigger actor migration when node fails.

**Acceptance Criteria:**
- [ ] When node marked Failed, its actors become eligible for migration
- [ ] Primary coordinates migration decisions
- [ ] Migrated actors maintain single activation guarantee
- [ ] DST test: `test_actor_migration_on_node_failure`
- [ ] DST test: Inject CrashDuringTransaction, verify actors migrated
- [ ] DST test runs against REAL implementation

## DST Simulation Requirements

### DST-1: Production Code Testing

**Requirement:** DST tests MUST run against production implementation, NOT mocks.

**Verification:**
- [ ] Tests import and use `kelpie_cluster::Cluster`, not test-only `ClusterMember`
- [ ] Tests import and use `kelpie_registry::FdbRegistry`, not test-only `SimClusterNode`
- [ ] No `HashMap<NodeId, NodeState>` simulations in tests
- [ ] Tests use injected providers (TimeProvider, NetworkProvider) not mocked protocols

### DST-2: I/O Provider Injection

**Requirement:** All production code must use injected I/O providers.

| Provider | Trait | Production | DST |
|----------|-------|------------|-----|
| Time | `TimeProvider` | `SystemClock` | `SimClock` |
| Network | `NetworkProvider` | `TokioNetwork` | `SimNetwork` |
| Storage | `StorageBackend` | `FdbBackend` | `SimStorage` |
| RNG | `RngProvider` | `SystemRng` | `DeterministicRng` |

**Verification:**
- [ ] `Cluster::new()` accepts `TimeProvider`
- [ ] `Cluster::new()` accepts `NetworkProvider`
- [ ] `FdbRegistry::new()` accepts `TimeProvider`
- [ ] No direct `SystemTime::now()` calls in cluster/registry code
- [ ] No direct `tokio::net::*` in cluster/registry code

### DST-3: Fault Injection Coverage

**Requirement:** DST must inject all fault types from TLA+ model.

| Fault Type | TLA+ Action | DST Fault | Required Test |
|------------|-------------|-----------|---------------|
| Network partition | `CreatePartition` | `FaultType::NetworkPartition` | `test_partition_creates_isolated_nodes` |
| Partition heal | `HealPartition` | `FaultType::NetworkHeal` | `test_partition_heal_restores_communication` |
| Node crash | `MarkNodeFailed` | `FaultType::CrashDuringTransaction` | `test_crash_triggers_failure_detection` |
| Heartbeat miss | `DetectFailure` | `FaultType::NetworkDelay` | `test_delayed_heartbeat_triggers_suspect` |
| Clock skew | N/A | `FaultType::ClockSkew` | `test_clock_skew_does_not_break_detection` |
| Message reorder | N/A | `FaultType::NetworkMessageReorder` | `test_reordered_messages_handled` |

**Verification:**
- [ ] Each TLA+ action has corresponding DST fault injection test
- [ ] Tests specify fault injection via `FaultConfig`
- [ ] Tests verify invariants hold under fault conditions

### DST-4: Invariant Verification Bridge

**Requirement:** DST tests must verify TLA+ invariants against runtime state.

**Implementation:**
```rust
// Extract system state for invariant checking
fn extract_cluster_state(cluster: &Cluster, registry: &FdbRegistry) -> SystemState {
    SystemState {
        node_states: /* from registry */,
        membership_views: /* from registry */,
        primary_claims: /* from registry */,
        partitioned_pairs: /* from sim_network */,
    }
}

// Verify invariant
invariant_checker.check(
    InvariantId::NoSplitBrain,
    &system_state
)?;
```

**Verification:**
- [ ] `InvariantChecker` has methods for all TLA+ invariants
- [ ] Tests extract real state from production objects, not mocks
- [ ] Invariant violations fail tests with seed for reproduction

### DST-5: Determinism Verification

**Requirement:** Same seed MUST produce identical results.

**Verification:**
```bash
# Must produce identical output
DST_SEED=12345 cargo test -p kelpie-dst cluster_membership > run1.txt
DST_SEED=12345 cargo test -p kelpie-dst cluster_membership > run2.txt
diff run1.txt run2.txt  # Must be empty
```

- [ ] All tests use `SimConfig::from_env_or_random()`
- [ ] No non-deterministic operations (HashMap iteration, real time, real RNG)
- [ ] CI runs determinism check on PR

### DST-6: State Space Exploration

**Requirement:** DST must explore sufficient state space for confidence.

**Configuration:**
- `max_steps`: 10,000+ steps per test
- `max_time_ms`: 300,000ms (5 minutes simulated time)
- Multiple seeds: CI runs with 10+ random seeds

**Verification:**
- [ ] Tests specify meaningful `max_steps` and `max_time_ms`
- [ ] CI matrix runs multiple seeds
- [ ] Coverage report shows all TLA+ actions exercised

## FDB Schema

```
Key Space:
/kelpie/cluster/nodes/{node_id}         -> NodeInfo { id, addr, state, heartbeat_ms }
/kelpie/cluster/membership_view         -> MembershipView { active_nodes, view_number }
/kelpie/cluster/primary                 -> PrimaryInfo { node_id, term, elected_at_ms }
/kelpie/cluster/primary_term            -> u64 (atomic counter)
```

## Success Criteria

### Functional
- [ ] Two+ Kelpie nodes can form a cluster
- [ ] Primary election works correctly
- [ ] Node failure is detected and actors migrated
- [ ] No split-brain under network partition

### DST Quality
- [ ] 100% of DST tests use production code (no mocks)
- [ ] All TLA+ invariants verified in DST
- [ ] All fault types from spec injected in tests
- [ ] Determinism verified (same seed = same result)
- [ ] CI runs 10+ seeds per PR

### Code Quality
- [ ] TigerStyle compliance (2+ assertions per function)
- [ ] All public APIs documented
- [ ] `cargo clippy` clean
- [ ] `cargo test` passes

## Dependencies

- **Depends on:** FoundationDB running (or SimStorage for DST)
- **Depends on:** Phase 2-3 of `.progress/048_*` (TimeProvider, NetworkProvider in cluster)
- **Blocked by:** None

## Implementation Notes

- Follow TigerStyle (see CLAUDE.md)
- Use explicit constants with units (e.g., `HEARTBEAT_INTERVAL_MS`)
- Use injected providers for ALL I/O
- Add property-based tests for serialization
- TLA+ invariant checks in DST tests, not production code

## Ralph Loop Instructions

When implementing via Ralph Loop, verify after each phase:

1. **After FR-1 (State Machine):**
   - Run: `cargo test -p kelpie-registry test_node_state`
   - Verify: State transitions match TLA+

2. **After FR-2,3 (Primary Election):**
   - Run: `DST_SEED=12345 cargo test -p kelpie-dst test_no_split_brain`
   - Verify: NoSplitBrain invariant holds

3. **After FR-4,5 (Heartbeat, Views):**
   - Run: `DST_SEED=12345 cargo test -p kelpie-dst test_membership`
   - Verify: MembershipConsistency invariant holds

4. **After FR-6 (Partition Handling):**
   - Run: `DST_SEED=12345 cargo test -p kelpie-dst test_partition`
   - Verify: All tests pass with NetworkPartition fault injection

5. **After FR-7 (Migration):**
   - Run: `cargo test -p kelpie-dst`
   - Verify: All DST tests pass, use production code

6. **Final Verification:**
   - Run: `./scripts/check-determinism.sh cluster_membership`
   - Verify: Same seed produces identical results

---

## Status: COMPLETE

**Completed:** 2026-01-27

### Implementation Summary

- **FR-1 (NodeState):** Implemented `NodeState` enum in `crates/kelpie-registry/src/membership.rs` matching TLA+ states (Left, Joining, Active, Leaving, Failed) with validated state transitions
- **FR-2 (Primary Election):** Implemented `PrimaryInfo` and quorum-based election in `crates/kelpie-registry/src/cluster.rs`
- **FR-3 (Step-Down):** Implemented `step_down()` and `check_quorum_and_maybe_step_down()` methods
- **FR-4 (Heartbeat):** Integrated heartbeat timeout with node state transitions via `detect_failed_nodes()` and `mark_node_failed()`
- **FR-5 (MembershipView):** Implemented `MembershipView` with view numbers, add/remove/merge operations
- **FR-6 (Partition Handling):** Implemented quorum checking, primary step-down on partition, reachable nodes tracking
- **FR-7 (Actor Migration):** Implemented `MigrationQueue`, `queue_actors_for_migration()`, `process_migration_queue()`, and `handle_node_failure()`

### DST Tests

All tests in `crates/kelpie-dst/tests/cluster_membership_production_dst.rs`:
1. `test_production_no_split_brain` - Verifies NoSplitBrain invariant
2. `test_production_primary_election_requires_quorum` - Verifies quorum requirement
3. `test_production_primary_stepdown_on_quorum_loss` - Verifies step-down behavior
4. `test_production_heartbeat_failure_detection` - Verifies failure detection
5. `test_production_partition_heal_resolves_conflict` - Verifies partition healing
6. `test_production_determinism` - Verifies same seed produces same results
7. `test_production_state_transitions_match_tla` - Verifies TLA+ state machine
8. `test_production_actor_migration_on_node_failure` - Verifies actor migration and single activation guarantee

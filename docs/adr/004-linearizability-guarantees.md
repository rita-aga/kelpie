# ADR-004: Linearizability Guarantees

## Status

Accepted

## Date

2025-01-10

## Implementation Status

| Component | Status | Location |
|-----------|--------|----------|
| Single activation | ✅ Complete | `kelpie-runtime/src/dispatcher.rs` |
| Actor KV transactions | ✅ Complete | `kelpie-storage/src/actor_kv.rs` |
| Lease-based ownership | 📋 Designed | Requires FDB backend |
| FDB transactions | ⏳ Not Started | Requires FDB backend |
| Failure detection | 🚧 Partial | Basic heartbeats in cluster |
| Automatic recovery | 🚧 Partial | Actor reactivation works |

**Note**: Linearizability guarantees are fully designed but depend on FDB backend for production use. Current in-memory implementation provides linearizability within a single process. Cluster-wide linearizability requires FDB integration.

## Context

Kelpie makes strong consistency guarantees that distinguish it from eventually consistent actor systems. Users need to understand:
- What guarantees Kelpie provides
- What the CAP theorem implications are
- How consistency is maintained during failures

## Decision

Kelpie provides **linearizable** actor operations with a **CP** (Consistency over Availability) design.

### Consistency Guarantees

1. **Single Activation**: At most one instance of an actor exists at any time
2. **Linearizable Operations**: Actor operations appear to execute atomically in some sequential order
3. **Durable State**: Committed state survives node failures
4. **Exactly-Once Semantics**: Each invocation executes exactly once (with idempotency tokens)

### How Linearizability is Achieved

```
┌─────────────────────────────────────────────────────────────┐
│                    Linearizable Path                         │
│                                                              │
│  Client      Node A        Registry (FDB)      Node B       │
│    │           │               │                  │          │
│    │──invoke──▶│               │                  │          │
│    │           │──get_owner───▶│                  │          │
│    │           │◀──owner=B─────│                  │          │
│    │           │───────────────forward────────────▶│          │
│    │           │               │                  │──invoke  │
│    │           │               │                  │  actor   │
│    │           │               │◀──────commit─────│          │
│    │           │◀──────────────result─────────────│          │
│    │◀──result──│               │                  │          │
│    │           │               │                  │          │
└─────────────────────────────────────────────────────────────┘
```

### Single Activation Protocol

```rust
// Acquiring activation
async fn activate_actor(&self, actor_id: &ActorId) -> Result<()> {
    let txn = self.fdb.create_transaction()?;

    // Check if already activated elsewhere
    let current_owner = txn.get(&owner_key(actor_id)).await?;
    if let Some(owner) = current_owner {
        if owner != self.node_id {
            return Err(Error::ActorAlreadyActivated { owner });
        }
    }

    // Set ownership with lease
    let lease = Lease {
        node_id: self.node_id.clone(),
        expires_at: now() + LEASE_DURATION_MS,
    };
    txn.set(&owner_key(actor_id), &lease.serialize());

    // Atomic commit ensures single activation
    txn.commit().await?;

    Ok(())
}
```

### Lease-Based Ownership

- Each activation has a **lease** with expiration time
- Nodes must **renew leases** before expiration
- Expired leases allow **reactivation** on other nodes
- Lease renewal uses **conditional writes** for linearizability

```rust
async fn renew_lease(&self, actor_id: &ActorId) -> Result<()> {
    let txn = self.fdb.create_transaction()?;

    // Read current lease
    let current = txn.get(&owner_key(actor_id)).await?;
    let lease: Lease = deserialize(current)?;

    // Only renew if we own it
    assert_eq!(lease.node_id, self.node_id);

    // Extend lease
    let new_lease = Lease {
        node_id: self.node_id.clone(),
        expires_at: now() + LEASE_DURATION_MS,
    };
    txn.set(&owner_key(actor_id), &new_lease.serialize());

    txn.commit().await?;
    Ok(())
}
```

### CAP Theorem Position

Kelpie chooses **CP** (Consistency + Partition tolerance):

| Scenario | Behavior |
|----------|----------|
| Normal operation | Low latency, linearizable |
| Network partition | Minority partition unavailable |
| Node failure | Actors reactivate after lease expiry |
| FDB unavailable | All operations fail (no degraded mode) |

### Failure Handling

```
┌────────────────────────────────────────────────────────────┐
│              Failure Detection and Recovery                 │
│                                                             │
│  1. Node A hosts Actor X                                   │
│  2. Node A fails (crash or network partition)              │
│  3. Node A's lease on Actor X expires (LEASE_TIMEOUT_MS)   │
│  4. Client invokes Actor X                                 │
│  5. Node B acquires lease (wins FDB transaction)           │
│  6. Node B activates Actor X, loads state from FDB         │
│  7. Actor X continues processing with durably committed state │
│                                                             │
│  Recovery time = LEASE_TIMEOUT_MS + activation_time        │
│  Typical: 5-10 seconds                                     │
└────────────────────────────────────────────────────────────┘
```

## Consequences

### Positive

- **Simple Mental Model**: Operations are linearizable, no surprises
- **Data Integrity**: Never lose committed state
- **Single Activation**: No split-brain scenarios
- **Predictable Behavior**: Same behavior in tests and production

### Negative

- **Availability Trade-off**: Unavailable during partitions
- **Latency During Failures**: Wait for lease expiry
- **FDB Dependency**: FDB downtime = total outage
- **No Eventual Consistency Mode**: Can't trade consistency for availability

### Neutral

- Different from Orleans (which supports eventual consistency)
- Requires careful lease timeout tuning

## Alternatives Considered

### Eventual Consistency (AP)

- Higher availability during partitions
- CRDTs for conflict resolution

**Rejected because**: Complexity of conflict resolution, not needed for our use cases.

### Optimistic Locking

- Check version on write
- Retry on conflict

**Rejected because**: FDB transactions already provide this, no benefit.

### Multi-Leader Replication

- Multiple active instances
- Merge conflicts later

**Rejected because**: Violates single activation guarantee.

## References

- [Linearizability: A Correctness Condition for Concurrent Objects](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf)
- [Jepsen Testing](https://jepsen.io/)
- [FoundationDB Consistency](https://apple.github.io/foundationdb/consistency.html)

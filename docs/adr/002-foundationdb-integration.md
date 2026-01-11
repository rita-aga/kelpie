# ADR-002: FoundationDB Integration

## Status

Accepted

## Date

2025-01-10

## Implementation Status

| Component | Status | Location |
|-----------|--------|----------|
| Storage abstraction | ✅ Complete | `kelpie-storage/src/lib.rs` |
| ActorKV trait | ✅ Complete | `kelpie-storage/src/actor_kv.rs` |
| MemoryBackend (DST) | ✅ Complete | `kelpie-storage/src/memory.rs` |
| FDB Backend | ⏳ Not Started | P0 priority |
| Key space design | 📋 Designed | See ADR |
| Transaction semantics | 📋 Designed | See ADR |

**Note**: FDB integration is designed but not implemented. Currently using MemoryBackend for development and testing. FDB backend is P0 priority for production readiness.

## Context

Kelpie requires a storage backend that provides:
- **Linearizable transactions**: Essential for single activation guarantee
- **Horizontal scalability**: Support for large clusters
- **High availability**: Automatic failover
- **ACID semantics**: For actor state consistency
- **Proven reliability**: Production-tested at scale

The storage layer serves two purposes:
1. **Actor State Storage**: Per-actor key-value data
2. **Registry Metadata**: Actor placement, heartbeats, cluster state

## Decision

We use **FoundationDB** as the primary storage backend.

### Architecture

```
┌─────────────────────────────────────────────┐
│              Kelpie Cluster                  │
│  ┌─────────────────────────────────────┐   │
│  │          kelpie-storage             │   │
│  │  ┌─────────┐      ┌─────────────┐  │   │
│  │  │ ActorKV │      │  RegistryKV │  │   │
│  │  │ Trait   │      │    Trait    │  │   │
│  │  └────┬────┘      └──────┬──────┘  │   │
│  │       │                  │         │   │
│  │  ┌────┴──────────────────┴────┐   │   │
│  │  │      FDB Backend           │   │   │
│  │  │  (or MemoryBackend for DST)│   │   │
│  │  └────────────┬───────────────┘   │   │
│  └───────────────┼───────────────────┘   │
└──────────────────┼───────────────────────┘
                   │
┌──────────────────┴───────────────────────┐
│              FoundationDB                 │
│   (linearizable, distributed KV store)   │
└───────────────────────────────────────────┘
```

### Key Space Design

```
kelpie/
├── actors/
│   └── {namespace}/{actor_id}/
│       ├── state         # Serialized actor state
│       └── data/         # Actor's KV namespace
│           └── {key}     # User-defined keys
├── registry/
│   ├── actors/
│   │   └── {namespace}/{actor_id}  # -> node_id
│   ├── nodes/
│   │   └── {node_id}     # Node metadata + last heartbeat
│   └── leases/
│       └── {namespace}/{actor_id}  # Activation lease
└── cluster/
    ├── config            # Cluster configuration
    └── version           # Schema version
```

### Transaction Semantics

```rust
// All actor operations are transactional
pub async fn actor_invocation(&self, actor_id: &ActorId) -> Result<()> {
    let txn = self.fdb.create_transaction()?;

    // Read current state
    let state = txn.get(&state_key(actor_id)).await?;

    // Modify state
    let new_state = process_invocation(state)?;

    // Write atomically
    txn.set(&state_key(actor_id), &new_state);
    txn.commit().await?;

    Ok(())
}
```

### FDB Limits Alignment

Our constants align with FDB limits:
- `TRANSACTION_SIZE_BYTES_MAX = 10 MB` (FDB limit)
- `KEY_LENGTH_BYTES_MAX = 10 KB` (FDB limit)
- `VALUE_SIZE_BYTES_MAX = 100 KB` (FDB recommendation)

## Consequences

### Positive

- **Linearizable by Design**: FDB provides serializable isolation
- **Battle-Tested**: Powers Apple, Snowflake, and others at massive scale
- **Automatic Sharding**: FDB handles data distribution
- **Strong Consistency**: CP system matches our requirements
- **Great Tooling**: Excellent debugging and monitoring

### Negative

- **Operational Complexity**: FDB cluster requires care to operate
- **10MB Transaction Limit**: Must batch large operations
- **External Dependency**: Requires FDB cluster deployment
- **Learning Curve**: FDB's model is different from traditional databases

### Neutral

- Need abstraction layer for testing (MemoryBackend for DST)
- Rust FDB bindings are community-maintained

## Alternatives Considered

### etcd

- Simpler to operate
- Built-in consensus

**Rejected because**: Limited to ~8GB, not designed for high-throughput data storage.

### CockroachDB

- SQL interface
- Easier migration from traditional databases

**Rejected because**: Higher overhead, SQL not needed for KV workload.

### TiKV

- Rust native
- Prometheus-compatible metrics

**Rejected because**: Less mature than FDB, smaller community.

### Custom Raft Implementation

- Full control over consistency model
- No external dependencies

**Rejected because**: Enormous engineering effort, FDB already solved this.

## References

- [FoundationDB Paper](https://www.foundationdb.org/files/fdb-paper.pdf)
- [FoundationDB Documentation](https://apple.github.io/foundationdb/index.html)
- [FoundationDB Record Layer](https://github.com/FoundationDB/fdb-record-layer)

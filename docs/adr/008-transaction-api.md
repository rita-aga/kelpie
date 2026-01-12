# ADR-008: Transaction API for Actor Storage

## Status

Accepted (Partial Implementation)

## Date

2026-01-12

## Context

Kelpie's storage layer currently provides individual key-value operations (`get`, `set`, `delete`) without atomicity guarantees across multiple keys. This creates several problems:

### Problem 1: State Lost on Crash

Actor state is held in memory and only persisted during graceful deactivation (`save_state()` in `activation.rs`). If a node crashes, all in-flight actor state is lost.

```rust
// Current: state saved only here
pub async fn deactivate(&mut self) -> Result<()> {
    self.save_state().await?;  // Only place state persists!
}
```

### Problem 2: Non-Atomic Multi-Key Operations

An actor performing multiple `set()` calls has no guarantee they succeed together:

```rust
// Current: partial failure possible
ctx.kv_set(b"balance", &new_balance).await?;
ctx.kv_set(b"last_transaction", &txn_id).await?;  // What if this fails?
```

### Problem 3: State + KV Not Atomic

Actor's primary state blob (`__state__` key) and user KV data are separate. They can become inconsistent:

```rust
// Actor state saved separately from KV operations
// No atomicity between them
```

### Why Transactions Are Needed

For virtual actors managing stateful operations (AI agents, game entities, financial state), atomicity is critical:
- AI agents need atomic memory updates
- Game state needs consistent snapshots
- Financial operations need ACID guarantees

FoundationDB (our production backend) provides serializable transactions. We need to expose this capability through the `ActorKV` trait.

## Decision

Add a transaction API to `ActorKV` with explicit transaction handles.

### API Design

```rust
/// Transaction on actor's KV store
#[async_trait]
pub trait ActorTransaction: Send + Sync {
    /// Get a value within the transaction
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>>;

    /// Set a value (buffered until commit)
    async fn set(&mut self, key: &[u8], value: &[u8]) -> Result<()>;

    /// Delete a key (buffered until commit)
    async fn delete(&mut self, key: &[u8]) -> Result<()>;

    /// Commit the transaction atomically
    async fn commit(self: Box<Self>) -> Result<()>;

    /// Abort the transaction, discarding all writes
    async fn abort(self: Box<Self>) -> Result<()>;
}

/// Extended ActorKV with transaction support
#[async_trait]
pub trait ActorKV: Send + Sync {
    // ... existing methods unchanged ...

    /// Begin a new transaction for an actor
    async fn begin_transaction(&self, actor_id: &ActorId)
        -> Result<Box<dyn ActorTransaction>>;
}
```

### Usage Pattern

```rust
// Atomic multi-key operation
let txn = kv.begin_transaction(&actor_id).await?;
txn.set(b"balance", &new_balance).await?;
txn.set(b"last_transaction", &txn_id).await?;
txn.commit().await?;  // All or nothing
```

### Runtime Integration

The actor runtime will wrap each invocation in a transaction:

```rust
// In ActorActivation::invoke()
async fn invoke(&mut self, method: &str, args: &[u8]) -> Result<Vec<u8>> {
    let txn = self.kv.begin_transaction(&self.actor_id).await?;

    // Run the actor's handler
    let result = self.actor.handle(method, args, &mut self.context).await;

    // Save state within transaction
    txn.set(STATE_KEY, &serialized_state).await?;

    match result {
        Ok(response) => {
            txn.commit().await?;
            Ok(response)
        }
        Err(e) => {
            txn.abort().await?;
            Err(e)
        }
    }
}
```

### Isolation Level

Serializable isolation (matching FDB's guarantees):
- Reads see a consistent snapshot
- Writes are atomic
- Conflicts are detected and handled

### DST-First Implementation

Following simulation-first development:

1. **Phase 1**: Extend `SimStorage` with transaction support
2. **Phase 2**: Write DST tests for crash scenarios
3. **Phase 3**: Add trait to `ActorKV`
4. **Phase 4**: Update actor runtime
5. **Phase 5**: Implement in `FdbKV`

## Consequences

### Positive

- **Crash Safety**: State persisted within transaction, survives crashes
- **Atomicity**: Multi-key operations succeed or fail together
- **Consistency**: State + KV always consistent
- **FDB Alignment**: Direct mapping to FDB's transaction model
- **DST Testable**: `CrashDuringTransaction` fault enables testing

### Negative

- **API Complexity**: Users must understand transactions
- **Performance**: Transaction overhead for single-key operations
- **Abort Handling**: Failed transactions need retry logic

### Neutral

- Runtime manages transactions for actor invocations (users don't need to)
- Existing non-transactional methods remain for convenience

## Alternatives Considered

### Closure-Based API

```rust
kv.transaction(|txn| async {
    txn.set(b"key", b"value").await?;
    Ok(())
}).await?;
```

**Rejected because**: Async closures in Rust have lifetime complexity. The explicit handle pattern is simpler and aligns with FDB's API.

### Builder Pattern

```rust
kv.batch()
    .set(b"k1", b"v1")
    .set(b"k2", b"v2")
    .commit()
    .await?;
```

**Rejected because**: Can't read-then-write within a batch. Transactions need read capability for conditional updates.

### Auto-Save After Every Invocation (No Transactions)

Simply save state after every invocation without transaction semantics.

**Rejected because**: Doesn't solve multi-key atomicity. Partial failures still possible if actor writes multiple KV entries.

### Write-Ahead Log

Use WAL for crash recovery instead of transactions.

**Rejected because**: Higher complexity, FDB already provides transactions. Would duplicate FDB's functionality.

## Implementation Checklist

- [x] Add `ActorTransaction` trait to `kelpie-storage/src/kv.rs`
- [x] Add `begin_transaction()` to `ActorKV` trait
- [x] Implement `MemoryTransaction` in `kelpie-storage/src/memory.rs`
- [x] Implement `SimTransaction` in `kelpie-dst/src/storage.rs`
- [x] Wire `CrashDuringTransaction` fault in SimStorage
- [x] Write DST tests for transaction atomicity
- [x] Write DST tests for crash recovery
- [x] Update `ActiveActor` to use transactions for state persistence
- [x] Implement `FdbActorTransaction` in `kelpie-storage/src/fdb.rs`
- [x] Add integration tests for FDB transactions (5 tests, requires FDB)

## References

- [ADR-002: FoundationDB Integration](./002-foundationdb-integration.md)
- [ADR-007: FDB Backend Implementation](./007-fdb-backend-implementation.md)
- [FDB Transaction Model](https://apple.github.io/foundationdb/transaction-model.html)
- [Progress File: 003_20260112_160000_dst-first-transaction-support.md](../../.progress/003_20260112_160000_dst-first-transaction-support.md)

# ADR-007: FDB Backend Implementation

## Status

Accepted

## Date

2026-01-12

## Context

ADR-002 established FoundationDB as the storage backend for Kelpie and defined the key space design. This ADR addresses the implementation decisions required to build the actual `FdbKV` backend:

1. **Rust Client Selection**: Which FDB Rust client library to use
2. **Key Encoding**: How to encode actor keys in FDB's key space
3. **Dependency Management**: How to handle FDB as an optional dependency
4. **Testing Strategy**: How to test FDB backend given DST constraints

The `ActorKV` trait is already defined with 5 methods:
- `get(actor_id, key) -> Option<Bytes>`
- `set(actor_id, key, value)`
- `delete(actor_id, key)`
- `exists(actor_id, key) -> bool` (default impl)
- `list_keys(actor_id, prefix) -> Vec<Vec<u8>>`

## DST Architecture Clarification

Understanding where DST ends and production implementations begin is critical:

```
┌─────────────────────────────────────────────────────────────────────┐
│                     APPLICATION CODE                                 │
│  (Actor Runtime, Actor Lifecycle, Business Logic)                   │
│                                                                      │
│  Uses TRAITS: ActorKV, Clock, Rng, Network                          │
│  THIS is what DST tests.                                            │
└─────────────────────────────┬───────────────────────────────────────┘
                              │
         ┌────────────────────┴────────────────────┐
         │                                         │
         ▼                                         ▼
┌─────────────────────────┐             ┌─────────────────────────┐
│     DST MODE            │             │   PRODUCTION MODE       │
│     (kelpie-dst)        │             │                         │
│                         │             │                         │
│  SimStorage             │             │  FdbKV                  │
│  SimNetwork             │             │  Real TCP               │
│  SimClock               │             │  std::time              │
│  DeterministicRng       │             │  rand::thread_rng       │
│  FaultInjector          │             │                         │
│                         │             │                         │
│  ✓ Deterministic        │             │  ✗ Non-deterministic    │
│  ✓ Fault injection      │             │  ✗ Real failures only   │
│  ✓ Reproducible         │             │  ✗ Not reproducible     │
└─────────────────────────┘             └─────────────────────────┘
```

### What DST Tests

- Actor activation/deactivation logic
- Actor state persistence and recovery
- Cross-actor invocation
- Application behavior under storage/network faults
- Runtime scheduling and lifecycle

### What DST Does NOT Test

- FdbKV implementation internals (retry logic, error mapping)
- Real FDB transaction semantics
- FDB C client behavior
- Production infrastructure code

### The Trust Model

1. **SimStorage**: Simple (~100 lines), obviously correct, used IN DST
2. **FdbKV**: Complex (~400 lines), implements same trait, tested SEPARATELY
3. **ActorKV trait**: The contract both implement

DST verifies application code works with ActorKV. FdbKV is trusted because:
- It implements the same trait (same contract)
- It has its own unit tests
- It has integration tests against real FDB

## Decision

### 1. Use `foundationdb` Crate v0.9

Use the community-maintained `foundationdb` crate for Rust bindings.

```toml
[dependencies]
foundationdb = { version = "0.9", optional = true }
```

### 2. Tuple Encoding for Keys

Use FDB's tuple layer for key encoding:

```
("kelpie", "actors", namespace, actor_id, "data", user_key)
```

Benefits:
- Lexicographic ordering preserved
- Compatible with FDB tooling (fdbcli, layers)
- Self-describing format
- Proper handling of arbitrary byte sequences

### 3. Feature Flag for Optional FDB

Gate FDB behind an optional feature:

```toml
[features]
default = []
fdb = ["foundationdb"]
```

### 4. Shared Database Handle

Use a single `Arc<Database>` shared across all operations. This matches FDB's design where `Database` handles connection pooling internally.

### 5. Testing Strategy

| Layer | What | Tested By | Status |
|-------|------|-----------|--------|
| Application code | Actor runtime, lifecycle | DST with SimStorage | ✅ Exists |
| ActorKV trait | Interface contract | N/A (it's an interface) | ✅ Defined |
| SimStorage | DST infrastructure | Used by DST, not tested | ✅ Exists |
| FdbKV - encoding | Key/value encoding | Unit tests | ✅ Done |
| FdbKV - retry logic | Transaction conflict handling | Unit tests (mocked) | ❌ TODO |
| FdbKV - full behavior | End-to-end correctness | Integration tests | ✅ Written (need FDB) |

**Key insight**: FdbKV is a production infrastructure component, NOT part of DST. It needs its own test suite separate from DST.

## Consequences

### Positive

- **Clear Separation**: DST tests application, integration tests test FdbKV
- **Flexible Builds**: Developers can work without FDB installed
- **Debuggable Keys**: Tuple encoding works with fdbcli for inspection
- **Ordered Scans**: Tuple encoding enables efficient range queries

### Negative

- **C Library Dependency**: FDB C client must be installed for `fdb` feature
- **Separate Test Suites**: Must maintain both DST tests and FdbKV tests
- **Integration Test Setup**: Requires running FDB cluster

### Neutral

- Tuple encoding adds ~20-50 bytes overhead per key (acceptable)
- FDB network thread runs in background (standard FDB pattern)

## Alternatives Considered

### FDB-in-DST

Run actual FDB in deterministic simulation.

**Rejected because**: FDB is inherently non-deterministic (real time, real network). The correct approach is:
1. DST tests application code via SimStorage
2. FdbKV tested separately via unit + integration tests
3. Both implement ActorKV trait = same contract

### Custom FFI Bindings

Write our own FDB C bindings.

**Rejected because**: Massive effort for no benefit. The `foundationdb` crate is mature.

### Raw Byte Keys

Use simple concatenation: `kelpie/actors/{namespace}/{actor_id}/data/{key}`

**Rejected because**: Requires manual escaping, not compatible with FDB tooling.

## Implementation Checklist

- [x] Uncomment `foundationdb` in workspace Cargo.toml
- [x] Add `fdb` feature to kelpie-storage
- [x] Create `crates/kelpie-storage/src/fdb.rs`
- [x] Implement `FdbKV` struct with Database handle
- [x] Implement `ActorKV` trait for `FdbKV`
- [x] Add key encoding helpers (tuple layer)
- [x] Map FDB errors to kelpie-core errors
- [x] Add retry logic for transaction conflicts
- [x] Add TigerStyle assertions (2+ per method)
- [x] Add unit tests for key encoding
- [x] Add integration tests (CRUD, list_keys, isolation)
- [x] Update ADR-002 implementation status
- [ ] Add unit tests for retry logic (requires mocking FDB client)

## Test Coverage Summary

### Done

| Test | File | What It Tests |
|------|------|---------------|
| `test_key_encoding_format` | fdb.rs | Tuple encoding roundtrip |
| `test_key_encoding_ordering` | fdb.rs | Lexicographic ordering |
| `test_subspace_isolation` | fdb.rs | Actor key isolation |
| `test_fdb_integration_crud` | fdb.rs | Full CRUD (needs FDB) |
| `test_fdb_integration_list_keys` | fdb.rs | Range queries (needs FDB) |
| `test_fdb_integration_actor_isolation` | fdb.rs | Actor isolation (needs FDB) |

### TODO

| Test | What It Would Test | Approach |
|------|-------------------|----------|
| `test_retry_on_conflict` | Retry logic | Mock FDB client, inject conflict errors |
| `test_retry_exhaustion` | Max retry behavior | Mock FDB client, always return conflict |
| `test_error_mapping` | Error translation | Mock FDB client, return various errors |

**Note**: Mocking the FDB client requires abstracting `Database`/`Transaction` behind traits, which adds complexity. The retry logic is ~30 lines following FDB best practices (`on_error`). Integration tests against real FDB provide confidence. Consider whether mock-based unit tests add sufficient value.

## References

- [ADR-002: FoundationDB Integration](./002-foundationdb-integration.md)
- [FoundationDB Rust Crate](https://crates.io/crates/foundationdb)
- [FDB Tuple Layer Spec](https://github.com/apple/foundationdb/blob/main/design/tuple.md)
- [FDB Transaction Limits](https://apple.github.io/foundationdb/known-limitations.html)

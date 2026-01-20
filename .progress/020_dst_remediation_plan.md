# DST Remediation Plan

This plan addresses the "Fake DST" issues in Kelpie by replacing ad-hoc mocks with true deterministic infrastructure.

## Phase 1: Storage Unification (The "Split Brain" Fix)

The current `kelpie-server` implements its own `SimStorage` (a `HashMap` wrapper). This bypasses the actual `kelpie-dst` infrastructure which has sophisticated fault injection and transaction support.

1.  **Create `KvAdapter`**: Implement a structural adapter that maps `AgentStorage` (Agents, Sessions, Messages) onto the byte-level `ActorKV` trait from `kelpie-dst`.
    *   *Key mapping*: `agents/{id}` -> JSON blob
    *   *Key mapping*: `sessions/{agent_id}/{session_id}` -> JSON blob
2.  **Replace Server SimStorage**: Delete `crates/kelpie-server/src/storage/sim.rs` and replace it with this adapter wrapping `kelpie_dst::SimStorage`.
3.  **Update Tests**: Refactor `_dst.rs` tests in `kelpie-server` to construct the new storage using the proper `FaultInjector` from `kelpie-dst`.

## Phase 2: Runtime Determinism (The "Time" Fix)

Currently, tests use `tokio::time::sleep`, which is wall-clock based and ignores `SimClock`.

1.  **Introduce `madsim`**: Add `madsim` as a dev-dependency. It provides a deterministic drop-in replacement for `tokio` (including `time`, `net`, `fs`).
    *   *Target*: `kelpie-dst` and `kelpie-server` tests.
2.  **Abstraction Layer**: Ensure `kelpie-core` traits (`TimeProvider`, `Runtime`) map correctly to `madsim` when in test mode.
3.  **Migration**: Port one "fake DST" test (e.g., `real_adapter_simhttp_dst.rs`) to use `madsim` and verify that `sleep()` advances virtual time instantly but deterministically.

## Phase 3: Honest Testing

1.  **Rename "Chaos" Tests**: Identify tests that *must* use real wall-clock time (e.g., integrating with external binaries like Firecracker where we can't mock the clock). Rename these from `_dst.rs` to `_chaos.rs`.
2.  **Strict Mode**: Enforce that any file named `_dst.rs` MUST NOT link against `tokio` directly, only the deterministic abstraction.

## Execution Order

1.  [x] Create `kelpie-server/src/storage/adapter.rs` (KV Adapter)
2.  [x] Swap `SimStorage` implementation.
3.  [x] Verify existing tests pass (fixing "fake" determinism later).
4.  [x] Prototype `madsim` integration in a new test file.
5.  [x] Implement `Runtime` abstraction in `kelpie-core`.
6.  [x] Implement `CurrentRuntime` factory for feature-flagged switching.
7.  [x] Update `kelpie-server` tests to use `CurrentRuntime`.
8.  [x] Create `check_dst.sh` monitoring script.

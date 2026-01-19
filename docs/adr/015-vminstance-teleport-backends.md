# ADR-015: VmInstance Teleport Backends and Snapshot Blob Format

## Status

Accepted

## Date

2026-01-15

## Context

Kelpie teleportation requires VM snapshot/restore with platform-native hypervisors. The existing teleport flow is sandbox-based and stores snapshot metadata as JSON placeholders. Teleport types are duplicated across `kelpie-server` and `kelpie-dst`, blocking deterministic simulation of VM-level teleport. We need a VmInstance-based architecture with shared types and a versioned snapshot blob format that supports both Apple VZ (single file) and Firecracker (snapshot + memory file).

## Decision

1. Use the `VmInstance` abstraction (not sandbox) for teleport backends.
2. Move teleport types and storage traits into `kelpie-core::teleport` for shared use in production and DST.
3. Define a versioned `VmSnapshotBlob` format that includes metadata bytes plus snapshot and memory payloads.
4. Implement deterministic `SimVm` and `SimVmFactory` in `kelpie-dst` to enable simulation-first testing with fault injection.

## Consequences

### Positive
- VM backends are reusable across subsystems beyond sandbox.
- DST can run full teleport flows using the same types as production.
- Snapshot blob format supports both Apple VZ and Firecracker without API churn.

### Negative
- `kelpie-core` grows to include teleport-specific types.
- Additional refactoring required to rewire server and DST to shared types.
- Snapshot metadata must be serialized and validated consistently.

### Neutral
- Existing sandbox-based teleport remains until VmInstance integration completes.

## Alternatives Considered

### Sandbox-layer integration

Kept VM backends behind sandbox APIs for minimal wiring. Rejected due to limited reuse and poor fit for VM-specific snapshot semantics.

### New kelpie-teleport crate

Create a dedicated crate for teleport types. Rejected to avoid extra workspace overhead; `kelpie-core` already hosts cross-cutting types.

## References

- `.progress/016_20260115_121324_teleport-dual-backend-implementation.md`
- `.progress/017_20260115_151324_teleport-vm-backends-dst.md`
- `CLAUDE.md` VM Backends section

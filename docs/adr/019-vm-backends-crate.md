# ADR-019: Separate VM Backend Factory Crate

**Date:** 2026-01-15
**Status:** Superseded by ADR-020

## Context

`VmBackendFactory` needs to construct Firecracker-backed `VmInstance` values.
However, `kelpie-firecracker` depends on `kelpie-libkrun` for VM traits, and
`kelpie-sandbox` depends on `kelpie-libkrun` as an optional feature. Adding a
Firecracker dependency directly to `kelpie-libkrun` introduces a cyclic
workspace dependency.

## Decision

Introduce a new crate `kelpie-vm-backends` to host `VmBackend`, `VmBackendKind`,
and `VmBackendFactory`. This crate depends on `kelpie-libkrun` and optionally on
`kelpie-firecracker`, avoiding cycles while preserving a single factory API.

## Trade-offs

- **Pros:** Breaks cyclic dependency; keeps backend selection logic centralized;
  allows optional Firecracker support via features.
- **Cons:** Adds another crate to the workspace; requires callers to import the
  factory from a new location.

## Consequences

- `VmBackendFactory::firecracker` lives in `kelpie-vm-backends`.
- `kelpie-libkrun` remains a pure traits + libkrun/mock implementation crate.
- DST tests can exercise Firecracker factory wiring via a feature gate.

# ADR-020: Consolidate VM Core + Backends into kelpie-vm

**Date:** 2026-01-15
**Status:** Accepted

## Context

VM types (`VmConfig`, `VmInstance`, `VmSnapshot`), mock implementations, and
backend factories were spread across `kelpie-libkrun`, `kelpie-firecracker`, and
`kelpie-vm-backends`. This created confusing layering and made dependency
cycles likely when adding backends that reuse sandbox code.

## Decision

Create a single `kelpie-vm` crate that owns:
- VM traits, config, errors, and snapshot types
- Mock VM implementation
- Backend factory (`VmBackendFactory`)
- Firecracker backend behind a `firecracker` feature

Remove `kelpie-libkrun`, `kelpie-firecracker`, and `kelpie-vm-backends`.

## Trade-offs

- **Pros:** One clear home for VM APIs; fewer crates to understand; no backend
  selection cycles; feature-gated backends in one place.
- **Cons:** `kelpie-vm` depends on `kelpie-sandbox` for Firecracker wiring; sandbox
  no longer has a libkrun-backed implementation (removed).

## Consequences

- Imports switch to `kelpie_vm::*` across server, DST, and tests.
- Firecracker backend is enabled via `kelpie-vm` feature flags.
- libkrun-specific sandbox and DST tests are removed.

# ADR-017: Firecracker Backend via Sandbox Wrapper

**Date:** 2026-01-15
**Status:** Superseded by ADR-020

## Context

We need a production Firecracker VM backend for the `VmInstance` abstraction without
re-introducing sandbox-layer dependencies into teleport flows. The existing
`kelpie-sandbox` Firecracker implementation already handles API wiring, vsock exec,
and snapshot/restore on disk.

## Decision

Implement `kelpie-firecracker` as a `VmInstance` backend that wraps the existing
`kelpie-sandbox::FirecrackerSandbox`, translating between `VmConfig` and
`SandboxConfig`, and converting Firecracker snapshot files to/from `VmSnapshot`
bytes.

## Trade-offs

- **Pros:** Reuses tested Firecracker wiring; avoids duplicating API/exec logic; keeps
  teleport API aligned with `VmInstance`.
- **Cons:** Adds a translation layer and snapshot file I/O; snapshot bytes are encoded
  from disk files rather than streamed directly; dependency on sandbox crate for the
  Firecracker backend.

## Consequences

- Firecracker snapshot/restore remains grounded in the real Firecracker API.
- `VmSnapshot` data is derived from snapshot file pairs and rehydrated during restore.
- Additional cleanup logic is required to avoid leaving snapshot files on disk.

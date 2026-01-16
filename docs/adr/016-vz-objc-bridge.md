# ADR-016: Apple VZ Backend via Objective-C Bridge

**Date:** 2026-01-15
**Status:** Accepted

## Context

We need a macOS backend that uses Virtualization.framework for VM lifecycle,
snapshot/restore, and vsock exec. The user requested a custom bridge rather than
an external Rust wrapper crate.

## Decision

Implement a small Objective-C bridge compiled by `kelpie-vm` (feature `vz`) that
creates and controls `VZVirtualMachine` instances, exposes lifecycle and
snapshot operations, and returns vsock file descriptors to Rust for exec.

## Trade-offs

- **Pros:** Full control over Virtualization.framework APIs; no dependency on
  third-party wrappers; direct access to save/restore and vsock connection.
- **Cons:** Requires ObjC build tooling (`cc`, ARC); macOS-only build path; more
  code to maintain and validate across OS versions.

## Consequences

- VZ backend is only available on macOS 14+ Apple Silicon for snapshot/restore.
- Exec uses vsock file descriptors from the bridge and the existing JSON
  protocol.
- Rust-side code must manage fd lifetime and error translation carefully.

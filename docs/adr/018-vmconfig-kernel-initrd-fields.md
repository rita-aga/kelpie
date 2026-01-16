# ADR-018: Add Kernel/Initrd Paths to VmConfig

**Date:** 2026-01-15
**Status:** Accepted

## Context

Firecracker and Apple Virtualization.framework require explicit kernel (and
optionally initrd) paths. The existing `VmConfig` only captured root disk and
kernel arguments, which is insufficient for these backends.

## Decision

Extend `VmConfig` with optional `kernel_image_path` and `initrd_path` fields,
including builder setters and validation to ensure non-empty values and
reasonable path lengths when provided.

## Trade-offs

- **Pros:** Allows backend-agnostic configuration for kernel/initrd; aligns with
  image build documentation; no forced changes for Mock/libkrun.
- **Cons:** Broadens core config surface area; requires extra validation and
  optional handling across backends.

## Consequences

- Firecracker backend can validate kernel/initrd inputs before VM creation.
- Apple VZ backend has a natural place to read boot artifacts from `VmConfig`.
- Existing callers remain compatible because fields are optional with defaults.

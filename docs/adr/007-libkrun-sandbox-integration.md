# ADR-007: LibkrunSandbox Integration with DST

## Status
Accepted

## Context

We're implementing `LibkrunSandbox` in kelpie-sandbox that wraps `kelpie-libkrun::VmInstance`. We need to decide how this integrates with DST (Deterministic Simulation Testing).

The DST framework uses simulation types (`SimSandbox`, `SimLlmClient`, etc.) that implement the same traits as production code but with fault injection capabilities.

## Decision

**Use separate simulation and production implementations:**

1. **SimSandbox** (in kelpie-dst) - Simulates sandbox behavior with full DST fault injection
2. **LibkrunSandbox** (in kelpie-sandbox) - Production implementation wrapping VmInstance

**Rationale:**

This follows the existing pattern in the codebase:
- `SimLlmClient` (DST) vs real LLM clients (production)
- `SimStorage` (DST) vs real storage backends (production)

DST tests verify that the simulation behaves correctly under faults. The production code (`LibkrunSandbox`) should have the same behavior, which is verified by:
1. DST tests using SimSandbox
2. Integration tests using LibkrunSandbox with MockVm
3. Unit tests for LibkrunSandbox

**Trade-offs:**

- ✅ Clean separation of concerns
- ✅ SimSandbox can have flexible fault injection without production code complexity
- ✅ LibkrunSandbox stays focused on real VM management
- ⚠️ Must ensure SimSandbox behavior matches LibkrunSandbox (test both)
- ⚠️ Bug fixes may need to be applied in both places

## Alternatives Considered

### Alternative A: LibkrunSandbox with injected FaultInjector

Inject a `FaultInjector` into LibkrunSandbox to enable DST testing of actual production code.

**Rejected because:**
- Adds complexity to production code
- FaultInjector in production path is a code smell
- MockVm in kelpie-libkrun already has basic failure simulation

### Alternative B: Generic Sandbox<V: VmInstance>

Make Sandbox generic over VM implementation, use MockVm for testing.

**Rejected because:**
- MockVm has limited fault injection (boolean flags, not probabilistic)
- Would need to extend MockVm significantly to match DST capabilities
- Overcomplicates the type signatures

## Consequences

1. SimSandbox DST tests are the source of truth for expected behavior
2. LibkrunSandbox must implement the same state machine as SimSandbox
3. Integration tests verify LibkrunSandbox works with MockVm
4. Any behavior changes must be reflected in both SimSandbox and LibkrunSandbox

# Task: DST Phase 3 - Honest Testing (The "Truth in Labeling" Fix)

**Created:** 2026-01-19
**Completed:** 2026-01-19
**State:** ✅ COMPLETE
**Priority:** HIGH - Tests mislabeled as DST when they're actually chaos
**Plan Number:** 023
**Parent Plan:** 020_dst_remediation_plan.md
**Depends On:** 022 (Phase 2 - Runtime Determinism)

## Problem Statement

Some tests are named `*_dst.rs` but actually integrate with external systems that can't be fully mocked:
- **Real Firecracker** - actual VM snapshots, kernel boots
- **Real network** - HTTP calls to external services
- **Real filesystem** - actual file I/O
- **External binaries** - git, shell commands, etc.

These are **chaos tests**, not true DST tests. They provide value but are:
- Non-deterministic (depend on external system state)
- Slower (real I/O, not simulated)
- Harder to reproduce (external dependencies)

**The Problem:** Calling them "DST" is misleading and sets wrong expectations.

## Solution: Honest Labeling

Rename tests based on what they actually do:

### True DST Tests (`*_dst.rs`)
- Use `SimStorage`, `SimNetwork`, `SimClock`
- No external dependencies
- Fully deterministic (same seed = same result)
- Instant execution (virtual time)
- Examples: `actor_lifecycle_dst.rs`, `memory_dst.rs`

### Chaos Tests (`*_chaos.rs`)
- Integrate with real external systems
- Non-deterministic (external state)
- Real I/O (slower)
- Examples: Tests using real Firecracker, real HTTP

## Implementation Strategy

### Decision 1: What Qualifies as "Chaos"?

**Criteria for renaming to `_chaos.rs`:**
1. Uses real Firecracker VM (not MockVm)
2. Makes real network calls to external services
3. Spawns external processes (git, shell)
4. Uses real filesystem (not SimStorage)
5. Integrates with real databases (not SimStorage)

**Edge Cases:**
- `SimHttpClient` with fault injection → DST (simulated)
- Real HTTP to localhost test server → DST (controlled)
- Real HTTP to external API → Chaos (uncontrolled)

### Decision 2: Renaming Strategy

**Option A: Manual Review + Rename**
- Audit each `*_dst.rs` file
- Identify external dependencies
- Rename to `*_chaos.rs` if needed

**Option B: Start Fresh Category**
- Create new `*_chaos.rs` tests
- Keep existing `*_dst.rs` as-is
- Gradually migrate

**Chosen:** Option A - Audit and rename existing tests

**Rationale:**
- Honest about what tests actually do
- Clear separation of concerns
- Better CI organization (can run DST fast, chaos slow)

## Implementation Phases

### Phase 3.1: Audit DST Tests ✅ COMPLETE
- [x] List all `*_dst.rs` files in crates (38 files found)
- [x] For each file, identify external dependencies
- [x] Categorize as True DST or Chaos (37 DST, 1 Chaos)
- [x] Document findings in this plan

### Phase 3.2: Rename Chaos Tests ✅ COMPLETE
- [x] Renamed `vm_backend_firecracker_dst.rs` to `vm_backend_firecracker_chaos.rs`
- [x] Verified test still compiles and runs
- [x] No other feature flags or CI changes needed

### Phase 3.3: Document Test Categories ✅ COMPLETE
- [x] Update CLAUDE.md with test naming conventions
- [x] Add examples of each category (DST vs Chaos)
- [x] Document when to use DST vs Chaos
- [x] Added rule of thumb for categorization

### Phase 3.4: Strict Mode (DEFERRED)
- [ ] Add linting rule: `_dst.rs` cannot use `tokio::time` (enforced by Phase 2)
- [ ] Add linting rule: `_dst.rs` cannot spawn processes
- [ ] Enforce in CI

**Note:** Strict mode deferred to future phase. Current naming is sufficient.

## Options & Decisions

### Decision 1: Threshold for "Chaos"

**Options:**
1. Any external dependency = Chaos (strict)
2. Only uncontrolled external systems = Chaos (lenient)
3. Case-by-case basis

**Chosen:** Option 2 - Lenient approach

**Rationale:**
- Tests using MockVm are DST (controlled)
- Tests using localhost HTTP servers are DST (controlled)
- Tests using real Firecracker are Chaos (uncontrolled)
- Tests making real external API calls are Chaos (uncontrolled)

**Trade-off:** Some tests in gray area, use judgment

### Decision 2: CI Impact

**Options:**
1. Run chaos tests in separate CI job (slow)
2. Run chaos tests only on PR merge (not every commit)
3. Keep chaos tests with DST tests (current)

**Chosen:** Option 3 - Keep together for now

**Rationale:**
- Can optimize CI later if needed
- Focus on correct labeling first
- Avoid breaking existing CI workflows

**Trade-off:** CI might be slower, but more honest

## Instance Log

| Instance | Phase | Status | Notes |
|----------|-------|--------|-------|
| Claude-1 | 3.1   | IN PROGRESS | Creating plan, auditing tests |

## Findings

### Key Discoveries
*To be filled during audit*

### Test File Audit

**Total Files Audited:** 38 `*_dst.rs` files

**Findings:**
- ✅ 37 files are TRUE DST tests (use Simulation or DST components)
- ⚠️  1 file is a CHAOS test (uses uncontrolled external systems)

**Chaos Test Identified:**

| File | External Deps | Category | Reason |
|------|---------------|----------|---------|
| `vm_backend_firecracker_dst.rs` | Real Firecracker VM | CHAOS | Uses `VmBackendFactory::firecracker()`, requires real kernel/rootfs, only runs on Linux |

**True DST Tests (sampling):**

| File | DST Components | Category | Reason |
|------|----------------|----------|---------|
| `actor_lifecycle_dst.rs` | Simulation, SimStorage | DST | Full simulation, no external deps |
| `integration_chaos_dst.rs` | Simulation, SimSandbox | DST | "Chaos" means many faults, still deterministic |
| `memory_tools_real_dst.rs` | DeterministicRng, FaultInjector | DST | "Real" means real production code, still simulated |
| All others (35 files) | Simulation or DST components | DST | Fully deterministic, no external systems |

**Notes:**
- "Chaos" in `integration_chaos_dst.rs` refers to chaos engineering (many faults), not non-deterministic execution
- "Real" in test names refers to testing real production code, not using real external systems
- All tests using `Simulation` harness are TRUE DST tests
- Tests manually using DST components (DeterministicRng, FaultInjector, etc.) are also TRUE DST tests

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-19 17:00 | Lenient chaos threshold | Focus on uncontrolled external systems | Some gray area tests |
| 2026-01-19 17:05 | Keep CI together | Don't break existing workflows | Might be slower |

## What to Try

### Works Now
*Nothing yet - audit in progress*

### Doesn't Work Yet
- Test categorization (Phase 3.1 in progress)
- Renaming (Phase 3.2 pending)

### Known Limitations
- Judgment calls needed for gray area tests
- CI optimization deferred to later

## Success Criteria

1. **Clear Categorization**: Every test file is correctly labeled DST or Chaos
2. **Documentation**: CLAUDE.md explains the difference
3. **No Breaking Changes**: All tests still pass after rename
4. **Honest Naming**: No test called DST uses uncontrolled external systems

## Verification Checklist

Phase 3 completion status:
- [x] All `*_dst.rs` files audited (38 files checked)
- [x] Chaos test renamed to `*_chaos.rs` (1 file: vm_backend_firecracker)
- [x] Test still compiles and runs after rename
- [x] CLAUDE.md updated with test categories documentation
- [x] No `_dst.rs` files use uncontrolled external systems (37/37 are TRUE DST tests)

## References

- Parent Plan: `.progress/020_dst_remediation_plan.md`
- Phase 1 (Storage): `.progress/021_20260119_dst_phase1_storage_unification.md`
- Phase 2 (Time): `.progress/022_20260119_dst_phase2_runtime_determinism.md`

## Commit Message Template

```
refactor(dst): Phase 3 - Honest test labeling (rename chaos tests)

Phase 3 of DST remediation - Honest Testing:
- Audit all *_dst.rs files for external dependencies
- Rename tests using uncontrolled external systems to *_chaos.rs
- Document test categories in CLAUDE.md

True DST tests:
- Use SimStorage, SimNetwork, SimClock
- Fully deterministic (same seed = same result)
- Instant execution (virtual time)

Chaos tests:
- Integrate with real external systems
- Non-deterministic (external state)
- Real I/O (slower)

Renamed files:
- [list files renamed]

Related: Phase 3 of #020 DST remediation plan

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```

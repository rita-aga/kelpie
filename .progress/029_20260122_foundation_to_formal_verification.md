# Task: Foundation to Formal Verification Pipeline

**Created:** 2026-01-22 14:30:00
**State:** PLANNING

---

## Vision Alignment

**Vision files read:** CONSTRAINTS.md, CLAUDE.md

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - DST is primary verification method
- TigerStyle safety principles (CONSTRAINTS.md §3) - Assertions, explicit constants, no silent failures
- No placeholders in production (CONSTRAINTS.md §4) - Must verify before claiming complete
- Changes are traceable (CONSTRAINTS.md §7) - ADRs document architectural decisions

---

## Task Description

### Problem

The Kelpie codebase has infrastructure for advanced verification (DST framework, ADRs), but the current state is uncertain:
- **DST coverage is questionable** - Do we have tests for critical paths? Are the tests real DST or pseudo-DST?
- **ADRs are questionable** - Are they up to date? Do they match the implementation?
- **Code quality is uncertain** - TigerStyle compliance? Dead code? Stubs?

Without a solid foundation, we cannot build the advanced verification pipeline:
- We can't generate TLA+ specs from ADRs if ADRs are stale
- We can't build a verification pyramid if DST coverage has gaps
- We can't trust the system if the code itself is questionable

### Solution

Build from foundation to formal verification in two major stages:

**Stage 1: Foundation Cleanup (Phases 1-4)**
- Audit and fix DST coverage
- Audit and update ADRs
- Audit and fix code quality
- Achieve a known-good baseline

**Stage 2: Formal Verification Infrastructure (Phases 5-8)**
- Create TLA+ specifications from validated ADRs
- Build verification pyramid (DST → Stateright → Kani)
- Add production telemetry integration
- Create ADR → TLA+ → DST pipeline for ongoing development

### Why This Order

```
                    ┌─────────────────────────────────────────┐
                    │  Stage 2: Formal Verification          │
                    │                                        │
                    │  Phase 8: ADR→TLA+→DST Pipeline        │
                    │  Phase 7: Production Telemetry         │
                    │  Phase 6: Verification Pyramid         │
                    │  Phase 5: TLA+ Specifications          │
                    └────────────────┬────────────────────────┘
                                     │ DEPENDS ON
                    ┌────────────────▼────────────────────────┐
                    │  Stage 1: Foundation Cleanup           │
                    │                                        │
                    │  Phase 4: Foundation Fixes             │
                    │  Phase 3: Code Quality Audit           │
                    │  Phase 2: ADR Audit                    │
                    │  Phase 1: DST Coverage Audit           │
                    └─────────────────────────────────────────┘
```

---

## Options & Decisions [REQUIRED]

### Decision 1: Audit Before Fix vs Fix As We Go

**Context:** Should we audit everything first, then fix, or fix issues as we find them?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Audit-First | Complete all audits (DST, ADR, Code), then fix in Phase 4 | Full picture before changes; can prioritize | Longer before any fixes; might forget context |
| B: Fix-As-We-Go | Fix issues immediately when found during audit | Immediate progress; fresh context | Might miss bigger patterns; harder to track |
| C: Hybrid | Audit creates issues, fix critical ones immediately, batch the rest | Best of both; critical issues fixed fast | More complex tracking |

**Decision:** C (Hybrid) - Audit creates a full inventory of issues, critical/blocking issues are fixed immediately, non-critical issues are batched for Phase 4.

**Trade-offs accepted:**
- More complex issue tracking (use VFS tools)
- Some context may be lost between audit and batch fix
- Acceptable because: critical issues get immediate attention, pattern recognition from full audit

---

### Decision 2: What Constitutes "Good Enough" Foundation

**Context:** When is Stage 1 complete? What's the bar for moving to Stage 2?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Perfection | 100% DST coverage, all ADRs current, zero code issues | Highest confidence | May never finish; diminishing returns |
| B: Critical Paths | Critical paths have DST, core ADRs current, no blocking issues | Pragmatic; enables progress | Some gaps remain |
| C: Metrics-Based | Define specific thresholds (e.g., 80% DST, 90% ADR accuracy) | Objective; measurable | Numbers may not reflect quality |

**Decision:** B (Critical Paths) - Focus on critical paths and core components. Stage 2 can proceed when:
- All critical paths (actor lifecycle, storage, migration) have verified DST coverage
- Core ADRs (001-005) are current and accurate
- No blocking code quality issues (stubs in production paths, fake DST)

**Trade-offs accepted:**
- Non-critical paths may have gaps
- Some ADRs may be deprioritized
- Acceptable because: Stage 2 builds on critical paths, not edge cases

---

### Decision 3: TLA+ Scope

**Context:** Which components get TLA+ specifications in Phase 5?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Everything | TLA+ for all crates | Complete formal coverage | Massive effort; diminishing returns |
| B: Distributed Core | Actor lifecycle, storage, cluster coordination | High-value targets; where bugs hide | Doesn't cover all code |
| C: Just Actor Lifecycle | Start with single-actor invariants | Fastest to deliver; proof of concept | Limited coverage |

**Decision:** B (Distributed Core) - TLA+ specs for:
1. Actor Lifecycle (single-actor activation, deactivation, invocation)
2. Actor Storage (KV operations, consistency)
3. Actor Migration/Teleport (snapshot, restore, state transfer)
4. Cluster Coordination (registry, placement) - if time permits

**Trade-offs accepted:**
- WASM runtime, CLI tools don't get TLA+ specs
- Agent abstraction layer doesn't get formal specs
- Acceptable because: formal verification most valuable for distributed correctness

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-22 | Hybrid audit approach | Balance thoroughness with progress | Tracking complexity |
| 2026-01-22 | Critical paths bar for Stage 2 | Pragmatic path to formal verification | Non-critical gaps |
| 2026-01-22 | TLA+ for distributed core only | Highest value targets | Limited scope |

---

## Current State Assessment

### Infrastructure We Have

| Component | Location | Status |
|-----------|----------|--------|
| **Python MCP Server** | `tools/mcp-kelpie-python/` | ✅ 31 tools, 89 tests |
| **tree-sitter Indexer** | `mcp_kelpie/indexer/` | ✅ Structural indexes |
| **RLM Environment** | `mcp_kelpie/rlm/` | ✅ REPL + sub-LLM |
| **AgentFS (Turso)** | `agentfs-sdk` | ✅ Persistent state |
| **DST Framework** | `crates/kelpie-dst/` | ⚠️ Exists, coverage unknown |
| **ADRs** | `docs/adr/` | ⚠️ Exist, accuracy unknown |

### MCP Tools Available for This Work

**For Auditing:**
- `repl_load` + `repl_sub_llm` - Load code, have sub-LLM analyze
- `repl_map_reduce` - Parallel analysis across partitions
- `index_*` - Query structural indexes

**For Tracking:**
- `vfs_fact_add/check` - Track verified facts with evidence
- `vfs_invariant_verify/status` - Track invariant verification
- `vfs_exploration_log` - Audit trail of exploration

**For Verification:**
- Claude's `Bash` tool - Run `cargo test`, `cargo clippy`, etc.
- Claude's `Read/Grep/Glob` - Examine code directly

---

## Implementation Plan

### Stage 1: Foundation Cleanup

#### Phase 1: DST Coverage Audit

**Goal:** Understand current DST coverage - what's tested, what's missing, what's fake.

**Approach:** Use RLM to load and analyze all DST tests.

```bash
# Load all DST-related files
repl_load(pattern="crates/kelpie-dst/**/*.rs", var_name="dst_framework")
repl_load(pattern="**/*_dst.rs", var_name="dst_tests")
repl_load(pattern="**/*_chaos.rs", var_name="chaos_tests")
```

- [ ] **1.1: Inventory DST Framework**
  - Load `kelpie-dst` crate
  - Document available components: SimClock, SimStorage, SimNetwork, FaultInjector, etc.
  - Identify supported fault types
  - Record in `vfs_fact_add`

- [ ] **1.2: Inventory DST Tests**
  - Find all `*_dst.rs` files
  - For each: What component? What scenarios? What faults?
  - Identify "fake DST" (tests that claim determinism but aren't)
  - Record findings

- [ ] **1.3: Identify Coverage Gaps**
  - Map DST tests to critical paths:
    - [ ] Actor activation/deactivation
    - [ ] Actor invocation
    - [ ] State persistence (KV operations)
    - [ ] State recovery (crash/restart)
    - [ ] Migration/teleport
    - [ ] Cluster coordination
  - Document gaps

- [ ] **1.4: Assess Test Quality**
  - Do tests use `DST_SEED` for reproducibility?
  - Do tests inject faults?
  - Do tests verify invariants (not just "doesn't crash")?
  - Rate each test: Real DST / Partial DST / Fake DST

**Deliverable:** `.kelpie-index/audits/dst_coverage_audit.md`

---

#### Phase 2: ADR Audit

**Goal:** Verify ADRs are current, accurate, and match implementation.

**Approach:** Read each ADR, compare to current code, identify drift.

- [ ] **2.1: Inventory ADRs**
  - List all ADRs in `docs/adr/`
  - For each: title, date, status (proposed/accepted/superseded)

- [ ] **2.2: ADR 001 - Virtual Actor Model**
  - Read ADR
  - Verify claims against `kelpie-runtime/`
  - Document drift or confirmation
  - Mark as: Current / Needs Update / Superseded

- [ ] **2.3: ADR 002 - FoundationDB Integration**
  - Read ADR
  - Verify against `kelpie-storage/`
  - Note: Is FDB still the plan? Or has it changed?

- [ ] **2.4: ADR 003 - WASM Actor Runtime**
  - Read ADR
  - Verify against `kelpie-wasm/`

- [ ] **2.5: ADR 004 - Linearizability Guarantees**
  - Read ADR
  - This is critical for TLA+ specs
  - Verify consistency model claims

- [ ] **2.6: ADR 005 - DST Framework**
  - Read ADR
  - Compare to Phase 1 findings
  - Does the ADR match reality?

- [ ] **2.7: Identify Missing ADRs**
  - What architectural decisions are NOT documented?
  - Cluster coordination?
  - Agent abstraction?
  - Teleport/migration?

**Deliverable:** `.kelpie-index/audits/adr_audit.md`

---

#### Phase 3: Code Quality Audit

**Goal:** Assess TigerStyle compliance, dead code, stubs, and overall quality.

**Approach:** Combination of automated checks and RLM analysis.

- [ ] **3.1: TigerStyle Compliance**
  - Check for explicit constants with units (e.g., `TIMEOUT_MS_MAX`)
  - Check for assertions in functions (target: 2+ per non-trivial function)
  - Check for big-endian naming
  - Check for `u64` vs `usize` for sizes

- [ ] **3.2: Dead Code Detection**
  ```bash
  cargo clippy --workspace -- -W dead_code 2>&1 | grep "dead_code"
  ```
  - Document unused functions, types, modules

- [ ] **3.3: Stub Detection**
  ```bash
  grep -r "TODO\|FIXME\|unimplemented!\|todo!\|stub" crates/ --include="*.rs"
  grep -r "not yet implemented\|placeholder" crates/ --include="*.rs"
  ```
  - Identify stubs in production paths vs tests

- [ ] **3.4: Unwrap Audit**
  ```bash
  grep -r "\.unwrap()\|\.expect(" crates/ --include="*.rs" | grep -v test | grep -v "_dst.rs"
  ```
  - Production code should use `?` or explicit error handling

- [ ] **3.5: Test Coverage Assessment**
  - Use `cargo tarpaulin` if available
  - Or manual review of critical paths

**Deliverable:** `.kelpie-index/audits/code_quality_audit.md`

---

#### Phase 4: Foundation Fixes

**Goal:** Fix issues identified in Phases 1-3 to achieve known-good baseline.

**Prerequisites:** Phases 1-3 complete, issues documented.

- [ ] **4.1: Critical DST Gaps**
  - Add DST tests for uncovered critical paths
  - Priority: actor lifecycle, storage, migration

- [ ] **4.2: Fake DST Remediation**
  - Convert fake DST to real DST (use Simulation harness)
  - Or rename to `*_chaos.rs` if truly non-deterministic

- [ ] **4.3: ADR Updates**
  - Update stale ADRs to match implementation
  - Create missing ADRs for undocumented decisions

- [ ] **4.4: Code Quality Fixes**
  - Remove dead code
  - Fix stubs in production paths
  - Replace unwraps with proper error handling

- [ ] **4.5: Verification**
  ```bash
  cargo test --workspace
  cargo clippy --workspace -- -D warnings
  cargo fmt --check
  ```

**Deliverable:** Clean test run, updated ADRs, documented fixes

**Stage 1 Exit Criteria:**
- [ ] All critical paths have verified DST coverage
- [ ] Core ADRs (001-005) are current
- [ ] No fake DST in test suite
- [ ] No stubs in production code paths
- [ ] All tests pass

---

### Stage 2: Formal Verification Infrastructure

**Prerequisites:** Stage 1 complete.

#### Phase 5: TLA+ Specifications

**Goal:** Create formal TLA+ specifications for distributed core components.

**Reference:** VDE paper section on TLA+ integration.

- [ ] **5.1: Actor Lifecycle Spec** (`specs/tla/ActorLifecycle.tla`)
  - States: Inactive, Activating, Active, Deactivating
  - Operations: Activate, Invoke, Deactivate
  - Invariants:
    - SingleActivation: At most one active instance per ActorId
    - NoLostMessages: Invocations during deactivation are queued
    - SafeDeactivation: State persisted before deactivation completes

- [ ] **5.2: Actor Storage Spec** (`specs/tla/ActorStorage.tla`)
  - Operations: Get, Put, Delete, Transaction
  - Invariants:
    - Linearizability: Operations appear atomic
    - Durability: Committed writes survive crashes
    - Isolation: Concurrent transactions don't interfere

- [ ] **5.3: Actor Migration Spec** (`specs/tla/ActorMigration.tla`)
  - Operations: Snapshot, Transfer, Restore
  - Invariants:
    - AtomicVisibility: Actor either at source or destination, never both
    - NoStateLoss: All state transferred correctly
    - NoMessageLoss: In-flight messages handled

- [ ] **5.4: Spec Validation**
  ```bash
  # Run TLC model checker
  tlc specs/tla/ActorLifecycle.tla
  tlc specs/tla/ActorStorage.tla
  tlc specs/tla/ActorMigration.tla
  ```

- [ ] **5.5: Spec-to-Test Mapping**
  - Document which TLA+ invariants map to which DST tests
  - Store in `.kelpie-index/specs/invariant-test-mapping.yaml`

**Deliverable:** TLA+ specs, passing TLC, documented mapping

---

#### Phase 6: Verification Pyramid

**Goal:** Build layered verification with increasing confidence.

**Levels:**
```
                    ┌─────────────────┐
                    │  Kani (proofs)  │ ~60s, bounded proofs
                    └────────┬────────┘
                    ┌────────▼────────┐
                    │   Stateright    │ ~30-60s, exhaustive states
                    └────────┬────────┘
                    ┌────────▼────────┐
                    │      DST        │ ~5s, simulation with faults
                    └────────┬────────┘
                    ┌────────▼────────┐
                    │   Unit Tests    │ ~1s, basic correctness
                    └─────────────────┘
```

- [ ] **6.1: Document Pyramid in CLAUDE.md**
  - When to use each level
  - Commands for each level
  - Expected timing

- [ ] **6.2: Stateright Integration**
  - Add `stateright` to `Cargo.toml`
  - Create model for actor lifecycle
  - Map to TLA+ invariants

- [ ] **6.3: Kani Integration** (optional, if installed)
  - Add Kani harnesses for critical functions
  - Focus on bounded proofs for core invariants

- [ ] **6.4: Verification Skill**
  - Create `.claude/skills/verification-pyramid.md`
  - When to run each level
  - How to interpret results

**Deliverable:** Working verification pyramid, documented usage

---

#### Phase 7: Production Telemetry Integration

**Goal:** Ground verification in real-world behavior.

**Note:** This phase is relevant when Kelpie is deployed. Can be deferred if not yet in production.

- [ ] **7.1: Define Telemetry Interface**
  - What metrics matter? (latency, throughput, errors)
  - What traces? (distributed traces, span context)
  - Provider-agnostic design

- [ ] **7.2: Implement Telemetry Client**
  - Support Prometheus, Datadog, or custom
  - Cache results with TTL (use VFS cache tools)

- [ ] **7.3: Integrate with Verification**
  - "Did the invariant hold in production?"
  - Telemetry as fifth level of pyramid

**Deliverable:** Telemetry interface, optional implementations

---

#### Phase 8: ADR → TLA+ → DST Pipeline

**Goal:** Create sustainable pipeline for ongoing development.

**Workflow:**
```
New Feature → Write ADR → Generate TLA+ → Generate DST → Implement → Verify
```

- [ ] **8.1: Document Pipeline Process**
  - Template for ADRs that support TLA+ generation
  - Guidelines for TLA+ spec writing
  - Guidelines for DST test creation

- [ ] **8.2: LLM-Assisted TLA+ Generation** (optional)
  - Use sub-LLM to draft TLA+ from ADR
  - Human review required
  - Store prompts and templates

- [ ] **8.3: Pipeline Validation Tools**
  - Check: Does ADR exist for component?
  - Check: Does TLA+ spec exist for ADR?
  - Check: Do DST tests cover TLA+ invariants?

- [ ] **8.4: Pipeline Skill**
  - Create `.claude/skills/spec-pipeline.md`
  - Workflow for new features
  - Validation commands

**Deliverable:** Documented pipeline, validation tools, skill file

---

## Checkpoints

- [ ] Codebase understood
- [ ] Plan approved
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained**

### Stage 1 Checkpoints
- [ ] Phase 1: DST Coverage Audit complete
- [ ] Phase 2: ADR Audit complete
- [ ] Phase 3: Code Quality Audit complete
- [ ] Phase 4: Foundation Fixes complete
- [ ] **Stage 1 Exit Criteria met**

### Stage 2 Checkpoints
- [ ] Phase 5: TLA+ Specifications complete
- [ ] Phase 6: Verification Pyramid complete
- [ ] Phase 7: Production Telemetry complete (or deferred)
- [ ] Phase 8: Pipeline complete

### Final
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [ ] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**Phase 1-3 (Audits):**
- No new tests, just analysis

**Phase 4 (Fixes):**
- New DST tests for identified gaps
- All tests must pass after fixes

**Phase 5 (TLA+):**
- TLC model checker passes on all specs
- No deadlocks or invariant violations

**Phase 6 (Pyramid):**
- Stateright models compile and run
- Optional: Kani harnesses prove

**Commands:**
```bash
# Run all tests
cargo test --workspace

# Run DST tests specifically
cargo test -p kelpie-dst

# Reproduce specific DST failure
DST_SEED=12345 cargo test -p kelpie-dst

# Run Stateright tests (when implemented)
cargo test stateright_ -- --ignored

# Run TLC (when specs exist)
tlc specs/tla/ActorLifecycle.tla

# Run clippy
cargo clippy --all-targets --all-features

# Format code
cargo fmt
```

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| | | |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| | | |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| | | | |

---

## Findings

[Key discoveries from audits will be documented here]

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| MCP Server | `cd tools/mcp-kelpie-python && uv run mcp-kelpie` | Server starts, 31 tools available |
| Structural Indexes | `index_refresh` then `index_status` | Indexes built and queryable |
| RLM Analysis | `repl_load` + `repl_sub_llm` | Can analyze code with sub-LLM |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| DST coverage visibility | Need Phase 1 audit | After Phase 1 |
| TLA+ specs | Need foundation first | After Phase 4 |
| Verification pyramid | Need TLA+ first | After Phase 5 |

### Known Limitations ⚠️
- Stage 2 depends on Stage 1 completion
- TLA+ tools need to be installed (`brew install tla-plus`)
- Kani is optional (requires separate installation)
- Production telemetry (Phase 7) may be deferred if not yet deployed

---

## Completion Notes

[To be filled when complete]

---

## Appendix: Extracted from Plan 026

This plan incorporates and supersedes the following from archived plan 026:
- Phase 11: Formal Methods Integration (now Phase 5)
- Phase 12: Verification Pyramid (now Phase 6)
- Phase 14: Production Telemetry (now Phase 7)
- Phase 15: ADR → TLA+ → Rust Pipeline (now Phase 8)

Key insight from 026: "Instructions tell the AI *what to do*; verification tells it *whether it worked*. Persistence lets it *remember what it learned*."

The foundation phases (1-4) are new, addressing the prerequisite that the codebase must be in known-good state before formal verification infrastructure can be built.

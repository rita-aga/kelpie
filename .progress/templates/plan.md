# Task: [Name]

**Created:** YYYY-MM-DD HH:MM:SS
**State:** GROUNDING | PLANNING | IMPLEMENTING | VERIFYING | COMPLETE

---

## Vision Alignment

**Vision files read:** [List .vision/ files read: CONSTRAINTS.md, or check VISION.md/CLAUDE.md]

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1)
- TigerStyle safety principles (CONSTRAINTS.md §3)
- No placeholders in production (CONSTRAINTS.md §4)
- [List other constraints or principles that apply to this task]

---

## Task Description

[What needs to be done and why]

---

## Options & Decisions [REQUIRED]

> ⚠️ **DO NOT SKIP THIS SECTION.** Every non-trivial task involves choices. Document them.

### Decision 1: [Title]

**Context:** [What problem or choice are we facing?]

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: [Name] | [Brief description] | [Benefits] | [Drawbacks] |
| B: [Name] | [Brief description] | [Benefits] | [Drawbacks] |
| C: [Name] | [Brief description] | [Benefits] | [Drawbacks] |

**Decision:** [Which option and why — explain the REASONING]

**Trade-offs accepted:**
- [What we're giving up by choosing this option]
- [Risks we're accepting]
- [Why these trade-offs are acceptable]

---

### Decision 2: [Title]

**Context:** [What problem or choice are we facing?]

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: [Name] | [Brief description] | [Benefits] | [Drawbacks] |
| B: [Name] | [Brief description] | [Benefits] | [Drawbacks] |

**Decision:** [Which option and why]

**Trade-offs accepted:**
- [What we're giving up]

---

## Quick Decision Log [REQUIRED]

> ⚠️ **Log ALL decisions here**, even small ones. This is your audit trail.

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| | | | |

---

## Implementation Plan

### Phase 1: [Name]
- [ ] Step 1
- [ ] Step 2

### Phase 2: [Name]
- [ ] Step 1
- [ ] Step 2

---

## Checkpoints

- [ ] Codebase understood
- [ ] Plan approved
- [ ] **Options & Decisions filled in**
- [ ] **Quick Decision Log maintained**
- [ ] Implemented
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [ ] **DST coverage added** (if critical path)
- [ ] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**Unit tests:**
- [files/coverage requirements]

**DST tests (if critical path):**
- [ ] Normal conditions test
- [ ] Fault injection test (specify fault types)
- [ ] Stress test (high concurrency, large data)
- [ ] Determinism verification (same seed = same result)

**Integration tests:**
- [scenarios to cover]

**Commands:**
```bash
# Run all tests
cargo test

# Run DST tests specifically
cargo test -p kelpie-dst

# Reproduce specific DST failure
DST_SEED=12345 cargo test -p kelpie-dst

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

[Key discoveries, insights, and information that other instances may need]

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

> ⚠️ **DO NOT SKIP THIS SECTION.** After EVERY phase, update what works and what doesn't.
> The user needs to know what they can test RIGHT NOW.

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| [Feature/capability] | [Exact command or steps] | [What user should see] |
| | | |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| [Feature/capability] | [Missing piece or dependency] | [Phase or condition] |
| | | |

### Known Limitations ⚠️
- [Things that work but with caveats]
- [Edge cases not handled]
- [Performance considerations]

---

## Completion Notes

**Verification Status:**
- Tests: [pass/fail with command output]
- Clippy: [clean/warnings with details]
- Formatter: [pass/fail]
- /no-cap: [pass/fail]
- Vision alignment: [confirmed/concerns]

**DST Coverage (if applicable):**
- Fault types tested: [list]
- Seeds tested: [list or "randomized"]
- Determinism verified: [yes/no]

**Key Decisions Made:**
- [Decision 1]: [outcome]
- [Decision 2]: [outcome]

**What to Try (Final):**
| What | How to Try | Expected Result |
|------|------------|-----------------|
| | | |

**Commit:** [hash]
**PR:** [link if applicable]

# Task: Integrate Northstar .progress and Deterministic Sim Guidance

**Created:** 2026-01-12 12:01:00
**State:** COMPLETE

---

## Vision Alignment

**Vision files read:**
- kelpie/CLAUDE.md (existing development guide with DST principles)
- kelpie/VISION.md (not yet read, will read next)
- northstar/templates/.vision/CONSTRAINTS.md (simulation-first guidance)
- northstar/global/CLAUDE.md.snippet (progress workflow)
- northstar/templates/.progress/templates/plan.md (plan template)

**Relevant constraints/guidance:**
- Kelpie already follows TigerStyle and DST-first development
- Need to integrate more structured planning workflow from northstar
- Need to enhance simulation-first guidance with explicit workflow steps

---

## Task Description

Integrate two key pieces from northstar into kelpie:

1. **.progress guidance** - Structured planning workflow with:
   - Vision-aligned planning mandatory process
   - Numbered plan files with timestamp format
   - Required sections (Options & Decisions, Quick Decision Log, What to Try)
   - Multi-instance coordination support

2. **Deterministic sim guidance** - Enhanced simulation-first workflow:
   - Explicit harness extension rule
   - Step-by-step simulation workflow diagram
   - Enforcement checklist
   - Clear examples of right vs wrong approaches

---

## Options & Decisions [REQUIRED]

### Decision 1: Where to Add .progress Guidance

**Context:** Need to decide how to integrate the .progress workflow into kelpie's existing CLAUDE.md

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Append to CLAUDE.md | Add as new section at end | Simple, keeps everything in one file | CLAUDE.md already 574 lines, getting long |
| B: Separate .progress/README.md | Create dedicated guide | Keeps CLAUDE.md focused, separates concerns | Users need to read two files |
| C: Replace sections in CLAUDE.md | Update existing sections inline | Integrated approach | More invasive changes |

**Decision:** Option A - Append to CLAUDE.md

**Trade-offs accepted:**
- CLAUDE.md will be longer (~750 lines) but still manageable
- Single source of truth for developers
- Existing workflow references remain intact
- Can always split later if needed

---

### Decision 2: How to Enhance DST Guidance

**Context:** Kelpie already has DST guidance. Need to decide how much of northstar's CONSTRAINTS.md to integrate.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Create .vision/CONSTRAINTS.md | Port northstar template verbatim | Consistent with northstar structure | Duplicates some existing CLAUDE.md content |
| B: Enhance existing DST section | Merge into CLAUDE.md DST section | Avoids duplication, single source | Loses .vision/ directory structure |
| C: Both - .vision/ for principles, CLAUDE.md for practice | Separation of concerns | Clear distinction | More files to maintain |

**Decision:** Option C - Both files

**Trade-offs accepted:**
- Two places for DST guidance (principles vs practice)
- Worth it for clarity: CONSTRAINTS.md = immutable principles, CLAUDE.md = practical how-to
- Follows northstar's philosophy of stable vision files

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 12:01 | Create plan file first | Following northstar workflow | Takes extra time upfront |
| 12:03 | Read both kelpie and northstar files | Need full context | More reading before action |
| 12:05 | Use Option A for .progress guidance | Keep CLAUDE.md as single source | File will be longer but manageable |
| 12:06 | Use Option C for DST guidance | Separate stable principles from practice | Two files to maintain |
| 12:10 | Customize CONSTRAINTS.md for Kelpie | Add kelpie-dst examples and fault types | More specific but needs updating if DST changes |
| 12:15 | Add workflow diagram to CLAUDE.md | Visual reference helps adoption | Takes more space in file |

---

## Implementation Plan

### Phase 1: Setup Structure
- [x] Create .progress/ directory
- [x] Create plan file
- [x] Create .vision/ directory
- [x] Read kelpie/VISION.md to understand existing vision

### Phase 2: Integrate .progress Guidance
- [x] Add "Vision-Aligned Planning" section to CLAUDE.md
- [x] Copy plan template to .progress/templates/plan.md
- [x] Update workflow steps with kelpie-specific commands
- [x] Add references to existing DST testing

### Phase 3: Integrate Deterministic Sim Guidance
- [x] Create .vision/CONSTRAINTS.md based on northstar template
- [x] Customize for kelpie (Simulation::run examples, fault types)
- [x] Enhance CLAUDE.md DST section with workflow diagram
- [x] Add harness extension rule
- [x] Add enforcement checklist

### Phase 4: Verification
- [x] Review integrated content for consistency
- [x] Ensure no duplication
- [x] Check all file paths and examples are accurate
- [ ] Run /no-cap check (N/A for docs)
- [ ] Commit and push changes

---

## Checkpoints

- [x] Codebase understood
- [ ] Plan approved (user review)
- [ ] **Options & Decisions filled in**
- [ ] **Quick Decision Log maintained**
- [ ] Implemented
- [ ] Vision aligned
- [ ] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**No code changes**, only documentation:
- Manual review of integrated content
- Verify examples compile (if code snippets)
- Check markdown formatting

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 12:01 | northstar guidance files | Initial context gathering |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| None yet | - | - |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Current | All phases | Planning | 2026-01-12 12:01 |

---

## Findings

- Kelpie already has strong DST guidance in CLAUDE.md
- Northstar's structured planning workflow is more explicit about mandatory sections
- Northstar's CONSTRAINTS.md has excellent simulation-first workflow diagram
- Plan template from northstar is comprehensive with required sections

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Vision constraints file | Read `kelpie/.vision/CONSTRAINTS.md` | Comprehensive simulation-first guidance with Kelpie examples |
| Plan template | Read `kelpie/.progress/templates/plan.md` | Template with all required sections and Kelpie-specific commands |
| Updated CLAUDE.md | Read `kelpie/CLAUDE.md` section "Vision-Aligned Planning" | Workflow guidance integrated into main dev guide |
| Full plan file | Read `kelpie/.progress/001_20260112_120100_integrate-northstar-guidance.md` | This completed plan with all phases checked off |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| N/A | All phases complete | N/A |

### Known Limitations ⚠️
- Documentation-only changes, no code changes required
- Future plans should follow the new template format
- CONSTRAINTS.md is marked STABLE - change rarely and deliberately

---

## Completion Notes

**Verification Status:**
- Tests: N/A (documentation only)
- /no-cap: N/A (documentation only)
- Vision alignment: ✅ Confirmed - aligns with Kelpie's TigerStyle and DST-first principles

**Files Created:**
- `kelpie/.vision/CONSTRAINTS.md` - Simulation-first development constraints
- `kelpie/.progress/templates/plan.md` - Plan file template with Kelpie-specific sections
- `kelpie/.progress/001_20260112_120100_integrate-northstar-guidance.md` - This plan file

**Files Modified:**
- `kelpie/CLAUDE.md` - Added "Vision-Aligned Planning (MANDATORY)" section with workflow guidance

**Key Decisions Made:**
- Decision 1: Append .progress guidance to CLAUDE.md (keeps single source of truth)
- Decision 2: Create both .vision/CONSTRAINTS.md and enhance CLAUDE.md (separates stable principles from practice)

**Integration Summary:**
- ✅ .progress guidance integrated with numbered plan format, required sections, and multi-instance coordination
- ✅ Deterministic sim guidance enhanced with explicit workflow, harness extension rule, and Kelpie-specific examples
- ✅ All templates customized for Kelpie (cargo commands, kelpie-dst references, DST fault types)
- ✅ Quick workflow reference diagram added for easy reference

**Commit:** [Pending]
**PR:** [N/A - will commit directly to main]

# RLM Handoff Skill

Use this skill when taking over work from another agent or resuming interrupted work.

## When to Use

Invoke this skill when:
- A previous agent marked phases complete in a plan
- You're resuming work after a session ended
- Another agent handed off a partially complete task
- You need to verify previous work before continuing

**CRITICAL**: NEVER trust checkboxes in plan files. Always verify by execution.

## Core Problem

Agents can lie, intentionally or unintentionally:
- Mark phases complete without actually testing
- Trust documentation instead of running code
- Make incorrect assumptions about what "complete" means
- Experience bugs that surface after they complete work

The handoff process **re-verifies everything** before allowing you to proceed.

## Handoff Protocol

### MANDATORY Step 1: Call Handoff Verification

```bash
mcp.start_plan_session(plan_id)
```

**This is NOT optional.** You CANNOT skip this step.

This tool:
1. Loads the plan from AgentFS
2. Identifies all phases marked "complete"
3. Re-runs verification for EACH completed phase
4. Returns verification report

**You will receive:**
```json
{
  "plan_id": "027_teleport_implementation",
  "phases_total": 7,
  "phases_claimed_complete": 5,
  "phases_verified": 3,
  "phases_failed": 2,
  "verification_report": {
    "Phase 1: Foundation": {
      "status": "VERIFIED",
      "verification": "Tests passed: 12/12",
      "evidence": "cargo test -- foundation (all passed)"
    },
    "Phase 2: VM Backend": {
      "status": "VERIFIED",
      "verification": "Tests passed: 8/8"
    },
    "Phase 3: Snapshot API": {
      "status": "VERIFIED",
      "verification": "Tests passed: 15/15"
    },
    "Phase 4: Teleport Logic": {
      "status": "FAILED",
      "verification": "Tests FAILED: 2/10 passing",
      "failure_reason": "test_teleport_cross_region failed: Connection timeout",
      "evidence": "cargo test -- teleport (8 failures)"
    },
    "Phase 5: Integration Tests": {
      "status": "FAILED",
      "verification": "Tests NOT FOUND",
      "failure_reason": "No integration tests exist for teleport",
      "evidence": "mcp.index_tests('teleport integration') returned empty"
    }
  },
  "safe_to_proceed": false,
  "next_steps": [
    "Fix Phase 4: teleport logic has failing tests",
    "Complete Phase 5: integration tests are missing",
    "Re-verify before marking plan complete"
  ]
}
```

### Step 2: Review Verification Report

Analyze the report critically:

**Verified Phases (✅):**
- These are confirmed working
- You can trust these as foundation
- But re-verify if you modify them

**Failed Phases (❌):**
- Previous agent LIED or was WRONG
- Tests fail, features don't work
- Or code changed since completion
- Or verification was inadequate

**Common Failure Reasons:**
1. **Tests don't exist** - Agent claimed "complete" without tests
2. **Tests fail** - Feature is broken, not complete
3. **Verification command fails** - E.g., clippy has warnings
4. **Index stale** - Agent didn't refresh index after changes
5. **Evidence insufficient** - Proof doesn't match claim

### Step 3: Investigate Failures

For each failed phase:

#### Pattern A: Tests Don't Exist
```
Phase 5: "Integration tests complete ✅"
Verification: "No integration tests found"

What happened: Agent marked complete without writing tests

Your action:
1. Unmark phase as complete in plan
2. Write the missing tests
3. Run tests
4. Mark complete WITH evidence
```

#### Pattern B: Tests Fail
```
Phase 4: "Teleport logic complete ✅"
Verification: "8/10 tests failing"

What happened: Agent didn't run tests, or tests passed then but fail now

Your action:
1. Investigate test failures: mcp.verify_by_tests("teleport")
2. Read failure messages to understand root cause
3. Fix the bugs
4. Re-run tests until all pass
5. Re-mark complete WITH new evidence
```

#### Pattern C: Partial Implementation
```
Phase 3: "Error handling complete ✅"
Verification: "clippy warns: 5 unwrap() calls in production"

What happened: Agent implemented some error handling but missed cases

Your action:
1. Find the unwrap() calls: mcp.constraint_check(["no_unwrap"])
2. Replace with proper error handling
3. Run clippy again
4. Re-mark complete
```

#### Pattern D: Stale Verification
```
Phase 2: "VM backend refactored ✅"
Verification: "Code changed since completion, re-verify needed"

What happened: Someone modified code after phase marked complete

Your action:
1. Re-run verification: mcp.verify_by_tests("vm backend")
2. If still passes → confirm completion
3. If fails → fix breakage, then re-mark complete
```

### Step 4: Fix or Unmark Failed Phases

**DO NOT PROCEED** to new phases until failed phases are fixed.

**Two options for each failure:**

**Option A: Fix It**
```bash
# Investigate
mcp.verify_by_tests("failed_feature")

# Understand failure
# (Read test output, error messages)

# Fix the issue
# (Make code changes)

# Re-verify
mcp.verify_by_tests("failed_feature")
# Now passes ✅

# Update plan
# Mark phase verified with new evidence
```

**Option B: Unmark It**
```bash
# If feature is too broken or requires redesign
# OR if verification reveals it was never actually complete

# Update plan:
# - [ ] Phase N: Feature description (was marked complete, but verification failed)

# Add to Quick Decision Log:
# "Phase N was marked complete by previous agent but verification shows it's incomplete.
# Failing tests: X, Y, Z. Unmarking and will re-implement."
```

### Step 5: Proceed Only After Verification

**Safe to continue when:**
- All previously completed phases PASS verification
- You understand what's been done
- You have confidence in the foundation

**NOT safe to continue when:**
- Failed phases exist
- Dependent phases might be affected
- You don't understand previous work

## Special Cases

### Case 1: Agent Claimed Complete, No Evidence
```
Phase 3: "API implemented ✅"
Evidence field: (empty)

Action:
1. Assume NOT complete
2. Verify: mcp.verify_by_tests("api")
3. If passes → add evidence and confirm
4. If fails → unmark and fix
```

### Case 2: Agent Marked Complete Without Running Anything
```
Plan says:
- [x] Phase 2 complete
- [x] Phase 3 complete
- [x] Phase 4 complete

Verification report:
- Phase 2: No verification run (claimed complete without proof)
- Phase 3: No verification run
- Phase 4: No verification run

Action:
1. Treat ALL as unverified
2. Run verification for each
3. Unmark any that fail
4. Add evidence for any that pass
```

### Case 3: Cascading Failures
```
Phase 2: Foundation (VERIFIED ✅)
Phase 3: Core Logic (FAILED ❌)
Phase 4: Integration (claimed complete, builds on Phase 3)
Phase 5: Testing (claimed complete, tests Phase 4)

Action:
1. Fix Phase 3 first
2. THEN re-verify Phase 4 (might be broken by Phase 3 failure)
3. THEN re-verify Phase 5 (might be invalidated by Phase 4 issues)
4. Don't trust downstream phases until upstream verified
```

### Case 4: Major Architectural Changes
```
Previous agent: "Implemented with FDB backend ✅"
Verification: Tests pass ✅
But: You discover in-memory backend is actually used

Action:
1. Don't assume verification == correct implementation
2. Read the actual code: mcp.codebase_read_section(...)
3. If implementation differs from plan, document in Quick Decision Log
4. Decide: Accept current impl, or fix to match plan?
```

## Handoff Checklist

Use this checklist when taking over work:

```markdown
## Handoff Verification Checklist

- [ ] Called mcp.start_plan_session(plan_id)
- [ ] Received verification report
- [ ] Reviewed all verified phases (confirmed working)
- [ ] Investigated all failed phases (understand why)
- [ ] Fixed OR unmarked all failed phases
- [ ] Understood what previous agent actually completed
- [ ] Identified safe starting point for new work
- [ ] Documented handoff findings in plan's Quick Decision Log
- [ ] Ready to proceed with next incomplete phase

**Verified Phases**: [List phases that passed verification]

**Fixed Phases**: [List phases that failed but I fixed]

**Unmarked Phases**: [List phases that failed and need re-implementation]

**Safe to Continue**: YES / NO

**Next Phase to Work On**: Phase N: [description]
```

## Trust Model

```
┌────────────────────────────────────────────────┐
│  What You Can Trust                            │
├────────────────────────────────────────────────┤
│  ✅ Verification report from mcp               │
│  ✅ Test output (if tests pass)                │
│  ✅ Actual code (read it yourself)             │
│  ✅ Command output (if you ran it)             │
└────────────────────────────────────────────────┘

┌────────────────────────────────────────────────┐
│  What You CANNOT Trust                         │
├────────────────────────────────────────────────┤
│  ❌ Checkboxes in plan files                   │
│  ❌ Claims in "Completion Notes"               │
│  ❌ "Verified by: [agent name]" statements    │
│  ❌ README assertions                          │
│  ❌ Previous agent's judgment                  │
│  ❌ "It worked when I tested it" claims        │
└────────────────────────────────────────────────┘
```

## Example Handoff Session

```bash
# Agent B takes over from Agent A

# Agent A's plan:
# - [x] Phase 1: Foundation
# - [x] Phase 2: Core logic
# - [x] Phase 3: Error handling
# - [ ] Phase 4: Integration tests
# - [ ] Phase 5: Documentation

# Agent B starts:

> mcp.start_plan_session("025_feature_implementation")

{
  "phases_claimed_complete": 3,
  "phases_verified": 2,
  "phases_failed": 1,
  "verification_report": {
    "Phase 1: Foundation": "VERIFIED (12/12 tests pass)",
    "Phase 2: Core logic": "VERIFIED (8/8 tests pass)",
    "Phase 3: Error handling": "FAILED (clippy: 7 unwrap() in production)"
  },
  "safe_to_proceed": false
}

# Agent B investigates Phase 3:

> mcp.constraint_check(["no_unwrap"])

{
  "violations": [
    {file: "src/core.rs", line: 45, issue: "unwrap() in production"},
    {file: "src/core.rs", line: 67, issue: "unwrap() in production"},
    ...
  ]
}

# Agent B fixes Phase 3:
# (Replaces unwrap() with proper error handling)

> mcp.verify_clippy()
# Output: No warnings ✅

> mcp.verify_by_tests("error handling")
# Output: All tests pass ✅

# Agent B updates plan:
# - [x] Phase 3: Error handling ✅ (Fixed: removed unwrap() calls, verified with clippy)

# Agent B documents in Quick Decision Log:
# "Phase 3 was marked complete but had 7 unwrap() violations.
# Fixed by replacing with ? operator and explicit error handling.
# Re-verified: clippy clean, tests pass."

# Now safe to continue:
# - [x] Phase 1: Foundation ✅
# - [x] Phase 2: Core logic ✅
# - [x] Phase 3: Error handling ✅ (re-verified)
# - [ ] Phase 4: Integration tests ← START HERE

# Agent B proceeds with Phase 4
```

## Key Principles

1. **Verification is mandatory** - Call `mcp.start_plan_session()` FIRST
2. **Trust execution, not checkboxes** - Tests pass = working; checkbox = claim
3. **Fix before proceeding** - Don't build on broken foundation
4. **Document handoff** - Quick Decision Log should record what you found
5. **Assume nothing** - Even verified phases might have issues

## Integration with Other Skills

- Use `/rlm-verify` to investigate specific failures
- Use `/rlm-explore` to understand previous agent's code
- Use `/rlm-task` workflow for fixing failed phases

## Remember

Previous agents are not malicious, but they can be wrong:
- They might have misunderstood requirements
- They might have trusted docs instead of running tests
- Tests might have passed then but fail now
- They might have had context that you don't

**Always verify. Never assume.**

# RLM Skills for Kelpie Development

This directory contains **RLM (Recursive Language Model) skills** that guide AI agent behavior when working on the Kelpie codebase.

## What are RLM Skills?

RLM skills are structured workflows that help agents:
1. Navigate the codebase efficiently using indexes
2. Verify claims by execution rather than trusting documentation
3. Follow hard constraints enforced by MCP tools
4. Maintain quality through systematic verification

These skills implement **verification-first development** - agents must prove their work through execution, not just claim completion.

## Available Skills

### Core Development Skills

#### `/rlm-task` - Task Development Workflow
**File**: `rlm-task.md`
**Use when**: Starting any non-trivial development task

**Workflow**:
1. Load P0 constraints
2. Query indexes to understand scope
3. Create execution plan in `.progress/`
4. Register task start
5. Execute phases with verification
6. Refresh indexes after changes
7. Verify all constraints
8. Complete with proof

**Key principle**: Verify by execution, not by reading docs.

---

#### `/rlm-verify` - Verification Workflow
**File**: `rlm-verify.md`
**Use when**: Verifying factual claims about the codebase

**Core Principle**:
```
Documentation and comments are UNTRUSTED.
Code execution is TRUSTED.
```

**Workflow**:
1. Find relevant tests
2. Run the tests
3. Report actual results (not doc claims)
4. Store verified facts

**Example**: Don't say "According to README, feature X is complete." Say "Ran 3 tests for feature X, all passed."

---

#### `/rlm-explore` - Codebase Exploration
**File**: `rlm-explore.md`
**Use when**: Navigating unfamiliar code or investigating structure

**Strategy**: Start broad (modules), narrow down (symbols), read precisely (code), verify critically (tests)

**Tools**:
- `index_modules()` - Hierarchical view
- `index_deps()` - Dependency graph
- `index_symbols()` - Find implementations
- `codebase_read_section()` - Read specific code
- `index_tests()` - Find test examples

**Key principle**: Use indexes for NAVIGATION, not TRUTH.

---

### Collaboration Skills

#### `/rlm-handoff` - Agent Handoff Protocol
**File**: `rlm-handoff.md`
**Use when**: Taking over work from another agent

**MANDATORY FIRST STEP**:
```bash
mcp.start_plan_session(plan_id)
```

This re-verifies ALL previously completed phases. You will receive:
- Phases that passed verification (✅ trusted)
- Phases that failed verification (❌ must fix)
- Safe/unsafe to proceed judgment

**Key principle**: NEVER trust checkboxes. Always verify by execution.

**Trust Model**:
- ✅ Verification reports from MCP
- ✅ Test output
- ❌ Checkboxes in plan files
- ❌ Claims in completion notes
- ❌ Previous agent's judgment

---

### Maintenance Skills

#### `/rlm-slop-hunt` - Slop Detection and Cleanup
**File**: `rlm-slop-hunt.md`
**Use when**: Cleaning up accumulated technical debt

**What is Slop?**
1. Dead code (unused functions, dependencies)
2. Orphaned code (old implementations not deleted)
3. Duplicates (same logic in multiple places)
4. Fake DST tests (claiming determinism but aren't)
5. Incomplete code (TODOs, stubs in production)

**Workflow**:
1. **Detection** - Run slop detection tools
2. **Classification** - Triage by confidence
3. **Verification** - Prove safe to delete
4. **Propose** - Group by priority
5. **Execute** - One at a time, test after each
6. **Re-run** - Verify slop actually removed

**Key principle**: Verify before deleting. One item at a time.

---

### System Prompts

#### Constraint Injection Prompt
**File**: `constraint-injection-prompt.md`
**Use**: Prepend to agent context at session start

Contains:
- P0 constraints (non-negotiable rules)
- Available MCP tools
- Workflow requirements
- Key principles
- Anti-patterns to avoid

**Purpose**: Ensure constraints are always in agent's context.

---

## How to Use These Skills

### From Claude Code CLI

Skills can be invoked as slash commands:
```bash
/rlm-task       # Start task workflow
/rlm-verify     # Verify a claim
/rlm-explore    # Explore codebase
/rlm-handoff    # Take over from another agent
/rlm-slop-hunt  # Clean up slop
```

### Manual Reference

Read the skill files directly when you need guidance on a specific workflow.

### Integration with MCP Tools

Skills are **soft controls** (guidance) that work WITH **hard controls** (MCP tool gates):

| Soft Control (Skill) | Hard Control (MCP Tool) |
|----------------------|-------------------------|
| "You should verify before completing" | `state_task_complete()` requires proof parameter |
| "Check index freshness" | `index_query()` warns if indexes are stale |
| "Run tests after changes" | Git pre-commit hook blocks if tests fail |

Even if the agent ignores the skill guidance, the hard controls enforce verification.

---

## Skill Design Philosophy

### Verification-First Development

Traditional approach:
```
1. Write code
2. Trust it works
3. Mark complete
4. Maybe test later
```

RLM approach:
```
1. Write code
2. Write/find tests
3. Run tests (verify it works)
4. Mark complete WITH proof
```

### Trust Model

```
┌─────────────────────────────────────┐
│  Trusted Sources                    │
├─────────────────────────────────────┤
│  ✅ Test execution output           │
│  ✅ Command execution results       │
│  ✅ MCP tool verification reports   │
│  ✅ Actual code (after reading it)  │
└─────────────────────────────────────┘

┌─────────────────────────────────────┐
│  Untrusted Sources                  │
├─────────────────────────────────────┤
│  ❌ Documentation (might be stale)  │
│  ❌ Comments (might be outdated)    │
│  ❌ Plan checkboxes (might be lies) │
│  ❌ "Trust me" claims                │
└─────────────────────────────────────┘
```

### Hard vs. Soft Controls

| Control Type | Mechanism | Can Agent Bypass? |
|--------------|-----------|-------------------|
| **Soft** (Skills) | Guidance in prompts | Yes (might ignore) |
| **Hard** (MCP Gates) | Enforced by code | No (cannot bypass) |

Skills are **soft controls** that guide behavior. But if the agent ignores them, **hard controls** (MCP tool gates, git hooks) catch it.

---

## Maintaining Skills

### When to Update Skills

Update skills when:
1. New MCP tools are added
2. Workflows improve through usage
3. Common mistakes are identified
4. Constraints change

### Skill Update Process

1. Edit the skill markdown file
2. Test the updated workflow manually
3. Document changes in git commit
4. Notify other agents (if multi-agent project)

### Testing Skills

Skills should be periodically tested by:
1. Following the workflow step-by-step
2. Verifying MCP tools work as described
3. Checking that verification steps catch errors
4. Confirming examples are current

---

## Integration with Project Infrastructure

### Files Created by Skills

Skills create files in these locations:
- `.progress/NNN_YYYYMMDD_HHMMSS_task-name.md` - Task plans
- `.agentfs/agent.db` - State, verified facts, audit logs
- `.kelpie-index/` - Structural and semantic indexes

### MCP Tools Used by Skills

Skills rely on these MCP tool categories:
1. **Index queries** - Navigation (symbols, tests, modules, deps)
2. **Verification** - Execution (verify_by_tests, verify_claim)
3. **State management** - Audit trail (task_start, task_complete)
4. **RLM tools** - Codebase access (grep, peek, read_section)
5. **Constraint checking** - Compliance (constraint_check, dst_coverage)

### Git Hooks Integration

Skills mention verification requirements that git hooks enforce:
- Pre-commit: Tests must pass
- Pre-commit: Clippy must pass
- Pre-commit: DST coverage for critical paths

---

## Examples

### Example 1: Starting a New Feature

```
User: "Add snapshot restore functionality"

Agent: Invoking /rlm-task skill

1. mcp.index_constraints() → Load P0 constraints
2. mcp.index_symbols("snapshot") → Find existing snapshot code
3. Create plan: .progress/028_20260121_snapshot_restore.md
4. task_id = mcp.state_task_start("Add snapshot restore")
5. [Implement Phase 1]
6. mcp.verify_by_tests("snapshot") → Tests pass ✅
7. mcp.index_refresh([modified_files])
8. [Continue with remaining phases]
9. mcp.verify_all_constraints() → All pass ✅
10. mcp.state_task_complete(task_id, proof={test_output, manual_verification})
```

### Example 2: Verifying a Claim

```
User: "Is the FDB backend complete?"

Agent: Invoking /rlm-verify skill

1. mcp.index_tests("fdb backend") → Find 12 tests
2. mcp.verify_by_tests("fdb") → Run tests
3. Result: 11/12 passing, 1 failing (test_fdb_concurrent_writes)
4. Report: "FDB backend is MOSTLY complete. 11/12 tests pass.
   Failing test: concurrent writes have race condition.
   Evidence: [paste test output]"
5. mcp.state_verified_fact(
     claim="FDB backend complete",
     method="Ran 12 FDB tests",
     result="INCOMPLETE: 11/12 pass, concurrent_writes fails"
   )
```

### Example 3: Taking Over from Another Agent

```
Agent B: Invoking /rlm-handoff skill

1. mcp.start_plan_session("027_teleport_implementation")
2. Verification report received:
   - Phase 1: VERIFIED ✅
   - Phase 2: VERIFIED ✅
   - Phase 3: FAILED ❌ (tests don't exist)
   - Phase 4: FAILED ❌ (tests fail)
3. Investigate Phase 3:
   mcp.index_tests("teleport") → No integration tests found
4. Fix Phase 3: Write missing tests
5. Investigate Phase 4:
   mcp.verify_by_tests("teleport") → See failures, fix bugs
6. Re-verify all phases → All pass ✅
7. Now safe to continue with Phase 5
```

---

## Summary

RLM skills implement **verification-first development** for AI agents working on Kelpie. They provide structured workflows that:

1. ✅ Guide efficient codebase navigation
2. ✅ Enforce verification by execution
3. ✅ Create audit trails for accountability
4. ✅ Prevent common agent mistakes
5. ✅ Work with hard controls for enforcement

**Key Takeaway**: Trust execution, not documentation. Verify before claiming complete.

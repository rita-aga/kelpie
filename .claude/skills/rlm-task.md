# RLM Task Skill

Use this skill when starting any development task in the Kelpie codebase.

## When to Use

This skill should be invoked at the start of ANY non-trivial task:
- Multi-step implementation
- Bug fixes requiring exploration
- Feature additions
- Refactoring work

## Workflow

When starting a task, follow this sequence:

### 1. Load Constraints
```
mcp.index_constraints()
```
- Injects P0 constraints into your reasoning
- These are NON-NEGOTIABLE rules that MUST be followed
- Examples: "No unwrap() in production", "All sizes must use u64", "2+ assertions per function"

### 2. Understand Scope
```
mcp.index_query(pattern)
```
- Query structural indexes to understand what exists
- Use `index_symbols()`, `index_modules()`, `index_deps()` to map dependencies
- Build a mental model of the codebase BEFORE making changes

### 3. Create Execution Plan
Create a numbered plan file in `.progress/NNN_YYYYMMDD_HHMMSS_task-name.md`:
- List explicit read/write/new file lists
- Break into phases with clear verification steps
- Include "Options & Decisions" section with 2-3 alternatives considered
- Add "Quick Decision Log" for tracking choices

### 4. Register Task Start
```
mcp.state_task_start(description)
```
- Logs task start with timestamp and description
- Returns task_id for tracking
- Creates audit trail

### 5. Execute Each Phase
For each phase in your plan:
- **Verify by execution, NOT by reading docs**
- Use `mcp.verify_by_tests()` to confirm behavior
- Use `mcp.verify_claim()` for command-based verification
- Update plan file after each phase completion

### 6. Refresh Indexes After Changes
```
mcp.index_refresh(changed_files)
```
- Keep indexes fresh after file modifications
- Ensures subsequent queries see updated state
- Required before marking task complete

### 7. Final Constraint Verification
```
mcp.verify_all_constraints()
```
- Runs ALL hard constraint checks
- Must pass before task completion
- Examples: cargo test, cargo clippy, no TODOs in production code

### 8. Complete Task
```
mcp.state_task_complete(task_id, proof)
```
- Requires PROOF of completion (not just a claim)
- Proof examples:
  - Test output showing all tests passing
  - Command output demonstrating feature works
  - Evidence of verification execution
- Cannot be bypassed - this is a HARD control

## Key Principles

1. **Never trust MD files** - Always verify claims by execution
2. **Indexes are tools, not truth** - Use for navigation, verify for facts
3. **Hard controls enforce behavior** - Tools like `state_task_complete` require proof
4. **Constraints are non-negotiable** - P0 constraints MUST be followed
5. **Verification before completion** - Run tests, not "looks good to me"

## Example Flow

```bash
# 1. Start task
task_id=$(mcp.state_task_start("Add FDB snapshot support"))

# 2. Load constraints
mcp.index_constraints() # → See "No unwrap() in production"

# 3. Query scope
mcp.index_symbols("snapshot") # → Find existing snapshot code
mcp.index_deps("kelpie-storage") # → Understand dependencies

# 4. Create plan
# Write to .progress/027_20260121_100000_fdb-snapshot-support.md

# 5. Execute phase 1
# ... make changes ...

# 6. Verify phase 1
mcp.verify_by_tests("snapshot") # → Run snapshot tests
# Tests pass ✅

# 7. Update indexes
mcp.index_refresh(["crates/kelpie-storage/src/fdb.rs"])

# 8. Execute remaining phases
# ... continue ...

# 9. Final verification
mcp.verify_all_constraints() # → cargo test, clippy, etc.
# All pass ✅

# 10. Complete
mcp.state_task_complete(task_id, proof={
  test_output: "All 156 tests passed",
  clippy_output: "No warnings",
  manual_verification: "Created snapshot, restored successfully"
})
```

## Anti-Patterns to Avoid

❌ **Don't skip verification**
```
# Phase 3 complete [x] (I checked and it looks good)
```

✅ **Do verify by execution**
```
# Phase 3 complete [x]
# Verification: cargo test -- snapshot_lifecycle
# Output: test snapshot_lifecycle ... ok
```

❌ **Don't trust stale indexes**
```
# Index shows no usages, safe to delete
```

✅ **Do refresh and re-query**
```
mcp.index_refresh([modified_files])
mcp.index_symbols("deleted_function") # → Verify no references
```

❌ **Don't bypass hard controls**
```
# Feature complete, skipping tests because they're slow
```

✅ **Do complete the verification**
```
mcp.verify_all_constraints() # → Run ALL tests, required for completion
```

## Integration with Hard Controls

This skill works WITH the hard control layer:
- **Soft control (this skill)**: Guides you to follow best practices
- **Hard control (MCP tools)**: Enforces verification requirements

Even if you forget to verify, the hard controls will catch it:
- `state_task_complete` requires proof
- `index_query` warns if indexes are stale
- Git hooks block commits if tests fail

## See Also

- `/rlm-verify` - For verification-specific workflows
- `/rlm-explore` - For codebase exploration patterns
- `/rlm-handoff` - For taking over from another agent

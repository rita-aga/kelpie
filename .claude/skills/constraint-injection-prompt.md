# Constraint Injection Prompt

This prompt should be prepended to agent context when working on Kelpie codebase tasks.

## System Prompt Prefix

```markdown
You are working on the Kelpie codebase, a distributed virtual actor system with linearizability guarantees.

## CRITICAL P0 CONSTRAINTS

These constraints are **NON-NEGOTIABLE** and MUST be followed in all code:

### Safety Constraints (Cannot Violate)

1. **No unwrap() in production code** (tests OK)
   - Use `?` operator or explicit error handling
   - Rationale: Prevents panics in production
   - Verification: `cargo clippy` catches most violations

2. **All sizes must use u64, not usize**
   - Rationale: Cross-platform portability
   - Example: `fn size_bytes(&self) -> u64` not `-> usize`
   - Verification: Code review

3. **Explicit constants with units in name**
   - Example: `TIMEOUT_MS: u64 = 5000` not `TIMEOUT: u64 = 5000`
   - Rationale: Prevents unit confusion bugs
   - Verification: Code review

4. **Functions must have 2+ assertions (preconditions + postconditions)**
   - Rationale: TigerStyle safety principle
   - Example:
     ```rust
     fn set_timeout(&mut self, timeout_ms: u64) {
         assert!(timeout_ms > 0);  // precondition
         assert!(timeout_ms <= MAX_TIMEOUT_MS);  // precondition

         self.timeout_ms = timeout_ms;

         assert!(self.timeout_ms > 0);  // postcondition
     }
     ```
   - Verification: Code review

5. **No silent error swallowing**
   - Using `.ok()` without logging is FORBIDDEN
   - Using `.unwrap()` without prior validation is FORBIDDEN
   - All errors must be:
     - Returned (using `?`)
     - Logged (using `error!()` or equivalent)
     - Or explicitly documented why safe to ignore
   - Verification: `cargo clippy`, manual review

6. **DST tests for all critical paths**
   - Critical paths = actor lifecycle, state persistence, cross-actor calls, failure recovery
   - DST test must use `Simulation` harness or `SimStorage`/`SimClock`/`DeterministicRng`
   - Rationale: Verify correctness under faults
   - Verification: Check `*_dst.rs` test files exist

### Verification Constraints

7. **Verify by execution, NOT by reading docs**
   - Never claim "feature X is complete" based on README
   - Always run tests to verify behavior
   - Use MCP tools: `mcp.verify_by_tests()`, `mcp.verify_claim()`

8. **Tests must pass before committing**
   - Run `cargo test` before EVERY commit
   - Run `cargo clippy` before EVERY commit
   - Run `cargo fmt --check` before EVERY commit
   - Rationale: Every commit is a potential rollback point

9. **No placeholders in production code**
   - Functions must have real implementations, not stubs
   - No `// TODO: implement this` in production paths
   - No `unimplemented!()` in production code
   - Tests can have placeholders while developing

10. **Evidence required for completion claims**
    - When marking task complete, provide:
      - Test output showing tests pass
      - Command output demonstrating feature works
      - Manual verification steps and results
    - Use `mcp.state_task_complete(task_id, proof)` with actual proof

## VERIFICATION TOOLS AVAILABLE

You have access to these MCP tools for verification:

### Index Queries (Navigation)
- `mcp.index_symbols(pattern, kind?)` - Find symbols matching pattern
- `mcp.index_tests(topic?, type?)` - Find tests related to topic
- `mcp.index_modules(crate?)` - Get module hierarchy
- `mcp.index_deps(crate?)` - Get dependency graph
- `mcp.index_status()` - Check index freshness

### Verification (Truth)
- `mcp.verify_by_tests(topic, type?)` - Find and run relevant tests
- `mcp.verify_claim(claim, method)` - Verify by running command
- `mcp.verify_all_tests(release?)` - Run full test suite
- `mcp.verify_clippy()` - Run clippy linter

### State Management (Audit Trail)
- `mcp.state_task_start(description)` - Start task with logging
- `mcp.state_task_complete(task_id, proof)` - Complete with evidence (HARD: requires proof)
- `mcp.state_verified_fact(claim, method, result)` - Record verified facts

### RLM Tools (Codebase Access)
- `mcp.rlm_execute(code)` - Execute Python code with codebase context
- `mcp.codebase_grep(pattern, file_pattern?, max_results?)` - Search code
- `mcp.codebase_peek(file_path, line, context?)` - Read lines around line number
- `mcp.codebase_read_section(file_path, symbol)` - Read specific function/struct

### Constraint Checking
- `mcp.constraint_check(check_types?)` - Run constraint checks
- `mcp.constraint_list()` - List all constraints

### DST Tools
- `mcp.dst_coverage_check(critical_paths?)` - Verify DST coverage
- `mcp.harness_check(fault_types?)` - Verify harness supports fault types

## WORKFLOW REQUIREMENTS

### When Starting a Task
1. Call `mcp.index_constraints()` to load P0 constraints
2. Call `mcp.index_query()` to understand existing code
3. Create plan in `.progress/NNN_YYYYMMDD_HHMMSS_task-name.md`
4. Register: `task_id = mcp.state_task_start(description)`

### During Implementation
1. Follow TigerStyle principles (safety > performance > DX)
2. Write tests FIRST (TDD when possible)
3. Use indexes for navigation, tests for verification
4. Update plan after each phase

### Before Completion
1. Run `mcp.verify_all_constraints()` - must pass
2. Run `mcp.verify_by_tests(topic)` - verify feature works
3. Check DST coverage: `mcp.dst_coverage_check()`
4. Complete: `mcp.state_task_complete(task_id, proof)` with evidence

### When Uncertain
1. **Don't guess** - Use `mcp.verify_by_tests()` to check
2. **Don't trust docs** - Run tests to see actual behavior
3. **Don't assume** - Query indexes to find actual code
4. **Ask for help** - If verification reveals unknowns, ask user

## KEY PRINCIPLES

1. **Hard controls enforce behavior** - MCP tools require evidence, not claims
2. **Verification before completion** - Run tests, don't "looks good to me"
3. **Indexes are navigation** - Use them to FIND code, not TRUST claims
4. **Tests are truth** - If tests pass, feature works; if fail, broken
5. **Constraints are non-negotiable** - P0 constraints MUST be followed

## ANTI-PATTERNS TO AVOID

❌ "According to the README, feature X is complete"
✅ "Ran tests for feature X (3 tests passed), verified working"

❌ "Phase 3 complete [x] (looks good)"
✅ "Phase 3 complete [x] (verified: cargo test passed, clippy clean)"

❌ "I'll add error handling later"
✅ "Adding error handling now (P0 constraint: no unwrap in production)"

❌ "Tests are slow, skipping for now"
✅ "Running tests before completion (P0 constraint: tests must pass)"

---

**Remember**: You are building safety-critical infrastructure. Every shortcut, every "TODO later", every untested claim creates technical debt and potential bugs. Build it right the first time using verification-first development.
```

## How to Use This Prompt

### Option 1: Prepend to System Instructions
When starting a Kelpie task, prepend this to the system prompt to inject constraints into the agent's context.

### Option 2: Reference in Skills
Skills like `/rlm-task` should reference this prompt:
```
"Reminder: Review constraint-injection-prompt.md for P0 constraints"
```

### Option 3: Dynamic Injection via MCP
The `mcp.index_constraints()` tool should return this content dynamically, ensuring constraints are always fresh.

## Benefits

1. **Always in context** - Agent can't forget constraints
2. **Tool integration** - Links constraints to verification tools
3. **Concrete examples** - Shows how to follow constraints
4. **Anti-patterns** - Teaches what NOT to do
5. **Enforcement layer** - Reminds agent that hard controls exist

## Maintenance

When adding new constraints:
1. Add to this file under appropriate category
2. Add verification method (how to check compliance)
3. Add examples and anti-patterns
4. Update MCP tool `mcp.constraint_list()` to return new constraint
5. Consider: Does this need a hard control (MCP gate) or soft control (guidance)?

# RLM Verify Skill

Use this skill when asked to verify factual claims about the codebase.

## When to Use

Invoke this skill whenever you need to answer questions like:
- "Is feature X implemented?"
- "Does the code handle error case Y?"
- "Are there tests for Z?"
- "Is constraint P followed?"

**CRITICAL**: NEVER trust documentation, comments, or plan files for factual claims. Always verify by execution.

## Core Principle

```
Documentation and comments are UNTRUSTED.
Code execution is TRUSTED.
```

Even if a README says "Feature X is complete", verify it by:
1. Finding the relevant tests
2. Running those tests
3. Observing the actual behavior

## Workflow

### 1. Find Relevant Tests
```
mcp.index_tests(topic, type?)
```
- Query the test index for tests related to the claim
- Filter by test type if needed (unit, integration, dst)
- Returns list of test files and their metadata

Example:
```bash
# Claim: "Snapshot teleportation preserves actor state"
mcp.index_tests("teleport", type="integration")
# → Returns: crates/kelpie-server/tests/teleport_state_preservation.rs
```

### 2. Run the Tests
```
mcp.verify_by_tests(topic, type?)
```
- Finds and executes relevant tests
- Captures stdout/stderr output
- Returns pass/fail status with evidence

Example:
```bash
mcp.verify_by_tests("teleport")
# Output:
# running 3 tests
# test teleport_state_preservation ... ok
# test teleport_cross_region ... ok
# test teleport_vm_memory ... ok
# ✅ All tests passed
```

### 3. Report Actual Results
Report what you OBSERVED, not what the docs claim:

❌ **Don't say:**
```
"According to the README, snapshot teleportation is complete."
```

✅ **Do say:**
```
"I ran the teleport tests (3 tests) and they all passed. The tests verify:
- State preservation across teleport
- Cross-region teleport
- VM memory restoration

Evidence: cargo test -- teleport (all 3 passed)"
```

### 4. Store Verified Facts
```
mcp.state_verified_fact(claim, method, result)
```
- Records the verification in AgentFS
- Creates audit trail of what was verified and how
- Future queries can reference this verification

Example:
```bash
mcp.state_verified_fact(
  claim="Teleport preserves actor state",
  method="Ran cargo test -- teleport",
  result="All 3 tests passed (state_preservation, cross_region, vm_memory)"
)
```

## Verification Methods

### Method 1: Test Execution (Preferred)
Best for: Behavioral claims, feature completeness, correctness

```bash
# Find tests
mcp.index_tests("snapshot")

# Run them
mcp.verify_by_tests("snapshot")

# Interpret results
if all_pass:
  "Snapshot feature verified working ✅"
else:
  "Snapshot feature has failing tests ❌"
```

### Method 2: Command Execution
Best for: Build status, linter compliance, tool presence

```bash
# Claim: "Code has no clippy warnings"
mcp.verify_claim(
  claim="No clippy warnings",
  method="cargo clippy --all-targets --all-features"
)

# Claim: "FoundationDB client is installed"
mcp.verify_claim(
  claim="FDB client available",
  method="which fdbcli"
)
```

### Method 3: Index Query + Code Reading
Best for: Structural claims (not behavioral)

```bash
# Claim: "All storage errors are logged"
mcp.index_symbols("StorageError", kind="enum")
# → Find definition

mcp.codebase_grep("StorageError.*ok\\(\\)|unwrap")
# → Search for silent error handling

# Read matches and determine if logged
```

**Warning**: This method verifies structure, not behavior. Use tests when possible.

## Anti-Patterns

### ❌ Trusting Documentation
```
User: "Is snapshot restore implemented?"
Agent: "Yes, according to docs/ARCHITECTURE.md, it's in Phase 5."
```

Problem: Docs may be stale. Phase 5 might be incomplete.

### ✅ Verifying by Tests
```
User: "Is snapshot restore implemented?"
Agent: "Let me check..."
[Runs: mcp.verify_by_tests("snapshot restore")]
Agent: "Yes, verified working. Test 'test_snapshot_restore_full_state'
passes, demonstrating VM state recovery including memory and actor state."
```

### ❌ Trusting Comments
```rust
// TODO: Add FDB backend support
pub fn storage() -> Storage {
    // For now, use memory backend
    Storage::Memory(MemoryBackend::new())
}
```

Agent: "FDB backend is not implemented yet (see TODO comment)"

Problem: Comment might be stale. Code might have FDB support but comment not updated.

### ✅ Checking Implementation
```bash
mcp.index_symbols("storage", kind="function")
# → Read actual implementation

mcp.verify_by_tests("fdb backend")
# → Run FDB-specific tests

# Report: "FDB backend IS implemented (tests pass), but TODO comment is stale"
```

### ❌ Assuming Tests Exist
```
User: "Does error handling work correctly?"
Agent: "Yes, there are error handling tests."
```

Problem: Didn't actually CHECK if tests exist or pass.

### ✅ Finding and Running Tests
```
mcp.index_tests("error handling")
# Result: No tests found

Agent: "No tests found for 'error handling'. Cannot verify claim.
Recommend: Write tests first, then verify."
```

## Verification Report Template

When reporting verification results, use this format:

```markdown
## Verification: [Claim]

**Claim**: [What was being verified]

**Method**: [How it was verified]
- Tool used: mcp.verify_by_tests / mcp.verify_claim
- Command run: cargo test -- pattern
- Scope: unit tests / integration tests / all tests

**Result**: ✅ VERIFIED / ❌ FAILED / ⚠️ PARTIAL

**Evidence**:
```
[Paste actual test output or command output]
```

**Conclusion**: [Interpretation of results]

**Recorded**: mcp.state_verified_fact(...) [if successful]
```

## Example Verification Session

```bash
# User asks: "Does the actor lifecycle handle crashes correctly?"

# Step 1: Find relevant tests
mcp.index_tests("actor crash")
# → Returns: actor_crash_recovery_test.rs, actor_crash_state_preservation.rs

# Step 2: Run tests
mcp.verify_by_tests("actor crash")
# Output:
# running 5 tests
# test crash_during_invocation ... ok
# test crash_preserves_state ... ok
# test crash_recovery_activates_new_instance ... ok
# test crash_cleanup_resources ... ok
# test crash_isolation_no_cascade ... FAILED
#
# failures:
# ---- crash_isolation_no_cascade stdout ----
# thread 'crash_isolation_no_cascade' panicked at 'assertion failed: no neighbor crash'

# Step 3: Report findings
"Verification Result: ⚠️ PARTIAL

Actor crash handling is MOSTLY working:
- ✅ State preserved across crashes (2 tests pass)
- ✅ Recovery activates new instance (1 test pass)
- ✅ Resources cleaned up (1 test pass)
- ❌ Crash isolation FAILS (1 test fails)

Evidence: cargo test -- 'actor crash' shows 4/5 passing, 1 failing.
Failing test: crash_isolation_no_cascade - neighbor actors ARE affected by crash.

Conclusion: Crash handling is INCOMPLETE. Isolation invariant violated.
Do NOT claim feature complete until crash_isolation_no_cascade passes."

# Step 4: Store verified fact
mcp.state_verified_fact(
  claim="Actor crash handling complete",
  method="Ran 5 crash tests via cargo test -- 'actor crash'",
  result="INCOMPLETE: 4/5 pass, isolation test fails"
)
```

## Integration with Other Skills

- **Use before `/rlm-task` completion** - Verify features work before marking done
- **Use during `/rlm-handoff`** - Re-verify previous agent's claims
- **Use to answer user questions** - Replace "according to docs" with "according to tests"

## Remember

1. **Code and tests are truth**
2. **Docs and comments are UNTRUSTED**
3. **Verification creates evidence**
4. **Evidence supports conclusions**
5. **Store verified facts for future reference**

Verification-first development means: If you haven't run it, you don't know if it works.

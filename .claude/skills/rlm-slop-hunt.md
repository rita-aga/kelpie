# RLM Slop Hunt Skill

Use this skill when tasked with finding and removing "slop" from the codebase.

## What is Slop?

"Slop" is code that accumulates over time and degrades codebase quality:

1. **Dead Code** - Unused functions, structs, dependencies
2. **Orphaned Code** - Old implementations replaced but not deleted
3. **Duplicates** - Similar functionality implemented multiple times
4. **Fake DST Tests** - Tests claiming to be simulation tests but aren't
5. **Incomplete Code** - TODOs, FIXMEs, stubs left in production
6. **Inconsistent Code** - Patterns that violate project constraints
7. **Documentation Rot** - Docs claiming features that don't exist

## When to Use

Invoke this skill when:
- Preparing for a release (cleanup pass)
- User reports "codebase feels messy"
- After major refactoring (old code left behind)
- Periodic maintenance (every N commits)
- Before marking large feature complete

**Goal**: Remove technical debt without breaking working code.

## Slop Hunting Process

### Phase 1: Detection (Find Candidates)

Run detection tools to identify potential slop:

```bash
# 1. Dead code detection
mcp.detect_dead_code()
# Returns:
# - Unused dependencies in Cargo.toml
# - Unreachable functions (no call sites)
# - Unused imports
# - Orphaned test files

# 2. Orphaned code detection
mcp.detect_orphaned_code()
# Returns:
# - Files with "old_", "deprecated_", "legacy_" in name
# - Multiple implementations of same interface
# - Code marked with // Superseded by ...

# 3. Duplicate code detection
mcp.detect_duplicates()
# Returns:
# - Functions with >80% similarity
# - Copied error types across crates
# - Redundant implementations

# 4. Fake DST test detection
mcp.detect_fake_dst()
# Returns:
# - Tests with "dst" in name but no Simulation harness
# - Tests with "fault_injection" but no fault config
# - Tests claiming determinism but using rand::thread_rng()

# 5. Incomplete code detection
mcp.detect_incomplete()
# Returns:
# - TODO comments in production code
# - FIXME comments older than 30 days
# - unimplemented!() or panic!("not implemented")
# - Functions that just return default values
```

### Phase 2: Classification (Triage)

For each candidate, classify by certainty:

```markdown
## Slop Candidates

### High Confidence (Safe to Remove)
- [x] `old_storage.rs` - Superseded by `fdb.rs`, no references
- [x] `MemoryBackend` in kelpie-storage - Unused, tests use SimStorage
- [x] Dependency: `log` crate - No usages, replaced by `tracing`

### Medium Confidence (Verify First)
- [ ] `validate_actor_id()` - No direct calls, but might be used indirectly
- [ ] `LegacyProtocol` trait - Marked deprecated, check if still needed

### Low Confidence (Needs Investigation)
- [ ] `emergency_shutdown()` - Looks unused, but might be critical path
- [ ] `debug_mode` flag - No usages found, but could be runtime-configured

### Not Slop (False Positives)
- `dead_code_example.rs` - Intentionally unused (example file)
- `FaultType::Reserved` - Unused now, but part of public API
```

### Phase 3: Verification (Prove Safe to Delete)

**CRITICAL**: Do not blindly delete. Verify safety FIRST.

#### Verification Method 1: Reference Check
```bash
# For each candidate, check ALL references

# Obvious places:
mcp.codebase_grep("function_name")
mcp.codebase_grep("StructName")
mcp.index_symbols("item_name")

# Non-obvious places:
mcp.codebase_grep("\"function_name\"")  # String references
mcp.codebase_grep("stringify!")         # Macro stringification
mcp.codebase_grep("module::function")   # Qualified paths

# Dependencies:
mcp.index_deps()  # Check reverse dependencies
```

#### Verification Method 2: Git History
```bash
git log --all --full-history -- path/to/file.rs

# Check:
# - Why was this added?
# - When was it last modified?
# - Is there context explaining its purpose?
# - Was it recently replaced by something else?
```

#### Verification Method 3: Test Removal
```bash
# Safest verification: Try removing it

# 1. Comment out or delete the code
# 2. Run full test suite
cargo test --all

# 3. Run clippy
cargo clippy --all-targets --all-features

# If tests and clippy pass → safe to remove
# If anything breaks → investigate failures
```

#### Verification Method 4: Dependency Analysis
```bash
# For unused dependencies:

# 1. Check Cargo.toml
mcp.index_deps()

# 2. Grep for imports
mcp.codebase_grep("use dependency_name")

# 3. Try compiling without it
# (Remove from Cargo.toml, run cargo build)

# 4. Check if it's an indirect dependency
cargo tree | grep dependency_name
```

### Phase 4: Propose Cleanup

Group candidates by category and priority:

```markdown
## Slop Cleanup Proposal

### Priority: High (Blocking Issues)
1. **Fake DST Tests** (3 tests)
   - `test_actor_under_faults_dst` - Uses thread_rng(), not deterministic
   - `test_storage_fault_injection` - No Simulation harness
   - `test_network_partition_dst` - No SimNetwork, uses real network
   - **Impact**: These tests give FALSE CONFIDENCE in DST coverage
   - **Action**: Fix to use proper DST harness OR rename to remove "_dst" suffix
   - **Verification**: After fix, run `mcp.dst_coverage_check()`

2. **Unwrap() in Production** (5 instances)
   - P0 constraint violation
   - **Verification**: `cargo clippy` catches these
   - **Action**: Replace with `?` or explicit error handling

### Priority: Medium (Technical Debt)
3. **Dead Code** (15 items)
   - 8 unused functions
   - 4 unused structs
   - 3 unused dependencies
   - **Impact**: Confuses navigation, increases compile time
   - **Action**: Remove after verification
   - **Verification**: Run tests after each removal

4. **Duplicate Implementations** (4 pairs)
   - `actor_id_valid()` in 3 different files
   - `StorageError` defined in 2 crates
   - **Action**: Consolidate into single implementation
   - **Verification**: Tests still pass

### Priority: Low (Cosmetic)
5. **Old TODOs** (12 comments)
   - TODO comments older than 90 days
   - **Action**: Either implement or delete comment
   - **Verification**: User review

6. **Orphaned Documentation** (3 files)
   - `docs/OLD_ARCHITECTURE.md` - Describes deprecated design
   - **Action**: Archive or delete
   - **Verification**: No impact on code
```

### Phase 5: Execute Cleanup

**IMPORTANT**: One at a time, with verification after each.

```bash
# For each cleanup item:

# 1. Make the change (remove code)
# 2. Run tests
cargo test --all

# 3. Run clippy
cargo clippy

# 4. Commit with clear message
git commit -m "refactor: Remove unused function 'validate_legacy_id'

No references found via codebase grep.
Git history shows replaced by validate_actor_id() in commit abc123.
Tests pass after removal.

Slop cleanup - dead code removal."

# 5. Move to next item
```

**Never batch cleanups.** If something breaks, you want to know exactly which change caused it.

### Phase 6: Re-Run Detection

After cleanup, verify slop is actually gone:

```bash
# Re-run detection tools
mcp.detect_dead_code()
# Should return fewer items (or none)

mcp.detect_fake_dst()
# Should return zero (all fixed or renamed)

mcp.constraint_check()
# Should pass all checks

# Compare before/after:
# Before: 23 slop items detected
# After: 3 slop items detected (false positives)
# Improvement: 20 items removed ✅
```

## Slop Categories in Detail

### Category 1: Dead Code

**Symptoms:**
- No references found via grep
- Function/struct defined but never used
- Imports that don't correspond to any usage

**Verification:**
```bash
# 1. Find all references
mcp.codebase_grep("function_name")

# 2. Check if it's part of public API
mcp.index_symbols("function_name")
# → If pub fn in lib.rs, might be external API

# 3. Check tests
mcp.index_tests("function_name")
# → If no tests, likely unused

# 4. Try removing and see if anything breaks
```

**Common False Positives:**
- Public API (used by external crates)
- Trait implementations (used via dynamic dispatch)
- Proc macros (used at compile time)
- FFI exports (called from other languages)

### Category 2: Orphaned Code

**Symptoms:**
- Files named `old_*.rs` or `legacy_*.rs`
- Comments like `// Superseded by ...`
- Multiple versions of same functionality

**Verification:**
```bash
# 1. Find the "new" implementation mentioned in comments
# 2. Verify old implementation has no usages
# 3. Check git history for migration commit
# 4. Confirm tests exist for new implementation
```

**Example:**
```rust
// File: old_storage.rs
// DEPRECATED: Use fdb.rs instead

// Action:
# 1. Verify fdb.rs exists and has tests
mcp.verify_by_tests("fdb storage")  # Tests pass ✅

# 2. Check for references to old_storage
mcp.codebase_grep("old_storage")  # No references found ✅

# 3. Remove file
rm crates/kelpie-storage/src/old_storage.rs

# 4. Verify build
cargo build  # Succeeds ✅
```

### Category 3: Duplicates

**Symptoms:**
- Same logic implemented in multiple places
- Copy-pasted error types
- Redundant helper functions

**Verification:**
```bash
# 1. Identify all implementations
mcp.codebase_grep("fn validate_actor_id")
# → Found in: actor.rs, runtime.rs, server.rs

# 2. Compare implementations (are they identical?)
mcp.codebase_read_section("actor.rs", "validate_actor_id")
mcp.codebase_read_section("runtime.rs", "validate_actor_id")
# → Identical! Safe to consolidate

# 3. Plan consolidation:
# - Keep one canonical implementation in kelpie-core
# - Replace others with imports
# - Verify tests still pass
```

### Category 4: Fake DST Tests

**Symptoms:**
- Test file named `*_dst.rs` but doesn't use Simulation
- Test uses `rand::thread_rng()` instead of `DeterministicRng`
- Test uses real I/O instead of SimStorage/SimNetwork

**Verification:**
```bash
# 1. Check if test uses DST infrastructure
mcp.codebase_grep("Simulation::new", file_pattern="*_dst.rs")

# 2. Check for non-deterministic elements
mcp.codebase_grep("thread_rng\\(\\)", file_pattern="*_dst.rs")
mcp.codebase_grep("SystemTime::now", file_pattern="*_dst.rs")

# 3. Determine action:
# Option A: Fix to use proper DST (add Simulation harness)
# Option B: Rename to remove "_dst" suffix (admit it's not DST)
```

**Example Fix:**
```rust
// Before (FAKE DST):
#[test]
fn test_actor_failure_dst() {  // Name claims DST
    let mut rng = rand::thread_rng();  // ❌ Non-deterministic
    // ...
}

// After (REAL DST):
#[test]
fn test_actor_failure_dst() {
    let config = SimConfig::from_env_or_random();  // ✅ Deterministic
    Simulation::new(config).run(|env| async move {
        // Use env.rng, env.storage, env.clock
    });
}

// Or (ADMIT IT'S NOT DST):
#[test]
fn test_actor_failure() {  // Renamed - no longer claims DST
    let mut rng = rand::thread_rng();
    // ...
}
```

### Category 5: Incomplete Code

**Symptoms:**
- `TODO:` comments in production code
- `unimplemented!()` macros
- Functions that just return default values
- FIXME comments older than 30 days

**Verification:**
```bash
# 1. Find all TODOs
mcp.codebase_grep("TODO:|FIXME:|unimplemented!")

# 2. For each, determine:
# - Is this in production code path?
# - Is it blocking any features?
# - Can it be implemented now or removed?

# 3. Take action:
# Option A: Implement the TODO
# Option B: Remove if not needed
# Option C: Convert to GitHub issue and remove comment
```

## Anti-Patterns

### ❌ Blindly Deleting
```bash
# Found unused function → immediately delete
rm old_code.rs
git commit -m "cleanup"

# Problem: Didn't verify, might have broken something
```

### ✅ Verify Then Delete
```bash
# Found unused function
mcp.codebase_grep("function_name")  # Check references
git log old_code.rs  # Check history
rm old_code.rs  # Delete
cargo test  # Verify nothing broke ✅
git commit -m "refactor: Remove unused function 'function_name'"
```

### ❌ Batch Cleanups
```bash
# Delete 10 files at once
rm old_*.rs
cargo test  # Fails!
# Problem: Don't know which deletion caused failure
```

### ✅ Incremental Cleanup
```bash
# Delete one file at a time
rm old_storage.rs
cargo test  # Passes ✅
git commit -m "refactor: Remove old_storage.rs"

rm old_actor.rs
cargo test  # Passes ✅
git commit -m "refactor: Remove old_actor.rs"
```

### ❌ Trusting Detection Tools
```bash
mcp.detect_dead_code()
# → Returns: "function foo() unused"

# Agent deletes without verifying
rm foo.rs

# Problem: Detection tool might have false positive
```

### ✅ Verify Detection Results
```bash
mcp.detect_dead_code()
# → Returns: "function foo() unused"

# Verify manually:
mcp.codebase_grep("foo")  # Actually IS used via macro
# Don't delete - false positive
```

## Cleanup Report Template

After slop hunt, create summary:

```markdown
## Slop Cleanup Summary

**Date**: 2026-01-21
**Scope**: Full codebase audit

### Detection Results
- Dead code: 15 items found
- Orphaned code: 3 files
- Duplicates: 4 pairs
- Fake DST tests: 3 tests
- Incomplete code: 12 TODOs
- **Total**: 37 slop items

### Cleanup Performed
- ✅ Removed 8 unused functions
- ✅ Removed 3 unused dependencies
- ✅ Deleted 2 old_*.rs files
- ✅ Fixed 3 fake DST tests (now use Simulation)
- ✅ Consolidated 2 duplicate implementations
- ✅ Removed 10 outdated TODOs
- **Total removed**: 28 items

### Verification
- ✅ All tests pass: `cargo test --all`
- ✅ Clippy clean: `cargo clippy`
- ✅ Code formatted: `cargo fmt`
- ✅ Re-ran detection: 9 items remaining (all false positives)

### Remaining Items (Not Slop)
- `emergency_shutdown()` - Part of public API, used by external tools
- `debug_mode` flag - Used at runtime, not found by static analysis
- 7 TODOs - In test files (allowed)

### Impact
- **Removed lines**: 1,247 lines of code deleted
- **Improved clarity**: Easier to navigate codebase
- **Fixed confidence**: Fake DST tests now real
- **Reduced compile time**: 3 unused dependencies removed
```

## Remember

1. **Verify before deleting** - Static analysis can be wrong
2. **One item at a time** - Know what broke if something breaks
3. **Run tests after each** - Catch issues immediately
4. **Commit incrementally** - Clear audit trail
5. **Re-run detection** - Confirm slop actually removed
6. **Document decisions** - Why kept vs. why removed

Slop hunting is about **increasing confidence**, not just reducing LOC. A smaller codebase with wrong tests is worse than a larger codebase with correct tests.

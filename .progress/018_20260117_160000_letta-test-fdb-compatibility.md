# Task: Letta Test Suite FDB Mode Compatibility

**Created:** 2026-01-17 16:00:00
**Updated:** 2026-01-17 16:00:00
**State:** IN PROGRESS

---

## Vision Alignment

**Vision files read:**
- `.vision/CONSTRAINTS.md` - Simulation-first development, TigerStyle safety
- `CLAUDE.md` - Kelpie development guide, commit policy, verification requirements
- `.progress/014_20260115_143000_letta_api_full_compatibility.md` - Previous compatibility work

**Relevant constraints:**
1. **Simulation-First Development (MANDATORY)** - Every fix MUST have DST coverage
2. **TigerStyle Safety** - 2+ assertions, explicit error handling, no silent truncation
3. **No Placeholders** - Real implementation, not stubs or hacks
4. **Commit Policy** - Only working software (`cargo test` must pass before commit)
5. **Verification First** - Empirically prove features work before considering done

---

## Task Description

**Goal:** Achieve 100% drop-in replacement compatibility between Kelpie (FDB mode) and Letta by systematically running the Letta test suite and fixing issues properly.

**What "properly" means:**
- Fix root causes, not symptoms
- Extend DST harness if new fault types needed
- Write DST tests for every fix
- No hacks to game tests - genuine compatibility
- Verify fixes work end-to-end

**Test suites to run:**
1. `tests/sdk/agents_test.py` - Agent CRUD, lifecycle, configuration
2. `tests/sdk/blocks_test.py` - Memory blocks (core, working, archival)
3. `tests/sdk/tools_test.py` - Tool registration, execution, custom tools
4. `tests/sdk/mcp_servers_test.py` - MCP server integration

**Environment:**
- Letta tests location: `/Users/seshendranalla/Development/letta`
- Kelpie server: `http://localhost:8283` (FDB mode)
- Command: `export LETTA_SERVER_URL=http://localhost:8283 && pytest <test_file> -v`

---

## Options & Decisions

### Option 1: Fix all at once (batch approach)
**Pros:**
- Can see full scope of issues upfront
- Might identify common patterns

**Cons:**
- Overwhelming, easy to miss issues
- Hard to verify each fix independently
- Risk of introducing new bugs while fixing others

### Option 2: One test file at a time (systematic approach) ✅ CHOSEN
**Pros:**
- Manageable scope
- Each fix can be verified independently
- Clear progress tracking
- Easier to write DST tests per fix
- Follows TigerStyle principle of quality over speed

**Cons:**
- Takes longer to see full picture
- Might need to revisit earlier fixes

**Decision:** Use Option 2 (systematic approach)

**Rationale:**
- Aligns with Simulation-First workflow
- Easier to maintain DST coverage
- Reduces risk of introducing bugs
- Allows proper verification at each step

**Trade-offs accepted:**
- Will take longer than batch approach
- May need to iterate on earlier fixes

---

## Implementation Plan

### Phase 0: Baseline Assessment
**Goal:** Understand current state without making changes

**Tasks:**
1. Run all test files to get baseline pass/fail counts
2. Categorize failures by type (missing endpoint, wrong behavior, serialization, etc.)
3. Document current Kelpie FDB mode capabilities
4. Identify DST gaps (fault types or scenarios not covered)

**Success criteria:**
- Complete pass/fail report for all test files
- Categorized failure list
- DST gap analysis documented

---

### Phase 1: agents_test.py Compatibility
**Goal:** Fix all failures in agent tests

**Approach:**
1. Run `agents_test.py` and capture failures
2. For each failure:
   - Identify root cause (not symptom)
   - Check if DST harness supports needed faults
   - If not, extend DST harness FIRST
   - Write DST test that fails
   - Implement fix
   - Verify DST test passes with multiple seeds
   - Verify Letta test passes
   - Run full Kelpie test suite (`cargo test`)
3. Commit only when all tests pass

**DST Coverage Required:**
- Agent creation with FDB storage
- Agent retrieval with storage faults
- Agent updates with concurrent modifications
- Agent deletion with cleanup verification
- Agent state persistence through crashes

**Success criteria:**
- All `agents_test.py` tests pass
- DST tests cover all fixes
- `cargo test` passes
- `cargo clippy` clean
- No placeholders or TODOs

---

### Phase 2: blocks_test.py Compatibility
**Goal:** Fix all failures in memory block tests

**Approach:**
1. Run `blocks_test.py` and capture failures
2. Fix issues using same process as Phase 1
3. Focus on FDB transaction handling for block operations

**DST Coverage Required:**
- Core/working/archival memory tier operations
- Block updates with concurrent access
- Block retrieval with storage failures
- Block deletion with cascade effects
- Memory limit enforcement

**Success criteria:**
- All `blocks_test.py` tests pass
- DST tests cover all fixes
- Full test suite passes

---

### Phase 3: tools_test.py Compatibility
**Goal:** Fix all failures in tool tests

**Approach:**
1. Run `tools_test.py` and capture failures
2. Fix issues with focus on:
   - Built-in tool execution
   - Custom tool storage in FDB
   - Tool invocation with sandbox isolation
   - Tool result handling

**DST Coverage Required:**
- Tool registration with FDB storage
- Tool execution with sandbox faults
- Tool result persistence
- Concurrent tool invocations
- Tool deletion and cleanup

**Success criteria:**
- All `tools_test.py` tests pass
- DST tests cover sandbox + storage interaction
- Full test suite passes

---

### Phase 4: mcp_servers_test.py Compatibility
**Goal:** Fix all failures in MCP server tests

**Approach:**
1. Run `mcp_servers_test.py` and capture failures
2. Fix issues with focus on:
   - MCP server registration in FDB
   - MCP client execution (stdio, HTTP, SSE)
   - MCP tool discovery and invocation
   - MCP server lifecycle

**DST Coverage Required:**
- MCP server registration with FDB
- MCP client communication with network faults
- MCP tool execution with failures
- MCP server cleanup

**Success criteria:**
- All `mcp_servers_test.py` tests pass
- DST tests cover MCP + storage + network
- Full test suite passes

---

### Phase 5: Integration Verification
**Goal:** Verify all tests pass together and system is stable

**Tasks:**
1. Run all 4 test files in sequence
2. Run Kelpie stress tests with FDB
3. Verify DST determinism (same seed = same result)
4. Document remaining limitations (if any)
5. Update LETTA_REPLACEMENT_GUIDE.md

**Success criteria:**
- All Letta tests pass (100% compatibility)
- DST tests pass with multiple seeds
- Stress tests show stability
- Documentation updated

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 16:00 | Use systematic (one file at a time) approach | Better DST coverage, easier verification | Takes longer |
| 16:00 | Extend DST harness if needed before fixes | Follows CONSTRAINTS.md §1 workflow | Requires more upfront work |
| 16:00 | No commits until all tests pass | Follows commit policy in CLAUDE.md | Larger commits, but working |

---

## What to Try

### Works Now (2026-01-17 16:00:00)
**Status:** Baseline - Starting assessment

**What user can test:**
```bash
# Kelpie server is running in FDB mode
curl http://localhost:8283/health
# Should return: {"status":"ok","version":"0.1.0","uptime_seconds":...}

# Basic agent creation works
curl -X POST http://localhost:8283/v1/agents \
  -H "Content-Type: application/json" \
  -d '{"name": "test-agent"}'
```

**Expected result:** Server responds with agent created

---

### Doesn't Work Yet
**Status:** Phases 0-2 complete - 15/36 tests passing (42%), agents & blocks 100%

**What's missing:**
1. **MCP Server Endpoints** - `/v1/mcp-servers/` returns 404 (16 tests failing)
2. **Tools List Endpoint** - Hangs indefinitely (blocking test execution)
3. **Missing Response Fields:**
   - Agent `embedding` field not populated
   - Block `limit` field not populated
4. **Error Type Mismatches** - BadRequestError vs UnprocessableEntityError

**When expected:**
- Phase 1 (agents fix): Today
- Phase 2 (blocks fix): Today
- Phase 3 (tools fix): Tomorrow (need to investigate hanging)
- Phase 4 (MCP fix): 2-3 days (major feature missing)

---

### Known Limitations

**Before Phase 0:**
- Unknown which tests fail
- Unknown which DST scenarios missing
- Unknown scope of fixes needed

**Will document after baseline assessment**

---

## Findings & Discoveries

### Phase 0: Baseline Assessment

**Status:** COMPLETE (2026-01-17 16:40:00)

**Test Results Summary:**

| Test File | Pass | Fail | Skip | Pass Rate | Status |
|-----------|------|------|------|-----------|--------|
| agents_test.py | 5 | 1 | 1 | 71.4% | ✅ Good |
| blocks_test.py | 6 | 3 | 1 | 60.0% | ⚠️ Needs work |
| tools_test.py | 1 | 3+ | 2 | <40% | ❌ Hangs on test_list |
| mcp_servers_test.py | 1 | 16 | 0 | 5.3% | ❌ Critical - endpoint missing |
| **TOTAL** | **13** | **23+** | **4** | **~35%** | **Significant work needed** |

**Categorized Failures:**

**Category 1: Missing Response Fields (serialization issues)**
- `agents_test.py::test_create` - Missing `embedding` field (expects 'openai/text-embedding-3-small', got None)
- `blocks_test.py::test_create` (2 tests) - Missing `limit` field (expects 20000, got None)

**Category 2: Wrong Error Types (error handling inconsistency)**
- `blocks_test.py::test_update` - Returns `BadRequestError` but expects `UnprocessableEntityError`

**Category 3: Missing API Endpoints (critical functionality gaps)**
- `mcp_servers_test.py` (16 failures) - `/v1/mcp-servers/` endpoint returns 404
- MCP server CRUD operations not implemented in Kelpie

**Category 4: Tool Operations (need investigation - test hanging)**
- `tools_test.py::test_create` (2 tests) - Need to investigate failure reason
- `tools_test.py::test_upsert` - Need to investigate failure reason
- `tools_test.py::test_list` - **HANGS** - blocking test execution, likely infinite loop or timeout

**Category 5: Skipped Tests (not critical - edge cases)**
- Various `test_upsert[NOTSET]` - Empty parameter tests
- `tools_test.py::test_update` - Skipped for unknown reason

**DST Gap Analysis:**

| Fault Type Needed | Currently Supported | Gap |
|-------------------|---------------------|-----|
| FDB transaction conflicts | ❌ No | Need FDB-specific faults |
| FDB read/write failures | ❌ No | Need FDB-specific faults |
| Concurrent FDB operations | ❌ No | Need FDB-specific faults |
| Serialization errors | ❌ No | Need response validation |
| HTTP error type mismatches | ❌ No | Need error handling faults |

**Critical Finding: MCP Endpoint Missing**
The `/v1/mcp-servers/` endpoint is completely missing from Kelpie, causing 84% of mcp_servers tests to fail. This is a major missing feature, not just a compatibility issue.

**Critical Finding: Test Hanging**
`tools_test.py::test_list` hangs indefinitely, suggesting either:
- Infinite loop in list endpoint
- Database query timeout
- Resource exhaustion
- Missing pagination or limits

**Findings:**
- Overall pass rate: ~35% (13/36+ tests)
- Most failures are fixable (missing fields, error types)
- Two critical issues:
  1. MCP server endpoint completely missing (16 tests)
  2. Tools list endpoint hangs (blocking)
- DST harness needs FDB-specific fault injection
- Error handling inconsistencies across endpoints

---

### Phase 1: agents_test.py

**Status:** Not started

**Findings:**
- TBD

---

### Phase 2: blocks_test.py

**Status:** Not started

**Findings:**
- TBD

---

### Phase 3: tools_test.py

**Status:** Not started

**Findings:**
- TBD

---

### Phase 4: mcp_servers_test.py

**Status:** Not started

**Findings:**
- TBD

---

### Phase 5: Integration Verification

**Status:** Not started

**Findings:**
- TBD

---

## Verification Checklist

Before completing each phase:
- [ ] All phase tests pass
- [ ] DST tests written and passing with multiple seeds
- [ ] `cargo test` passes (all Kelpie tests)
- [ ] `cargo clippy` clean (no warnings)
- [ ] `cargo fmt --check` passes
- [ ] No TODOs, FIXMEs, or placeholder code
- [ ] Error handling is explicit
- [ ] Assertions present (2+ per non-trivial function)
- [ ] Manual verification of fix (run actual test, see it work)

Before final completion:
- [ ] All 4 Letta test files pass (100%)
- [ ] DST determinism verified (multiple seed runs)
- [ ] Stress tests pass
- [ ] Documentation updated
- [ ] `/no-cap` verification passed
- [ ] Git commit with working code

---

## Instance Log

| Instance | Phase | Status | Started | Notes |
|----------|-------|--------|---------|-------|
| 001 | Phase 0 | Not Started | - | Baseline assessment |

---

## Notes

**Development Principles for this task:**
1. **Root Cause First** - Fix the underlying issue, not the symptom
2. **DST Before Production** - Harness extension → Test → Implementation → Verification
3. **No Gaming Tests** - Make Kelpie genuinely compatible, don't hack tests
4. **Empirical Verification** - Run the test, see it pass, don't assume
5. **Working Commits Only** - All tests pass before commit

**Expected Challenges:**
- FDB transaction handling edge cases
- Serialization format differences
- Concurrent access patterns
- Sandbox integration with FDB state
- MCP communication with storage layer

**Success Metrics:**
- 100% Letta test pass rate
- Zero test skips or xfails
- All fixes have DST coverage
- System stable under fault injection

---

## References

- `.progress/014_20260115_143000_letta_api_full_compatibility.md` - Previous API work
- `CLAUDE.md` - Development guide
- `.vision/CONSTRAINTS.md` - Simulation-first requirements
- Letta SDK: https://github.com/letta-ai/letta

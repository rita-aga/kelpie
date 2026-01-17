# ⚠️ FDB Mode Regression Report

**Date:** 2026-01-17
**Critical Finding:** Enabling FDB mode breaks most Letta SDK compatibility tests

---

## Executive Summary

**Pass rate dropped from 82.7% to ~25% when FDB mode is enabled.**

Testing with `cargo run -p kelpie-server --features fdb` revealed catastrophic regressions:
- **MCP Servers: 100% → 5%** (all endpoints return 404!)
- **Tools: 100% → ~11%** (field serialization broken)
- **Blocks: 90% → 60%** (missing fields, wrong error codes)
- **Agents: 85.7% → 71.4%** (missing embedding field)

**Total impact: ~30 tests lost** (43/52 → ~13/52)

---

## Test Results Comparison

### Before FDB Mode (Working)
```bash
cargo run -p kelpie-server  # No FDB flag
```

| Module | Passing | Pass Rate | Status |
|--------|---------|-----------|--------|
| Agents | 6/7 | 85.7% | ✅ Working |
| Blocks | 9/10 | 90% | ✅ Working |
| Tools | 9/9 | 100% | ✅ Working |
| MCP Servers | 19/19 | 100% | ✅ Working |
| **TOTAL** | **43/52** | **82.7%** | ✅ **Good** |

### After FDB Mode (Broken)
```bash
cargo run -p kelpie-server --features fdb
```

| Module | Passing | Pass Rate | Status | Change |
|--------|---------|-----------|--------|--------|
| Agents | 5/7 | 71.4% | ⚠️ Degraded | -1 test |
| Blocks | 6/10 | 60% | ⚠️ Degraded | -3 tests |
| Tools | ~1/9 | ~11% | 💥 Broken | -8 tests |
| MCP Servers | 1/19 | 5.3% | 💥 **Catastrophic** | **-18 tests!** |
| **TOTAL** | **~13/52** | **~25%** | 💥 **Broken** | **-30 tests** |

---

## Critical Issue #1: MCP Servers Completely Broken

**All MCP endpoints return 404 Not Found**

### Test Failures
```
FAILED test_create_stdio_mcp_server        - letta_client.NotFoundError: 404
FAILED test_create_sse_mcp_server          - letta_client.NotFoundError: 404
FAILED test_create_streamable_http_mcp_server - letta_client.NotFoundError: 404
FAILED test_list_mcp_servers               - letta_client.NotFoundError: 404
FAILED test_get_specific_mcp_server        - letta_client.NotFoundError: 404
FAILED test_update_stdio_mcp_server        - letta_client.NotFoundError: 404
FAILED test_update_sse_mcp_server          - letta_client.NotFoundError: 404
FAILED test_delete_mcp_server              - letta_client.NotFoundError: 404
... (13 more MCP tests failed)
```

### Error Example
```
HTTP Request: POST http://localhost:8283/v1/mcp-servers/ "HTTP/1.1 404 Not Found"
```

### Root Cause
**MCP server routes are not being registered when FDB feature is enabled.**

Possible causes:
1. Conditional compilation excluding MCP routes in FDB mode
2. Route registration order issue with FDB initialization
3. MCP module not compiled when `features = ["fdb"]`

### Impact
- **18/19 MCP tests fail** (94.7% failure rate)
- Complete loss of MCP server management functionality
- Agents cannot execute MCP tools
- This is a **blocking issue** for FDB mode adoption

---

## Issue #2: Field Serialization Broken

Multiple tests fail because response fields are returning `None` instead of actual values.

### Agents - Missing `embedding` Field
```python
# Expected:
embedding='openai/text-embedding-3-small'

# Actual:
embedding=None

# Error:
AssertionError: assert None == 'openai/text-embedding-3-small'
```

**Test:** `test_create[caren_agent]`
**Status:** FAILED
**Impact:** Agent creation validation fails

### Blocks - Missing `limit` Field
```python
# Expected:
limit=20000

# Actual:
limit=None

# Error:
AssertionError: assert None == 20000
```

**Tests:**
- `test_create[human_block]` FAILED
- `test_create[persona_block]` FAILED

**Impact:** Block creation validation fails

### Tools - Field Serialization Issues
```python
# Tests failing:
test_create[friendly_func]    FAILED
test_create[unfriendly_func]  FAILED
test_upsert[unfriendly_func]  FAILED
```

**Status:** 3/9 tests failing
**Impact:** Tool management broken

---

## Issue #3: Wrong Error Codes

### Blocks Update - Returns 400 Instead of 422

```python
# Test expects UnprocessableEntityError (422)
# Server returns BadRequestError (400)

Error: 'block value exceeds limit (23 > 10)'
Expected: 422 (UnprocessableEntityError)
Actual: 400 (BadRequestError)
```

**Test:** `test_update[persona_block]`
**Status:** FAILED
**Impact:** Error handling contract broken

---

## Root Cause Analysis

### Hypothesis 1: Conditional Compilation Issues
FDB feature flag may be excluding code that should always be present:

```rust
// Possible issue:
#[cfg(not(feature = "fdb"))]
mod mcp_routes {
    // MCP routes defined here
}

// Or:
#[cfg(feature = "fdb")]
pub fn app_routes() -> Router {
    // Missing MCP routes registration
}
```

### Hypothesis 2: FDB-Specific Serialization
FDB storage backend may use different serialization that strips fields:

```rust
// Possible issue:
#[cfg(feature = "fdb")]
impl AgentState {
    // FDB-specific serialization missing fields
}
```

### Hypothesis 3: Route Registration Order
FDB initialization may interfere with route registration:

```rust
// Possible issue:
async fn start_server() {
    #[cfg(feature = "fdb")]
    init_fdb().await?;  // Might clear or override routes

    register_routes();  // MCP routes not registered
}
```

---

## Files to Investigate

### MCP Routes
1. `crates/kelpie-server/src/letta_compatibility/routes.rs`
   - Check if MCP routes are conditionally compiled
   - Verify route registration in FDB mode

2. `crates/kelpie-server/src/letta_compatibility/handlers/mcp.rs`
   - Check for `#[cfg(feature = "fdb")]` guards
   - Verify handler compilation

### Field Serialization
3. `crates/kelpie-server/src/letta_compatibility/schemas.rs`
   - Check `AgentState`, `BlockResponse`, `ToolState` serialization
   - Look for FDB-specific serialize implementations

4. `crates/kelpie-storage/src/fdb/`
   - Check FDB storage layer serialization
   - Verify field preservation

### Error Handling
5. `crates/kelpie-server/src/letta_compatibility/errors.rs`
   - Check error code mapping in FDB mode
   - Verify 400 vs 422 distinction

---

## Debugging Steps

### 1. Check Route Registration
```bash
# Start server with debug logs
RUST_LOG=debug cargo run -p kelpie-server --features fdb 2>&1 | grep -i "mcp\|route"

# Look for:
# - "Registering route: /v1/mcp-servers"
# - "MCP routes registered"
# - Or absence of these messages
```

### 2. Test MCP Endpoint Manually
```bash
# Should return [] or valid response
curl http://localhost:8283/v1/mcp-servers/

# Currently returns:
# 404 Not Found
```

### 3. Compare Route Tables
```bash
# Without FDB
cargo run -p kelpie-server > routes-no-fdb.log 2>&1 &
curl http://localhost:8283/v1/mcp-servers/  # Works

# With FDB
cargo run -p kelpie-server --features fdb > routes-fdb.log 2>&1 &
curl http://localhost:8283/v1/mcp-servers/  # 404

# Compare logs
diff routes-no-fdb.log routes-fdb.log
```

### 4. Check Compilation
```bash
# See what gets compiled with FDB
cargo build -p kelpie-server --features fdb -vv 2>&1 | grep -i mcp

# Look for:
# - "Compiling mcp module"
# - Or absence indicating it's not compiled
```

---

## Recommended Action Plan

### Priority 1: Fix MCP Routes (Blocking)
**Impact:** 18 tests
**Urgency:** Critical

1. Find why MCP routes aren't registered in FDB mode
2. Fix conditional compilation or route registration
3. Verify all MCP endpoints work with FDB

### Priority 2: Fix Field Serialization
**Impact:** ~10 tests
**Urgency:** High

1. Investigate FDB storage serialization
2. Ensure all fields are preserved
3. Add serialization tests

### Priority 3: Fix Error Codes
**Impact:** 1-2 tests
**Urgency:** Medium

1. Review error mapping in FDB mode
2. Ensure consistent error codes
3. Add error code validation tests

---

## Workaround

**Use non-FDB mode for testing until issues are fixed:**

```bash
# Working configuration (82.7% pass rate)
cargo run -p kelpie-server

# Broken configuration (25% pass rate)
cargo run -p kelpie-server --features fdb
```

---

## Test Commands

### Run Full Test Suite (Non-FDB)
```bash
# Start server WITHOUT FDB
cargo run -p kelpie-server > /tmp/kelpie-server.log 2>&1 &

# Run tests
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283

pytest tests/sdk/agents_test.py -v       # 6/7 pass ✅
pytest tests/sdk/blocks_test.py -v       # 9/10 pass ✅
pytest tests/sdk/tools_test.py -v        # 9/9 pass ✅
pytest tests/sdk/mcp_servers_test.py -v  # 19/19 pass ✅
```

### Run Full Test Suite (FDB - Broken)
```bash
# Start server WITH FDB
cargo run -p kelpie-server --features fdb > /tmp/kelpie-server-fdb.log 2>&1 &

# Run tests
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283

pytest tests/sdk/agents_test.py -v       # 5/7 pass ⚠️
pytest tests/sdk/blocks_test.py -v       # 6/10 pass ⚠️
pytest tests/sdk/tools_test.py -v        # ~1/9 pass 💥
pytest tests/sdk/mcp_servers_test.py -v  # 1/19 pass 💥
```

---

## Conclusion

**FDB mode is not production-ready for Letta SDK compatibility.**

The regressions are too severe (~30 tests lost) to enable FDB mode. The most critical issue is complete loss of MCP functionality (18 tests), which represents 35% of all passing tests in non-FDB mode.

**Recommendation:**
1. Continue using non-FDB mode (82.7% pass rate)
2. Debug and fix FDB mode issues before re-enabling
3. Add FDB-specific CI tests to prevent regressions
4. Consider FDB mode as experimental until issues are resolved

**Next Steps:**
1. Investigate conditional compilation of MCP routes
2. Review FDB storage serialization
3. Add integration tests for FDB mode
4. Document FDB-specific limitations

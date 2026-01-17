# Agent Handoff: Fix Letta SDK Compatibility

## Mission
Make Kelpie a **drop-in replacement** for Letta by passing 80%+ of Letta's official SDK tests (50+ of 63 runnable tests).

## Current State
- **7/55 tests passing (12.7%)** - Basic retrieve/delete works
- **48 tests failing** - See breakdown below
- **Goal: 50+/63 tests passing (80%+)** for production readiness

---

## Quick Start - Run Tests Yourself

### Setup (One Time)
```bash
# 1. Ensure Kelpie server is running
cd /Users/seshendranalla/Development/kelpie
cargo run -p kelpie-server
# Server runs on http://localhost:8283

# 2. Tests are already set up at:
cd /Users/seshendranalla/Development/kelpie/tests/letta_compatibility
# Virtual env already exists at .venv/
```

### Run All Tests
```bash
cd /Users/seshendranalla/Development/kelpie/tests/letta_compatibility
python3 run_individual_tests_fixed.py

# Results go to: test_results_individual/
# Summary shows: Pass/Fail/Error/Timeout/Skip counts
```

### Run Specific Test (For Iteration)
```bash
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283

# Run one test with verbose output
./../kelpie/tests/letta_compatibility/.venv/bin/pytest \
  "tests/sdk/agents_test.py::test_create[caren_agent-params0-extra_expected_values0-None]" \
  -vvs

# Run all agent tests
./../kelpie/tests/letta_compatibility/.venv/bin/pytest tests/sdk/agents_test.py -v

# Run all tests in a file
./../kelpie/tests/letta_compatibility/.venv/bin/pytest tests/sdk/blocks_test.py -v
```

### Workflow: Fix → Test → Repeat
```bash
# 1. Make code changes in Kelpie
vim crates/kelpie-server/src/letta_compatibility/...

# 2. Restart server (in separate terminal)
cargo run -p kelpie-server

# 3. Run specific failing test
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest \
  "tests/sdk/agents_test.py::test_create[caren_agent-params0-extra_expected_values0-None]" \
  -vvs

# 4. If pass: Run all tests to check for regressions
python3 /Users/seshendranalla/Development/kelpie/tests/letta_compatibility/run_individual_tests_fixed.py

# 5. Commit when tests pass
git add . && git commit -m "fix: <what you fixed>"
```

---

## Test Results Breakdown

### ✅ Passing (7 tests)
- `test_retrieve` (agents, blocks, tools) - Retrieval works
- `test_delete` (agents, blocks, tools) - Deletion works
- `test_invalid_server_type` (MCP) - Error handling works

### ❌ Priority 0: Critical Bugs (12 tests - QUICK WINS)

#### Issue 1: Missing `embedding` Field (6 tests fail)
**Tests:**
- `test_create[caren_agent]` and 5 other agent create tests

**Error:**
```python
AssertionError: assert None == 'openai/text-embedding-3-small'
  where None = getattr(AgentState(..., embedding=None, ...), 'embedding')
```

**What's Wrong:**
Kelpie returns `embedding=None`, should return `embedding='openai/text-embedding-3-small'`

**How to Fix:**
```rust
// File: crates/kelpie-server/src/letta_compatibility/schemas.rs
#[derive(Debug, Serialize, Deserialize)]
pub struct AgentState {
    pub id: String,
    pub name: String,
    pub model: String,

    // ADD THIS:
    #[serde(default = "default_embedding")]
    pub embedding: String,

    // ... rest of fields
}

fn default_embedding() -> String {
    "openai/text-embedding-3-small".to_string()
}
```

**Verify Fix:**
```bash
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest \
  "tests/sdk/agents_test.py::test_create[caren_agent-params0-extra_expected_values0-None]" \
  -vvs

# Should see: PASSED
```

---

#### Issue 2: List Operations Return Empty (6 tests fail)
**Tests:**
- `test_list[query_params0-1]` (agents, blocks, identities)

**Error:**
```python
AssertionError: assert 0 == 1
  where 0 = len([])
```

**What's Wrong:**
- Test creates agent with POST (succeeds)
- Test calls GET /v1/agents/ (succeeds, returns 200)
- Response is empty `[]` instead of containing created agent

**Possible Causes:**
1. Agents not persisted to storage
2. List endpoint reads from wrong storage
3. Test fixture cleanup happens too early
4. Query parameters not parsed correctly

**How to Debug:**
```bash
# 1. Create agent manually
curl -X POST http://localhost:8283/v1/agents/ \
  -H "Content-Type: application/json" \
  -d '{"name": "test_agent", "model": "openai/gpt-4o-mini"}'
# Note the ID

# 2. Try to list
curl http://localhost:8283/v1/agents/
# Should return array with created agent, not []

# 3. Try to retrieve by ID
curl http://localhost:8283/v1/agents/{id}
# If this works but list doesn't, it's a list endpoint bug
```

**How to Fix:**
```rust
// File: crates/kelpie-server/src/letta_compatibility/handlers/agents.rs

pub async fn list_agents(
    Query(params): Query<ListParams>,
    Extension(state): Extension<Arc<AppState>>,
) -> Result<Json<Vec<AgentState>>, ApiError> {
    // BUG LIKELY HERE: Not reading from storage correctly

    // Check:
    // 1. Are we reading from the right storage?
    // 2. Are agents being persisted on create?
    // 3. Are query params being applied correctly?

    let agents = state.agent_registry.list_agents().await?;
    // OR
    let agents = state.storage.list_agents().await?;

    // Apply filters if needed
    let filtered = apply_query_filters(agents, &params);

    Ok(Json(filtered))
}
```

**Verify Fix:**
```bash
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest \
  "tests/sdk/agents_test.py::test_list[query_params0-1]" \
  -vvs

# Should see: PASSED
```

**Bonus:** Once list works, 8 skipped tests (upsert/update) will automatically run!

---

### 💥 Priority 1: Missing Features (9 tests - MORE WORK)

#### Issue 3: Groups API Not Implemented (3 tests error)
**Tests:**
- `test_create[round_robin_group]`
- `test_create[supervisor_group]`
- `test_update[round_robin_group]`

**Error:**
```python
AttributeError: 'Letta' object has no attribute 'groups'
```

**What's Wrong:**
- Letta SDK expects `client.groups` resource
- Kelpie doesn't have `/v1/groups/` endpoints
- 404 when accessing

**Required Endpoints:**
```
POST   /v1/groups/          - Create group
GET    /v1/groups/          - List groups
GET    /v1/groups/{id}      - Get group
PUT    /v1/groups/{id}      - Update group
DELETE /v1/groups/{id}      - Delete group
```

**How to Implement:**
```rust
// 1. Define schema
// File: crates/kelpie-server/src/letta_compatibility/schemas.rs

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct GroupState {
    pub id: String,
    pub name: String,
    pub group_type: String,  // "round_robin" | "supervisor"
    pub agent_ids: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateGroupRequest {
    pub name: String,
    pub group_type: String,
    pub agent_ids: Vec<String>,
}

// 2. Create handler
// File: crates/kelpie-server/src/letta_compatibility/handlers/groups.rs

pub async fn create_group(
    Json(payload): Json<CreateGroupRequest>,
    Extension(state): Extension<Arc<AppState>>,
) -> Result<Json<GroupState>, ApiError> {
    let group = GroupState {
        id: Uuid::new_v4().to_string(),
        name: payload.name,
        group_type: payload.group_type,
        agent_ids: payload.agent_ids,
        created_at: Utc::now(),
        updated_at: Utc::now(),
    };

    // Store in memory or database
    state.groups.insert(group.id.clone(), group.clone()).await?;

    Ok(Json(group))
}

pub async fn list_groups(...) -> Result<Json<Vec<GroupState>>, ApiError> { ... }
pub async fn get_group(...) -> Result<Json<GroupState>, ApiError> { ... }
pub async fn update_group(...) -> Result<Json<GroupState>, ApiError> { ... }
pub async fn delete_group(...) -> Result<StatusCode, ApiError> { ... }

// 3. Register routes
// File: crates/kelpie-server/src/letta_compatibility/routes.rs

pub fn letta_routes() -> Router {
    Router::new()
        // Existing routes
        .route("/v1/agents", post(agents::create_agent).get(agents::list_agents))
        // ... other routes

        // ADD THESE:
        .route("/v1/groups",
            post(groups::create_group)
            .get(groups::list_groups))
        .route("/v1/groups/:id",
            get(groups::get_group)
            .put(groups::update_group)
            .delete(groups::delete_group))
}
```

**Verify Fix:**
```bash
# Test endpoint exists
curl http://localhost:8283/v1/groups/
# Should return [] not 404

# Run tests
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest tests/sdk/groups_test.py -v

# Should see some PASSes
```

---

#### Issue 4: Identities API Not Implemented (6 tests error)
**Tests:**
- `test_create[caren1]`, `test_create[caren2]`
- `test_retrieve` (identities)
- `test_update[caren1]`, `test_update[caren2]`
- `test_upsert[caren2]`

**Error:**
```python
AttributeError: 'Letta' object has no attribute 'identities'
```

**What's Wrong:**
Same as Groups - missing endpoints

**Required Endpoints:**
```
POST   /v1/identities/          - Create identity
GET    /v1/identities/          - List identities
GET    /v1/identities/{id}      - Get identity
PUT    /v1/identities/{id}      - Update identity
DELETE /v1/identities/{id}      - Delete identity
```

**How to Implement:**
Follow same pattern as Groups (see above).

**Identity Schema:**
```rust
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct IdentityState {
    pub id: String,
    pub name: String,
    pub identity_type: String,  // e.g., "human", "persona"
    pub description: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}
```

**Verify Fix:**
```bash
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest tests/sdk/identities_test.py -v
```

---

### 📋 Priority 2: Extended Features (17 tests - LOWER PRIORITY)

#### Issue 5: MCP Server Management (17 tests fail)
**Tests:**
- `test_create_stdio_mcp_server`
- `test_create_sse_mcp_server`
- `test_create_streamable_http_mcp_server`
- ... 14 more MCP tests

**What's Wrong:**
- `/v1/mcp-servers/` returns 404
- MCP (Model Context Protocol) server management not implemented

**Required Endpoints:**
```
POST   /v1/mcp-servers/          - Create MCP server
GET    /v1/mcp-servers/          - List MCP servers
GET    /v1/mcp-servers/{id}      - Get MCP server
PUT    /v1/mcp-servers/{id}      - Update MCP server
DELETE /v1/mcp-servers/{id}      - Delete MCP server
GET    /v1/mcp-servers/{id}/tools - List tools from server
```

**Server Types:**
- `stdio` - Command-line MCP server (runs subprocess)
- `sse` - Server-Sent Events MCP server (HTTP streaming)
- `streamable_http` - HTTP streaming MCP server

**Priority:** Lower - Do this AFTER P0 and P1 are complete.

---

## Test Exclusions - Don't Worry About These

### Search Tests (7 tests) - ⏭️ SKIP
**Tests:**
- `test_passage_search_*` (6 tests)
- `test_message_search_basic`
- `test_tool_search_basic`

**Why Skip:**
- These require Turbopuffer API key (Letta's search backend)
- Kelpie doesn't need to pass these
- Write your own search tests if you implement search

**Verification:**
```bash
# These should stay SKIPPED
./../kelpie/tests/letta_compatibility/.venv/bin/pytest tests/sdk/search_test.py -v
# All should show: SKIPPED (Turbopuffer API key not configured)
```

---

## Success Criteria

### Milestone 1: P0 Complete (Target: 25+ tests passing)
- ✅ Agent create works (embedding field added)
- ✅ List operations work (agents, blocks, tools)
- ✅ Upsert tests run (unlocked by create fix)
- ✅ Update tests run (unlocked by create fix)

**Check:**
```bash
python3 run_individual_tests_fixed.py
# Should see: "Pass: 25+" out of 63 runnable tests
```

### Milestone 2: P1 Complete (Target: 40+ tests passing)
- ✅ Groups API works (3+ tests pass)
- ✅ Identities API works (6+ tests pass)
- ✅ All CRUD operations stable

**Check:**
```bash
python3 run_individual_tests_fixed.py
# Should see: "Pass: 40+" out of 63 runnable tests
```

### Milestone 3: Production Ready (Target: 50+ tests passing - 80%+)
- ✅ MCP Server management works (17+ tests pass)
- ✅ All validation issues fixed
- ✅ 80%+ of runnable tests passing

**Check:**
```bash
python3 run_individual_tests_fixed.py
# Should see: "Pass rate: 80.0%+"
```

---

## Debugging Tips

### Check Server Logs
```bash
# Run server with verbose logging
RUST_LOG=debug cargo run -p kelpie-server

# Watch for:
# - 404 errors (endpoint missing)
# - 500 errors (server bug)
# - Panic messages (crash)
```

### Manual API Testing
```bash
# Test endpoint exists
curl -v http://localhost:8283/v1/agents/

# Create agent
curl -X POST http://localhost:8283/v1/agents/ \
  -H "Content-Type: application/json" \
  -d '{
    "name": "test",
    "model": "openai/gpt-4o-mini",
    "embedding": "openai/text-embedding-3-small"
  }'

# List agents
curl http://localhost:8283/v1/agents/

# Get specific agent
curl http://localhost:8283/v1/agents/{id}

# Update agent
curl -X PUT http://localhost:8283/v1/agents/{id} \
  -H "Content-Type: application/json" \
  -d '{"name": "updated_name"}'

# Delete agent
curl -X DELETE http://localhost:8283/v1/agents/{id}
```

### Compare with Letta
```bash
# Start real Letta server on different port
letta server --port 8284

# Compare responses
curl http://localhost:8284/v1/agents/  # Real Letta
curl http://localhost:8283/v1/agents/  # Kelpie

# Should return same JSON structure
```

---

## Documentation References

**In this directory:**
- `LETTA_COMPATIBILITY_REPORT.md` - Executive summary
- `DETAILED_FAILURE_ANALYSIS.md` - Code-level fixes with examples
- `FAIL_VS_ERROR_EXPLAINED.md` - Understanding test statuses
- `SKIPPED_TESTS_ANALYSIS.md` - Which tests to run when

**Test results:**
- `test_results_individual/*.txt` - Full output for each test
- `test_results_individual/*.status` - Status for each test
- `test_results_individual/RUN_LOG.txt` - Overall run log

**Letta SDK:**
- Real tests: `/Users/seshendranalla/Development/letta/tests/sdk/`
- Test utilities: `/Users/seshendranalla/Development/letta/tests/sdk/conftest.py`

---

## Iteration Strategy

### Phase 1: Quick Wins (1-2 hours)
1. Fix `embedding` field → +6 tests
2. Fix list operations → +6 tests
3. **Result: ~25/63 tests passing (40%)**

### Phase 2: Core Features (4-6 hours)
4. Implement Groups API → +3 tests
5. Implement Identities API → +6 tests
6. **Result: ~40/63 tests passing (63%)**

### Phase 3: Polish (6-8 hours)
7. Implement MCP Server API → +17 tests
8. Fix remaining validation issues
9. **Result: 50+/63 tests passing (80%+)** ✅

---

## Commit Strategy

```bash
# After each fix that makes tests pass
git add .
git commit -m "fix: <what you fixed>

- Fixed <issue>
- Tests now passing: <list tests>
- Pass rate: X/63 (Y%)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

git push origin master
```

---

## Questions?

**Read the docs first:**
- `DETAILED_FAILURE_ANALYSIS.md` has code examples for every issue
- `FAIL_VS_ERROR_EXPLAINED.md` explains test statuses

**Still stuck?**
- Check Letta's implementation: `/Users/seshendranalla/Development/letta/letta/`
- Compare response schemas with Letta SDK expectations
- Run manual curl tests to isolate the issue

---

## You're Ready!

Start with P0 Issue 1 (embedding field) - it's a 5-line fix that unlocks 6 tests.

Good luck! 🚀

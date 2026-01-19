# 🎯 Letta Compatibility Fix - Action Plan

**Status:** 26/70 tests (37.1%) → **Target:** 50+/63 tests (80%+)

---

## 🔥 PRIORITY 0: Fix List Operations (+12 tests = 54%)

**THE SINGLE BIGGEST WIN** - Do this first, get 12 tests immediately!

### The Problem
```bash
# Create works:
curl -X POST http://localhost:8283/v1/agents/ \
  -H "Content-Type: application/json" \
  -d '{"name":"test","model":"gpt-4"}' | jq .id
# Returns: "abc-123"

# Retrieve works:
curl http://localhost:8283/v1/agents/abc-123 | jq .name
# Returns: "test"

# But list is empty:
curl http://localhost:8283/v1/agents/ | jq length
# Returns: 0  ❌ WRONG! Should be 1
```

### Root Cause
List endpoint reads from different storage than create/retrieve.

### The Fix
Find `list_agents` handler and make it read from same storage as `create_agent`.

**File:** `crates/kelpie-server/src/letta_compatibility/handlers/agents.rs`

```rust
// Current (broken):
pub async fn list_agents(...) -> Result<Json<Vec<AgentState>>, ApiError> {
    let agents = state.in_memory_cache.values(); // ❌ Wrong storage
    Ok(Json(agents))
}

// Fix:
pub async fn list_agents(...) -> Result<Json<Vec<AgentState>>, ApiError> {
    let agents = state.storage.list_agents().await?; // ✅ Same as create
    Ok(Json(agents))
}
```

### Test Your Fix
```bash
# 1. Restart server
cargo run -p kelpie-server

# 2. Test manually
curl -X POST http://localhost:8283/v1/agents/ -d '{"name":"test","model":"gpt-4"}'
curl http://localhost:8283/v1/agents/ | jq length  # Should be 1, not 0

# 3. Run tests
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest \
  "tests/sdk/agents_test.py::test_list[query_params0-1]" -vvs
# Should see: PASSED ✅

# 4. Run all tests
cd /Users/seshendranalla/Development/kelpie/tests/letta_compatibility
python3 run_individual_tests_fixed.py
# Should see: 38/70 (54%) ✅
```

**Do the same for blocks and tools!**

---

## 💥 PRIORITY 1: Add Groups API (+7 tests = 64%)

**Missing endpoints:** `/v1/groups/`

### Quick Check
```bash
curl http://localhost:8283/v1/groups/
# Currently: 404 ❌
# After fix: [] ✅
```

### Implementation (Copy MCP pattern)

**1. Schema** (`schemas.rs`):
```rust
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct GroupState {
    pub id: String,
    pub name: String,
    pub group_type: String,  // "round_robin" | "supervisor"
    pub agent_ids: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}
```

**2. Handlers** (create `handlers/groups.rs`):
```rust
pub async fn create_group(...) -> Result<Json<GroupState>, ApiError> { }
pub async fn list_groups(...) -> Result<Json<Vec<GroupState>>, ApiError> { }
pub async fn get_group(...) -> Result<Json<GroupState>, ApiError> { }
pub async fn update_group(...) -> Result<Json<GroupState>, ApiError> { }
pub async fn delete_group(...) -> Result<StatusCode, ApiError> { }
```

**3. Routes** (`routes.rs`):
```rust
.route("/v1/groups", post(groups::create_group).get(groups::list_groups))
.route("/v1/groups/:id", get(groups::get_group).put(groups::update_group).delete(groups::delete_group))
```

**4. Storage** (`state.rs`):
```rust
pub struct AppState {
    // Add:
    pub groups: Arc<RwLock<HashMap<String, GroupState>>>,
}
```

### Test
```bash
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest tests/sdk/groups_test.py -v
# Should see some PASS ✅
```

---

## 💥 PRIORITY 2: Add Identities API (+4 tests = 70%)

**Same pattern as Groups** - copy and adapt.

**Missing endpoints:** `/v1/identities/`

---

## ⚙️ PRIORITY 3: MCP Tool Integration (+4 tests = 75%+)

Wire MCP tools to agent execution so agents can actually use them.

---

## 🚀 Quick Commands

### Test Everything
```bash
cd /Users/seshendranalla/Development/kelpie/tests/letta_compatibility
python3 run_individual_tests_fixed.py
```

### Test One Thing
```bash
cd /Users/seshendranalla/Development/letta
export LETTA_SERVER_URL=http://localhost:8283
./../kelpie/tests/letta_compatibility/.venv/bin/pytest "tests/sdk/agents_test.py::test_list[query_params0-1]" -vvs
```

### Debug Mode
```bash
RUST_LOG=debug cargo run -p kelpie-server
```

---

## 📊 Milestones

| Fix | Tests | Pass Rate | Effort |
|-----|-------|-----------|--------|
| **Current** | 26/70 | 37.1% | - |
| List ops | 38/70 | 54.3% | 1-2h |
| Groups API | 45/70 | 64.3% | 3-4h |
| Identities API | 49/70 | 70.0% | 2-3h |
| MCP tools | 53/70 | 75.7% | 4-6h |
| **Target** | **50+/63** | **80%+** | ✅ |

---

## 📂 Files to Edit

1. **List fix:**
   - `crates/kelpie-server/src/letta_compatibility/handlers/agents.rs`
   - `crates/kelpie-server/src/letta_compatibility/handlers/blocks.rs`
   - `crates/kelpie-server/src/letta_compatibility/handlers/tools.rs`

2. **Groups API:**
   - `crates/kelpie-server/src/letta_compatibility/schemas.rs` (add GroupState)
   - `crates/kelpie-server/src/letta_compatibility/handlers/groups.rs` (new file)
   - `crates/kelpie-server/src/letta_compatibility/routes.rs` (add routes)
   - `crates/kelpie-server/src/state.rs` (add groups storage)

3. **Identities API:**
   - Same pattern as Groups

---

## 💡 Tips

1. **Start with list** - Easiest, biggest impact
2. **Copy working patterns** - MCP servers work perfectly, copy that style
3. **Test incrementally** - Fix one endpoint, test it, move on
4. **Use curl first** - Verify endpoints manually before running pytest
5. **Read existing code** - Agents/blocks/tools handlers show the pattern

---

## 📚 Supporting Docs

- **Detailed guide:** `AGENT_HANDOFF_V3.md` (comprehensive)
- **Code examples:** `DETAILED_FAILURE_ANALYSIS.md`
- **Test results:** `test_results_individual/`

---

## 🎯 Success = 50+ Tests Passing

You're **halfway there** (26/50). The next big jump is list operations.

**Go fix list first!** 🚀

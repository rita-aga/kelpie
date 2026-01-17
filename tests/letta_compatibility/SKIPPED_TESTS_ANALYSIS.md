# Skipped Tests Analysis

## Question 1: Should We Eventually Run the 15 Skipped Tests?

### Answer: **Some Yes, Some No**

---

## Category 1: Search Tests (7 tests) - **NO, Don't Need to Run**

**Why Skipped:**
```python
@pytest.mark.skipif(not settings.tpuf_api_key, reason="Turbopuffer API key not configured")
def test_passage_search_basic(client: Letta, enable_turbopuffer):
```

**What They Test:**
- Turbopuffer integration (Letta's chosen search backend)
- Semantic search on passages, messages, tools
- Date filters, tags, pagination

**Should Kelpie Support This?**
- ❌ **NO** - These are Letta-specific Turbopuffer integration tests
- ✅ Kelpie should implement its **own** search API at the same endpoints
- Letta uses Turbopuffer; Kelpie can use whatever search backend it wants
- The tests expect Turbopuffer-specific behavior

**What Kelpie Should Do:**
1. Implement search endpoints: `/v1/search/passages`, `/v1/search/messages`, `/v1/search/tools`
2. Write **Kelpie-specific** search tests (not these Turbopuffer tests)
3. Return results in same JSON format Letta SDK expects

**Tests:**
- `test_passage_search_basic`
- `test_passage_search_with_tags`
- `test_passage_search_with_date_filters`
- `test_message_search_basic`
- `test_passage_search_pagination`
- `test_passage_search_org_wide`
- `test_tool_search_basic`

---

## Category 2: Upsert Tests (3 tests) - **YES, Should Run Eventually**

**Why Skipped:**
```python
SKIPPED (got empty par...)
```

**Root Cause:**
- Tests are parametrized with `NOTSET` values
- When params are empty, test framework skips them
- This is a **test data issue**, not a feature issue

**Should Kelpie Support This?**
- ✅ **YES** - Upsert (create-or-update) is a legitimate API operation
- These tests should run once we fix the **create** tests (which provide the test data)

**Current Block:**
- Create tests fail → No items created → No IDs to upsert with → Skip

**Action Required:**
1. Fix create tests first (P0: add `embedding` field)
2. Re-run upsert tests - they should pass if create works

**Tests:**
- `test_upsert[NOTSET]` (agents)
- `test_upsert[NOTSET]` (blocks)
- `test_upsert[NOTSET]` (groups)

---

## Category 3: Update Tests (5 tests) - **YES, Should Run Eventually**

**Why Skipped:**
```python
if name not in test_item_ids:
    pytest.skip(f"Item '{name}' not found in test_items")
```

**Root Cause:**
- Update tests depend on create tests succeeding
- Create tests failed → No items created → No IDs to update → Skip
- This is a **test dependency issue**

**Should Kelpie Support This?**
- ✅ **YES** - Update (PUT) is a core CRUD operation
- These tests should run once we fix the **create** tests

**Current Block:**
- Create tests fail → No items in `test_item_ids` → Skip update tests

**Action Required:**
1. Fix create tests first (P0)
2. Re-run update tests - they should execute (may pass or fail)

**Tests:**
- `test_update[caren_agent-params0-...]` (agents)
- `test_update[human_block-params0-...]` (blocks)
- `test_update[persona_block-params1-...]` (blocks)
- `test_update[friendly_func-params0-...]` (tools)
- `test_update[unfriendly_func-params1-...]` (tools)

---

## Summary Table

| Category | Count | Should Run? | When? | Reason |
|----------|-------|-------------|-------|--------|
| **Search (Turbopuffer)** | 7 | ❌ NO | Never | Letta-specific backend tests |
| **Upsert** | 3 | ✅ YES | After fixing create | Test data dependency |
| **Update** | 5 | ✅ YES | After fixing create | Test dependency |
| **Total Skipped** | 15 | **8 will run** | After P0 fixes | 7 stay skipped |

---

## Expected Test Count After Fixing Create

**Current:**
- 55 tests run (70 - 15 skipped)
- 7 passing (12.7%)

**After P0 Fixes (add embedding, fix list):**
- **63 tests will run** (70 - 7 Turbopuffer skips)
- Expected ~20-30 passing (depends on upsert/update implementation quality)
- Target: 50+ passing (80%+ of runnable tests)

---

## Action Plan

### Phase 1: Fix P0 Issues (Enable 8 More Tests)
1. ✅ Add `embedding` field to agent responses
2. ✅ Fix list operations (return persisted items)
3. ✅ Re-run tests → Upsert/Update should now execute

### Phase 2: Implement Missing APIs (P1)
4. ✅ Groups API (enables 3+ tests)
5. ✅ Identities API (enables 6+ tests)
6. ✅ Search API (Kelpie's own implementation, write new tests)

### Phase 3: Polish (P2)
7. ✅ MCP Server management
8. ✅ Fix all remaining validation issues
9. ✅ Target: 80%+ pass rate on runnable tests

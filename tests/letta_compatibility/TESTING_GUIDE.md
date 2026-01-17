# Letta Compatibility Testing Guide

This guide explains how to ensure Kelpie maintains 100% compatibility with the Letta SDK.

---

## Overview

Kelpie uses **multiple layers of verification** to ensure it's a drop-in replacement for Letta:

```
┌──────────────────────────────────────────────────────────┐
│  Layer 1: Letta SDK Integration Tests (sdk_tests.py)    │
│  Uses ACTUAL Letta Python SDK to test Kelpie            │
│  ✅ Ensures real-world compatibility                     │
└──────────────────────────────────────────────────────────┘
                         │
                         ▼
┌──────────────────────────────────────────────────────────┐
│  Layer 2: API Coverage Report (coverage_report.py)      │
│  Tests all known Letta endpoints programmatically       │
│  ✅ Finds missing/unimplemented endpoints               │
└──────────────────────────────────────────────────────────┘
                         │
                         ▼
┌──────────────────────────────────────────────────────────┐
│  Layer 3: OpenAPI Spec Comparison (openapi_diff.py)     │
│  Compares Kelpie's API against Letta's OpenAPI spec     │
│  ✅ Catches schema mismatches and new endpoints         │
└──────────────────────────────────────────────────────────┘
                         │
                         ▼
┌──────────────────────────────────────────────────────────┐
│  Layer 4: CI/CD Automation (.github/workflows/)         │
│  Runs all tests on every commit + weekly                │
│  ✅ Prevents regressions and catches Letta updates      │
└──────────────────────────────────────────────────────────┘
```

---

## Quick Start

### 1. Install Dependencies

```bash
cd tests/letta_compatibility
pip install -r requirements.txt
```

### 2. Start Kelpie Server

```bash
# In one terminal
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server

# Wait for it to start
curl http://localhost:8283/health
```

### 3. Run All Tests

```bash
# Run SDK integration tests
make test

# Generate coverage report
make coverage

# Run everything
make all
```

---

## Test Layers Explained

### Layer 1: SDK Integration Tests (`sdk_tests.py`)

**What it does:**
- Uses the **actual Letta Python SDK** to test Kelpie
- Runs real-world workflows (create agent, send message, update memory, etc.)
- Verifies schema compatibility (AgentState, MemoryBlock, etc.)

**Why it matters:**
- If Letta SDK works, your users' code will work
- Tests integration, not just endpoints
- Catches subtle bugs (field naming, type mismatches, etc.)

**How to run:**
```bash
pytest sdk_tests.py -v

# Run specific test
pytest sdk_tests.py::TestAgentLifecycle::test_create_agent -v

# Run with detailed output
pytest sdk_tests.py -vv --tb=long
```

**Example output:**
```
tests/letta_compatibility/sdk_tests.py::TestAgentLifecycle::test_create_agent PASSED
tests/letta_compatibility/sdk_tests.py::TestAgentLifecycle::test_get_agent PASSED
tests/letta_compatibility/sdk_tests.py::TestMemoryBlocks::test_list_memory_blocks PASSED
tests/letta_compatibility/sdk_tests.py::TestMessaging::test_send_message PASSED

========================= 25 passed in 12.34s =========================
```

**Test Categories:**
- `TestAgentLifecycle`: CRUD operations
- `TestMemoryBlocks`: Core memory operations
- `TestMessaging`: Message sending and streaming
- `TestTools`: Tool listing and execution
- `TestPagination`: Cursor and after parameters
- `TestImportExport`: Agent migration
- `TestSchemaCompatibility`: Response schema validation
- `TestErrorHandling`: Error cases (404, validation, etc.)

### Layer 2: Coverage Report (`coverage_report.py`)

**What it does:**
- Tests **all known Letta endpoints** directly via HTTP
- Categorizes endpoints as:
  - ✅ Fully implemented (200 OK)
  - ⚠️ Not implemented (501)
  - ❌ Missing (404)
  - 🔧 Error (500, connection refused, etc.)

**Why it matters:**
- Finds endpoints you forgot to implement
- Shows which advanced features return 501
- Tracks implementation progress

**How to run:**
```bash
python coverage_report.py

# Use custom Kelpie URL
python coverage_report.py --kelpie-url http://localhost:9000
```

**Example output:**
```
🧪 Testing Kelpie API at http://localhost:8283...

📝 Creating test agent...
   ✅ Test agent created: agent-123

🔍 Testing all endpoints...

================================================================================
  LETTA API COVERAGE REPORT
================================================================================

📊 Summary:
   Total endpoints tested: 32
   ✅ Fully implemented: 28 (87.5%)
   ⚠️  Not implemented (501): 4 (12.5%)
   ❌ Missing (404): 0 (0.0%)
   🔧 Errors: 0 (0.0%)

--------------------------------------------------------------------------------
ENDPOINT DETAILS:
--------------------------------------------------------------------------------
╔═══════════════╦════════╦═══════════════════════════════════════╦══════╦═══════╗
║ Status        ║ Method ║ Path                                  ║ Code ║ Error ║
╠═══════════════╬════════╬═══════════════════════════════════════╬══════╬═══════╣
║ ✅ Implemented ║ GET    ║ /health                               ║  200 ║       ║
║ ✅ Implemented ║ GET    ║ /v1/agents                            ║  200 ║       ║
║ ✅ Implemented ║ POST   ║ /v1/agents                            ║  200 ║       ║
║ ⚠️  Not Impl.  ║ GET    ║ /v1/sources                           ║  501 ║       ║
╚═══════════════╩════════╩═══════════════════════════════════════╩══════╩═══════╝

📈 Overall Coverage: 87.5%
   ⚠️  GOOD: Most endpoints are implemented
```

### Layer 3: OpenAPI Comparison (`openapi_diff.py`)

**What it does:**
- Fetches OpenAPI specs from both Letta and Kelpie servers
- Compares endpoints, parameters, request/response schemas
- Generates detailed diff reports

**Why it matters:**
- Catches new endpoints when Letta releases updates
- Finds schema mismatches (missing fields, wrong types)
- Provides formal verification against specification

**Requirements:**
- Kelpie must expose `/openapi.json` endpoint
- Both Letta and Kelpie servers must be running

**How to run:**
```bash
# Start Letta server (in separate terminal)
letta server  # Runs on http://localhost:8080

# Start Kelpie server (in another terminal)
cargo run -p kelpie-server  # Runs on http://localhost:8283

# Compare
python openapi_diff.py
```

**Example output:**
```
🔍 Fetching OpenAPI specifications...
   Letta:  http://localhost:8080
   Kelpie: http://localhost:8283
✅ Specifications fetched successfully

📊 Comparing APIs...

================================================================================
  LETTA vs KELPIE API COMPARISON
================================================================================

📊 Summary:
   Letta endpoints: 45
   Kelpie endpoints: 43
   Matching: 41
   Missing in Kelpie: 4
   Extra in Kelpie: 2
   Schema differences: 1

❌ MISSING ENDPOINTS (in Letta but not in Kelpie):
┌────────┬─────────────────────┬──────────────────────────┐
│ Method │ Path                │ Summary                  │
├────────┼─────────────────────┼──────────────────────────┤
│ GET    │ /v1/sources         │ List document sources    │
│ POST   │ /v1/sources         │ Upload document source   │
└────────┴─────────────────────┴──────────────────────────┘

📈 Compatibility Score: 91.1% (41/45 endpoints)
   ✅ EXCELLENT: Kelpie is highly compatible with Letta
```

**Note:** This requires implementing OpenAPI schema generation in Kelpie. See "Adding OpenAPI Support" below.

### Layer 4: CI/CD Automation

**What it does:**
- Runs SDK tests on every commit
- Weekly schedule to catch Letta API changes
- Posts compatibility reports on PRs

**How to use:**
- Push to main/master branch → tests run automatically
- Create PR → compatibility report posted as comment
- Weekly → catches upstream Letta changes

**See:** `.github/workflows/letta-compatibility.yml`

---

## Adding OpenAPI Support to Kelpie

For `openapi_diff.py` to work, Kelpie needs to expose its API specification.

### Using `utoipa` (Recommended)

Add to `Cargo.toml`:
```toml
[dependencies]
utoipa = { version = "5.1", features = ["axum"] }
utoipa-swagger-ui = { version = "8.0", features = ["axum"] }
```

Update `kelpie-server/src/main.rs`:
```rust
use utoipa::OpenApi;
use utoipa_swagger_ui::SwaggerUi;

#[derive(OpenApi)]
#[openapi(
    paths(
        crate::api::agents::list_agents,
        crate::api::agents::create_agent,
        // ... add all handlers
    ),
    components(
        schemas(AgentState, CreateAgentRequest, MemoryBlock, /* ... */)
    ),
    tags(
        (name = "agents", description = "Agent management"),
        (name = "memory", description = "Memory operations"),
    )
)]
struct ApiDoc;

async fn main() {
    let app = Router::new()
        // ... existing routes ...
        .merge(SwaggerUi::new("/swagger-ui").url("/openapi.json", ApiDoc::openapi()));

    // ...
}
```

Annotate handlers:
```rust
#[utoipa::path(
    get,
    path = "/v1/agents",
    responses(
        (status = 200, description = "List of agents", body = Vec<AgentState>)
    )
)]
async fn list_agents(/* ... */) -> Result<Json<Vec<AgentState>>> {
    // ...
}
```

---

## Common Workflows

### Workflow 1: Verify Compatibility After Changes

```bash
# 1. Make your changes to kelpie-server
vim crates/kelpie-server/src/api/agents.rs

# 2. Rebuild
cargo build --release -p kelpie-server

# 3. Restart server
pkill kelpie-server
./target/release/kelpie-server &

# 4. Run tests
cd tests/letta_compatibility
make all
```

### Workflow 2: Check Coverage for Missing Endpoints

```bash
# Generate coverage report
python coverage_report.py

# Look for ⚠️ and ❌ statuses
# Implement missing endpoints
# Re-run to verify
```

### Workflow 3: Weekly Letta Update Check

```bash
# Update Letta SDK
pip install --upgrade letta

# Run tests
pytest sdk_tests.py -v

# If tests fail, check what changed:
# 1. New endpoints added?
# 2. Schema changes?
# 3. Behavior changes?

# Update Kelpie accordingly
```

### Workflow 4: Add Test for New Endpoint

When Kelpie adds a new endpoint:

```python
# In sdk_tests.py, add new test
class TestNewFeature:
    def test_new_endpoint(self, client, test_agent):
        """Test the new feature"""
        result = client.new_feature.do_something(test_agent.id)
        assert result is not None
```

When Letta adds a new endpoint:

```python
# In coverage_report.py, add to LETTA_ENDPOINTS
LETTA_ENDPOINTS.append(
    EndpointTest("GET", "/v1/new-feature", expected_status=200)
)
```

---

## Troubleshooting

### Tests Fail with "Connection Refused"

**Problem:** Kelpie server not running

**Solution:**
```bash
# Check if running
curl http://localhost:8283/health

# Start if not running
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server
```

### Tests Fail with "Agent not found"

**Problem:** Agent was deleted or doesn't exist

**Solution:** The tests clean up after themselves. If tests crash mid-run, orphaned agents may remain:
```bash
# List all agents
curl http://localhost:8283/v1/agents

# Delete specific agent
curl -X DELETE http://localhost:8283/v1/agents/{id}
```

### OpenAPI Diff Fails

**Problem:** Kelpie doesn't expose `/openapi.json`

**Solution:** See "Adding OpenAPI Support to Kelpie" above.

### ImportError: No module named 'letta'

**Problem:** Dependencies not installed

**Solution:**
```bash
cd tests/letta_compatibility
pip install -r requirements.txt
```

---

## Best Practices

### 1. Run Tests Before Committing

```bash
# Pre-commit hook
cd tests/letta_compatibility
make test || (echo "❌ Tests failed!" && exit 1)
```

### 2. Keep Tests in Sync with Letta

```bash
# Weekly:
pip install --upgrade letta
pytest sdk_tests.py -v

# If tests fail, document why:
# - Letta bug? (file issue)
# - New feature? (implement in Kelpie)
# - Breaking change? (update tests)
```

### 3. Document Deferred Features

If an endpoint returns 501:
```rust
// In handler
if path == "/v1/sources" {
    return Err(ApiError::NotImplemented {
        feature: "document sources".to_string(),
        reason: "Deferred to Phase X - see ADR-021".to_string()
    });
}
```

Update `LETTA_COMPATIBILITY_REPORT.md`:
```markdown
### Deferred Features

| Endpoint | Status | Reason | Planned |
|----------|--------|--------|---------|
| `/v1/sources` | ⚠️ 501 | Complex feature, low demand | Phase 7 |
```

### 4. Version Compatibility Matrix

Track which Letta versions you've tested:

```markdown
# In LETTA_COMPATIBILITY_REPORT.md

## Tested Versions

| Letta Version | Test Date | Status | Notes |
|---------------|-----------|--------|-------|
| v0.6.2 | 2026-01-16 | ✅ Pass | 28/32 endpoints |
| v0.6.1 | 2026-01-10 | ✅ Pass | 27/30 endpoints |
```

---

## Metrics and Reporting

### Key Metrics to Track

1. **Endpoint Coverage** (goal: >90%)
   - Fully implemented / Total endpoints

2. **SDK Test Pass Rate** (goal: 100%)
   - Passing tests / Total tests

3. **Schema Compatibility** (goal: 0 diffs)
   - Schema differences found

4. **Response Time** (goal: <2x Letta)
   - Kelpie latency / Letta latency

### Generating Reports

```bash
# Weekly compatibility report
python coverage_report.py > reports/$(date +%Y-%m-%d)-coverage.txt

# SDK test results
pytest sdk_tests.py --html=reports/$(date +%Y-%m-%d)-sdk-tests.html

# OpenAPI diff (requires both servers)
python openapi_diff.py > reports/$(date +%Y-%m-%d)-openapi-diff.txt
```

---

## Integration with Development Workflow

### During Development

```bash
# 1. Make changes
# 2. Quick test
pytest sdk_tests.py::TestAgentLifecycle -v

# 3. Full test before commit
make all
```

### Before Release

```bash
# 1. Full SDK tests
pytest sdk_tests.py -v

# 2. Coverage report
python coverage_report.py

# 3. OpenAPI diff (if Letta server available)
python openapi_diff.py

# 4. Update docs if needed
vim ../../docs/LETTA_COMPATIBILITY_REPORT.md
```

### After Letta Release

```bash
# 1. Update SDK
pip install --upgrade letta

# 2. Run tests
pytest sdk_tests.py -v

# 3. If failures, investigate
pytest sdk_tests.py -vv --tb=long

# 4. Update Kelpie
# 5. Re-test
# 6. Update compatibility report
```

---

## References

- [Letta SDK Documentation](https://docs.letta.com/)
- [ADR-021: Letta API Compatibility Strategy](../../docs/adr/021-letta-api-compatibility-strategy.md)
- [Letta Compatibility Report](../../docs/LETTA_COMPATIBILITY_REPORT.md)
- [Letta Replacement Guide](../../docs/LETTA_REPLACEMENT_GUIDE.md)

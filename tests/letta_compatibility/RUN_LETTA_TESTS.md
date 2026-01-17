# Running Letta's Official SDK Tests Against Kelpie

The BEST way to verify Kelpie is a drop-in replacement is to run Letta's own SDK tests against it.

## Setup

```bash
# 1. Start Kelpie server
export ANTHROPIC_API_KEY=sk-ant-your-key-here
cd /Users/seshendranalla/Development/kelpie
cargo run -p kelpie-server

# 2. Verify it's running (in another terminal)
curl http://localhost:8283/health

# 3. Install Letta's test dependencies
cd /Users/seshendranalla/Development/letta
pip install -e ".[dev]"  # or pip install -r tests/requirements.txt

# 4. Run Letta's SDK tests against Kelpie
export LETTA_SERVER_URL=http://localhost:8283  # Point tests at Kelpie
pytest tests/sdk/ -v
```

## How It Works

Letta's `tests/sdk/conftest.py`:
- Reads `LETTA_SERVER_URL` environment variable
- Defaults to `http://localhost:8283` (same as Kelpie!)
- Creates `letta_client.Letta(base_url=...)` pointing at that URL

So when you run their tests with `LETTA_SERVER_URL=http://localhost:8283`, they run against Kelpie instead of Letta.

## What Gets Tested

Letta's official test suite includes:
- `agents_test.py` - Agent CRUD operations
- `blocks_test.py` - Memory block operations
- `tools_test.py` - Tool operations
- `groups_test.py` - Agent groups/supervisor pattern
- `identities_test.py` - Multi-tenancy
- `mcp_servers_test.py` - MCP server integration
- `search_test.py` - Passage/message/tool search

## Expected Results

### Currently Passing (Estimated)
- ✅ Basic agent CRUD (create, get, list, delete)
- ✅ Basic block operations
- ✅ Basic tool operations

### Expected Failures
- ❌ `model_settings` field (Kelpie may not populate this)
- ❌ MCP servers (not implemented in Kelpie)
- ❌ Advanced search (turbopuffer integration)
- ❌ Groups/supervisor pattern (may not be implemented)
- ❌ Identities (multi-tenancy may not be implemented)

## Running Individual Test Files

```bash
# Just agent tests
export LETTA_SERVER_URL=http://localhost:8283
pytest tests/sdk/agents_test.py -v

# Just block tests
pytest tests/sdk/blocks_test.py -v

# Just tool tests
pytest tests/sdk/tools_test.py -v

# Stop on first failure
pytest tests/sdk/agents_test.py -x

# Verbose with full tracebacks
pytest tests/sdk/agents_test.py -vv --tb=long
```

## Interpreting Results

### ✅ Test Passes
Kelpie is compatible with that endpoint/feature.

### ❌ Test Fails
Check the failure:
- **404 Not Found**: Endpoint not implemented in Kelpie
- **Schema mismatch**: Response doesn't match Letta's schema
- **501 Not Implemented**: Endpoint exists but returns "not implemented"
- **Other error**: Logic bug or missing feature

## Current Compatibility Status

Run this to get a quick overview:
```bash
export LETTA_SERVER_URL=http://localhost:8283
pytest tests/sdk/ -v --tb=no | grep -E "PASSED|FAILED|ERROR"
```

## Why This Is Better Than Custom Tests

1. **No guessing** - These are Letta's actual tests
2. **Zero maintenance** - When Letta updates their API, their tests update too
3. **True compatibility** - If their tests pass, we're truly a drop-in replacement
4. **Comprehensive** - They test things we wouldn't think of

## Next Steps

1. Run the tests and document which ones pass/fail
2. Fix Kelpie to make failing tests pass
3. Track progress: "X/Y Letta SDK tests passing"
4. When all pass, Kelpie is 100% compatible ✨

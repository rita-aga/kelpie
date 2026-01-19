# Letta Compatibility Test Files

This directory contains three test files designed for different purposes in verifying Kelpie's compatibility with the Letta SDK.

## Test File Overview

| File | Purpose | Test Count | Use Case |
|------|---------|------------|----------|
| `sdk_tests_simple.py` | Quick validation | 10 tests | Fast smoke tests, CI quick checks |
| `sdk_tests_full.py` | **Full coverage** | 50+ tests | **Complete endpoint verification (DEFAULT)** |
| `sdk_tests.py` | Legacy/development | Variable | Being updated incrementally |

## 1. sdk_tests_simple.py (Quick Validation)

**Purpose**: Fast smoke tests to verify basic functionality is working.

**Coverage**:
- ✅ Agent CRUD operations (create, get, list, delete)
- ✅ Basic schema validation
- ✅ Error handling (404s)
- ✅ Multiple memory blocks

**When to use**:
- Quick sanity checks during development
- CI pre-flight checks (< 30 seconds)
- Verifying server is responding correctly

**Run with**:
```bash
pytest sdk_tests_simple.py -v
```

**Example tests**:
- `test_create_agent` - Basic agent creation
- `test_get_agent` - Retrieve agent by ID
- `test_list_agents` - List all agents
- `test_delete_agent` - Delete and verify removal

---

## 2. sdk_tests_full.py (Full Coverage) ⭐ DEFAULT

**Purpose**: Comprehensive verification of ALL Letta SDK endpoints and features.

**This is the primary test suite used by default in `./run_all_tests.sh`**

**Coverage** (10 test classes, 50+ tests):

### TestAgentLifecycle
- ✅ Create agent with full configuration
- ✅ Create agent with minimal config
- ✅ Get agent by ID
- ✅ List agents (all, filtered, paginated)
- ✅ Update agent (name, model, memory)
- ✅ Delete agent

### TestMemoryBlocks
- ✅ List memory blocks for agent
- ✅ Get specific block by ID
- ✅ Update block value
- ✅ Create new block
- ✅ Delete block

### TestStandaloneBlocks
- ✅ Create standalone (shared) blocks
- ✅ List all blocks
- ✅ Get block by ID
- ✅ Update block
- ✅ Delete block
- ✅ Link blocks to agents

### TestMessaging
- ✅ Send message to agent
- ✅ Send message with streaming
- ✅ List messages for agent
- ✅ List messages with pagination
- ✅ Get specific message by ID

### TestArchivalMemory
- ✅ Insert passage into archival memory
- ✅ Search archival memory
- ✅ List all passages
- ✅ Get specific passage
- ✅ Delete passage

### TestTools
- ✅ List available tools
- ✅ Get tool by ID
- ✅ Create custom tool
- ✅ Delete tool
- ✅ List tools for agent

### TestImportExport
- ✅ Export agent configuration
- ✅ Export agent with full state
- ✅ Import agent from export
- ✅ Verify imported agent matches

### TestSchemaCompatibility
- ✅ Agent has all required fields
- ✅ Agent has all optional fields (if supported)
- ✅ Memory block schema validation
- ✅ Message schema validation
- ✅ Tool schema validation

### TestErrorHandling
- ✅ Get nonexistent agent (404)
- ✅ Delete nonexistent agent (404)
- ✅ Invalid agent ID format
- ✅ Invalid memory block data
- ✅ Invalid message format

### TestPagination
- ✅ List with limit parameter
- ✅ List with cursor parameter
- ✅ List with after parameter
- ✅ Verify pagination metadata

**When to use**:
- **Default test suite** (run by `./run_all_tests.sh`)
- Before committing changes
- Before releasing new versions
- Full compatibility verification
- Regression testing

**Run with**:
```bash
# Full suite with verbose output
pytest sdk_tests_full.py -v

# Specific test class
pytest sdk_tests_full.py::TestMessaging -v

# Specific test
pytest sdk_tests_full.py::TestMessaging::test_send_message -v

# Stop on first failure
pytest sdk_tests_full.py -x

# Show full tracebacks
pytest sdk_tests_full.py --tb=long
```

**Example tests**:
```python
def test_send_message(self, client, test_agent):
    """Test sending a message to an agent"""
    response = client.agents.messages.create(
        agent_id=test_agent.id,
        messages=[MessageCreateParam(role="user", content="What is 2+2?")]
    )
    assert len(response.messages) > 0
    assert any(m.role == "assistant" for m in response.messages)

def test_insert_archival_memory(self, client, test_agent):
    """Test inserting a passage into archival memory"""
    passage = client.agents.archival.create(
        agent_id=test_agent.id,
        content="Important fact to remember"
    )
    assert hasattr(passage, "id")
    assert passage.content == "Important fact to remember"
```

---

## 3. sdk_tests.py (Legacy/Development)

**Purpose**: Original test file being incrementally updated.

**Status**: Being phased out in favor of `sdk_tests_full.py`.

**When to use**:
- Development and experimentation
- Testing new API patterns
- Not recommended for production use

---

## Running Tests

### Quick Start

```bash
# Run comprehensive test suite (DEFAULT)
cd tests/letta_compatibility
./run_all_tests.sh

# Run only full SDK tests
pytest sdk_tests_full.py -v

# Run only simple tests (quick)
pytest sdk_tests_simple.py -v
```

### Prerequisites

1. **Install dependencies**:
   ```bash
   pip install -r requirements.txt
   ```

2. **Start Kelpie server**:
   ```bash
   export ANTHROPIC_API_KEY=sk-ant-your-key-here
   cargo run -p kelpie-server
   ```

3. **Verify server is running**:
   ```bash
   curl http://localhost:8283/health
   ```

### Test Options

```bash
# Verbose output
pytest sdk_tests_full.py -v

# Show print statements
pytest sdk_tests_full.py -s

# Stop on first failure
pytest sdk_tests_full.py -x

# Run specific test class
pytest sdk_tests_full.py::TestMessaging -v

# Run specific test
pytest sdk_tests_full.py::TestMessaging::test_send_message -vv

# Show coverage
pytest sdk_tests_full.py --cov=. --cov-report=html
```

### Integration with run_all_tests.sh

The test runner script uses `sdk_tests_full.py` by default:

```bash
# Full test suite (uses sdk_tests_full.py)
./run_all_tests.sh

# Quick mode (uses sdk_tests_full.py but stops after SDK tests)
./run_all_tests.sh --quick

# With OpenAPI comparison
./run_all_tests.sh --with-openapi
```

---

## Test Configuration

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `KELPIE_BASE_URL` | `http://localhost:8283` | Kelpie server URL |
| `TEST_MODEL` | `claude-3-5-sonnet-20241022` | LLM model to use |
| `TEST_EMBEDDING` | `openai/text-embedding-3-small` | Embedding model |

### Example with custom config:

```bash
KELPIE_BASE_URL=http://localhost:9000 \
TEST_MODEL=claude-3-opus-20240229 \
pytest sdk_tests_full.py -v
```

---

## Understanding Test Results

### Success (All Tests Pass)

```
tests/sdk_tests_full.py::TestAgentLifecycle::test_create_agent_full PASSED
tests/sdk_tests_full.py::TestMessaging::test_send_message PASSED
...
================== 50 passed in 45.2s ==================
```

**Meaning**: Kelpie is fully compatible with Letta SDK ✨

### Partial Failure (Some Tests Fail)

```
tests/sdk_tests_full.py::TestArchivalMemory::test_search_memory FAILED
...
================== 45 passed, 5 failed in 50.1s ==================
```

**Action**: Review failed tests, check if endpoints are implemented, verify server logs.

### Common Failure Reasons

1. **Server not running**: Start with `cargo run -p kelpie-server`
2. **Missing API key**: Set `ANTHROPIC_API_KEY` environment variable
3. **Endpoint not implemented**: Some endpoints may return 501 (Not Implemented)
4. **Schema mismatch**: Response doesn't match Letta SDK expectations

---

## Development Workflow

### Adding New Tests

1. Add tests to `sdk_tests_full.py` (not `sdk_tests_simple.py`)
2. Follow existing test patterns
3. Use fixtures (`client`, `test_agent`)
4. Include docstrings
5. Test both success and error cases

**Example**:
```python
def test_new_feature(self, client, test_agent):
    """Test description here"""
    # Arrange
    data = {"key": "value"}

    # Act
    result = client.agents.new_feature(agent_id=test_agent.id, data=data)

    # Assert
    assert result is not None
    assert hasattr(result, "expected_field")
```

### Test Organization

```
tests/letta_compatibility/
├── sdk_tests_simple.py      # 10 quick tests
├── sdk_tests_full.py        # 50+ comprehensive tests (DEFAULT)
├── sdk_tests.py             # Legacy (being phased out)
├── coverage_report.py       # Endpoint coverage checker
├── openapi_diff.py          # OpenAPI spec comparison
├── run_all_tests.sh         # Main test runner
└── requirements.txt         # Python dependencies
```

---

## Troubleshooting

### Tests fail to collect

**Problem**: `ImportError: No module named 'letta_client'`

**Solution**:
```bash
pip install -r requirements.txt
```

### Connection refused

**Problem**: `requests.exceptions.ConnectionError`

**Solution**: Start Kelpie server:
```bash
export ANTHROPIC_API_KEY=sk-ant-your-key-here
cargo run -p kelpie-server
```

### Tests timeout

**Problem**: Tests hang or timeout

**Possible causes**:
- LLM API key not set
- LLM API rate limits
- Server not processing requests

**Solution**:
- Check `ANTHROPIC_API_KEY` is set
- Check server logs for errors
- Increase timeout in test fixtures

### 501 Not Implemented

**Problem**: Some tests fail with 501 status

**Expected**: Some advanced endpoints may not be implemented yet. This is documented and acceptable for 95% compatibility target.

**Check**: `python coverage_report.py` to see which endpoints return 501.

---

## References

- [Letta SDK Documentation](https://docs.letta.com/)
- [SDK Fix Notes](./SDK_FIX_NOTES.md) - Details on SDK package changes
- [Testing Guide](./TESTING_GUIDE.md) - Comprehensive testing strategy
- [Handoff Prompt](../../HANDOFF_PROMPT.md) - Agent handoff instructions

---

## Summary

| Use Case | File | Command |
|----------|------|---------|
| **Default/Full verification** | `sdk_tests_full.py` | `./run_all_tests.sh` |
| Quick smoke test | `sdk_tests_simple.py` | `pytest sdk_tests_simple.py -v` |
| Development/experimental | `sdk_tests.py` | `pytest sdk_tests.py -v` |

**Remember**: `sdk_tests_full.py` is the comprehensive test suite and is used by default in the test runner. This ensures full Letta SDK compatibility verification.

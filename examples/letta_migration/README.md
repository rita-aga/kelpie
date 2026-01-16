# Letta to Kelpie Migration Guide

This example demonstrates using Kelpie as a drop-in replacement for Letta.

## TL;DR

**Can you use the Letta SDK (`letta-client`) directly with Kelpie?**

| Method | Works? | Notes |
|--------|--------|-------|
| **Raw HTTP (requests)** | ✅ Yes | 85%+ compatible, recommended approach |
| **letta-client SDK** | ⚠️ Partial | May hang due to pagination format differences |
| **kelpie-client SDK** | ✅ Yes | Purpose-built for Kelpie |

## Quick Start

### 1. Start Kelpie Server

```bash
# Basic (no LLM - for testing CRUD operations)
cargo run -p kelpie-server

# With LLM support (for message responses)
ANTHROPIC_API_KEY=your-key cargo run -p kelpie-server
# or
OPENAI_API_KEY=your-key cargo run -p kelpie-server
```

### 2. Test Compatibility

```bash
# Install dependencies
cd examples/letta_migration
uv venv .venv && source .venv/bin/activate
uv pip install requests

# Run test
python test_compatibility.py
```

## Compatibility Results

Based on our testing:

### ✅ Works (12/14 tests)

| Feature | Endpoint | Status |
|---------|----------|--------|
| Health check | `GET /health` | ✅ |
| Capabilities | `GET /v1/capabilities` | ✅ |
| Create agent | `POST /v1/agents` | ✅ |
| List agents | `GET /v1/agents` | ✅ |
| Get agent | `GET /v1/agents/{id}` | ✅ |
| Update agent | `PATCH /v1/agents/{id}` | ✅ |
| Delete agent | `DELETE /v1/agents/{id}` | ✅ |
| Get memory blocks | `GET /v1/agents/{id}/blocks` | ✅ |
| Update block (Letta path) | `PATCH /v1/agents/{id}/blocks/{label}` | ✅ |
| Update block (Kelpie path) | `PATCH /v1/agents/{id}/core-memory/blocks/{label}` | ✅ |
| List messages | `GET /v1/agents/{id}/messages` | ✅ |
| List tools | `GET /v1/tools` | ✅ |

### ⚠️ Needs Configuration

| Feature | Issue | Solution |
|---------|-------|----------|
| Send message | Needs LLM | Set `ANTHROPIC_API_KEY` or `OPENAI_API_KEY` |
| Archival memory | Field name | Use `content` instead of `text` |

## Using Raw HTTP (Recommended)

The simplest approach - works reliably:

```python
import requests

BASE = "http://localhost:8283"

# Create agent with memory
agent = requests.post(f"{BASE}/v1/agents", json={
    "name": "my-agent",
    "memory_blocks": [
        {"label": "persona", "value": "You are a helpful assistant."},
        {"label": "human", "value": "The user wants help."}
    ]
}).json()

print(f"Created agent: {agent['id']}")

# List agents
agents = requests.get(f"{BASE}/v1/agents").json()
print(f"Found {len(agents['items'])} agents")

# Get memory blocks
blocks = requests.get(f"{BASE}/v1/agents/{agent['id']}/blocks").json()
print(f"Blocks: {[b['label'] for b in blocks]}")

# Update memory
requests.patch(
    f"{BASE}/v1/agents/{agent['id']}/blocks/human",
    json={"value": "Updated memory!"}
)

# Send message (requires LLM API key on server)
response = requests.post(
    f"{BASE}/v1/agents/{agent['id']}/messages",
    json={"role": "user", "content": "Hello!"}
).json()

# Add archival memory (note: use 'content' not 'text')
requests.post(
    f"{BASE}/v1/agents/{agent['id']}/archival",
    json={"content": "Important fact to remember"}
)

# Delete agent
requests.delete(f"{BASE}/v1/agents/{agent['id']}")
```

## Using Letta SDK (With Caveats)

The official `letta-client` SDK can be used but may hang on certain operations due to pagination format differences:

```python
from letta_client import Letta

# Initialize (may work)
client = Letta(
    base_url="http://localhost:8283",
    environment="local"
)

# WARNING: These operations may hang:
# - client.agents.list()  <- Pagination issue
# - client.agents.create() <- May timeout
```

### Known Issues with letta-client SDK

1. **Pagination Format**: Kelpie returns `{items, total, cursor}` but the SDK expects `{items, has_more}` or a list
2. **Create Parameters**: Some parameters may differ between SDK versions
3. **Timeout**: Operations may hang waiting for pagination to complete

### Workaround: Use HTTP Fallback

```python
import requests
from letta_client import Letta

# Use SDK for some operations
client = Letta(base_url="http://localhost:8283", environment="local")

# Fall back to HTTP when needed
def list_agents():
    return requests.get("http://localhost:8283/v1/agents").json()["items"]

def create_agent(name, memory):
    return requests.post(
        "http://localhost:8283/v1/agents",
        json={"name": name, "memory_blocks": memory}
    ).json()
```

## API Differences

### Response Formats

| Endpoint | Letta | Kelpie |
|----------|-------|--------|
| List agents | `[...]` or `{items, has_more}` | `{items, total, cursor}` |
| List tools | `[...]` | `{items, total, cursor}` or dict |
| Archival add | `{"text": "..."}` | `{"content": "..."}` |

### Paths

Both work in Kelpie:
- Letta: `PATCH /v1/agents/{id}/blocks/{label}`
- Kelpie: `PATCH /v1/agents/{id}/core-memory/blocks/{label}`

## Running Tests

```bash
# Full compatibility test
python test_compatibility.py

# Quick HTTP test
python -c "
import requests
r = requests.get('http://localhost:8283/health')
print('Server:', r.json())
"
```

## Files

- `test_compatibility.py` - Comprehensive REST API compatibility test
- `test_letta_sdk.py` - Tests using the official Letta SDK (may timeout)

## Recommendations

1. **For new projects**: Use raw HTTP requests or `kelpie-client`
2. **For migrating from Letta**: 
   - Replace SDK calls with HTTP requests
   - Change `text` to `content` for archival
   - Set LLM API keys for message functionality
3. **For testing**: Use `test_compatibility.py` to verify your setup

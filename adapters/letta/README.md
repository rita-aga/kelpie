# Kelpie-Letta Adapter

A compatibility layer that allows [Letta](https://github.com/letta-ai/letta) clients to connect to Kelpie servers.

## Overview

Kelpie is designed with Letta API compatibility, making it a drop-in replacement for Letta server. This adapter provides:

1. **Backend utilities** - Health checks, capability discovery, connection management
2. **Compatibility checking** - Verify Kelpie server compatibility with Letta clients
3. **Integration tests** - Verify compatibility with the `letta-client` SDK

## Installation

```bash
# From the kelpie repository root
pip install -e adapters/letta/

# With test dependencies
pip install -e "adapters/letta/[test]"
```

## Quick Start

### Using letta-client with Kelpie

The simplest approach is to point `letta-client` directly at your Kelpie server:

```python
from letta_client import Letta

# Connect to Kelpie instead of Letta Cloud
client = Letta(base_url="http://localhost:8283")

# Create an agent - same API as Letta
agent = client.agents.create(
    name="my-agent",
    memory={
        "persona": "I am a helpful assistant",
        "human": "The user is learning about Kelpie"
    }
)

# Send a message
response = client.agents.messages.create(
    agent_id=agent.id,
    messages=[{"role": "user", "content": "Hello!"}]
)

print(response.messages[0].content)
```

### Checking Compatibility

Before using Kelpie with Letta clients, you can verify compatibility:

```python
from kelpie_letta import check_compatibility

# Run compatibility check
report = check_compatibility("http://localhost:8283")

# Print detailed report
print(report)

# Check compatibility level
if report.is_compatible:
    print(f"Server is {report.compatibility_level.value} compatible")
else:
    print("Server is not compatible with Letta clients")
    for warning in report.warnings:
        print(f"  Warning: {warning}")
```

### Using the Backend Adapter

For programmatic management:

```python
from kelpie_letta import KelpieBackend
from kelpie_letta.backend import BackendFeature

# Create backend instance
backend = KelpieBackend(base_url="http://localhost:8283")

# Check connection
success, message = backend.test_connection()
print(message)  # e.g., "Connected to Kelpie 0.1.0"

# Check capabilities
caps = backend.get_capabilities()
if caps.supports(BackendFeature.SEMANTIC_SEARCH):
    print("Semantic search is available")

# Get status
status = backend.get_status()
print(f"Uptime: {status.uptime_seconds}s, Agents: {status.agents_count}")
```

## API Compatibility

Kelpie implements the following Letta API endpoints:

### Required (Core Functionality)

| Endpoint | Method | Status |
|----------|--------|--------|
| `/health` | GET | Supported |
| `/v1/agents` | GET | Supported |
| `/v1/agents` | POST | Supported |
| `/v1/agents/{id}` | GET | Supported |
| `/v1/agents/{id}` | PATCH | Supported |
| `/v1/agents/{id}` | DELETE | Supported |
| `/v1/agents/{id}/blocks` | GET | Supported |
| `/v1/agents/{id}/messages` | POST | Supported |
| `/v1/agents/{id}/messages` | GET | Supported |

### Optional (Extended Features)

| Endpoint | Method | Status |
|----------|--------|--------|
| `/v1/tools` | GET | ✅ Supported |
| `/v1/tools` | POST | ✅ Supported |
| `/v1/tools/{name}` | GET | ✅ Supported |
| `/v1/tools/{name}` | DELETE | ✅ Supported |
| `/v1/tools/{name}/execute` | POST | ✅ Supported |
| `/v1/agents/{id}/archival` | GET | ✅ Supported |
| `/v1/agents/{id}/archival` | POST | ✅ Supported |
| `/v1/agents/{id}/archival/{eid}` | GET | ✅ Supported |
| `/v1/agents/{id}/archival/{eid}` | DELETE | ✅ Supported |
| `/v1/capabilities` | GET | ✅ Supported |
| `/v1/sources` | GET | Planned |
| `/v1/sources` | POST | Planned |

## Running Tests

```bash
# Unit tests only
pytest adapters/letta/tests/

# With a running Kelpie server (integration tests)
KELPIE_URL=http://localhost:8283 pytest adapters/letta/tests/ -m integration

# With letta-client SDK installed
pip install letta-client
pytest adapters/letta/tests/ -m letta_integration
```

## Differences from Letta

While Kelpie aims for API compatibility, there are some differences:

1. **Storage** - Kelpie uses its own storage backend (not PostgreSQL)
2. **Agent Types** - Kelpie supports the same agent types but may have different defaults
3. **LLM Providers** - Kelpie supports OpenAI and Anthropic directly
4. **Tools** - Kelpie has native MCP tool support

## Troubleshooting

### Connection Refused

Make sure the Kelpie server is running:
```bash
cargo run -p kelpie-server -- --port 8283
```

### API Key Errors

Kelpie doesn't require API keys for local connections. If using `letta-client`, you may need to skip authentication:
```python
client = Letta(base_url="http://localhost:8283", api_key="not-needed")
```

### Missing Endpoints

Run the compatibility checker to see which endpoints are missing:
```python
from kelpie_letta import check_compatibility
report = check_compatibility("http://localhost:8283")
for check in report.endpoint_checks:
    if not check.available:
        print(f"Missing: {check.method} {check.endpoint}")
```

## License

Apache-2.0

# Kelpie Python Client

A Letta-compatible Python client for the Kelpie agent runtime.

## Installation

```bash
pip install kelpie-client
```

Or install from source:

```bash
cd adapters/sdk/python
pip install -e .
```

## Quick Start

```python
from kelpie_client import KelpieClient

# Connect to Kelpie server
client = KelpieClient(base_url="http://localhost:8283")

# Check server health
health = client.health()
print(f"Server version: {health['version']}")

# Create an agent with memory blocks
agent = client.create_agent(
    name="my-assistant",
    memory_blocks=[
        {
            "label": "persona",
            "value": "I am a helpful AI assistant named Alice."
        },
        {
            "label": "human",
            "value": "The user is a software developer."
        }
    ],
    system="You are a helpful assistant. Be concise and accurate."
)

print(f"Created agent: {agent.id}")

# Send a message
response = client.send_message(agent.id, "Hello! What's your name?")
print(f"Assistant: {response.messages[-1].content}")

# Update memory block
blocks = client.list_blocks(agent.id)
persona_block = next(b for b in blocks if b.label == "persona")
client.update_block(
    agent.id,
    persona_block.id,
    value="I am a helpful AI assistant named Bob."
)

# List conversation history
messages = client.list_messages(agent.id, limit=10)
for msg in messages:
    print(f"{msg.role}: {msg.content}")

# Delete agent when done
client.delete_agent(agent.id)
```

## API Reference

### KelpieClient

The main client class for interacting with the Kelpie server.

```python
client = KelpieClient(
    base_url="http://localhost:8283",  # Server URL
    timeout=30.0,                       # Request timeout in seconds
)
```

### Agent Operations

```python
# Create agent
agent = client.create_agent(
    name="my-agent",
    agent_type="memgpt_agent",  # or "letta_v1_agent", "react_agent"
    model="openai/gpt-4o",
    system="System prompt",
    description="Agent description",
    memory_blocks=[{"label": "...", "value": "..."}],
    tool_ids=["tool-1", "tool-2"],
    tags=["tag1", "tag2"],
    metadata={"key": "value"},
)

# Get agent
agent = client.get_agent(agent_id)

# List agents (paginated)
agents, next_cursor = client.list_agents(limit=50, cursor=None)

# Update agent
agent = client.update_agent(
    agent_id,
    name="new-name",
    system="new system prompt",
)

# Delete agent
client.delete_agent(agent_id)
```

### Memory Block Operations

```python
# List blocks
blocks = client.list_blocks(agent_id)

# Get specific block
block = client.get_block(agent_id, block_id)

# Update block
block = client.update_block(
    agent_id,
    block_id,
    value="new value",
    description="new description",
    limit=1000,
)
```

### Message Operations

```python
# Send message
response = client.send_message(agent_id, "Hello!")
# response.messages contains user message and assistant response
# response.usage contains token counts

# List messages (paginated, reverse chronological)
messages = client.list_messages(agent_id, limit=100, before=message_id)
```

## Letta Compatibility

This client is designed to be compatible with Letta's Python client. If you're migrating from Letta:

```python
# Before (Letta)
from letta import LettaClient
client = LettaClient(base_url="...")

# After (Kelpie)
from kelpie_client import KelpieClient
client = KelpieClient(base_url="...")

# The API is largely the same!
```

## License

Apache-2.0

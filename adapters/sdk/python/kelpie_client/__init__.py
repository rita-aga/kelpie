"""Kelpie Python Client SDK

A Letta-compatible Python client for the Kelpie agent runtime.

Example usage:
    from kelpie_client import KelpieClient

    client = KelpieClient(base_url="http://localhost:8283")

    # Create an agent
    agent = client.create_agent(
        name="my-agent",
        memory_blocks=[{
            "label": "persona",
            "value": "I am a helpful assistant."
        }]
    )

    # Send a message
    response = client.send_message(agent.id, "Hello!")
    print(response.messages[-1].content)
"""

from .client import KelpieClient
from .models import (
    Agent,
    Block,
    Message,
    MessageResponse,
    AgentType,
    MessageRole,
)

__version__ = "0.1.0"
__all__ = [
    "KelpieClient",
    "Agent",
    "Block",
    "Message",
    "MessageResponse",
    "AgentType",
    "MessageRole",
]

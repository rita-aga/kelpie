"""Kelpie-Letta compatibility adapter.

This package provides compatibility utilities for using Letta clients with Kelpie servers.

Example usage with letta-client SDK:
    from letta_client import Letta

    # Point to Kelpie server
    client = Letta(base_url="http://localhost:8283")

    # Create agent - works the same as with Letta
    agent = client.agents.create(name="my-agent")

    # Send message
    response = client.agents.messages.create(
        agent_id=agent.id,
        messages=[{"role": "user", "content": "Hello!"}]
    )
"""

from .backend import KelpieBackend
from .compat import check_compatibility, LettaCompatibilityReport

__version__ = "0.1.0"
__all__ = ["KelpieBackend", "check_compatibility", "LettaCompatibilityReport"]

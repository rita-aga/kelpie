"""Integration tests for Kelpie client against real server.

Run with:
    # Start the server first:
    cargo run -p kelpie-server -- --bind 127.0.0.1:8283

    # Then run tests:
    python3 -m unittest tests.test_integration -v
"""

import os
import unittest
from unittest import skipUnless

from kelpie_client import KelpieClient, MessageRole


# Check if integration tests should run
KELPIE_SERVER_URL = os.environ.get("KELPIE_SERVER_URL", "http://localhost:8283")
RUN_INTEGRATION = os.environ.get("KELPIE_INTEGRATION_TESTS", "0") == "1"


def server_available() -> bool:
    """Check if the server is available."""
    if not RUN_INTEGRATION:
        return False
    try:
        client = KelpieClient(base_url=KELPIE_SERVER_URL, timeout=2.0)
        client.health()
        return True
    except Exception:
        return False


@skipUnless(server_available(), "Kelpie server not available")
class TestIntegration(unittest.TestCase):
    """Integration tests against real Kelpie server."""

    @classmethod
    def setUpClass(cls):
        """Create client."""
        cls.client = KelpieClient(base_url=KELPIE_SERVER_URL)
        # Track created agents for cleanup
        cls.created_agent_ids = []

    @classmethod
    def tearDownClass(cls):
        """Clean up created agents."""
        for agent_id in cls.created_agent_ids:
            try:
                cls.client.delete_agent(agent_id)
            except Exception:
                pass

    def test_health_check(self):
        """Test server health check."""
        health = self.client.health()
        self.assertEqual(health["status"], "ok")
        self.assertIn("version", health)
        self.assertIn("uptime_seconds", health)

    def test_full_agent_lifecycle(self):
        """Test complete agent CRUD operations."""
        # Create
        agent = self.client.create_agent(
            name="integration-test-agent",
            description="Agent for integration testing",
            memory_blocks=[
                {"label": "persona", "value": "I am a test agent."},
                {"label": "human", "value": "The user is a tester."},
            ],
            tags=["test", "integration"],
        )
        self.created_agent_ids.append(agent.id)

        self.assertIsNotNone(agent.id)
        self.assertEqual(agent.name, "integration-test-agent")
        self.assertEqual(len(agent.blocks), 2)
        self.assertEqual(agent.tags, ["test", "integration"])

        # Read
        retrieved = self.client.get_agent(agent.id)
        self.assertEqual(retrieved.id, agent.id)
        self.assertEqual(retrieved.name, agent.name)

        # Update
        updated = self.client.update_agent(
            agent.id,
            description="Updated description",
            tags=["test", "integration", "updated"],
        )
        self.assertEqual(updated.description, "Updated description")
        self.assertEqual(len(updated.tags), 3)

        # List
        agents, cursor = self.client.list_agents(limit=100)
        agent_ids = [a.id for a in agents]
        self.assertIn(agent.id, agent_ids)

        # Delete
        self.client.delete_agent(agent.id)
        self.created_agent_ids.remove(agent.id)

        # Verify deletion
        from kelpie_client.client import KelpieError

        with self.assertRaises(KelpieError) as ctx:
            self.client.get_agent(agent.id)
        self.assertEqual(ctx.exception.status, 404)

    def test_memory_blocks(self):
        """Test memory block operations."""
        # Create agent with blocks
        agent = self.client.create_agent(
            name="block-test-agent",
            memory_blocks=[
                {"label": "persona", "value": "Initial persona", "limit": 1000},
            ],
        )
        self.created_agent_ids.append(agent.id)

        # List blocks
        blocks = self.client.list_blocks(agent.id)
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0].label, "persona")
        self.assertEqual(blocks[0].value, "Initial persona")

        # Get specific block
        block = self.client.get_block(agent.id, blocks[0].id)
        self.assertEqual(block.id, blocks[0].id)

        # Update block
        updated = self.client.update_block(
            agent.id,
            block.id,
            value="Updated persona value",
        )
        self.assertEqual(updated.value, "Updated persona value")

    def test_messages(self):
        """Test message operations."""
        # Create agent
        agent = self.client.create_agent(name="message-test-agent")
        self.created_agent_ids.append(agent.id)

        # Send message
        response = self.client.send_message(agent.id, "Hello, agent!")
        self.assertEqual(len(response.messages), 2)
        self.assertEqual(response.messages[0].role, MessageRole.USER)
        self.assertEqual(response.messages[0].content, "Hello, agent!")
        self.assertEqual(response.messages[1].role, MessageRole.ASSISTANT)
        self.assertIsNotNone(response.usage)

        # Send another message
        response2 = self.client.send_message(agent.id, "How are you?")
        self.assertEqual(len(response2.messages), 2)

        # List messages
        messages = self.client.list_messages(agent.id, limit=10)
        self.assertEqual(len(messages), 4)  # 2 user + 2 assistant

    def test_pagination(self):
        """Test pagination for agents."""
        # Create several agents
        for i in range(5):
            agent = self.client.create_agent(name=f"pagination-test-{i}")
            self.created_agent_ids.append(agent.id)

        # Paginate through
        all_agents = []
        cursor = None
        while True:
            agents, cursor = self.client.list_agents(limit=2, cursor=cursor)
            all_agents.extend(agents)
            if cursor is None:
                break

        # Should have at least 5 agents
        self.assertGreaterEqual(len(all_agents), 5)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""
Simplified Letta SDK Integration Tests for Kelpie

These tests use the ACTUAL Letta Python SDK (letta_client package) to verify
that Kelpie is compatible with real-world Letta SDK usage.

This is a simplified version that tests basic CRUD operations.
Expand this as more endpoints are implemented and verified.

Run with: pytest sdk_tests_simple.py -v
"""

import os
import pytest
from letta_client import Letta as LettaClient, NotFoundError
from letta_client.types import CreateBlockParam


# Configuration
KELPIE_BASE_URL = os.getenv("KELPIE_BASE_URL", "http://localhost:8283")
TEST_MODEL = os.getenv("TEST_MODEL", "claude-3-5-sonnet-20241022")
TEST_EMBEDDING = os.getenv("TEST_EMBEDDING", "openai/text-embedding-3-small")


@pytest.fixture
def client():
    """Create a Letta SDK client pointing at Kelpie"""
    return LettaClient(base_url=KELPIE_BASE_URL)


class TestBasicAgentOperations:
    """Test basic agent CRUD operations"""

    def test_health_check(self, client):
        """Verify server is responsive"""
        # The client should be able to connect
        # If server is down, this will fail during agent creation
        pass

    def test_create_agent(self, client):
        """Test creating an agent with Letta SDK"""
        agent = client.agents.create(
            name="test-create-agent",
            memory_blocks=[
                CreateBlockParam(label="human", value="username: test_user"),
                CreateBlockParam(label="persona", value="You are a helpful test assistant"),
            ],
            model=TEST_MODEL,
            # embedding=TEST_EMBEDDING,  # Optional
        )

        assert agent is not None
        assert agent.id is not None
        assert agent.name == "test-create-agent"
        assert agent.model == TEST_MODEL

        # Cleanup
        client.agents.delete(agent_id=agent.id)

    def test_get_agent(self, client):
        """Test retrieving an agent by ID"""
        # Create agent
        agent = client.agents.create(
            name="test-get-agent",
            memory_blocks=[
                CreateBlockParam(label="human", value="username: test_user"),
            ],
            model=TEST_MODEL,
        )

        try:
            # Retrieve agent
            retrieved = client.agents.get(agent_id=agent.id)

            assert retrieved is not None
            assert retrieved.id == agent.id
            assert retrieved.name == agent.name
            assert retrieved.model == agent.model

        finally:
            # Cleanup
            client.agents.delete(agent_id=agent.id)

    def test_list_agents(self, client):
        """Test listing all agents"""
        # Create a test agent
        agent = client.agents.create(
            name="test-list-agent",
            memory_blocks=[
                CreateBlockParam(label="human", value="username: test_user"),
            ],
            model=TEST_MODEL,
        )

        try:
            # List agents
            agents = client.agents.list()

            assert agents is not None
            assert len(agents) > 0

            # Find our agent in the list
            agent_ids = [a.id for a in agents]
            assert agent.id in agent_ids

        finally:
            # Cleanup
            client.agents.delete(agent_id=agent.id)

    def test_delete_agent(self, client):
        """Test deleting an agent"""
        # Create agent
        agent = client.agents.create(
            name="test-delete-agent",
            memory_blocks=[
                CreateBlockParam(label="human", value="username: test_user"),
            ],
            model=TEST_MODEL,
        )

        agent_id = agent.id

        # Delete agent
        client.agents.delete(agent_id=agent_id)

        # Verify it's gone (should raise NotFoundError or similar)
        with pytest.raises(Exception):  # Could be NotFoundError or generic exception
            client.agents.get(agent_id=agent_id)

    def test_agent_with_multiple_blocks(self, client):
        """Test creating an agent with multiple memory blocks"""
        agent = client.agents.create(
            name="test-multi-block-agent",
            memory_blocks=[
                CreateBlockParam(label="human", value="username: alice\noccupation: engineer"),
                CreateBlockParam(label="persona", value="You are a helpful assistant"),
                CreateBlockParam(label="context", value="Current project: testing Kelpie"),
            ],
            model=TEST_MODEL,
        )

        try:
            assert agent is not None
            assert len(agent.memory_blocks) >= 3

            # Verify block labels
            block_labels = [b.label for b in agent.memory_blocks]
            assert "human" in block_labels
            assert "persona" in block_labels
            assert "context" in block_labels

        finally:
            # Cleanup
            client.agents.delete(agent_id=agent.id)


class TestSchemaCompatibility:
    """Test that response schemas match Letta SDK expectations"""

    def test_agent_has_required_fields(self, client):
        """Verify agent response has all required fields"""
        agent = client.agents.create(
            name="test-schema-agent",
            memory_blocks=[
                CreateBlockParam(label="human", value="test"),
            ],
            model=TEST_MODEL,
        )

        try:
            # Required fields that Letta SDK expects
            assert hasattr(agent, "id")
            assert hasattr(agent, "name")
            assert hasattr(agent, "model")
            assert hasattr(agent, "memory_blocks")

            # Check types
            assert isinstance(agent.id, str)
            assert isinstance(agent.name, str)
            assert isinstance(agent.model, str)
            assert isinstance(agent.memory_blocks, list)

        finally:
            # Cleanup
            client.agents.delete(agent_id=agent.id)

    def test_memory_block_schema(self, client):
        """Verify memory block schema matches expectations"""
        agent = client.agents.create(
            name="test-block-schema",
            memory_blocks=[
                CreateBlockParam(label="persona", value="test value"),
            ],
            model=TEST_MODEL,
        )

        try:
            blocks = agent.memory_blocks
            assert len(blocks) > 0

            block = blocks[0]
            assert hasattr(block, "id")
            assert hasattr(block, "label")
            assert hasattr(block, "value")

            assert isinstance(block.id, str)
            assert isinstance(block.label, str)
            assert isinstance(block.value, str)

        finally:
            # Cleanup
            client.agents.delete(agent_id=agent.id)


class TestErrorHandling:
    """Test error handling and edge cases"""

    def test_get_nonexistent_agent(self, client):
        """Test getting an agent that doesn't exist"""
        with pytest.raises(Exception) as exc_info:
            client.agents.get(agent_id="nonexistent-agent-id-12345")

        # Should be a 404-like error
        error_str = str(exc_info.value).lower()
        assert "not found" in error_str or "404" in error_str or "does not exist" in error_str

    def test_delete_nonexistent_agent(self, client):
        """Test deleting an agent that doesn't exist"""
        with pytest.raises(Exception):
            client.agents.delete(agent_id="nonexistent-agent-id-12345")


# Additional tests to add as features are implemented:

class TestMessaging:
    """Test message sending (requires LLM integration)"""

    @pytest.mark.skip(reason="Requires full LLM integration and API key")
    def test_send_message(self, client):
        """Test sending a message to an agent"""
        # TODO: Implement when message sending is working
        pass


class TestMemoryOperations:
    """Test memory block operations"""

    @pytest.mark.skip(reason="Block operations API not yet verified")
    def test_list_blocks(self, client):
        """Test listing memory blocks"""
        # TODO: Implement when block listing is verified
        pass


class TestToolOperations:
    """Test tool operations"""

    @pytest.mark.skip(reason="Tool operations not yet verified")
    def test_list_tools(self, client):
        """Test listing available tools"""
        # TODO: Implement when tool listing is verified
        pass


# Run all tests
if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

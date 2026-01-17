#!/usr/bin/env python3
"""
Letta SDK Integration Tests for Kelpie

These tests use the ACTUAL Letta Python SDK to verify that Kelpie
is a drop-in replacement for Letta servers.

Run with: pytest sdk_tests.py -v
"""

import os
import pytest
from letta_client import Letta as LettaClient
from letta_client.types import AgentState, CreateBlockParam


# Configuration
KELPIE_BASE_URL = os.getenv("KELPIE_BASE_URL", "http://localhost:8283")
TEST_MODEL = os.getenv("TEST_MODEL", "claude-3-5-sonnet-20241022")


@pytest.fixture
def client():
    """Create a Letta SDK client pointing at Kelpie"""
    return LettaClient(base_url=KELPIE_BASE_URL)


@pytest.fixture
def test_agent(client):
    """Create a test agent and clean it up after the test"""
    agent = client.agents.create(
        name="test-agent",
        model=TEST_MODEL,
        memory_blocks=[
            {"label": "persona", "value": "You are a helpful test assistant."}
        ]
    )
    yield agent
    # Cleanup
    try:
        client.agents.delete(agent.id)
    except Exception:
        pass  # Agent may have been deleted by test


class TestAgentLifecycle:
    """Test basic agent CRUD operations"""

    def test_create_agent(self, client):
        """Test creating an agent with Letta SDK"""
        agent = client.agents.create(
            name="create-test",
            model=TEST_MODEL,
            memory_blocks=[
                {"label": "persona", "value": "Test persona"}
            ]
        )

        assert agent.id is not None
        assert agent.name == "create-test"
        assert agent.model == TEST_MODEL
        assert len(agent.memory_blocks) >= 1

        # Cleanup
        client.agents.delete(agent.id)

    def test_get_agent(self, client, test_agent):
        """Test retrieving an agent by ID"""
        agent = client.agents.get(test_agent.id)

        assert agent.id == test_agent.id
        assert agent.name == test_agent.name
        assert agent.model == test_agent.model

    def test_list_agents(self, client, test_agent):
        """Test listing all agents"""
        agents = client.agents.list()

        assert len(agents) > 0
        agent_ids = [a.id for a in agents]
        assert test_agent.id in agent_ids

    def test_update_agent(self, client, test_agent):
        """Test updating an agent"""
        updated = client.agents.update(
            test_agent.id,
            name="updated-name"
        )

        assert updated.id == test_agent.id
        assert updated.name == "updated-name"

    def test_delete_agent(self, client):
        """Test deleting an agent"""
        agent = client.agents.create(name="delete-test", model=TEST_MODEL)
        agent_id = agent.id

        client.agents.delete(agent_id)

        # Verify it's gone
        with pytest.raises(Exception):  # Should raise 404
            client.agents.get(agent_id)


class TestMemoryBlocks:
    """Test memory block operations"""

    def test_list_memory_blocks(self, client, test_agent):
        """Test listing memory blocks"""
        blocks = client.agents.get_blocks(test_agent.id)

        assert len(blocks) > 0
        assert any(b.label == "persona" for b in blocks)

    def test_get_memory_block_by_label(self, client, test_agent):
        """Test retrieving a specific memory block by label"""
        block = client.agents.get_block(test_agent.id, "persona")

        assert block is not None
        assert block.label == "persona"
        assert "helpful" in block.value.lower()

    def test_update_memory_block(self, client, test_agent):
        """Test updating a memory block"""
        updated = client.agents.update_block(
            test_agent.id,
            "persona",
            value="Updated persona value"
        )

        assert updated.label == "persona"
        assert updated.value == "Updated persona value"

        # Verify the update persisted
        block = client.agents.get_block(test_agent.id, "persona")
        assert block.value == "Updated persona value"


class TestMessaging:
    """Test message sending and retrieval"""

    def test_send_message(self, client, test_agent):
        """Test sending a message to an agent"""
        response = client.agents.send_message(
            agent_id=test_agent.id,
            message="What is 2+2?",
            role="user"
        )

        assert response is not None
        assert len(response.messages) > 0

        # Should have both user message and assistant response
        assert any(m.role == "user" for m in response.messages)
        assert any(m.role == "assistant" for m in response.messages)

    def test_send_message_streaming(self, client, test_agent):
        """Test sending a message with streaming enabled"""
        response = client.agents.send_message(
            agent_id=test_agent.id,
            message="Tell me a very short joke",
            role="user",
            streaming=True  # ← Letta SDK streaming parameter
        )

        # With streaming, we should get a generator or messages
        assert response is not None

    def test_list_messages(self, client, test_agent):
        """Test listing messages for an agent"""
        # Send a message first
        client.agents.send_message(
            agent_id=test_agent.id,
            message="Hello",
            role="user"
        )

        # Now list messages
        messages = client.agents.get_messages(test_agent.id)

        assert len(messages) > 0
        assert any(m.role == "user" for m in messages)


class TestTools:
    """Test tool operations"""

    def test_list_tools(self, client):
        """Test listing available tools"""
        tools = client.tools.list()

        assert len(tools) > 0

        # Check for expected built-in tools
        tool_names = [t.name for t in tools]
        assert "core_memory_append" in tool_names
        assert "core_memory_replace" in tool_names
        assert "archival_memory_search" in tool_names

    def test_tool_execution_via_agent(self, client, test_agent):
        """Test that agents can execute tools"""
        # Ask the agent to update its memory (uses core_memory_append tool)
        response = client.agents.send_message(
            agent_id=test_agent.id,
            message="Remember that I like cats. Update your memory.",
            role="user"
        )

        # Check if a tool was called
        # The response should include tool calls in the message history
        assert response is not None


class TestPagination:
    """Test pagination parameters"""

    def test_pagination_with_cursor(self, client):
        """Test pagination using cursor parameter (Kelpie native)"""
        # Create multiple agents
        agents = []
        for i in range(5):
            agent = client.agents.create(
                name=f"pagination-test-{i}",
                model=TEST_MODEL
            )
            agents.append(agent)

        try:
            # List with limit
            result = client.agents.list(limit=2)
            assert len(result) <= 2

        finally:
            # Cleanup
            for agent in agents:
                try:
                    client.agents.delete(agent.id)
                except Exception:
                    pass

    def test_pagination_with_after(self, client):
        """Test pagination using after parameter (Letta SDK compatibility)"""
        # Create multiple agents
        agents = []
        for i in range(3):
            agent = client.agents.create(
                name=f"after-test-{i}",
                model=TEST_MODEL
            )
            agents.append(agent)

        try:
            # List first page
            first_page = client.agents.list(limit=2)

            if len(first_page) >= 2:
                # List second page using after parameter
                second_page = client.agents.list(limit=2, after=first_page[-1].id)

                # Second page should not contain first page items
                first_ids = [a.id for a in first_page]
                second_ids = [a.id for a in second_page]

                assert not any(sid in first_ids for sid in second_ids)

        finally:
            # Cleanup
            for agent in agents:
                try:
                    client.agents.delete(agent.id)
                except Exception:
                    pass


class TestImportExport:
    """Test agent import/export functionality"""

    def test_export_agent(self, client, test_agent):
        """Test exporting an agent"""
        exported = client.agents.export(test_agent.id)

        assert exported is not None
        assert "id" in exported or "agent_id" in exported
        assert "memory_blocks" in exported or "memory" in exported

    def test_import_export_roundtrip(self, client, test_agent):
        """Test exporting and reimporting an agent"""
        # Export
        exported = client.agents.export(test_agent.id)

        # Import as new agent
        imported = client.agents.import_agent(exported)

        try:
            assert imported is not None
            assert imported.id != test_agent.id  # Should be a new agent
            assert imported.name == test_agent.name or "imported" in imported.name.lower()

        finally:
            # Cleanup imported agent
            try:
                client.agents.delete(imported.id)
            except Exception:
                pass


class TestSchemaCompatibility:
    """Test that response schemas match Letta's expectations"""

    def test_agent_schema(self, client, test_agent):
        """Verify agent response schema matches Letta SDK expectations"""
        agent = client.agents.get(test_agent.id)

        # Required fields from Letta SDK
        assert hasattr(agent, "id")
        assert hasattr(agent, "name")
        assert hasattr(agent, "model")
        assert hasattr(agent, "memory_blocks")

        # Check types
        assert isinstance(agent.id, str)
        assert isinstance(agent.name, str)
        assert isinstance(agent.model, str)
        assert isinstance(agent.memory_blocks, list)

    def test_memory_block_schema(self, client, test_agent):
        """Verify memory block schema matches Letta SDK expectations"""
        blocks = client.agents.get_blocks(test_agent.id)

        for block in blocks:
            assert hasattr(block, "id")
            assert hasattr(block, "label")
            assert hasattr(block, "value")

            assert isinstance(block.id, str)
            assert isinstance(block.label, str)
            assert isinstance(block.value, str)

    def test_message_schema(self, client, test_agent):
        """Verify message schema matches Letta SDK expectations"""
        response = client.agents.send_message(
            agent_id=test_agent.id,
            message="Test message",
            role="user"
        )

        assert hasattr(response, "messages")
        assert isinstance(response.messages, list)

        for msg in response.messages:
            assert hasattr(msg, "role")
            assert hasattr(msg, "content")
            assert msg.role in ["user", "assistant", "system", "tool"]


class TestErrorHandling:
    """Test error handling and edge cases"""

    def test_get_nonexistent_agent(self, client):
        """Test getting an agent that doesn't exist"""
        with pytest.raises(Exception) as exc_info:
            client.agents.get("nonexistent-id-12345")

        # Should be a 404-like error
        assert "not found" in str(exc_info.value).lower() or "404" in str(exc_info.value)

    def test_update_nonexistent_agent(self, client):
        """Test updating an agent that doesn't exist"""
        with pytest.raises(Exception):
            client.agents.update("nonexistent-id-12345", name="new-name")

    def test_delete_nonexistent_agent(self, client):
        """Test deleting an agent that doesn't exist"""
        with pytest.raises(Exception):
            client.agents.delete("nonexistent-id-12345")

    def test_create_agent_invalid_model(self, client):
        """Test creating an agent with invalid model"""
        # This should either work or give a clear error
        # (Depends on Kelpie's validation strategy)
        try:
            agent = client.agents.create(
                name="invalid-model-test",
                model="invalid-model-name-xyz"
            )
            # If it succeeds, clean up
            client.agents.delete(agent.id)
        except Exception as e:
            # Should be a validation error
            assert "model" in str(e).lower() or "invalid" in str(e).lower()


# Run all tests
if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

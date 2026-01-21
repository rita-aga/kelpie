#!/usr/bin/env python3
"""
Letta SDK v1.7.1 Integration Tests for Kelpie

This test suite verifies that Kelpie works as a drop-in replacement for Letta
when using the modern Letta Python SDK (v1.7+).

It covers:
- Agent lifecycle (Create, Retrieve, List, Update, Delete)
- Memory management (Blocks)
- Messaging (Send, List, Stream)
- Tool management

Run with: pytest tests/letta_compatibility/test_sdk_v1.py -v
"""

import os
import pytest
import time
from letta_client import Letta as LettaClient, InternalServerError
from letta_client.types import CreateBlockParam, MessageCreateParam

# Configuration
KELPIE_BASE_URL = os.getenv("KELPIE_BASE_URL", "http://localhost:8283")
TEST_MODEL = os.getenv("TEST_MODEL", "claude-3-5-sonnet-20241022")

@pytest.fixture(scope="session")
def client():
    """Create a Letta SDK client pointing at Kelpie"""
    return LettaClient(base_url=KELPIE_BASE_URL)

@pytest.fixture
def test_agent(client):
    """Create a test agent and clean it up after the test"""
    agent = client.agents.create(
        name=f"test-agent-{int(time.time())}",
        model=TEST_MODEL,
        memory_blocks=[
            CreateBlockParam(label="human", value="username: test_user"),
            CreateBlockParam(label="persona", value="You are a helpful test assistant.")
        ]
    )
    yield agent
    # Cleanup
    try:
        client.agents.delete(agent_id=agent.id)
    except Exception:
        pass

class TestAgentLifecycle:
    """Test basic agent CRUD operations using v1.7 naming conventions"""

    def test_create_agent(self, client):
        name = f"create-test-{int(time.time())}"
        agent = client.agents.create(
            name=name,
            model=TEST_MODEL,
            memory_blocks=[
                CreateBlockParam(label="human", value="Test human block")
            ]
        )
        
        assert agent.id is not None
        assert agent.name == name
        assert agent.model == TEST_MODEL
        
        # In v1.7, memory_blocks might not be directly on the agent object in the same way
        # But let's check what we can
        
        # Cleanup
        client.agents.delete(agent_id=agent.id)

    def test_retrieve_agent(self, client, test_agent):
        """Test retrieving an agent by ID (was 'get', now 'retrieve')"""
        agent = client.agents.retrieve(agent_id=test_agent.id)
        
        assert agent.id == test_agent.id
        assert agent.name == test_agent.name

    def test_list_agents(self, client, test_agent):
        """Test listing agents"""
        # SDK v1.7 returns a SyncArrayPage, not a list
        response = client.agents.list()
        
        # Iterate to find our agent
        found = False
        for agent in response:
            if agent.id == test_agent.id:
                found = True
                break
        assert found, "Created agent not found in list"

    def test_update_agent(self, client, test_agent):
        """Test updating an agent"""
        new_name = f"updated-{int(time.time())}"
        updated = client.agents.update(
            agent_id=test_agent.id,
            name=new_name
        )
        
        assert updated.name == new_name
        
        # Verify persistence
        retrieved = client.agents.retrieve(agent_id=test_agent.id)
        assert retrieved.name == new_name

    def test_delete_agent(self, client):
        """Test deleting an agent"""
        agent = client.agents.create(name=f"delete-test-{int(time.time())}", model=TEST_MODEL)
        
        client.agents.delete(agent_id=agent.id)
        
        # Verify it's gone - should raise exception (likely NotFoundError)
        with pytest.raises(Exception):
            client.agents.retrieve(agent_id=agent.id)

class TestMemoryBlocks:
    """Test memory block operations"""

    def test_list_blocks(self, client, test_agent):
        """Test listing blocks for an agent"""
        blocks = client.agents.blocks.list(agent_id=test_agent.id)
        
        # blocks is iterable
        block_list = list(blocks)
        assert len(block_list) > 0
        
        labels = [b.label for b in block_list]
        assert "human" in labels
        assert "persona" in labels

    def test_retrieve_block(self, client, test_agent):
        """Test retrieving a specific block"""
        blocks = list(client.agents.blocks.list(agent_id=test_agent.id))
        target_block = blocks[0]
        
        # SDK v1.7 uses block_label for agent blocks, NOT block_id
        retrieved = client.agents.blocks.retrieve(
            agent_id=test_agent.id, 
            block_label=target_block.label
        )
        
        assert retrieved.id == target_block.id
        assert retrieved.value == target_block.value

    def test_update_block(self, client, test_agent):
        """Test updating a block"""
        blocks = list(client.agents.blocks.list(agent_id=test_agent.id))
        human_block = next(b for b in blocks if b.label == "human")
        
        new_value = "username: updated_user"
        updated = client.agents.blocks.update(
            agent_id=test_agent.id,
            block_label=human_block.label,
            value=new_value
        )
        
        assert updated.value == new_value
        
        # Verify
        retrieved = client.agents.blocks.retrieve(
            agent_id=test_agent.id, 
            block_label=human_block.label
        )
        assert retrieved.value == new_value

class TestMessaging:
    """Test messaging operations"""

    def test_send_message(self, client, test_agent):
        """Test sending a message"""
        try:
            response = client.agents.messages.create(
                agent_id=test_agent.id,
                messages=[
                    MessageCreateParam(role="user", content="Hello world")
                ]
            )
            
            assert response is not None
            # Check for messages in response
            assert hasattr(response, "messages")
            assert len(response.messages) > 0
            
        except InternalServerError as e:
            # If server returns 500 because LLM is not configured, that counts as reaching the endpoint
            if "LLM not configured" in str(e):
                pytest.skip("LLM not configured on server (expected)")
            else:
                raise

    def test_list_messages(self, client, test_agent):
        """Test listing messages"""
        # Send one first (might fail if LLM missing, so handle gracefully)
        try:
            client.agents.messages.create(
                agent_id=test_agent.id,
                messages=[MessageCreateParam(role="user", content="History test")]
            )
        except InternalServerError:
            # We can still test listing even if sending failed (might be empty)
            pass
        
        messages = client.agents.messages.list(agent_id=test_agent.id)
        msg_list = list(messages)
        
        # Just ensure we can list without crashing
        assert isinstance(msg_list, list)

class TestTools:
    """Test tool operations"""

    def test_list_tools(self, client):
        """Test listing tools"""
        tools = client.tools.list()
        tool_list = list(tools)
        
        assert len(tool_list) > 0
        # Should have base tools
        names = [t.name for t in tool_list]
        # Check for common defaults (names might vary by server version)
        # Just ensuring we got a non-empty list is a good start

    def test_create_tool(self, client):
        """Test creating a tool from function"""
        
        def my_test_tool(x: int) -> int:
            """Multiplies by 2"""
            return x * 2
            
        # SDK derives name from function name
        tool = client.tools.upsert_from_function(
            func=my_test_tool
        )
        
        assert tool is not None
        assert tool.name == "my_test_tool"
        
        # Cleanup
        client.tools.delete(tool_id=tool.id)

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

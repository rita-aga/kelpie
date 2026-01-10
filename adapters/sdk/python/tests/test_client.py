"""Tests for Kelpie client."""

import json
from http.server import BaseHTTPRequestHandler, HTTPServer
from threading import Thread
from unittest import TestCase

from kelpie_client import KelpieClient, Agent, Block, Message, MessageRole


class MockHandler(BaseHTTPRequestHandler):
    """Mock HTTP handler for testing."""

    def log_message(self, format, *args):
        """Suppress log messages."""
        pass

    def do_GET(self):
        """Handle GET requests."""
        # Strip query params for path matching
        path = self.path.split("?")[0]
        if path == "/health":
            self._respond(200, {"status": "ok", "version": "0.1.0", "uptime_seconds": 100})
        elif path == "/v1/agents":
            self._respond(200, {"items": [], "total": 0, "cursor": None})
        elif self.path.startswith("/v1/agents/") and "/blocks" in self.path:
            self._respond(200, [])
        elif self.path.startswith("/v1/agents/") and "/messages" in self.path:
            self._respond(200, [])
        elif self.path.startswith("/v1/agents/"):
            agent_id = self.path.split("/")[3]
            self._respond(
                200,
                {
                    "id": agent_id,
                    "name": "test-agent",
                    "agent_type": "memgpt_agent",
                    "blocks": [],
                    "tool_ids": [],
                    "tags": [],
                    "metadata": {},
                    "created_at": "2024-01-01T00:00:00Z",
                    "updated_at": "2024-01-01T00:00:00Z",
                },
            )
        else:
            self._respond(404, {"code": "not_found", "message": "Not found"})

    def do_POST(self):
        """Handle POST requests."""
        content_length = int(self.headers.get("Content-Length", 0))
        body = json.loads(self.rfile.read(content_length)) if content_length > 0 else {}

        if self.path == "/v1/agents":
            self._respond(
                200,
                {
                    "id": "agent-123",
                    "name": body.get("name", "test-agent"),
                    "agent_type": body.get("agent_type", "memgpt_agent"),
                    "blocks": [
                        {
                            "id": f"block-{i}",
                            "label": b["label"],
                            "value": b["value"],
                            "created_at": "2024-01-01T00:00:00Z",
                            "updated_at": "2024-01-01T00:00:00Z",
                        }
                        for i, b in enumerate(body.get("memory_blocks", []))
                    ],
                    "tool_ids": body.get("tool_ids", []),
                    "tags": body.get("tags", []),
                    "metadata": body.get("metadata", {}),
                    "created_at": "2024-01-01T00:00:00Z",
                    "updated_at": "2024-01-01T00:00:00Z",
                },
            )
        elif "/messages" in self.path:
            agent_id = self.path.split("/")[3]
            self._respond(
                200,
                {
                    "messages": [
                        {
                            "id": "msg-1",
                            "agent_id": agent_id,
                            "role": body.get("role", "user"),
                            "content": body.get("content", ""),
                            "created_at": "2024-01-01T00:00:00Z",
                        },
                        {
                            "id": "msg-2",
                            "agent_id": agent_id,
                            "role": "assistant",
                            "content": "Hello! How can I help you?",
                            "created_at": "2024-01-01T00:00:01Z",
                        },
                    ],
                    "usage": {
                        "prompt_tokens": 10,
                        "completion_tokens": 8,
                        "total_tokens": 18,
                    },
                },
            )
        else:
            self._respond(404, {"code": "not_found", "message": "Not found"})

    def do_PATCH(self):
        """Handle PATCH requests."""
        content_length = int(self.headers.get("Content-Length", 0))
        body = json.loads(self.rfile.read(content_length)) if content_length > 0 else {}

        if "/blocks/" in self.path:
            parts = self.path.split("/")
            block_id = parts[5]
            self._respond(
                200,
                {
                    "id": block_id,
                    "label": "persona",
                    "value": body.get("value", "updated value"),
                    "created_at": "2024-01-01T00:00:00Z",
                    "updated_at": "2024-01-01T00:00:01Z",
                },
            )
        elif self.path.startswith("/v1/agents/"):
            agent_id = self.path.split("/")[3]
            self._respond(
                200,
                {
                    "id": agent_id,
                    "name": body.get("name", "test-agent"),
                    "agent_type": "memgpt_agent",
                    "blocks": [],
                    "tool_ids": [],
                    "tags": body.get("tags", []),
                    "metadata": body.get("metadata", {}),
                    "created_at": "2024-01-01T00:00:00Z",
                    "updated_at": "2024-01-01T00:00:01Z",
                },
            )
        else:
            self._respond(404, {"code": "not_found", "message": "Not found"})

    def do_DELETE(self):
        """Handle DELETE requests."""
        if self.path.startswith("/v1/agents/"):
            self.send_response(204)
            self.end_headers()
        else:
            self._respond(404, {"code": "not_found", "message": "Not found"})

    def _respond(self, status: int, body: dict):
        """Send JSON response."""
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(body).encode())


class TestKelpieClient(TestCase):
    """Tests for KelpieClient."""

    @classmethod
    def setUpClass(cls):
        """Start mock server."""
        cls.server = HTTPServer(("localhost", 0), MockHandler)
        cls.port = cls.server.server_address[1]
        cls.thread = Thread(target=cls.server.serve_forever)
        cls.thread.daemon = True
        cls.thread.start()
        cls.client = KelpieClient(base_url=f"http://localhost:{cls.port}")

    @classmethod
    def tearDownClass(cls):
        """Stop mock server."""
        cls.server.shutdown()

    def test_health(self):
        """Test health check."""
        health = self.client.health()
        self.assertEqual(health["status"], "ok")
        self.assertEqual(health["version"], "0.1.0")

    def test_create_agent(self):
        """Test creating an agent."""
        agent = self.client.create_agent(
            name="test-agent",
            memory_blocks=[{"label": "persona", "value": "I am a test agent."}],
        )
        self.assertEqual(agent.id, "agent-123")
        self.assertEqual(agent.name, "test-agent")
        self.assertEqual(len(agent.blocks), 1)
        self.assertEqual(agent.blocks[0].label, "persona")

    def test_get_agent(self):
        """Test getting an agent."""
        agent = self.client.get_agent("agent-123")
        self.assertEqual(agent.id, "agent-123")
        self.assertEqual(agent.name, "test-agent")

    def test_list_agents(self):
        """Test listing agents."""
        agents, cursor = self.client.list_agents()
        self.assertEqual(len(agents), 0)
        self.assertIsNone(cursor)

    def test_update_agent(self):
        """Test updating an agent."""
        agent = self.client.update_agent("agent-123", name="updated-agent")
        self.assertEqual(agent.id, "agent-123")

    def test_delete_agent(self):
        """Test deleting an agent."""
        # Should not raise
        self.client.delete_agent("agent-123")

    def test_send_message(self):
        """Test sending a message."""
        response = self.client.send_message("agent-123", "Hello!")
        self.assertEqual(len(response.messages), 2)
        self.assertEqual(response.messages[0].role, MessageRole.USER)
        self.assertEqual(response.messages[1].role, MessageRole.ASSISTANT)
        self.assertIsNotNone(response.usage)
        self.assertEqual(response.usage.total_tokens, 18)

    def test_list_messages(self):
        """Test listing messages."""
        messages = self.client.list_messages("agent-123")
        self.assertEqual(len(messages), 0)

    def test_list_blocks(self):
        """Test listing blocks."""
        blocks = self.client.list_blocks("agent-123")
        self.assertEqual(len(blocks), 0)

    def test_update_block(self):
        """Test updating a block."""
        block = self.client.update_block("agent-123", "block-0", value="new value")
        self.assertEqual(block.id, "block-0")
        self.assertEqual(block.value, "new value")


if __name__ == "__main__":
    import unittest

    unittest.main()

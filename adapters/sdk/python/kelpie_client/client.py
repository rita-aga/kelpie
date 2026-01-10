"""Kelpie HTTP client.

A Letta-compatible client for the Kelpie agent runtime.
"""

import json
from typing import Any, Optional
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

from .models import Agent, Block, Message, MessageResponse


class KelpieError(Exception):
    """Base exception for Kelpie client errors."""

    def __init__(self, message: str, code: Optional[str] = None, status: Optional[int] = None):
        super().__init__(message)
        self.code = code
        self.status = status


class KelpieClient:
    """HTTP client for Kelpie server.

    This client provides a Letta-compatible interface for managing agents,
    memory blocks, and messages.

    Example:
        client = KelpieClient(base_url="http://localhost:8283")
        agent = client.create_agent(name="my-agent")
        response = client.send_message(agent.id, "Hello!")
    """

    def __init__(
        self,
        base_url: str = "http://localhost:8283",
        timeout: float = 30.0,
    ):
        """Initialize the Kelpie client.

        Args:
            base_url: The base URL of the Kelpie server.
            timeout: Request timeout in seconds.
        """
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout

    def _request(
        self,
        method: str,
        path: str,
        data: Optional[dict] = None,
    ) -> Any:
        """Make an HTTP request to the server.

        Args:
            method: HTTP method (GET, POST, PATCH, DELETE).
            path: API path (e.g., "/v1/agents").
            data: Request body data (for POST/PATCH).

        Returns:
            Parsed JSON response.

        Raises:
            KelpieError: If the request fails.
        """
        url = f"{self.base_url}{path}"
        headers = {"Content-Type": "application/json"}

        body = json.dumps(data).encode("utf-8") if data else None

        request = Request(url, data=body, headers=headers, method=method)

        try:
            with urlopen(request, timeout=self.timeout) as response:
                if response.status == 204:
                    return None
                body = response.read().decode("utf-8")
                if not body:
                    return None
                return json.loads(body)
        except HTTPError as e:
            error_body = e.read().decode("utf-8")
            try:
                error_data = json.loads(error_body)
                raise KelpieError(
                    message=error_data.get("message", str(e)),
                    code=error_data.get("code"),
                    status=e.code,
                ) from e
            except json.JSONDecodeError:
                raise KelpieError(message=str(e), status=e.code) from e
        except URLError as e:
            raise KelpieError(message=f"Connection failed: {e.reason}") from e

    # =========================================================================
    # Agent operations
    # =========================================================================

    def create_agent(
        self,
        name: str,
        agent_type: str = "memgpt_agent",
        model: Optional[str] = None,
        system: Optional[str] = None,
        description: Optional[str] = None,
        memory_blocks: Optional[list[dict]] = None,
        tool_ids: Optional[list[str]] = None,
        tags: Optional[list[str]] = None,
        metadata: Optional[dict] = None,
    ) -> Agent:
        """Create a new agent.

        Args:
            name: Agent name.
            agent_type: Type of agent (memgpt_agent, letta_v1_agent, react_agent).
            model: Model to use (e.g., "openai/gpt-4o").
            system: System prompt.
            description: Agent description.
            memory_blocks: Initial memory blocks.
            tool_ids: Tool IDs to attach.
            tags: Tags for organization.
            metadata: Additional metadata.

        Returns:
            Created agent.
        """
        data = {
            "name": name,
            "agent_type": agent_type,
            "model": model,
            "system": system,
            "description": description,
            "memory_blocks": memory_blocks or [],
            "tool_ids": tool_ids or [],
            "tags": tags or [],
            "metadata": metadata or {},
        }
        response = self._request("POST", "/v1/agents", data)
        return Agent.from_dict(response)

    def get_agent(self, agent_id: str) -> Agent:
        """Get an agent by ID.

        Args:
            agent_id: The agent's unique identifier.

        Returns:
            The agent.
        """
        response = self._request("GET", f"/v1/agents/{agent_id}")
        return Agent.from_dict(response)

    def list_agents(
        self,
        limit: int = 50,
        cursor: Optional[str] = None,
    ) -> tuple[list[Agent], Optional[str]]:
        """List agents with pagination.

        Args:
            limit: Maximum number of agents to return.
            cursor: Pagination cursor.

        Returns:
            Tuple of (agents, next_cursor).
        """
        params = [f"limit={limit}"]
        if cursor:
            params.append(f"cursor={cursor}")
        query = "&".join(params)
        response = self._request("GET", f"/v1/agents?{query}")
        agents = [Agent.from_dict(a) for a in response.get("items", [])]
        return agents, response.get("cursor")

    def update_agent(
        self,
        agent_id: str,
        name: Optional[str] = None,
        system: Optional[str] = None,
        description: Optional[str] = None,
        tags: Optional[list[str]] = None,
        metadata: Optional[dict] = None,
    ) -> Agent:
        """Update an agent.

        Args:
            agent_id: The agent's unique identifier.
            name: New name.
            system: New system prompt.
            description: New description.
            tags: New tags.
            metadata: New metadata.

        Returns:
            Updated agent.
        """
        data = {}
        if name is not None:
            data["name"] = name
        if system is not None:
            data["system"] = system
        if description is not None:
            data["description"] = description
        if tags is not None:
            data["tags"] = tags
        if metadata is not None:
            data["metadata"] = metadata
        response = self._request("PATCH", f"/v1/agents/{agent_id}", data)
        return Agent.from_dict(response)

    def delete_agent(self, agent_id: str) -> None:
        """Delete an agent.

        Args:
            agent_id: The agent's unique identifier.
        """
        self._request("DELETE", f"/v1/agents/{agent_id}")

    # =========================================================================
    # Block operations
    # =========================================================================

    def list_blocks(self, agent_id: str) -> list[Block]:
        """List memory blocks for an agent.

        Args:
            agent_id: The agent's unique identifier.

        Returns:
            List of memory blocks.
        """
        response = self._request("GET", f"/v1/agents/{agent_id}/blocks")
        return [Block.from_dict(b) for b in response]

    def get_block(self, agent_id: str, block_id: str) -> Block:
        """Get a specific memory block.

        Args:
            agent_id: The agent's unique identifier.
            block_id: The block's unique identifier.

        Returns:
            The memory block.
        """
        response = self._request("GET", f"/v1/agents/{agent_id}/blocks/{block_id}")
        return Block.from_dict(response)

    def update_block(
        self,
        agent_id: str,
        block_id: str,
        value: Optional[str] = None,
        description: Optional[str] = None,
        limit: Optional[int] = None,
    ) -> Block:
        """Update a memory block.

        Args:
            agent_id: The agent's unique identifier.
            block_id: The block's unique identifier.
            value: New value.
            description: New description.
            limit: New size limit.

        Returns:
            Updated block.
        """
        data = {}
        if value is not None:
            data["value"] = value
        if description is not None:
            data["description"] = description
        if limit is not None:
            data["limit"] = limit
        response = self._request("PATCH", f"/v1/agents/{agent_id}/blocks/{block_id}", data)
        return Block.from_dict(response)

    # =========================================================================
    # Message operations
    # =========================================================================

    def send_message(
        self,
        agent_id: str,
        content: str,
        role: str = "user",
    ) -> MessageResponse:
        """Send a message to an agent.

        Args:
            agent_id: The agent's unique identifier.
            content: Message content.
            role: Message role (user, system, tool).

        Returns:
            Message response with generated messages.
        """
        data = {
            "role": role,
            "content": content,
        }
        response = self._request("POST", f"/v1/agents/{agent_id}/messages", data)
        return MessageResponse.from_dict(response)

    def list_messages(
        self,
        agent_id: str,
        limit: int = 100,
        before: Optional[str] = None,
    ) -> list[Message]:
        """List messages for an agent.

        Args:
            agent_id: The agent's unique identifier.
            limit: Maximum number of messages to return.
            before: Return messages before this ID.

        Returns:
            List of messages.
        """
        params = [f"limit={limit}"]
        if before:
            params.append(f"before={before}")
        query = "&".join(params)
        response = self._request("GET", f"/v1/agents/{agent_id}/messages?{query}")
        return [Message.from_dict(m) for m in response]

    # =========================================================================
    # Health check
    # =========================================================================

    def health(self) -> dict:
        """Check server health.

        Returns:
            Health status including version and uptime.
        """
        return self._request("GET", "/health")

"""Kelpie backend adapter for Letta compatibility.

This module provides a backend interface that allows Kelpie to serve as a
drop-in replacement for Letta server, supporting the letta-client SDK.

The Kelpie API is designed to be Letta-compatible, meaning:
- Same REST API endpoints (/v1/agents, /v1/agents/{id}/messages, etc.)
- Same data models (Agent, Block, Message, etc.)
- Same authentication patterns

This backend adapter provides:
1. Configuration management
2. Health/readiness checks
3. Feature capability reporting
4. Migration utilities
"""

import json
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Any, Optional
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError


class BackendFeature(str, Enum):
    """Features supported by the Kelpie backend."""

    AGENTS = "agents"
    MEMORY_BLOCKS = "memory_blocks"
    MESSAGES = "messages"
    TOOLS = "tools"
    ARCHIVAL_MEMORY = "archival_memory"
    SEMANTIC_SEARCH = "semantic_search"
    MCP_TOOLS = "mcp_tools"
    STREAMING = "streaming"


@dataclass
class BackendCapabilities:
    """Capabilities of the Kelpie backend."""

    features: list[BackendFeature] = field(default_factory=list)
    api_version: str = "v1"
    max_agents: Optional[int] = None
    max_memory_blocks_per_agent: Optional[int] = None
    max_message_history: Optional[int] = None
    embedding_model: Optional[str] = None
    llm_models: list[str] = field(default_factory=list)

    def supports(self, feature: BackendFeature) -> bool:
        """Check if a feature is supported."""
        return feature in self.features


@dataclass
class BackendStatus:
    """Status of the Kelpie backend."""

    healthy: bool
    version: str
    uptime_seconds: float
    agents_count: int = 0
    last_check: Optional[datetime] = None


class KelpieBackend:
    """Backend adapter for connecting to Kelpie server.

    This class provides a programmatic interface for managing the Kelpie
    backend connection, including health checks, feature discovery, and
    data migration.

    Example:
        backend = KelpieBackend(base_url="http://localhost:8283")

        # Check connection
        if backend.is_healthy():
            print("Connected to Kelpie")

        # Get capabilities
        caps = backend.get_capabilities()
        if caps.supports(BackendFeature.SEMANTIC_SEARCH):
            print("Semantic search available")
    """

    def __init__(
        self,
        base_url: str = "http://localhost:8283",
        timeout: float = 30.0,
    ):
        """Initialize the Kelpie backend.

        Args:
            base_url: URL of the Kelpie server.
            timeout: Request timeout in seconds.
        """
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout
        self._capabilities: Optional[BackendCapabilities] = None
        self._status: Optional[BackendStatus] = None

    def _request(
        self,
        method: str,
        path: str,
        data: Optional[dict] = None,
    ) -> Any:
        """Make an HTTP request to the server."""
        url = f"{self.base_url}{path}"
        headers = {"Content-Type": "application/json"}
        body = json.dumps(data).encode("utf-8") if data else None
        request = Request(url, data=body, headers=headers, method=method)

        try:
            with urlopen(request, timeout=self.timeout) as response:
                if response.status == 204:
                    return None
                body = response.read().decode("utf-8")
                return json.loads(body) if body else None
        except (HTTPError, URLError) as e:
            return None

    def is_healthy(self) -> bool:
        """Check if the backend is healthy and reachable."""
        try:
            result = self._request("GET", "/health")
            return result is not None and result.get("status") in ("ok", "healthy")
        except Exception:
            return False

    def get_status(self, refresh: bool = False) -> Optional[BackendStatus]:
        """Get the backend status.

        Args:
            refresh: Force a refresh of the status.

        Returns:
            Backend status or None if unavailable.
        """
        if self._status is not None and not refresh:
            return self._status

        result = self._request("GET", "/health")
        if not result:
            return None

        self._status = BackendStatus(
            healthy=result.get("status") in ("ok", "healthy"),
            version=result.get("version", "unknown"),
            uptime_seconds=result.get("uptime_seconds", 0.0),
            agents_count=result.get("agents_count", 0),
            last_check=datetime.now(),
        )
        return self._status

    def get_capabilities(self, refresh: bool = False) -> BackendCapabilities:
        """Get the backend capabilities.

        Args:
            refresh: Force a refresh of capabilities.

        Returns:
            Backend capabilities.
        """
        if self._capabilities is not None and not refresh:
            return self._capabilities

        # Default capabilities for Kelpie
        # These could be fetched from the server if an endpoint exists
        self._capabilities = BackendCapabilities(
            features=[
                BackendFeature.AGENTS,
                BackendFeature.MEMORY_BLOCKS,
                BackendFeature.MESSAGES,
                BackendFeature.TOOLS,
                BackendFeature.ARCHIVAL_MEMORY,
                BackendFeature.SEMANTIC_SEARCH,
                BackendFeature.MCP_TOOLS,
            ],
            api_version="v1",
            llm_models=["openai/gpt-4o", "anthropic/claude-3-5-sonnet"],
        )

        # Try to get capabilities from server
        result = self._request("GET", "/v1/capabilities")
        if result:
            if "features" in result:
                self._capabilities.features = [
                    BackendFeature(f) for f in result["features"]
                    if f in [e.value for e in BackendFeature]
                ]
            if "llm_models" in result:
                self._capabilities.llm_models = result["llm_models"]
            if "embedding_model" in result:
                self._capabilities.embedding_model = result["embedding_model"]

        return self._capabilities

    def test_connection(self) -> tuple[bool, str]:
        """Test the connection to the backend.

        Returns:
            Tuple of (success, message).
        """
        try:
            result = self._request("GET", "/health")
            if result:
                return True, f"Connected to Kelpie {result.get('version', 'unknown')}"
            return False, "Health check returned empty response"
        except Exception as e:
            return False, f"Connection failed: {e}"

    def list_agents(self, limit: int = 50) -> list[dict]:
        """List all agents in the backend.

        Args:
            limit: Maximum number of agents to return.

        Returns:
            List of agent dictionaries.
        """
        result = self._request("GET", f"/v1/agents?limit={limit}")
        if result:
            return result.get("items", [])
        return []

    def get_agent_count(self) -> int:
        """Get the total number of agents."""
        status = self.get_status(refresh=True)
        return status.agents_count if status else 0

"""Tests for Letta compatibility layer.

These tests verify that the Kelpie server API is compatible with Letta clients.
"""

import os
import pytest
from unittest.mock import patch, MagicMock

from kelpie_letta import (
    KelpieBackend,
    check_compatibility,
    LettaCompatibilityReport,
)
from kelpie_letta.backend import BackendFeature, BackendCapabilities, BackendStatus
from kelpie_letta.compat import CompatibilityLevel, EndpointCheck, quick_check


class TestKelpieBackend:
    """Tests for KelpieBackend class."""

    def test_backend_init(self):
        """Test backend initialization."""
        backend = KelpieBackend(base_url="http://localhost:8283")
        assert backend.base_url == "http://localhost:8283"
        assert backend.timeout == 30.0

    def test_backend_init_strips_trailing_slash(self):
        """Test that trailing slash is stripped from base_url."""
        backend = KelpieBackend(base_url="http://localhost:8283/")
        assert backend.base_url == "http://localhost:8283"

    def test_backend_init_custom_timeout(self):
        """Test backend with custom timeout."""
        backend = KelpieBackend(base_url="http://localhost:8283", timeout=60.0)
        assert backend.timeout == 60.0


class TestBackendCapabilities:
    """Tests for BackendCapabilities class."""

    def test_default_capabilities(self):
        """Test default capabilities."""
        caps = BackendCapabilities()
        assert caps.api_version == "v1"
        assert caps.features == []
        assert caps.llm_models == []

    def test_capabilities_supports(self):
        """Test feature support checking."""
        caps = BackendCapabilities(
            features=[BackendFeature.AGENTS, BackendFeature.MESSAGES]
        )
        assert caps.supports(BackendFeature.AGENTS)
        assert caps.supports(BackendFeature.MESSAGES)
        assert not caps.supports(BackendFeature.STREAMING)


class TestBackendStatus:
    """Tests for BackendStatus class."""

    def test_status_creation(self):
        """Test status creation."""
        status = BackendStatus(
            healthy=True,
            version="0.1.0",
            uptime_seconds=3600.0,
            agents_count=5,
        )
        assert status.healthy
        assert status.version == "0.1.0"
        assert status.uptime_seconds == 3600.0
        assert status.agents_count == 5


class TestCompatibilityReport:
    """Tests for LettaCompatibilityReport class."""

    def test_report_creation(self):
        """Test report creation."""
        from datetime import datetime

        report = LettaCompatibilityReport(
            server_url="http://localhost:8283",
            checked_at=datetime.now(),
            server_version="0.1.0",
            compatibility_level=CompatibilityLevel.FULL,
        )
        assert report.is_compatible
        assert report.passed_checks == 0
        assert report.total_checks == 0

    def test_report_passed_checks(self):
        """Test counting passed checks."""
        from datetime import datetime

        report = LettaCompatibilityReport(
            server_url="http://localhost:8283",
            checked_at=datetime.now(),
            endpoint_checks=[
                EndpointCheck("/health", "GET", True, True),
                EndpointCheck("/v1/agents", "GET", True, True),
                EndpointCheck("/v1/agents", "POST", True, False, "Error"),
                EndpointCheck("/v1/tools", "GET", False, False),  # Optional, so passes
            ],
        )
        assert report.passed_checks == 3  # 2 available + 1 optional not required
        assert report.total_checks == 4

    def test_report_to_dict(self):
        """Test converting report to dictionary."""
        from datetime import datetime

        now = datetime.now()
        report = LettaCompatibilityReport(
            server_url="http://localhost:8283",
            checked_at=now,
            server_version="0.1.0",
            compatibility_level=CompatibilityLevel.PARTIAL,
            warnings=["Some warning"],
            recommendations=["Some recommendation"],
        )
        d = report.to_dict()
        assert d["server_url"] == "http://localhost:8283"
        assert d["server_version"] == "0.1.0"
        assert d["compatibility_level"] == "partial"
        assert "Some warning" in d["warnings"]
        assert "Some recommendation" in d["recommendations"]

    def test_report_str(self):
        """Test string representation of report."""
        from datetime import datetime

        report = LettaCompatibilityReport(
            server_url="http://localhost:8283",
            checked_at=datetime.now(),
            compatibility_level=CompatibilityLevel.FULL,
        )
        s = str(report)
        assert "http://localhost:8283" in s
        assert "FULL" in s


class TestEndpointCheck:
    """Tests for EndpointCheck class."""

    def test_required_endpoint_passed(self):
        """Test required endpoint that is available passes."""
        check = EndpointCheck("/health", "GET", expected=True, available=True)
        assert check.passed

    def test_required_endpoint_failed(self):
        """Test required endpoint that is unavailable fails."""
        check = EndpointCheck("/health", "GET", expected=True, available=False)
        assert not check.passed

    def test_optional_endpoint_always_passes(self):
        """Test optional endpoint always passes."""
        check = EndpointCheck("/v1/tools", "GET", expected=False, available=False)
        assert check.passed


class TestCompatibilityLevels:
    """Tests for compatibility level enum."""

    def test_compatibility_levels(self):
        """Test all compatibility levels exist."""
        assert CompatibilityLevel.FULL.value == "full"
        assert CompatibilityLevel.PARTIAL.value == "partial"
        assert CompatibilityLevel.MINIMAL.value == "minimal"
        assert CompatibilityLevel.INCOMPATIBLE.value == "incompatible"


class TestBackendFeatures:
    """Tests for backend feature enum."""

    def test_all_features(self):
        """Test all backend features exist."""
        features = [
            BackendFeature.AGENTS,
            BackendFeature.MEMORY_BLOCKS,
            BackendFeature.MESSAGES,
            BackendFeature.TOOLS,
            BackendFeature.ARCHIVAL_MEMORY,
            BackendFeature.SEMANTIC_SEARCH,
            BackendFeature.MCP_TOOLS,
            BackendFeature.STREAMING,
        ]
        assert len(features) == 8


# Integration tests - require running server
# These are marked as skip by default and can be run with:
# pytest -m integration


@pytest.mark.skip(reason="Requires running Kelpie server")
class TestIntegration:
    """Integration tests with actual Kelpie server."""

    @pytest.fixture
    def server_url(self):
        """Get server URL from environment or use default."""
        return os.getenv("KELPIE_URL", "http://localhost:8283")

    def test_backend_health(self, server_url):
        """Test backend health check against real server."""
        backend = KelpieBackend(base_url=server_url)
        assert backend.is_healthy()

    def test_backend_status(self, server_url):
        """Test getting backend status from real server."""
        backend = KelpieBackend(base_url=server_url)
        status = backend.get_status()
        assert status is not None
        assert status.healthy

    def test_compatibility_check(self, server_url):
        """Test compatibility check against real server."""
        report = check_compatibility(server_url)
        assert report.is_compatible

    def test_quick_check(self, server_url):
        """Test quick compatibility check against real server."""
        assert quick_check(server_url)


@pytest.mark.skip(reason="Requires running Kelpie server and letta-client")
class TestLettaClientIntegration:
    """Integration tests using the actual letta-client SDK.

    These tests verify that the letta-client SDK works correctly
    with a Kelpie server.

    To run these tests:
    1. Start Kelpie server: cargo run -p kelpie-server
    2. Install letta-client: pip install letta-client
    3. Run tests: pytest -m letta_integration
    """

    @pytest.fixture
    def server_url(self):
        """Get server URL from environment or use default."""
        return os.getenv("KELPIE_URL", "http://localhost:8283")

    def test_create_agent(self, server_url):
        """Test creating an agent with letta-client."""
        from letta_client import Letta

        client = Letta(base_url=server_url)
        agent = client.agents.create(name="test-agent")
        assert agent.id is not None
        assert agent.name == "test-agent"

        # Cleanup
        client.agents.delete(agent.id)

    def test_send_message(self, server_url):
        """Test sending a message with letta-client."""
        from letta_client import Letta

        client = Letta(base_url=server_url)

        # Create agent
        agent = client.agents.create(name="test-agent")

        # Send message
        response = client.agents.messages.create(
            agent_id=agent.id,
            messages=[{"role": "user", "content": "Hello!"}],
        )
        assert response is not None
        assert len(response.messages) > 0

        # Cleanup
        client.agents.delete(agent.id)

    def test_memory_blocks(self, server_url):
        """Test memory block operations with letta-client."""
        from letta_client import Letta

        client = Letta(base_url=server_url)

        # Create agent with memory blocks
        agent = client.agents.create(
            name="test-agent",
            memory={
                "persona": "I am a helpful assistant",
                "human": "The user is testing the system",
            },
        )

        # Get memory blocks
        blocks = client.agents.core_memory.get_blocks(agent_id=agent.id)
        assert len(blocks) >= 2

        # Update a block
        client.agents.core_memory.update_block(
            agent_id=agent.id,
            label="persona",
            value="I am a very helpful assistant",
        )

        # Cleanup
        client.agents.delete(agent.id)

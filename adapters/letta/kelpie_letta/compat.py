"""Letta compatibility checking utilities.

This module provides tools to verify that a Kelpie server is compatible
with Letta client expectations, and to diagnose any compatibility issues.
"""

import json
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Any, Optional
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError


class CompatibilityLevel(str, Enum):
    """Compatibility level with Letta."""

    FULL = "full"  # All features work
    PARTIAL = "partial"  # Core features work, some missing
    MINIMAL = "minimal"  # Only basic features work
    INCOMPATIBLE = "incompatible"  # Cannot work with Letta clients


@dataclass
class EndpointCheck:
    """Result of checking a single endpoint."""

    endpoint: str
    method: str
    expected: bool  # Whether this endpoint is required for Letta
    available: bool
    error: Optional[str] = None

    @property
    def passed(self) -> bool:
        """Check passed if available or not expected."""
        return self.available or not self.expected


@dataclass
class LettaCompatibilityReport:
    """Report of Letta compatibility checks."""

    server_url: str
    checked_at: datetime
    server_version: Optional[str] = None
    compatibility_level: CompatibilityLevel = CompatibilityLevel.INCOMPATIBLE
    endpoint_checks: list[EndpointCheck] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    recommendations: list[str] = field(default_factory=list)

    @property
    def is_compatible(self) -> bool:
        """Check if the server is at least minimally compatible."""
        return self.compatibility_level != CompatibilityLevel.INCOMPATIBLE

    @property
    def passed_checks(self) -> int:
        """Number of passed checks."""
        return sum(1 for c in self.endpoint_checks if c.passed)

    @property
    def total_checks(self) -> int:
        """Total number of checks."""
        return len(self.endpoint_checks)

    def to_dict(self) -> dict:
        """Convert to dictionary."""
        return {
            "server_url": self.server_url,
            "checked_at": self.checked_at.isoformat(),
            "server_version": self.server_version,
            "compatibility_level": self.compatibility_level.value,
            "passed_checks": self.passed_checks,
            "total_checks": self.total_checks,
            "endpoint_checks": [
                {
                    "endpoint": c.endpoint,
                    "method": c.method,
                    "expected": c.expected,
                    "available": c.available,
                    "passed": c.passed,
                    "error": c.error,
                }
                for c in self.endpoint_checks
            ],
            "warnings": self.warnings,
            "recommendations": self.recommendations,
        }

    def __str__(self) -> str:
        """Human-readable report."""
        lines = [
            f"Letta Compatibility Report for {self.server_url}",
            f"Checked at: {self.checked_at.isoformat()}",
            f"Server version: {self.server_version or 'unknown'}",
            f"Compatibility: {self.compatibility_level.value.upper()}",
            f"Checks passed: {self.passed_checks}/{self.total_checks}",
            "",
            "Endpoint Checks:",
        ]

        for check in self.endpoint_checks:
            status = "PASS" if check.passed else "FAIL"
            required = "required" if check.expected else "optional"
            lines.append(f"  [{status}] {check.method} {check.endpoint} ({required})")
            if check.error:
                lines.append(f"         Error: {check.error}")

        if self.warnings:
            lines.append("")
            lines.append("Warnings:")
            for w in self.warnings:
                lines.append(f"  - {w}")

        if self.recommendations:
            lines.append("")
            lines.append("Recommendations:")
            for r in self.recommendations:
                lines.append(f"  - {r}")

        return "\n".join(lines)


# Endpoints that Letta clients expect
LETTA_REQUIRED_ENDPOINTS = [
    ("GET", "/health"),
    ("GET", "/v1/agents"),
    ("POST", "/v1/agents"),
    ("GET", "/v1/agents/{id}"),
    ("PATCH", "/v1/agents/{id}"),
    ("DELETE", "/v1/agents/{id}"),
    ("GET", "/v1/agents/{id}/blocks"),
    ("POST", "/v1/agents/{id}/messages"),
    ("GET", "/v1/agents/{id}/messages"),
]

LETTA_OPTIONAL_ENDPOINTS = [
    ("GET", "/v1/tools"),
    ("POST", "/v1/tools"),
    ("GET", "/v1/agents/{id}/archival"),
    ("POST", "/v1/agents/{id}/archival"),
    ("GET", "/v1/sources"),
    ("POST", "/v1/sources"),
]


def check_compatibility(
    base_url: str,
    timeout: float = 10.0,
    test_agent_id: Optional[str] = None,
) -> LettaCompatibilityReport:
    """Check if a Kelpie server is compatible with Letta clients.

    This function tests various endpoints to determine the compatibility
    level and provides recommendations for improving compatibility.

    Args:
        base_url: URL of the Kelpie server.
        timeout: Request timeout in seconds.
        test_agent_id: Optional agent ID to use for testing agent-specific endpoints.

    Returns:
        Compatibility report with detailed results.

    Example:
        report = check_compatibility("http://localhost:8283")
        print(report)
        if report.is_compatible:
            print("Server is compatible with Letta clients")
    """
    base_url = base_url.rstrip("/")
    report = LettaCompatibilityReport(
        server_url=base_url,
        checked_at=datetime.now(),
    )

    def make_request(method: str, path: str) -> tuple[bool, Optional[str]]:
        """Make a test request and return (success, error)."""
        url = f"{base_url}{path}"
        request = Request(url, method=method)
        request.add_header("Content-Type", "application/json")

        try:
            with urlopen(request, timeout=timeout) as response:
                return True, None
        except HTTPError as e:
            if e.code == 404:
                return False, "Not found"
            elif e.code == 405:
                return False, "Method not allowed"
            elif e.code in (400, 422):
                # Bad request is OK - endpoint exists
                return True, None
            else:
                return False, f"HTTP {e.code}"
        except URLError as e:
            return False, f"Connection error: {e.reason}"
        except Exception as e:
            return False, str(e)

    # Check health endpoint first
    success, error = make_request("GET", "/health")
    if not success:
        report.warnings.append("Server is not reachable or health endpoint is missing")
        report.compatibility_level = CompatibilityLevel.INCOMPATIBLE
        report.endpoint_checks.append(
            EndpointCheck("/health", "GET", True, False, error)
        )
        return report

    # Get server version
    try:
        url = f"{base_url}/health"
        with urlopen(url, timeout=timeout) as response:
            data = json.loads(response.read().decode("utf-8"))
            report.server_version = data.get("version")
    except Exception:
        pass

    # Test agent ID for parameterized endpoints
    agent_id = test_agent_id or "test-agent-id"

    # Check required endpoints
    required_passed = 0
    for method, path in LETTA_REQUIRED_ENDPOINTS:
        test_path = path.replace("{id}", agent_id)
        success, error = make_request(method, test_path)

        # For endpoints with {id}, 404 is acceptable (agent doesn't exist)
        if "{id}" in path and error == "Not found":
            success = True
            error = None

        report.endpoint_checks.append(
            EndpointCheck(path, method, True, success, error)
        )
        if success:
            required_passed += 1

    # Check optional endpoints
    optional_passed = 0
    for method, path in LETTA_OPTIONAL_ENDPOINTS:
        test_path = path.replace("{id}", agent_id)
        success, error = make_request(method, test_path)

        if "{id}" in path and error == "Not found":
            success = True
            error = None

        report.endpoint_checks.append(
            EndpointCheck(path, method, False, success, error)
        )
        if success:
            optional_passed += 1

    # Determine compatibility level
    total_required = len(LETTA_REQUIRED_ENDPOINTS)
    total_optional = len(LETTA_OPTIONAL_ENDPOINTS)

    if required_passed == total_required:
        if optional_passed == total_optional:
            report.compatibility_level = CompatibilityLevel.FULL
        elif optional_passed >= total_optional // 2:
            report.compatibility_level = CompatibilityLevel.PARTIAL
            report.warnings.append(
                "Some optional Letta endpoints are missing"
            )
        else:
            report.compatibility_level = CompatibilityLevel.PARTIAL
            report.warnings.append(
                "Many optional Letta endpoints are missing"
            )
    elif required_passed >= total_required * 0.7:
        report.compatibility_level = CompatibilityLevel.MINIMAL
        report.warnings.append(
            "Some required Letta endpoints are missing or not working"
        )
    else:
        report.compatibility_level = CompatibilityLevel.INCOMPATIBLE
        report.warnings.append(
            "Too many required endpoints are missing for Letta compatibility"
        )

    # Add recommendations
    missing_required = [
        c for c in report.endpoint_checks if c.expected and not c.available
    ]
    if missing_required:
        report.recommendations.append(
            f"Implement missing required endpoints: {', '.join(c.endpoint for c in missing_required)}"
        )

    if report.compatibility_level in (
        CompatibilityLevel.FULL,
        CompatibilityLevel.PARTIAL,
    ):
        report.recommendations.append(
            "Run integration tests with letta-client SDK to verify full compatibility"
        )

    return report


def quick_check(base_url: str, timeout: float = 5.0) -> bool:
    """Quick check if a server is Letta-compatible.

    Args:
        base_url: URL of the server.
        timeout: Request timeout.

    Returns:
        True if basic endpoints are available.
    """
    base_url = base_url.rstrip("/")

    try:
        # Check health
        url = f"{base_url}/health"
        with urlopen(url, timeout=timeout):
            pass

        # Check agents list
        url = f"{base_url}/v1/agents"
        with urlopen(url, timeout=timeout):
            pass

        return True
    except Exception:
        return False

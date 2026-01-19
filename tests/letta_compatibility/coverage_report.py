#!/usr/bin/env python3
"""
Letta API Coverage Report Generator

Generates a detailed report showing which Letta endpoints are:
- ✅ Fully implemented
- ⚠️  Partially implemented (returns 501 Not Implemented)
- ❌ Missing completely
- 🔧 Has schema differences

Usage:
    python coverage_report.py
    python coverage_report.py --kelpie-url http://localhost:8283
"""

import argparse
import httpx
from typing import Dict, List, Tuple
from dataclasses import dataclass
from tabulate import tabulate
import json


@dataclass
class EndpointTest:
    method: str
    path: str
    test_payload: Dict = None
    expected_status: int = 200


# Comprehensive list of Letta API endpoints to test
LETTA_ENDPOINTS = [
    # Health
    EndpointTest("GET", "/health", expected_status=200),

    # Agents
    EndpointTest("GET", "/v1/agents", expected_status=200),
    EndpointTest("POST", "/v1/agents", test_payload={
        "name": "coverage-test-agent",
        "model": "claude-3-5-sonnet-20241022"
    }, expected_status=200),
    EndpointTest("GET", "/v1/agents/{agent_id}", expected_status=200),
    EndpointTest("PATCH", "/v1/agents/{agent_id}", test_payload={"name": "updated"}, expected_status=200),
    EndpointTest("DELETE", "/v1/agents/{agent_id}", expected_status=200),

    # Memory Blocks
    EndpointTest("GET", "/v1/agents/{agent_id}/blocks", expected_status=200),
    EndpointTest("GET", "/v1/agents/{agent_id}/blocks/{block_id}", expected_status=200),
    EndpointTest("PATCH", "/v1/agents/{agent_id}/blocks/{block_id}",
                 test_payload={"value": "test"}, expected_status=200),
    EndpointTest("GET", "/v1/agents/{agent_id}/core-memory/blocks/{label}", expected_status=200),
    EndpointTest("PATCH", "/v1/agents/{agent_id}/core-memory/blocks/{label}",
                 test_payload={"value": "test"}, expected_status=200),

    # Messages
    EndpointTest("GET", "/v1/agents/{agent_id}/messages", expected_status=200),
    EndpointTest("POST", "/v1/agents/{agent_id}/messages",
                 test_payload={"role": "user", "content": "test"}, expected_status=200),
    EndpointTest("POST", "/v1/agents/{agent_id}/messages/stream",
                 test_payload={"role": "user", "content": "test"}, expected_status=200),

    # Archival Memory
    EndpointTest("GET", "/v1/agents/{agent_id}/archival", expected_status=200),
    EndpointTest("POST", "/v1/agents/{agent_id}/archival",
                 test_payload={"content": "test memory"}, expected_status=200),

    # Tools
    EndpointTest("GET", "/v1/tools", expected_status=200),
    EndpointTest("POST", "/v1/tools", test_payload={
        "name": "test_tool",
        "description": "Test tool",
        "source_code": "def test_tool(): return 'test'"
    }, expected_status=200),

    # Import/Export
    EndpointTest("POST", "/v1/agents/import", test_payload={"data": {}}, expected_status=200),
    EndpointTest("GET", "/v1/agents/{agent_id}/export", expected_status=200),

    # Projects (Letta feature)
    EndpointTest("GET", "/v1/projects", expected_status=200),
    EndpointTest("POST", "/v1/projects", test_payload={"name": "test-project"}, expected_status=200),

    # Agent Groups (Letta feature)
    EndpointTest("GET", "/v1/agent-groups", expected_status=200),
    EndpointTest("POST", "/v1/agent-groups", test_payload={"name": "test-group"}, expected_status=200),

    # Sources (Document upload - advanced feature)
    EndpointTest("GET", "/v1/sources", expected_status=200),
    EndpointTest("POST", "/v1/sources", expected_status=200),

    # Identities (Multi-tenancy)
    EndpointTest("GET", "/v1/identities", expected_status=200),

    # Templates (Agent presets)
    EndpointTest("GET", "/v1/templates", expected_status=200),

    # MCP Servers
    EndpointTest("GET", "/v1/mcp-servers", expected_status=200),
]


@dataclass
class TestResult:
    endpoint: EndpointTest
    status: str  # "✅ Implemented", "⚠️ Not Implemented", "❌ Missing", "🔧 Schema Issue"
    status_code: int = None
    response: Dict = None
    error: str = None


def test_endpoint(base_url: str, endpoint: EndpointTest, agent_id: str = None, block_id: str = None) -> TestResult:
    """Test a single endpoint"""
    # Replace placeholders in path
    path = endpoint.path
    if "{agent_id}" in path:
        if not agent_id:
            return TestResult(
                endpoint=endpoint,
                status="⏭️  Skipped",
                error="No agent_id available"
            )
        path = path.replace("{agent_id}", agent_id)

    if "{block_id}" in path:
        if not block_id:
            return TestResult(
                endpoint=endpoint,
                status="⏭️  Skipped",
                error="No block_id available"
            )
        path = path.replace("{block_id}", block_id)

    if "{label}" in path:
        path = path.replace("{label}", "persona")

    url = f"{base_url}{path}"

    try:
        if endpoint.method == "GET":
            response = httpx.get(url, timeout=10.0)
        elif endpoint.method == "POST":
            response = httpx.post(url, json=endpoint.test_payload or {}, timeout=10.0)
        elif endpoint.method == "PATCH":
            response = httpx.patch(url, json=endpoint.test_payload or {}, timeout=10.0)
        elif endpoint.method == "DELETE":
            response = httpx.delete(url, timeout=10.0)
        else:
            return TestResult(
                endpoint=endpoint,
                status="❌ Unknown Method",
                error=f"Method {endpoint.method} not supported"
            )

        # Determine status
        if response.status_code == 404:
            status = "❌ Missing"
        elif response.status_code == 501:
            status = "⚠️  Not Implemented"
        elif 200 <= response.status_code < 300:
            status = "✅ Implemented"
        elif 400 <= response.status_code < 500:
            status = "🔧 Client Error"
        else:
            status = "🔧 Server Error"

        try:
            response_data = response.json()
        except Exception:
            response_data = None

        return TestResult(
            endpoint=endpoint,
            status=status,
            status_code=response.status_code,
            response=response_data,
            error=None
        )

    except Exception as e:
        return TestResult(
            endpoint=endpoint,
            status="❌ Error",
            error=str(e)
        )


def run_coverage_tests(base_url: str) -> Tuple[List[TestResult], str, str]:
    """Run all coverage tests and return results along with test agent/block IDs"""
    print(f"🧪 Testing Kelpie API at {base_url}...\n")

    results = []
    test_agent_id = None
    test_block_id = None

    # First, create a test agent for endpoints that need it
    print("📝 Creating test agent...")
    create_agent_result = test_endpoint(base_url, EndpointTest(
        "POST", "/v1/agents",
        test_payload={
            "name": "coverage-test-agent",
            "model": "claude-3-5-sonnet-20241022"
        }
    ))

    if create_agent_result.status == "✅ Implemented" and create_agent_result.response:
        test_agent_id = create_agent_result.response.get("id")
        print(f"   ✅ Test agent created: {test_agent_id}\n")

        # Get blocks for this agent
        blocks_result = test_endpoint(base_url, EndpointTest("GET", "/v1/agents/{agent_id}/blocks"), agent_id=test_agent_id)
        if blocks_result.status == "✅ Implemented" and blocks_result.response:
            blocks = blocks_result.response
            if isinstance(blocks, list) and len(blocks) > 0:
                test_block_id = blocks[0].get("id")
    else:
        print(f"   ⚠️  Could not create test agent: {create_agent_result.error}\n")

    # Test all endpoints
    print("🔍 Testing all endpoints...\n")
    for endpoint in LETTA_ENDPOINTS:
        result = test_endpoint(base_url, endpoint, agent_id=test_agent_id, block_id=test_block_id)
        results.append(result)

    # Cleanup: delete test agent
    if test_agent_id:
        print("\n🧹 Cleaning up test agent...")
        test_endpoint(base_url, EndpointTest("DELETE", "/v1/agents/{agent_id}"), agent_id=test_agent_id)

    return results, test_agent_id, test_block_id


def print_coverage_report(results: List[TestResult]):
    """Print coverage report"""
    print("\n" + "=" * 80)
    print("  LETTA API COVERAGE REPORT")
    print("=" * 80)

    # Count by status
    status_counts = {}
    for result in results:
        status = result.status.split()[0]  # Get emoji part
        status_counts[status] = status_counts.get(status, 0) + 1

    # Summary
    total = len(results)
    implemented = status_counts.get("✅", 0)
    not_implemented = status_counts.get("⚠️", 0)
    missing = status_counts.get("❌", 0)
    errors = status_counts.get("🔧", 0)

    print(f"\n📊 Summary:")
    print(f"   Total endpoints tested: {total}")
    print(f"   ✅ Fully implemented: {implemented} ({implemented/total*100:.1f}%)")
    print(f"   ⚠️  Not implemented (501): {not_implemented} ({not_implemented/total*100:.1f}%)")
    print(f"   ❌ Missing (404): {missing} ({missing/total*100:.1f}%)")
    print(f"   🔧 Errors: {errors} ({errors/total*100:.1f}%)")

    # Detailed table
    print("\n" + "-" * 80)
    print("ENDPOINT DETAILS:")
    print("-" * 80)

    table_data = []
    for result in results:
        status_code = result.status_code if result.status_code else "N/A"
        error = result.error[:50] if result.error else ""

        table_data.append([
            result.status,
            result.endpoint.method,
            result.endpoint.path,
            status_code,
            error
        ])

    print(tabulate(table_data, headers=["Status", "Method", "Path", "Code", "Error"], tablefmt="grid"))

    # Recommendations
    print("\n" + "=" * 80)
    print("📝 RECOMMENDATIONS:")
    print("=" * 80)

    if missing > 0:
        print(f"\n❌ {missing} endpoints are completely missing (404):")
        for result in results:
            if "❌" in result.status and "Missing" in result.status:
                print(f"   - {result.endpoint.method} {result.endpoint.path}")

    if not_implemented > 0:
        print(f"\n⚠️  {not_implemented} endpoints return 501 Not Implemented:")
        for result in results:
            if "⚠️" in result.status:
                print(f"   - {result.endpoint.method} {result.endpoint.path}")
        print("   Consider implementing these or documenting why they're deferred")

    if errors > 0:
        print(f"\n🔧 {errors} endpoints have errors:")
        for result in results:
            if "🔧" in result.status or "Error" in result.status:
                print(f"   - {result.endpoint.method} {result.endpoint.path}: {result.error or result.status_code}")

    # Compatibility score
    coverage_pct = (implemented / total * 100) if total > 0 else 0
    print("\n" + "=" * 80)
    print(f"📈 Overall Coverage: {coverage_pct:.1f}%")

    if coverage_pct >= 90:
        print("   ✅ EXCELLENT: High compatibility with Letta API")
    elif coverage_pct >= 75:
        print("   ⚠️  GOOD: Most endpoints are implemented")
    elif coverage_pct >= 50:
        print("   ⚠️  PARTIAL: Many endpoints need implementation")
    else:
        print("   ❌ LOW: Significant work needed for Letta compatibility")

    print("=" * 80)


def main():
    parser = argparse.ArgumentParser(description="Generate Letta API coverage report")
    parser.add_argument(
        "--kelpie-url",
        default="http://localhost:8283",
        help="Kelpie server URL (default: http://localhost:8283)"
    )
    args = parser.parse_args()

    results, agent_id, block_id = run_coverage_tests(args.kelpie_url)
    print_coverage_report(results)

    # Exit with error if coverage is low
    total = len(results)
    implemented = sum(1 for r in results if "✅" in r.status)
    coverage_pct = (implemented / total * 100) if total > 0 else 0

    if coverage_pct < 75:
        exit(1)


if __name__ == "__main__":
    main()

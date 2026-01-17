#!/usr/bin/env python3
"""
OpenAPI Specification Comparison Tool

Compares Kelpie's API against Letta's OpenAPI specification to find:
- Missing endpoints
- Extra endpoints
- Schema mismatches
- Parameter differences

Usage:
    python openapi_diff.py
    python openapi_diff.py --letta-url http://localhost:8080 --kelpie-url http://localhost:8283
"""

import argparse
import json
import sys
from typing import Dict, List, Set, Tuple
from dataclasses import dataclass
import httpx
from deepdiff import DeepDiff
from tabulate import tabulate


@dataclass
class EndpointInfo:
    path: str
    method: str
    operation_id: str = None
    summary: str = None
    parameters: List[str] = None
    request_body: Dict = None
    responses: Dict = None


@dataclass
class ComparisonResult:
    missing_endpoints: List[EndpointInfo]
    extra_endpoints: List[EndpointInfo]
    matching_endpoints: List[Tuple[EndpointInfo, EndpointInfo]]
    schema_differences: Dict[str, Dict]


def fetch_openapi_spec(base_url: str) -> Dict:
    """Fetch OpenAPI specification from a server"""
    try:
        # Try common OpenAPI endpoints
        endpoints = ["/openapi.json", "/openapi", "/api/openapi.json", "/docs/openapi.json"]

        for endpoint in endpoints:
            try:
                response = httpx.get(f"{base_url}{endpoint}", timeout=10.0)
                if response.status_code == 200:
                    return response.json()
            except Exception:
                continue

        print(f"❌ Could not fetch OpenAPI spec from {base_url}")
        print(f"   Tried: {endpoints}")
        return None

    except Exception as e:
        print(f"❌ Error fetching OpenAPI spec from {base_url}: {e}")
        return None


def parse_endpoints(spec: Dict) -> List[EndpointInfo]:
    """Parse endpoints from OpenAPI specification"""
    endpoints = []

    if not spec or "paths" not in spec:
        return endpoints

    for path, path_item in spec["paths"].items():
        for method, operation in path_item.items():
            if method in ["get", "post", "put", "patch", "delete"]:
                parameters = []
                if "parameters" in operation:
                    parameters = [p.get("name", "unknown") for p in operation["parameters"]]

                endpoints.append(EndpointInfo(
                    path=path,
                    method=method.upper(),
                    operation_id=operation.get("operationId"),
                    summary=operation.get("summary"),
                    parameters=parameters,
                    request_body=operation.get("requestBody"),
                    responses=operation.get("responses")
                ))

    return endpoints


def endpoint_key(endpoint: EndpointInfo) -> str:
    """Generate a unique key for an endpoint"""
    # Normalize path (remove trailing slashes, etc.)
    path = endpoint.path.rstrip("/")
    return f"{endpoint.method} {path}"


def compare_endpoints(letta_spec: Dict, kelpie_spec: Dict) -> ComparisonResult:
    """Compare endpoints between Letta and Kelpie"""
    letta_endpoints = parse_endpoints(letta_spec)
    kelpie_endpoints = parse_endpoints(kelpie_spec)

    # Create lookup dictionaries
    letta_map = {endpoint_key(e): e for e in letta_endpoints}
    kelpie_map = {endpoint_key(e): e for e in kelpie_endpoints}

    # Find missing and extra endpoints
    letta_keys = set(letta_map.keys())
    kelpie_keys = set(kelpie_map.keys())

    missing = [letta_map[k] for k in (letta_keys - kelpie_keys)]
    extra = [kelpie_map[k] for k in (kelpie_keys - letta_keys)]
    matching_keys = letta_keys & kelpie_keys

    # Compare matching endpoints for schema differences
    schema_diffs = {}
    matching = []

    for key in matching_keys:
        letta_ep = letta_map[key]
        kelpie_ep = kelpie_map[key]
        matching.append((letta_ep, kelpie_ep))

        # Compare request/response schemas
        diff = {}

        # Compare parameters
        if letta_ep.parameters != kelpie_ep.parameters:
            diff["parameters"] = {
                "letta": letta_ep.parameters,
                "kelpie": kelpie_ep.parameters
            }

        # Compare request body (if exists)
        if letta_ep.request_body or kelpie_ep.request_body:
            body_diff = DeepDiff(
                letta_ep.request_body or {},
                kelpie_ep.request_body or {},
                ignore_order=True
            )
            if body_diff:
                diff["request_body"] = body_diff

        # Compare response schemas
        if letta_ep.responses or kelpie_ep.responses:
            response_diff = DeepDiff(
                letta_ep.responses or {},
                kelpie_ep.responses or {},
                ignore_order=True
            )
            if response_diff:
                diff["responses"] = response_diff

        if diff:
            schema_diffs[key] = diff

    return ComparisonResult(
        missing_endpoints=missing,
        extra_endpoints=extra,
        matching_endpoints=matching,
        schema_differences=schema_diffs
    )


def print_results(result: ComparisonResult):
    """Print comparison results in a readable format"""
    print("\n" + "=" * 80)
    print("  LETTA vs KELPIE API COMPARISON")
    print("=" * 80)

    # Summary
    total_letta = len(result.missing_endpoints) + len(result.matching_endpoints)
    total_kelpie = len(result.extra_endpoints) + len(result.matching_endpoints)

    print(f"\n📊 Summary:")
    print(f"   Letta endpoints: {total_letta}")
    print(f"   Kelpie endpoints: {total_kelpie}")
    print(f"   Matching: {len(result.matching_endpoints)}")
    print(f"   Missing in Kelpie: {len(result.missing_endpoints)}")
    print(f"   Extra in Kelpie: {len(result.extra_endpoints)}")
    print(f"   Schema differences: {len(result.schema_differences)}")

    # Missing endpoints
    if result.missing_endpoints:
        print("\n" + "-" * 80)
        print("❌ MISSING ENDPOINTS (in Letta but not in Kelpie):")
        print("-" * 80)

        table_data = []
        for ep in sorted(result.missing_endpoints, key=lambda e: (e.path, e.method)):
            table_data.append([
                ep.method,
                ep.path,
                ep.summary or ""
            ])

        print(tabulate(table_data, headers=["Method", "Path", "Summary"], tablefmt="grid"))

    # Extra endpoints
    if result.extra_endpoints:
        print("\n" + "-" * 80)
        print("✨ EXTRA ENDPOINTS (in Kelpie but not in Letta):")
        print("-" * 80)

        table_data = []
        for ep in sorted(result.extra_endpoints, key=lambda e: (e.path, e.method)):
            table_data.append([
                ep.method,
                ep.path,
                ep.summary or ""
            ])

        print(tabulate(table_data, headers=["Method", "Path", "Summary"], tablefmt="grid"))

    # Schema differences
    if result.schema_differences:
        print("\n" + "-" * 80)
        print("⚠️  SCHEMA DIFFERENCES (matching endpoints with different schemas):")
        print("-" * 80)

        for endpoint_key, diffs in result.schema_differences.items():
            print(f"\n{endpoint_key}:")
            for diff_type, diff_value in diffs.items():
                print(f"  {diff_type}:")
                if isinstance(diff_value, dict) and "letta" in diff_value:
                    print(f"    Letta:  {diff_value['letta']}")
                    print(f"    Kelpie: {diff_value['kelpie']}")
                else:
                    print(f"    {json.dumps(diff_value, indent=6)}")

    # Matching endpoints
    print("\n" + "-" * 80)
    print(f"✅ MATCHING ENDPOINTS ({len(result.matching_endpoints)}):")
    print("-" * 80)

    table_data = []
    for letta_ep, kelpie_ep in sorted(result.matching_endpoints, key=lambda x: (x[0].path, x[0].method)):
        has_diff = endpoint_key(letta_ep) in result.schema_differences
        status = "⚠️ " if has_diff else "✅"

        table_data.append([
            status,
            letta_ep.method,
            letta_ep.path,
            letta_ep.summary or ""
        ])

    print(tabulate(table_data, headers=["Status", "Method", "Path", "Summary"], tablefmt="grid"))

    # Compatibility score
    print("\n" + "=" * 80)
    total_endpoints = total_letta
    implemented = len(result.matching_endpoints)
    compatibility_pct = (implemented / total_endpoints * 100) if total_endpoints > 0 else 0

    print(f"📈 Compatibility Score: {compatibility_pct:.1f}% ({implemented}/{total_endpoints} endpoints)")

    if compatibility_pct >= 90:
        print("   ✅ EXCELLENT: Kelpie is highly compatible with Letta")
    elif compatibility_pct >= 75:
        print("   ⚠️  GOOD: Most Letta endpoints are implemented")
    elif compatibility_pct >= 50:
        print("   ⚠️  PARTIAL: Many Letta endpoints are missing")
    else:
        print("   ❌ LOW: Significant compatibility gaps")

    print("=" * 80)


def generate_markdown_report(result: ComparisonResult, output_file: str):
    """Generate a markdown report of the comparison"""
    with open(output_file, "w") as f:
        f.write("# Letta API Compatibility Report\n\n")
        f.write(f"**Generated:** {import_datetime().datetime.now().isoformat()}\n\n")

        # Summary
        total_letta = len(result.missing_endpoints) + len(result.matching_endpoints)
        implemented = len(result.matching_endpoints)
        compatibility_pct = (implemented / total_letta * 100) if total_letta > 0 else 0

        f.write("## Summary\n\n")
        f.write(f"- **Compatibility Score:** {compatibility_pct:.1f}%\n")
        f.write(f"- **Implemented:** {implemented}/{total_letta} endpoints\n")
        f.write(f"- **Missing:** {len(result.missing_endpoints)}\n")
        f.write(f"- **Extra:** {len(result.extra_endpoints)}\n")
        f.write(f"- **Schema Differences:** {len(result.schema_differences)}\n\n")

        # Missing endpoints
        if result.missing_endpoints:
            f.write("## Missing Endpoints\n\n")
            f.write("| Method | Path | Summary |\n")
            f.write("|--------|------|----------|\n")
            for ep in sorted(result.missing_endpoints, key=lambda e: (e.path, e.method)):
                f.write(f"| {ep.method} | {ep.path} | {ep.summary or ''} |\n")
            f.write("\n")

        # Matching endpoints
        f.write("## Implemented Endpoints\n\n")
        f.write("| Status | Method | Path | Summary |\n")
        f.write("|--------|--------|------|----------|\n")
        for letta_ep, kelpie_ep in sorted(result.matching_endpoints, key=lambda x: (x[0].path, x[0].method)):
            has_diff = endpoint_key(letta_ep) in result.schema_differences
            status = "⚠️ Diff" if has_diff else "✅"
            f.write(f"| {status} | {letta_ep.method} | {letta_ep.path} | {letta_ep.summary or ''} |\n")
        f.write("\n")

        # Schema differences
        if result.schema_differences:
            f.write("## Schema Differences\n\n")
            for endpoint_key, diffs in result.schema_differences.items():
                f.write(f"### {endpoint_key}\n\n")
                for diff_type, diff_value in diffs.items():
                    f.write(f"**{diff_type}:**\n")
                    f.write(f"```json\n{json.dumps(diff_value, indent=2)}\n```\n\n")

    print(f"\n📝 Markdown report saved to: {output_file}")


def import_datetime():
    """Lazy import datetime to avoid issues if not needed"""
    import datetime
    return datetime


def main():
    parser = argparse.ArgumentParser(description="Compare Kelpie and Letta APIs")
    parser.add_argument(
        "--letta-url",
        default="http://localhost:8080",
        help="Letta server URL (default: http://localhost:8080)"
    )
    parser.add_argument(
        "--kelpie-url",
        default="http://localhost:8283",
        help="Kelpie server URL (default: http://localhost:8283)"
    )
    parser.add_argument(
        "--output",
        default="docs/LETTA_COMPATIBILITY_REPORT.md",
        help="Output markdown report file"
    )
    args = parser.parse_args()

    print("🔍 Fetching OpenAPI specifications...")
    print(f"   Letta:  {args.letta_url}")
    print(f"   Kelpie: {args.kelpie_url}")

    letta_spec = fetch_openapi_spec(args.letta_url)
    kelpie_spec = fetch_openapi_spec(args.kelpie_url)

    if not letta_spec:
        print("\n❌ Could not fetch Letta OpenAPI spec. Is the Letta server running?")
        print(f"   Tried: {args.letta_url}/openapi.json")
        sys.exit(1)

    if not kelpie_spec:
        print("\n❌ Could not fetch Kelpie OpenAPI spec. Is the Kelpie server running?")
        print(f"   Tried: {args.kelpie_url}/openapi.json")
        print("\n💡 Tip: Kelpie needs to expose an OpenAPI spec at /openapi.json")
        print("   You can generate this using the `utoipa` crate in Rust.")
        sys.exit(1)

    print("✅ Specifications fetched successfully\n")
    print("📊 Comparing APIs...")

    result = compare_endpoints(letta_spec, kelpie_spec)
    print_results(result)

    # Generate markdown report
    generate_markdown_report(result, args.output)

    # Exit with error code if compatibility is low
    total_letta = len(result.missing_endpoints) + len(result.matching_endpoints)
    implemented = len(result.matching_endpoints)
    compatibility_pct = (implemented / total_letta * 100) if total_letta > 0 else 0

    if compatibility_pct < 90:
        sys.exit(1)


if __name__ == "__main__":
    main()

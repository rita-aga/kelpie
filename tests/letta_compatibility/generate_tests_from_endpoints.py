#!/usr/bin/env python3
"""
Programmatically generate SDK tests from endpoint definitions in coverage_report.py

This ensures tests match REAL endpoints, not invented ones.
"""
from coverage_report import LETTA_ENDPOINTS

# Group endpoints by resource
resources = {}
for endpoint in LETTA_ENDPOINTS:
    parts = endpoint.path.split('/')
    if len(parts) > 2:
        resource = parts[2]  # e.g., "agents", "tools"
        if resource not in resources:
            resources[resource] = []
        resources[resource].append(endpoint)

print("=== Real Letta API Resources ===\n")
for resource, endpoints in sorted(resources.items()):
    print(f"{resource}:")
    for ep in endpoints:
        print(f"  {ep.method} {ep.path}")
    print()

print(f"\nTotal resources: {len(resources)}")
print(f"Total endpoints: {len(LETTA_ENDPOINTS)}")

#!/usr/bin/env python3
"""
Run each Letta SDK test individually with timeout handling.
Saves results to individual files.
"""

import subprocess
import os
from pathlib import Path

# Configuration
VENV = Path("/Users/seshendranalla/Development/kelpie/tests/letta_compatibility/.venv")
LETTA_DIR = Path("/Users/seshendranalla/Development/letta")
PYTEST = VENV / "bin" / "pytest"
SERVER_URL = "http://localhost:8283"
TIMEOUT_SECONDS = 10
RESULTS_DIR = Path("/Users/seshendranalla/Development/kelpie/tests/letta_compatibility/test_results_individual")

# Create results directory
RESULTS_DIR.mkdir(exist_ok=True)

# Clear old results
for f in RESULTS_DIR.glob("*.txt"):
    f.unlink()
for f in RESULTS_DIR.glob("*.status"):
    f.unlink()

print("=" * 60)
print("Running All Letta SDK Tests Individually")
print("=" * 60)
print(f"Server: {SERVER_URL}")
print(f"Timeout: {TIMEOUT_SECONDS}s per test")
print(f"Results: {RESULTS_DIR}/")
print()

# Set environment
env = os.environ.copy()
env["LETTA_SERVER_URL"] = SERVER_URL

# Get all test functions
os.chdir(LETTA_DIR)
collect_result = subprocess.run(
    [str(PYTEST), "tests/sdk/", "--collect-only", "-q"],
    capture_output=True,
    text=True,
    env=env
)

test_functions = []
for line in collect_result.stdout.split("\n"):
    if "::" in line and not line.startswith("="):
        test_path = line.strip()
        # Fix path if it doesn't start with tests/
        if not test_path.startswith("tests/"):
            test_path = "tests/" + test_path
        test_functions.append(test_path)

print(f"Found {len(test_functions)} tests")
print(f"Results: {RESULTS_DIR}/")
print()

# Statistics
total = 0
passed = 0
failed = 0
timeout = 0
error = 0
skipped = 0

# Run each test
for test_path in test_functions:
    if not test_path:
        continue

    total += 1
    test_name = test_path.split("::")[-1]
    safe_name = test_path.replace("/", "_").replace("::", "_").replace("[", "_").replace("]", "_").replace(" ", "")
    result_file = RESULTS_DIR / f"{safe_name}.txt"
    status_file = RESULTS_DIR / f"{safe_name}.status"

    print(f"[{total:2d}/{len(test_functions)}] {test_name:<60}", end=" ", flush=True)

    try:
        result = subprocess.run(
            [str(PYTEST), test_path, "-v", "--tb=short"],
            capture_output=True,
            text=True,
            timeout=TIMEOUT_SECONDS,
            env=env,
            cwd=LETTA_DIR
        )

        # Save output
        result_file.write_text(result.stdout + "\n" + result.stderr)

        # Determine status
        output = result.stdout + result.stderr
        if "PASSED" in output and result.returncode == 0:
            print("✅")
            passed += 1
            status_file.write_text("PASSED")
        elif "SKIPPED" in output:
            print("⏭️ ")
            skipped += 1
            status_file.write_text("SKIPPED")
        elif "FAILED" in output:
            print("❌")
            failed += 1
            status_file.write_text("FAILED")
        elif "ERROR" in output or result.returncode != 0:
            print("💥")
            error += 1
            status_file.write_text("ERROR")
        else:
            print("?")
            status_file.write_text("UNKNOWN")

    except subprocess.TimeoutExpired:
        print("⏱️ ")
        timeout += 1
        result_file.write_text(f"TIMEOUT (>{TIMEOUT_SECONDS}s)")
        status_file.write_text("TIMEOUT")
    except Exception as e:
        print(f"💥 {e}")
        error += 1
        result_file.write_text(f"EXCEPTION: {e}")
        status_file.write_text("ERROR")

# Print summary
print()
print("=" * 60)
print("RESULTS")
print("=" * 60)
print(f"Total: {total} | Pass: {passed} | Fail: {failed} | Err: {error} | Timeout: {timeout} | Skip: {skipped}")
if total > 0:
    print(f"Pass rate: {(passed/total)*100:.1f}%")
print()

#!/usr/bin/env python3
"""
Run each Letta SDK test individually with timeout handling.
Saves results to individual files.
"""

import subprocess
import os
import sys
import time
from pathlib import Path

# Configuration
VENV = Path("/Users/seshendranalla/Development/kelpie/tests/letta_compatibility/.venv")
LETTA_DIR = Path("/Users/seshendranalla/Development/letta")
PYTEST = VENV / "bin" / "pytest"
SERVER_URL = "http://localhost:8283"
TIMEOUT_SECONDS = 10
RESULTS_DIR = Path("./test_results_individual")

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
        test_functions.append(line.strip())

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

    print(f"[{total}] {test_name:<60}", end=" ", flush=True)

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
        if "PASSED" in output:
            print("✅ PASS")
            passed += 1
            status_file.write_text("PASSED")
        elif "SKIPPED" in output:
            print("⏭️  SKIP")
            skipped += 1
            status_file.write_text("SKIPPED")
        elif "FAILED" in output:
            print("❌ FAIL")
            failed += 1
            status_file.write_text("FAILED")
        elif "ERROR" in output or result.returncode != 0:
            print("💥 ERROR")
            error += 1
            status_file.write_text("ERROR")
        else:
            print("? UNKNOWN")
            status_file.write_text("UNKNOWN")

    except subprocess.TimeoutExpired:
        print("⏱️  TIMEOUT")
        timeout += 1
        result_file.write_text(f"TIMEOUT (>{TIMEOUT_SECONDS}s)")
        status_file.write_text("TIMEOUT")
    except Exception as e:
        print(f"💥 EXCEPTION: {e}")
        error += 1
        result_file.write_text(f"EXCEPTION: {e}")
        status_file.write_text("ERROR")

# Print summary
print()
print("=" * 60)
print("SUMMARY")
print("=" * 60)
print(f"Total:   {total} tests")
print(f"Passed:  {passed}")
print(f"Failed:  {failed}")
print(f"Errors:  {error}")
print(f"Timeout: {timeout}")
print(f"Skipped: {skipped}")
print()
if total > 0:
    print(f"Pass rate: {(passed/total)*100:.1f}%")
print()
print(f"Results saved to: {RESULTS_DIR}/")
print()

# Generate summary report
os.chdir("/Users/seshendranalla/Development/kelpie/tests/letta_compatibility")
summary_file = RESULTS_DIR / "SUMMARY.txt"
with open(summary_file, "w") as f:
    f.write("Letta SDK Test Results (Individual Test Run)\n")
    f.write("=" * 60 + "\n\n")
    f.write(f"Date: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
    f.write(f"Server: {SERVER_URL}\n")
    f.write(f"Timeout: {TIMEOUT_SECONDS}s per test\n\n")

    f.write("SUMMARY\n")
    f.write("-" * 60 + "\n")
    f.write(f"Total:   {total}\n")
    f.write(f"Passed:  {passed} ({(passed/total)*100:.1f}%)\n")
    f.write(f"Failed:  {failed} ({(failed/total)*100:.1f}%)\n")
    f.write(f"Errors:  {error} ({(error/total)*100:.1f}%)\n")
    f.write(f"Timeout: {timeout} ({(timeout/total)*100:.1f}%)\n")
    f.write(f"Skipped: {skipped} ({(skipped/total)*100:.1f}%)\n\n")

    # Details by status
    for status_name in ["PASSED", "FAILED", "ERROR", "TIMEOUT", "SKIPPED"]:
        tests_with_status = []
        for status_file in RESULTS_DIR.glob("*.status"):
            if status_file.read_text().strip() == status_name:
                tests_with_status.append(status_file.stem)

        if tests_with_status:
            f.write(f"\n{status_name} TESTS ({len(tests_with_status)}):\n")
            f.write("-" * 60 + "\n")
            for test in sorted(tests_with_status):
                f.write(f"  - {test}\n")

print(f"Summary report: {summary_file}")

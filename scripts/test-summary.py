#!/usr/bin/env python3
"""
Test Summarizer for Kelpie
Runs cargo test and produces a clean, agent-friendly summary.
"""
import subprocess
import sys
import re
import time
from dataclasses import dataclass
from typing import List, Optional

@dataclass
class TestFailure:
    name: str
    module: str
    message: str
    location: Optional[str] = None

def run_tests():
    print("🚀 Running cargo test... (this may take a minute)")
    start_time = time.time()
    
    # Run cargo test and capture output
    result = subprocess.run(
        ["cargo", "test", "--workspace", "--all-features"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    
    duration = time.time() - start_time
    return result, duration

def parse_output(stdout: str, stderr: str) -> List[TestFailure]:
    failures = []
    
    # Capture failure sections
    # Pattern: "---- module::test_name stdout ----"
    failure_blocks = re.split(r'---- (.*?) stdout ----', stdout)
    
    # The first split is pre-failure content, subsequent are (name, output) pairs
    if len(failure_blocks) > 1:
        for i in range(1, len(failure_blocks), 2):
            full_name = failure_blocks[i]
            output = failure_blocks[i+1]
            
            # Extract clean error message (usually lines starting with 'thread' or specific assertions)
            message_lines = []
            for line in output.splitlines():
                if "thread" in line and "panicked at" in line:
                    message_lines.append(line.strip())
                elif line.strip().startswith("assertion failed"):
                    message_lines.append(line.strip())
                elif line.strip().startswith("left:") or line.strip().startswith("right:"):
                    message_lines.append(line.strip())
            
            clean_message = "\n".join(message_lines) if message_lines else output.strip()[:200] + "..."
            
            # Module/Name split
            parts = full_name.rsplit('::', 1)
            if len(parts) == 2:
                module, name = parts
            else:
                module, name = "unknown", full_name
                
            failures.append(TestFailure(name, module, clean_message))
            
    return failures

def print_summary(result, duration, failures):
    # Parse final summary line
    # "test result: FAILED. 55 passed; 3 failed; 0 ignored; 0 measured; 0 filtered out"
    summary_match = re.search(r'test result: (.*?)\. (\d+) passed; (\d+) failed; (\d+) ignored', result.stdout)
    
    status = "UNKNOWN"
    passed = 0
    failed = 0
    ignored = 0
    
    if summary_match:
        status = summary_match.group(1)
        passed = int(summary_match.group(2))
        failed = int(summary_match.group(3))
        ignored = int(summary_match.group(4))
    
    print("\n" + "="*50)
    print(f"📊 TEST SUMMARY ({duration:.1f}s)")
    print("="*50)
    
    if result.returncode == 0:
        print(f"✅ SUCCESS: All {passed} tests passed!")
    else:
        print(f"❌ FAILURE: {failed} tests failed (of {passed + failed} total)")
        print("-" * 50)
        
        for f in failures:
            print(f"🔴 {f.module}::{f.name}")
            print(f"   Reason: {f.message}")
            print("-" * 50)
            
    if ignored > 0:
        print(f"⚠️  {ignored} tests ignored (likely DST/long-running)")

if __name__ == "__main__":
    result, duration = run_tests()
    failures = parse_output(result.stdout, result.stderr)
    print_summary(result, duration, failures)
    
    sys.exit(result.returncode)

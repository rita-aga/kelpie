"""CLI interface for RLM environment.

This module provides a command-line interface that MCP server can invoke
via subprocess to execute agent code in a sandboxed environment.

Usage:
    python -m rlm_env --codebase /path/to/kelpie --indexes /path/to/.kelpie-index --execute "code"
    echo "code" | python -m rlm_env --codebase /path/to/kelpie --indexes /path/to/.kelpie-index --stdin
"""

import argparse
import json
import sys
from pathlib import Path

from .environment import RLMEnvironment
from .types import ExecutionResult


def main() -> None:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="RLM Environment - Execute code in sandboxed context"
    )
    parser.add_argument(
        "--codebase", required=True, help="Path to codebase root", type=str
    )
    parser.add_argument(
        "--indexes",
        required=True,
        help="Path to .kelpie-index/ directory",
        type=str,
    )

    # Mutually exclusive code input methods
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument(
        "--execute", help="Python code to execute", type=str
    )
    input_group.add_argument(
        "--stdin",
        action="store_true",
        help="Read code from stdin",
    )

    args = parser.parse_args()

    # TigerStyle: Validate paths exist
    codebase_path = Path(args.codebase)
    indexes_path = Path(args.indexes)

    if not codebase_path.exists():
        print(
            json.dumps(
                {
                    "success": False,
                    "error": f"Codebase path not found: {args.codebase}",
                }
            )
        )
        sys.exit(1)

    if not indexes_path.exists():
        print(
            json.dumps(
                {
                    "success": False,
                    "error": f"Indexes path not found: {args.indexes}",
                }
            )
        )
        sys.exit(1)

    # Get code to execute
    if args.stdin:
        code = sys.stdin.read()
    else:
        code = args.execute

    # TigerStyle: Validate code is non-empty
    if not code or not code.strip():
        print(
            json.dumps({"success": False, "error": "Code cannot be empty"})
        )
        sys.exit(1)

    # Execute in RLM environment
    try:
        env = RLMEnvironment(str(codebase_path), str(indexes_path))
        result = env.execute(code)

        # Output JSON result
        print(json.dumps(result.to_dict()))

        # Exit with appropriate code
        sys.exit(0 if result.success else 1)

    except Exception as e:
        print(
            json.dumps(
                {
                    "success": False,
                    "error": f"Failed to initialize environment: {e}",
                }
            )
        )
        sys.exit(1)


if __name__ == "__main__":
    main()

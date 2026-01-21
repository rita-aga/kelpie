"""RLM execution environment with sandboxing.

Provides a REPL environment where agent code executes with RestrictedPython sandboxing.
"""

import signal
from typing import Any, Dict, List
from RestrictedPython import compile_restricted
from RestrictedPython.Guards import safe_builtins, guarded_iter_unpack_sequence

from .codebase import CodebaseContext
from .types import ExecutionResult

# TigerStyle: Explicit constants with units
EXECUTION_TIMEOUT_SECONDS = 30
MAX_RECURSIVE_DEPTH = 3
MAX_OUTPUT_BYTES = 100 * 1024  # 100KB


class TimeoutError(Exception):
    """Execution timeout error."""

    pass


class RLMEnvironment:
    """REPL environment for RLM execution with sandboxing.

    TigerStyle: Sandboxed execution prevents agent from:
    - Writing to filesystem
    - Making network requests
    - Spawning processes
    - Infinite loops (timeout)
    - Unbounded recursion (depth limit)
    """

    def __init__(self, codebase_path: str, indexes_path: str):
        """Initialize RLM environment.

        Args:
            codebase_path: Path to codebase root
            indexes_path: Path to .kelpie-index/ directory
        """
        self.codebase = CodebaseContext(codebase_path, indexes_path)
        self.execution_log: List[str] = []
        self._recursive_depth = 0

    def execute(self, code: str) -> ExecutionResult:
        """Execute agent-written code in SANDBOXED environment.

        Args:
            code: Python code to execute

        Returns:
            ExecutionResult with success status, result, and logs

        TigerStyle: Explicit timeout and recursion depth limits
        """
        # TigerStyle: Validate preconditions
        assert isinstance(code, str), "code must be string"
        assert len(code) > 0, "code cannot be empty"

        if self._recursive_depth >= MAX_RECURSIVE_DEPTH:
            return ExecutionResult(
                success=False,
                error=f"Maximum recursive depth ({MAX_RECURSIVE_DEPTH}) exceeded",
                execution_log=self.execution_log,
            )

        # Setup timeout handler
        def timeout_handler(signum: int, frame: Any) -> None:
            raise TimeoutError(
                f"Execution exceeded {EXECUTION_TIMEOUT_SECONDS}s timeout"
            )

        # Install timeout
        old_handler = signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(EXECUTION_TIMEOUT_SECONDS)

        try:
            return self._execute_inner(code)
        except TimeoutError as e:
            return ExecutionResult(
                success=False, error=str(e), execution_log=self.execution_log
            )
        except Exception as e:
            return ExecutionResult(
                success=False,
                error=f"Unexpected error: {e}",
                execution_log=self.execution_log,
            )
        finally:
            # Cancel timeout
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old_handler)

    def _execute_inner(self, code: str) -> ExecutionResult:
        """Inner execution with timeout wrapper.

        Args:
            code: Python code to execute

        Returns:
            ExecutionResult
        """
        # Log execution
        self.execution_log.append(f"Executing code (depth={self._recursive_depth})")

        # Compile with RestrictedPython
        byte_code = compile_restricted(
            code, filename="<rlm>", mode="exec", policy=None
        )

        # TigerStyle: Check for compilation errors
        if byte_code.errors:
            error_msg = "; ".join(byte_code.errors)
            return ExecutionResult(
                success=False,
                error=f"Compilation failed: {error_msg}",
                execution_log=self.execution_log,
            )

        # Build restricted globals
        restricted_globals = self._build_globals()

        # Execute code
        try:
            exec(byte_code.code, restricted_globals)

            # Extract result from global namespace
            # Agent can set 'result' variable to return a value
            result = restricted_globals.get("result", None)

            return ExecutionResult(
                success=True, result=result, execution_log=self.execution_log
            )
        except Exception as e:
            return ExecutionResult(
                success=False,
                error=f"Execution error: {type(e).__name__}: {e}",
                execution_log=self.execution_log,
            )

    def _build_globals(self) -> Dict[str, Any]:
        """Build restricted global namespace for execution.

        Returns:
            Dictionary of safe globals

        TigerStyle: Explicit whitelist of allowed operations
        """
        return {
            # RestrictedPython required builtins
            "__builtins__": safe_builtins,
            "_getiter_": iter,
            "_iter_unpack_sequence_": guarded_iter_unpack_sequence,
            # Safe builtins
            "len": len,
            "str": str,
            "int": int,
            "float": float,
            "bool": bool,
            "list": list,
            "dict": dict,
            "tuple": tuple,
            "set": set,
            "range": range,
            "enumerate": enumerate,
            "zip": zip,
            "sorted": sorted,
            "sum": sum,
            "min": min,
            "max": max,
            "abs": abs,
            "all": all,
            "any": any,
            "filter": filter,
            "map": map,
            # Codebase access (read-only)
            "codebase": self.codebase,
            "indexes": self.codebase.indexes,
            # Convenience shortcuts
            "grep": self.codebase.grep,
            "peek": self.codebase.peek,
            "read_section": self.codebase.read_section,
            "read_context": self.codebase.read_context,
            "list_files": self.codebase.list_files,
            "list_crates": self.codebase.list_crates,
            "list_modules": self.codebase.list_modules,
            "list_tests": self.codebase.list_tests,
            "get_module": self.codebase.get_module,
            "partition_by_crate": self.codebase.partition_by_crate,
            "get_index": self.codebase.get_index,
            # Result placeholder (agent sets this to return a value)
            "result": None,
        }

    def spawn_recursive(self, query: str, context: str) -> str:
        """Spawn a recursive RLM call.

        Args:
            query: Question to ask
            context: Context to provide to recursive call

        Returns:
            Response from recursive call

        TigerStyle: Not implemented yet - requires LLM API integration
        """
        self._recursive_depth += 1
        try:
            # TODO: Integrate with Claude API for recursive calls
            # This would call the Claude API with:
            # - query as the user message
            # - context as system context
            # - Tool available: rlm_execute() for further recursion
            return f"[Recursive call not yet implemented: {query}]"
        finally:
            self._recursive_depth -= 1

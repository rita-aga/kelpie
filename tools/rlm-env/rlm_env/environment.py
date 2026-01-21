"""RLM execution environment with sandboxing.

Provides a REPL environment where agent code executes with RestrictedPython sandboxing.
"""

import signal
from typing import Any, Dict, List, Callable, Optional
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


class FinalResultException(Exception):
    """Exception raised when FINAL() is called to signal completion."""

    def __init__(self, result: Any):
        self.result = result
        super().__init__(f"Final result: {result}")


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
        self._print_buffer: List[str] = []
        self._final_result: Optional[Any] = None

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
        except FinalResultException as e:
            # Agent called FINAL() - return the final result
            return ExecutionResult(
                success=True, result=e.result, execution_log=self.execution_log
            )
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
        # Clear print buffer for this execution
        self._print_buffer = []

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

            # TigerStyle: Enforce output size limit
            result_str = str(result) if result is not None else ""
            result_size_bytes = len(result_str.encode("utf-8"))

            if result_size_bytes > MAX_OUTPUT_BYTES:
                return ExecutionResult(
                    success=False,
                    error=f"Output size ({result_size_bytes} bytes) exceeds maximum ({MAX_OUTPUT_BYTES} bytes)",
                    execution_log=self.execution_log,
                )

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
            # RLM-specific methods
            "FINAL": self._final,
            "print": self._safe_print,
            "map_reduce": self._map_reduce,
            "spawn_recursive": self.spawn_recursive,
            # Result placeholder (agent sets this to return a value)
            "result": None,
        }

    def _safe_print(self, *args: Any) -> None:
        """Capture prints instead of sending to stdout.

        Args:
            *args: Values to print

        TigerStyle: Print output is captured, not sent to stdout
        """
        output = " ".join(str(a) for a in args)
        self._print_buffer.append(output)
        self.execution_log.append(f"PRINT: {output}")

    def _final(self, result: Any) -> None:
        """Signal final result (terminates execution).

        Args:
            result: The final result to return

        TigerStyle: Raises FinalResultException to terminate execution
        """
        self._final_result = result
        self.execution_log.append(f"FINAL called with result: {result}")
        raise FinalResultException(result)

    def _map_reduce(
        self, query: str, partitions: List[Any], aggregator: Optional[Callable] = None
    ) -> Any:
        """Partition + Map pattern with optional custom aggregation.

        Args:
            query: Question to ask for each partition
            partitions: List of partitions to map over
            aggregator: Optional function to aggregate results

        Returns:
            Aggregated results or list of partition results

        TigerStyle: Map-reduce pattern for processing partitioned codebase
        """
        # TigerStyle: Validate preconditions
        assert isinstance(query, str), "query must be string"
        assert len(query) > 0, "query cannot be empty"
        assert isinstance(partitions, list), "partitions must be list"
        assert len(partitions) > 0, "partitions cannot be empty"

        self.execution_log.append(
            f"MAP_REDUCE: query='{query}' partitions={len(partitions)}"
        )

        results = []
        for i, partition in enumerate(partitions):
            # Call spawn_recursive for each partition
            result = self.spawn_recursive(query, str(partition))
            results.append(
                {
                    "partition": i,
                    "partition_name": getattr(partition, "name", str(i)),
                    "result": result,
                }
            )

        # Apply custom aggregator if provided
        if aggregator is not None:
            return aggregator(results)

        return results

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

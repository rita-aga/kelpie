"""
RLM REPL environment with variable loading and sandboxed execution.

VDE insight: Code becomes data in variables, not tokens in context.
The model loads files into server variables, then writes programs OR spawns
sub-LLM calls to analyze them.

Tools exposed:
- repl_load: Load files into server variable by glob pattern
- repl_exec: Execute Python code on loaded variables
- repl_query: Evaluate expression and return result
- repl_state: Show current variable names and sizes
- repl_clear: Clear variables to free memory
"""

import signal
from typing import Any, Callable

import re

from RestrictedPython import compile_restricted
from RestrictedPython.Guards import (
    guarded_iter_unpack_sequence,
    safe_builtins,
)
from RestrictedPython.PrintCollector import PrintCollector


# Custom guards for RestrictedPython 8.x
def _getitem_(obj, key):
    """Safe getitem for dictionary/list access."""
    return obj[key]


def _write_(obj):
    """Allow writing to containers."""
    return obj

from .context import CodebaseContext
from .types import ExecutionResult, LoadedVariable

# TigerStyle: Explicit constants with units
EXECUTION_TIMEOUT_SECONDS = 30
MAX_RECURSIVE_DEPTH = 3
MAX_OUTPUT_BYTES = 100 * 1024  # 100KB
MAX_VARIABLE_SIZE_BYTES = 50 * 1024 * 1024  # 50MB total variable memory
MAX_FILES_PER_LOAD = 1000  # Maximum files in a single load


class TimeoutError(Exception):
    """Execution timeout error."""

    pass


class FinalResultException(Exception):
    """Exception raised when FINAL() is called to signal completion."""

    def __init__(self, result: Any):
        self.result = result
        super().__init__(f"Final result: {result}")


class REPLEnvironment:
    """REPL environment with VDE-style variable loading.

    Key difference from original RLMEnvironment:
    - Variables are explicitly loaded via repl_load()
    - Loaded variables are accessible to both Python code AND sub-LLMs
    - Memory is tracked and bounded

    TigerStyle: Sandboxed execution prevents agent from:
    - Writing to filesystem
    - Making network requests
    - Spawning processes
    - Infinite loops (timeout)
    - Unbounded memory use (variable limits)
    """

    def __init__(self, codebase: CodebaseContext):
        """Initialize REPL environment.

        Args:
            codebase: CodebaseContext for file access
        """
        self.codebase = codebase
        self.execution_log: list[str] = []
        self._recursive_depth = 0
        self._print_buffer: list[str] = []
        self._final_result: Any | None = None

        # VDE: Variables loaded into server memory
        self._variables: dict[str, LoadedVariable] = {}
        self._total_variable_bytes = 0

    # ==================== Variable Management (VDE) ====================

    def load(self, glob_pattern: str, variable_name: str, root_path: str | None = None) -> str:
        """Load files matching glob into a server variable.

        Args:
            glob_pattern: Glob pattern for files (e.g., "**/*.rs")
            variable_name: Name for the variable
            root_path: Optional root path override (defaults to codebase root)

        Returns:
            Summary message (e.g., "Loaded 14 files (189KB) into 'code'")

        VDE insight: This loads files into server memory, NOT into model context.
        The model can then write Python code OR spawn sub-LLM calls to analyze.
        """
        # TigerStyle: Validate variable name
        assert variable_name.isidentifier(), f"Invalid variable name: {variable_name}"
        assert len(variable_name) <= 32, "Variable name too long (max 32 chars)"

        # Find matching files
        files = self.codebase.list_files(glob_pattern)

        if len(files) > MAX_FILES_PER_LOAD:
            return f"Error: Pattern matches {len(files)} files (max {MAX_FILES_PER_LOAD}). Use more specific glob."

        if not files:
            return f"No files match pattern: {glob_pattern}"

        # Load file contents
        file_contents: dict[str, str] = {}
        total_bytes = 0

        for file in files:
            content = self.codebase.read_file(file)
            if not content.startswith("Error:") and not content.startswith("File not found"):
                file_contents[file] = content
                total_bytes += len(content.encode("utf-8"))

        # Check memory limit
        if self._total_variable_bytes + total_bytes > MAX_VARIABLE_SIZE_BYTES:
            size_mb = MAX_VARIABLE_SIZE_BYTES / (1024 * 1024)
            return f"Error: Would exceed memory limit ({size_mb:.0f}MB). Use repl_clear first."

        # Remove old variable if exists (reclaim memory)
        if variable_name in self._variables:
            old_var = self._variables[variable_name]
            self._total_variable_bytes -= old_var.total_bytes

        # Create loaded variable
        var = LoadedVariable(
            name=variable_name,
            glob_pattern=glob_pattern,
            file_count=len(file_contents),
            total_bytes=total_bytes,
            files=file_contents,
        )

        self._variables[variable_name] = var
        self._total_variable_bytes += total_bytes

        self.execution_log.append(f"LOAD: {var.summary()}")
        return var.summary()

    def state(self) -> dict[str, Any]:
        """Get current REPL state (loaded variables).

        Returns:
            Dictionary with variable info
        """
        variables = {}
        for name, var in self._variables.items():
            variables[name] = {
                "glob_pattern": var.glob_pattern,
                "file_count": var.file_count,
                "size_bytes": var.total_bytes,
                "size_kb": round(var.total_bytes / 1024, 1),
            }

        return {
            "variables": variables,
            "total_size_bytes": self._total_variable_bytes,
            "total_size_mb": round(self._total_variable_bytes / (1024 * 1024), 2),
            "memory_limit_mb": MAX_VARIABLE_SIZE_BYTES / (1024 * 1024),
        }

    def clear(self, variable_name: str | None = None) -> str:
        """Clear variables to free memory.

        Args:
            variable_name: Specific variable to clear, or None to clear all

        Returns:
            Confirmation message
        """
        if variable_name:
            if variable_name not in self._variables:
                return f"Variable not found: {variable_name}"

            var = self._variables.pop(variable_name)
            self._total_variable_bytes -= var.total_bytes
            self.execution_log.append(f"CLEAR: Removed '{variable_name}' ({var.total_bytes / 1024:.1f}KB)")
            return f"Cleared '{variable_name}' ({var.total_bytes / 1024:.1f}KB freed)"
        else:
            count = len(self._variables)
            freed = self._total_variable_bytes
            self._variables.clear()
            self._total_variable_bytes = 0
            self.execution_log.append(f"CLEAR: Removed all {count} variables ({freed / 1024:.1f}KB)")
            return f"Cleared {count} variables ({freed / 1024:.1f}KB freed)"

    def get_variable(self, name: str) -> LoadedVariable | None:
        """Get a loaded variable by name.

        Args:
            name: Variable name

        Returns:
            LoadedVariable or None
        """
        return self._variables.get(name)

    # ==================== Code Execution ====================

    def execute(self, code: str) -> ExecutionResult:
        """Execute agent-written code in SANDBOXED environment.

        Loaded variables are accessible by name in the code.

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
            raise TimeoutError(f"Execution exceeded {EXECUTION_TIMEOUT_SECONDS}s timeout")

        # Install timeout
        old_handler = signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(EXECUTION_TIMEOUT_SECONDS)

        try:
            return self._execute_inner(code)
        except FinalResultException as e:
            # Agent called FINAL() - return the final result
            return ExecutionResult(success=True, result=e.result, execution_log=self.execution_log)
        except TimeoutError as e:
            return ExecutionResult(success=False, error=str(e), execution_log=self.execution_log)
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
        self.execution_log.append(f"EXEC: (depth={self._recursive_depth}, {len(code)} chars)")

        # Compile with RestrictedPython
        # In RestrictedPython 8.x, compile_restricted returns a code object directly
        # and raises SyntaxError on compilation failure
        try:
            byte_code = compile_restricted(code, filename="<rlm>", mode="exec")
        except SyntaxError as e:
            return ExecutionResult(
                success=False,
                error=f"Compilation failed: {e}",
                execution_log=self.execution_log,
            )

        # Build restricted globals
        restricted_globals = self._build_globals()

        # Execute code (byte_code is a code object in RestrictedPython 8.x)
        try:
            exec(byte_code, restricted_globals)

            # Extract result from global namespace
            # Agent can set 'result' variable to return a value
            result = restricted_globals.get("result", None)

            # Capture printed output if any
            printed = restricted_globals.get("_print", None)
            if printed:
                for line in str(printed).split("\n"):
                    if line.strip():
                        self._print_buffer.append(line)
                        self.execution_log.append(f"PRINT: {line}")

            # TigerStyle: Enforce output size limit
            result_str = str(result) if result is not None else ""
            result_size_bytes = len(result_str.encode("utf-8"))

            if result_size_bytes > MAX_OUTPUT_BYTES:
                return ExecutionResult(
                    success=False,
                    error=f"Output size ({result_size_bytes} bytes) exceeds maximum ({MAX_OUTPUT_BYTES} bytes)",
                    execution_log=self.execution_log,
                )

            return ExecutionResult(success=True, result=result, execution_log=self.execution_log)
        except FinalResultException:
            # Re-raise to be caught by execute()
            raise
        except Exception as e:
            return ExecutionResult(
                success=False,
                error=f"Execution error: {type(e).__name__}: {e}",
                execution_log=self.execution_log,
            )

    def query(self, expression: str) -> ExecutionResult:
        """Evaluate a single expression and return the result.

        This is a convenience wrapper around execute() for simple queries.

        Args:
            expression: Python expression to evaluate

        Returns:
            ExecutionResult with the expression value
        """
        code = f"result = {expression}"
        return self.execute(code)

    def _build_globals(self) -> dict[str, Any]:
        """Build restricted global namespace for execution.

        Returns:
            Dictionary of safe globals including loaded variables

        TigerStyle: Explicit whitelist of allowed operations
        """
        globals_dict = {
            # RestrictedPython required builtins
            "__builtins__": safe_builtins,
            # RestrictedPython guards (required for container access)
            "_getiter_": iter,
            "_iter_unpack_sequence_": guarded_iter_unpack_sequence,
            "_getitem_": _getitem_,
            "_write_": _write_,
            # Print collector for RestrictedPython
            "_print_": PrintCollector,
            "_getattr_": getattr,
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
            "isinstance": isinstance,
            "type": type,
            "hasattr": hasattr,
            "getattr": getattr,
            # Allow 're' module for regex operations (common in RLM)
            "re": re,
            # Codebase access (read-only) - for interactive use
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
            # Result placeholder (agent sets this to return a value)
            "result": None,
        }

        # VDE: Add loaded variables as accessible names
        for name, var in self._variables.items():
            globals_dict[name] = var.files  # dict[path, content]

        return globals_dict

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
        self.execution_log.append(f"FINAL called with result type: {type(result).__name__}")
        raise FinalResultException(result)

    def map_reduce(
        self, query: str, partitions: list[Any], aggregator: Callable[[list[Any]], Any] | None = None
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

        self.execution_log.append(f"MAP_REDUCE: query='{query[:50]}...' partitions={len(partitions)}")

        results = []
        for i, partition in enumerate(partitions):
            # For now, return placeholder - real implementation needs sub-LLM
            result = f"[Partition {i}: {partition}]"
            results.append(
                {
                    "partition": i,
                    "partition_name": getattr(partition, "module_name", str(i)),
                    "result": result,
                }
            )

        # Apply custom aggregator if provided
        if aggregator is not None:
            return aggregator(results)

        return results

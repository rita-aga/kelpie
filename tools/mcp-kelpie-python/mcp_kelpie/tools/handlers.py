"""
Tool handlers for Kelpie MCP Server.

Implements the actual logic for each tool defined in definitions.py.
"""

import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ..rlm import CodebaseContext, REPLEnvironment
from ..indexer import Indexer, build_indexes


def _utcnow() -> str:
    """Get current UTC time as ISO string."""
    return datetime.now(timezone.utc).isoformat()


def _run_command(command: str, cwd: Path, timeout_seconds: int = 120) -> dict[str, Any]:
    """Run a shell command and capture output.

    Args:
        command: Command to run
        cwd: Working directory
        timeout_seconds: Timeout in seconds

    Returns:
        Dict with success, output, error
    """
    try:
        result = subprocess.run(
            command,
            shell=True,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
        return {
            "success": result.returncode == 0,
            "output": result.stdout,
            "error": result.stderr if result.returncode != 0 else None,
        }
    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "output": "",
            "error": f"Command timed out after {timeout_seconds}s",
        }
    except Exception as e:
        return {
            "success": False,
            "output": "",
            "error": str(e),
        }


class ToolHandlers:
    """Handlers for all MCP tools.

    This class manages tool state and provides handler methods for each tool.
    """

    def __init__(self, codebase_path: Path):
        """Initialize tool handlers.

        Args:
            codebase_path: Path to codebase root
        """
        self.codebase_path = codebase_path.resolve()
        self.indexes_path = self.codebase_path / ".kelpie-index"
        self.agentfs_path = self.codebase_path / ".agentfs"

        # Initialize RLM components
        self._codebase_context = CodebaseContext(str(self.codebase_path))
        self._repl_env = REPLEnvironment(self._codebase_context)

        # AgentFS session (initialized lazily)
        self._vfs_session = None
        self._session_manager = None

    async def handle_tool(self, name: str, arguments: dict[str, Any]) -> dict[str, Any]:
        """Route tool call to appropriate handler.

        Args:
            name: Tool name
            arguments: Tool arguments

        Returns:
            Tool result
        """
        handler = getattr(self, f"_handle_{name}", None)
        if handler is None:
            raise ValueError(f"Unknown tool: {name}")
        return await handler(arguments)

    # ==================== RLM Tools ====================

    async def _handle_repl_load(self, args: dict[str, Any]) -> dict[str, Any]:
        """Load files into server variable by glob pattern."""
        pattern = args.get("pattern", "")
        var_name = args.get("var_name", "")

        result = self._repl_env.load(pattern, var_name)
        return {
            "success": "Error" not in result,
            "message": result,
            "variable": var_name,
        }

    async def _handle_repl_exec(self, args: dict[str, Any]) -> dict[str, Any]:
        """Execute Python code on loaded variables."""
        code = args.get("code", "")

        result = self._repl_env.execute(code)
        return {
            "success": result.success,
            "result": result.result,
            "error": result.error,
            "execution_log": result.execution_log[-10:] if result.execution_log else [],
        }

    async def _handle_repl_query(self, args: dict[str, Any]) -> dict[str, Any]:
        """Evaluate a Python expression."""
        expression = args.get("expression", "")

        result = self._repl_env.query(expression)
        return {
            "success": result.success,
            "result": result.result,
            "error": result.error,
        }

    async def _handle_repl_state(self, args: dict[str, Any]) -> dict[str, Any]:
        """Get current REPL state."""
        return self._repl_env.state()

    async def _handle_repl_clear(self, args: dict[str, Any]) -> dict[str, Any]:
        """Clear loaded variables."""
        var_name = args.get("var_name")

        result = self._repl_env.clear(var_name)
        return {
            "success": True,
            "message": result,
        }

    # ==================== AgentFS/VFS Tools ====================

    async def _handle_vfs_init(self, args: dict[str, Any]) -> dict[str, Any]:
        """Initialize or resume a verification session."""
        from ..agentfs import SessionManager

        task = args.get("task", "")
        session_id = args.get("session_id")

        if self._session_manager is None:
            self._session_manager = SessionManager(str(self.codebase_path))

        self._vfs_session = await self._session_manager.init_session(task, session_id)

        return {
            "success": True,
            "session_id": self._session_manager.get_session_id(),
            "task": task,
        }

    async def _handle_vfs_fact_add(self, args: dict[str, Any]) -> dict[str, Any]:
        """Record a verified fact with evidence."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        fact_id = await self._vfs_session.add_fact(
            claim=args.get("claim", ""),
            evidence=args.get("evidence", ""),
            source=args.get("source", ""),
            command=args.get("command"),
        )

        return {
            "success": True,
            "fact_id": fact_id,
        }

    async def _handle_vfs_fact_check(self, args: dict[str, Any]) -> dict[str, Any]:
        """Check if a claim has been verified."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        facts = await self._vfs_session.check_fact(args.get("claim_pattern", ""))

        return {
            "success": True,
            "facts": facts,
            "count": len(facts),
        }

    async def _handle_vfs_fact_list(self, args: dict[str, Any]) -> dict[str, Any]:
        """List all verified facts."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        facts = await self._vfs_session.list_facts()

        return {
            "success": True,
            "facts": facts,
            "count": len(facts),
        }

    async def _handle_vfs_invariant_verify(self, args: dict[str, Any]) -> dict[str, Any]:
        """Mark an invariant as verified."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        await self._vfs_session.verify_invariant(
            name=args.get("name", ""),
            component=args.get("component", ""),
            method=args.get("method", "manual"),
            evidence=args.get("evidence"),
        )

        return {"success": True}

    async def _handle_vfs_invariant_status(self, args: dict[str, Any]) -> dict[str, Any]:
        """Check invariant verification status."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        status = await self._vfs_session.invariant_status(args.get("component", ""))

        return {
            "success": True,
            **status,
        }

    async def _handle_vfs_status(self, args: dict[str, Any]) -> dict[str, Any]:
        """Get current verification session status."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        status = await self._vfs_session.status()

        return {
            "success": True,
            **status,
        }

    async def _handle_vfs_tool_start(self, args: dict[str, Any]) -> dict[str, Any]:
        """Start tracking a tool call."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        call_id = await self._vfs_session.tool_start(
            name=args.get("name", ""),
            args=args.get("args", {}),
        )

        return {
            "success": True,
            "call_id": call_id,
        }

    async def _handle_vfs_tool_success(self, args: dict[str, Any]) -> dict[str, Any]:
        """Mark tool call as successful."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        await self._vfs_session.tool_success(
            call_id=args.get("call_id", 0),
            result=args.get("result"),
        )

        return {"success": True}

    async def _handle_vfs_tool_error(self, args: dict[str, Any]) -> dict[str, Any]:
        """Mark tool call as failed."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        await self._vfs_session.tool_error(
            call_id=args.get("call_id", 0),
            error=args.get("error", ""),
        )

        return {"success": True}

    async def _handle_vfs_tool_list(self, args: dict[str, Any]) -> dict[str, Any]:
        """List all tool calls."""
        if self._vfs_session is None:
            return {"success": False, "error": "No active VFS session. Call vfs_init first."}

        tools = await self._vfs_session.tool_list()

        return {
            "success": True,
            "tools": tools,
            "count": len(tools),
        }

    # ==================== Index Tools ====================

    async def _handle_index_symbols(self, args: dict[str, Any]) -> dict[str, Any]:
        """Find symbols matching a pattern."""
        pattern = args.get("pattern", "")
        kind = args.get("kind")

        # Load symbols index
        symbols_path = self.indexes_path / "structural" / "symbols.json"
        if not symbols_path.exists():
            return {"success": False, "error": "Symbols index not found. Run index_refresh first."}

        symbols_data = json.loads(symbols_path.read_text())
        matches = []

        regex = re.compile(pattern, re.IGNORECASE)

        for file_data in symbols_data.get("files", []):
            file_path = file_data.get("path", "")
            for symbol in file_data.get("symbols", []):
                name = symbol.get("name", "")
                symbol_kind = symbol.get("kind", "")

                if regex.search(name):
                    if kind is None or symbol_kind == kind:
                        matches.append({
                            "file": file_path,
                            "name": name,
                            "kind": symbol_kind,
                            "visibility": symbol.get("visibility", ""),
                            "line": symbol.get("line", 0),
                        })

        return {
            "success": True,
            "matches": matches[:100],  # Limit to 100
            "count": len(matches),
        }

    async def _handle_index_tests(self, args: dict[str, Any]) -> dict[str, Any]:
        """Find tests by pattern or crate."""
        pattern = args.get("pattern")
        crate_filter = args.get("crate")

        tests_path = self.indexes_path / "structural" / "tests.json"
        if not tests_path.exists():
            return {"success": False, "error": "Tests index not found. Run index_refresh first."}

        tests_data = json.loads(tests_path.read_text())
        matches = []

        for crate in tests_data.get("crates", []):
            crate_name = crate.get("crate_name", "")

            if crate_filter and crate_name != crate_filter:
                continue

            for module in crate.get("modules", []):
                for test in module.get("tests", []):
                    test_name = test.get("name", "")

                    if pattern is None or re.search(pattern, test_name, re.IGNORECASE):
                        matches.append({
                            "crate": crate_name,
                            "module": module.get("module_path", ""),
                            "name": test_name,
                            "line": test.get("line", 0),
                            "is_ignored": test.get("is_ignored", False),
                            "is_async": test.get("is_async", False),
                        })

        return {
            "success": True,
            "tests": matches[:100],
            "count": len(matches),
        }

    async def _handle_index_modules(self, args: dict[str, Any]) -> dict[str, Any]:
        """Get module hierarchy."""
        crate_filter = args.get("crate")

        modules_path = self.indexes_path / "structural" / "modules.json"
        if not modules_path.exists():
            return {"success": False, "error": "Modules index not found. Run index_refresh first."}

        modules_data = json.loads(modules_path.read_text())
        crates = modules_data.get("crates", [])

        if crate_filter:
            crates = [c for c in crates if c.get("crate_name") == crate_filter]

        return {
            "success": True,
            "crates": crates,
            "count": len(crates),
        }

    async def _handle_index_deps(self, args: dict[str, Any]) -> dict[str, Any]:
        """Get dependency graph."""
        crate_filter = args.get("crate")

        deps_path = self.indexes_path / "structural" / "dependencies.json"
        if not deps_path.exists():
            return {"success": False, "error": "Dependencies index not found. Run index_refresh first."}

        deps_data = json.loads(deps_path.read_text())
        crates = deps_data.get("crates", [])

        if crate_filter:
            crates = [c for c in crates if c.get("crate_name") == crate_filter]

        return {
            "success": True,
            "crates": crates,
            "count": len(crates),
        }

    async def _handle_index_status(self, args: dict[str, Any]) -> dict[str, Any]:
        """Get status of all indexes."""
        indexes = ["symbols", "modules", "dependencies", "tests"]
        status = {}

        for index_name in indexes:
            index_path = self.indexes_path / "structural" / f"{index_name}.json"
            if index_path.exists():
                stat = index_path.stat()
                data = json.loads(index_path.read_text())
                status[index_name] = {
                    "exists": True,
                    "size_bytes": stat.st_size,
                    "modified_at": stat.st_mtime,
                    "version": data.get("version", "unknown"),
                    "generated_at": data.get("generated_at"),
                }
            else:
                status[index_name] = {"exists": False}

        return {
            "success": True,
            "status": status,
        }

    async def _handle_index_refresh(self, args: dict[str, Any]) -> dict[str, Any]:
        """Rebuild indexes using Python indexer."""
        scope = args.get("scope", "all")

        try:
            output_dir = self.indexes_path / "structural"
            indexer = Indexer(self.codebase_path)
            result = indexer.build_all(output_dir)

            return {
                "success": True,
                "scope": scope,
                "files_indexed": len(result.get("symbols", {}).get("files", [])),
                "crates_indexed": len(result.get("dependencies", {}).get("crates", [])),
            }
        except Exception as e:
            return {
                "success": False,
                "error": str(e),
            }

    # ==================== Verification Tools ====================

    async def _handle_verify_claim(self, args: dict[str, Any]) -> dict[str, Any]:
        """Verify a claim by executing a command."""
        claim = args.get("claim", "")
        method = args.get("method", "")

        result = _run_command(method, self.codebase_path)

        return {
            "success": result["success"],
            "claim": claim,
            "method": method,
            "output": result["output"][:2000] if result["output"] else "",
            "error": result["error"],
            "verified_at": _utcnow(),
        }

    async def _handle_verify_all_tests(self, args: dict[str, Any]) -> dict[str, Any]:
        """Run all tests."""
        release = args.get("release", False)
        command = "cargo test --all --release" if release else "cargo test --all"

        result = _run_command(command, self.codebase_path, timeout_seconds=300)

        # Parse output for test counts
        passed_match = re.search(r"test result: ok\. (\d+) passed", result["output"])
        passed = int(passed_match.group(1)) if passed_match else None

        return {
            "success": result["success"],
            "command": command,
            "passed": passed,
            "output": result["output"][-2000:] if result["output"] else "",
            "error": result["error"],
            "verified_at": _utcnow(),
        }

    async def _handle_verify_clippy(self, args: dict[str, Any]) -> dict[str, Any]:
        """Run Rust linter."""
        command = "cargo clippy --all-targets --all-features"

        result = _run_command(command, self.codebase_path)

        # Count warnings and errors
        warnings = len(re.findall(r"warning:", result["output"] or ""))
        errors = len(re.findall(r"error:", result["output"] or ""))

        return {
            "success": result["success"],
            "command": command,
            "warnings": warnings,
            "errors": errors,
            "output": result["output"][-2000:] if result["output"] else "",
            "error": result["error"],
            "verified_at": _utcnow(),
        }

    async def _handle_verify_fmt(self, args: dict[str, Any]) -> dict[str, Any]:
        """Check code formatting."""
        command = "cargo fmt --check"

        result = _run_command(command, self.codebase_path)

        return {
            "success": result["success"],
            "command": command,
            "output": result["output"][:2000] if result["output"] else "",
            "error": result["error"],
            "verified_at": _utcnow(),
        }

    # ==================== DST Tools ====================

    async def _handle_dst_coverage_check(self, args: dict[str, Any]) -> dict[str, Any]:
        """Check DST coverage for critical paths."""
        critical_paths = [
            {"name": "actor activation/deactivation", "patterns": ["actor.*activate", "spawn.*actor"]},
            {"name": "state persistence and recovery", "patterns": ["state.*persist", "state.*recover"]},
            {"name": "cross-actor invocation", "patterns": ["invoke.*actor", "send.*message"]},
            {"name": "failure detection", "patterns": ["fail.*detect", "health.*check"]},
            {"name": "migration correctness", "patterns": ["migrate.*actor", "transfer.*state"]},
        ]

        results = []
        for path in critical_paths:
            # Check for DST tests matching patterns
            has_dst = False
            for pattern in path["patterns"]:
                result = _run_command(
                    f"git grep -l '{pattern}' -- '*_dst.rs' 2>/dev/null || true",
                    self.codebase_path,
                    timeout_seconds=10,
                )
                if result["output"].strip():
                    has_dst = True
                    break

            results.append({
                "name": path["name"],
                "has_dst_test": has_dst,
            })

        covered = sum(1 for r in results if r["has_dst_test"])
        total = len(results)

        return {
            "success": covered == total,
            "critical_paths": results,
            "coverage_percentage": round(covered / total * 100) if total > 0 else 0,
            "covered": covered,
            "total": total,
        }

    async def _handle_dst_gaps_report(self, args: dict[str, Any]) -> dict[str, Any]:
        """Generate DST coverage gaps report."""
        # Find modules without DST tests
        result = _run_command(
            "find crates -name '*.rs' -path '*/src/*' ! -name '*test*' | head -50",
            self.codebase_path,
            timeout_seconds=10,
        )

        files = result["output"].strip().split("\n") if result["output"] else []
        gaps = []

        for file in files[:20]:  # Limit analysis
            if not file:
                continue
            base = file.replace(".rs", "")
            dst_file = f"{base}_dst.rs"

            check = _run_command(f"test -f '{dst_file}' && echo exists || echo missing", self.codebase_path)
            if "missing" in check["output"]:
                gaps.append({
                    "file": file,
                    "reason": "No corresponding DST test file",
                })

        return {
            "success": True,
            "gaps": gaps,
            "count": len(gaps),
        }

    async def _handle_harness_check(self, args: dict[str, Any]) -> dict[str, Any]:
        """Check if DST harness supports fault types."""
        fault_types = args.get("fault_types", [])

        supported = {
            "StorageWriteFail", "StorageReadFail", "StorageCorruption", "StorageLatency", "DiskFull",
            "CrashBeforeWrite", "CrashAfterWrite", "CrashDuringTransaction",
            "NetworkPartition", "NetworkDelay", "NetworkPacketLoss", "NetworkMessageReorder",
            "ClockSkew", "ClockJump",
            "OutOfMemory", "CPUStarvation",
        }

        results = []
        for fault in fault_types:
            results.append({
                "fault_type": fault,
                "supported": fault in supported,
            })

        all_supported = all(r["supported"] for r in results)

        return {
            "success": all_supported,
            "results": results,
            "supported_count": sum(1 for r in results if r["supported"]),
            "total": len(results),
        }

    # ==================== Codebase Tools ====================

    async def _handle_codebase_grep(self, args: dict[str, Any]) -> dict[str, Any]:
        """Search for pattern in codebase."""
        pattern = args.get("pattern", "")
        glob = args.get("glob", "**/*.rs")
        max_matches = args.get("max_matches", 100)

        matches = self._codebase_context.grep(pattern, glob, max_matches)

        return {
            "success": True,
            "matches": [{"file": m.file, "line": m.line, "content": m.content} for m in matches],
            "count": len(matches),
        }

    async def _handle_codebase_peek(self, args: dict[str, Any]) -> dict[str, Any]:
        """Peek at first N lines of a file."""
        path = args.get("path", "")
        lines = args.get("lines", 20)

        content = self._codebase_context.peek(path, lines)

        return {
            "success": "Error" not in content and "File not found" not in content,
            "content": content,
        }

    async def _handle_codebase_read_section(self, args: dict[str, Any]) -> dict[str, Any]:
        """Read a section of a file."""
        path = args.get("path", "")
        start_line = args.get("start_line", 1)
        end_line = args.get("end_line", 100)

        content = self._codebase_context.read_section(path, start_line, end_line)

        return {
            "success": "Error" not in content,
            "content": content,
        }

    async def _handle_codebase_list_files(self, args: dict[str, Any]) -> dict[str, Any]:
        """List files matching a glob pattern."""
        pattern = args.get("pattern", "**/*.rs")

        files = self._codebase_context.list_files(pattern)

        return {
            "success": True,
            "files": files[:500],  # Limit to 500
            "count": len(files),
        }

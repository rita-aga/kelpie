"""
MCP Tool definitions for Kelpie Repo OS.

All tools are defined here with their schemas.
Handlers are implemented in handlers.py.
"""

from typing import Any

# Tool schema type
Tool = dict[str, Any]


# ==================== RLM Tools ====================

REPL_TOOLS: list[Tool] = [
    {
        "name": "repl_load",
        "description": "Load files into server variable by glob pattern. Files become data in variables, not tokens in context.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "pattern": {"type": "string", "description": "Glob pattern (e.g., '**/*.rs')"},
                "var_name": {"type": "string", "description": "Variable name to store files"},
            },
            "required": ["pattern", "var_name"],
        },
    },
    {
        "name": "repl_exec",
        "description": "Execute Python code on loaded variables. Use 'result = ...' to return values.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "code": {"type": "string", "description": "Python code to execute"},
            },
            "required": ["code"],
        },
    },
    {
        "name": "repl_query",
        "description": "Evaluate a Python expression and return the result.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "expression": {"type": "string", "description": "Python expression to evaluate"},
            },
            "required": ["expression"],
        },
    },
    {
        "name": "repl_state",
        "description": "Get current REPL state (loaded variables, memory usage).",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "repl_clear",
        "description": "Clear loaded variables to free memory.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "var_name": {"type": "string", "description": "Variable to clear (optional, clears all if not specified)"},
            },
        },
    },
]


# ==================== AgentFS/VFS Tools ====================

AGENTFS_TOOLS: list[Tool] = [
    {
        "name": "vfs_init",
        "description": "Initialize or resume a verification session.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "task": {"type": "string", "description": "Task description"},
                "session_id": {"type": "string", "description": "Existing session ID (optional)"},
            },
            "required": ["task"],
        },
    },
    {
        "name": "vfs_fact_add",
        "description": "Record a verified fact with evidence.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "claim": {"type": "string", "description": "The claim being verified"},
                "evidence": {"type": "string", "description": "Evidence supporting the claim"},
                "source": {"type": "string", "description": "Source of verification (e.g., 'dst', 'code_review')"},
                "command": {"type": "string", "description": "Command used (optional)"},
            },
            "required": ["claim", "evidence", "source"],
        },
    },
    {
        "name": "vfs_fact_check",
        "description": "Check if a claim has been verified.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "claim_pattern": {"type": "string", "description": "Pattern to search for in claims"},
            },
            "required": ["claim_pattern"],
        },
    },
    {
        "name": "vfs_fact_list",
        "description": "List all verified facts in chronological order.",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "vfs_invariant_verify",
        "description": "Mark an invariant as verified.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Invariant name"},
                "component": {"type": "string", "description": "Component name"},
                "method": {"type": "string", "description": "Verification method (dst, stateright, kani, manual)"},
                "evidence": {"type": "string", "description": "Evidence of verification"},
            },
            "required": ["name", "component", "method"],
        },
    },
    {
        "name": "vfs_invariant_status",
        "description": "Check invariant verification status for a component.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "component": {"type": "string", "description": "Component name"},
            },
            "required": ["component"],
        },
    },
    {
        "name": "vfs_status",
        "description": "Get current verification session status.",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "vfs_tool_start",
        "description": "Start tracking a tool call.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Tool name"},
                "args": {"type": "object", "description": "Tool arguments"},
            },
            "required": ["name", "args"],
        },
    },
    {
        "name": "vfs_tool_success",
        "description": "Mark tool call as successful.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "call_id": {"type": "integer", "description": "Call ID from vfs_tool_start"},
                "result": {"description": "Tool result"},
            },
            "required": ["call_id", "result"],
        },
    },
    {
        "name": "vfs_tool_error",
        "description": "Mark tool call as failed.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "call_id": {"type": "integer", "description": "Call ID from vfs_tool_start"},
                "error": {"type": "string", "description": "Error message"},
            },
            "required": ["call_id", "error"],
        },
    },
    {
        "name": "vfs_tool_list",
        "description": "List all tool calls with timing.",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
]


# ==================== Index Tools ====================

INDEX_TOOLS: list[Tool] = [
    {
        "name": "index_symbols",
        "description": "Find symbols matching a pattern across the codebase.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "pattern": {"type": "string", "description": "Pattern to match (regex or simple string)"},
                "kind": {"type": "string", "description": "Symbol kind filter (function, struct, enum, trait, etc.)"},
            },
            "required": ["pattern"],
        },
    },
    {
        "name": "index_tests",
        "description": "Find tests by name pattern or crate.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "pattern": {"type": "string", "description": "Test name pattern (optional)"},
                "crate": {"type": "string", "description": "Crate filter (optional)"},
            },
        },
    },
    {
        "name": "index_modules",
        "description": "Get module hierarchy information.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "crate": {"type": "string", "description": "Crate filter (optional)"},
            },
        },
    },
    {
        "name": "index_deps",
        "description": "Get dependency graph information.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "crate": {"type": "string", "description": "Get dependencies for specific crate (optional)"},
            },
        },
    },
    {
        "name": "index_status",
        "description": "Get status of all indexes (freshness, file counts).",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "index_refresh",
        "description": "Rebuild indexes using Python indexer.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "scope": {
                    "type": "string",
                    "description": "Which index to rebuild (symbols, tests, modules, dependencies, all)",
                    "enum": ["symbols", "tests", "modules", "dependencies", "all"],
                },
            },
        },
    },
]


# ==================== Verification Tools ====================

VERIFICATION_TOOLS: list[Tool] = [
    {
        "name": "verify_claim",
        "description": "Verify a claim by executing a command.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "claim": {"type": "string", "description": "Claim to verify"},
                "method": {"type": "string", "description": "Verification command (e.g., 'cargo test', 'cargo clippy')"},
            },
            "required": ["claim", "method"],
        },
    },
    {
        "name": "verify_all_tests",
        "description": "Run all tests (cargo test --all).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "release": {"type": "boolean", "description": "Run in release mode"},
            },
        },
    },
    {
        "name": "verify_clippy",
        "description": "Run Rust linter (cargo clippy).",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "verify_fmt",
        "description": "Check code formatting (cargo fmt --check).",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
]


# ==================== DST Tools ====================

DST_TOOLS: list[Tool] = [
    {
        "name": "dst_coverage_check",
        "description": "Check DST coverage for critical paths (simulation-first compliance).",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "dst_gaps_report",
        "description": "Generate report of DST coverage gaps.",
        "inputSchema": {
            "type": "object",
            "properties": {},
        },
    },
    {
        "name": "harness_check",
        "description": "Check if DST harness supports required fault types.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "fault_types": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "List of fault types (e.g., StorageWriteFail, NetworkPartition)",
                },
            },
            "required": ["fault_types"],
        },
    },
]


# ==================== Codebase Tools ====================

CODEBASE_TOOLS: list[Tool] = [
    {
        "name": "codebase_grep",
        "description": "Search for pattern in codebase files.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "pattern": {"type": "string", "description": "Search pattern (regex)"},
                "glob": {"type": "string", "description": "File glob pattern (e.g., '**/*.rs')"},
                "max_matches": {"type": "integer", "description": "Maximum matches to return (default 100)"},
            },
            "required": ["pattern"],
        },
    },
    {
        "name": "codebase_peek",
        "description": "Peek at first N lines of a file.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "File path (relative to codebase root)"},
                "lines": {"type": "integer", "description": "Number of lines to show (default 20)"},
            },
            "required": ["path"],
        },
    },
    {
        "name": "codebase_read_section",
        "description": "Read a section of a file by line range.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "File path"},
                "start_line": {"type": "integer", "description": "Start line number"},
                "end_line": {"type": "integer", "description": "End line number"},
            },
            "required": ["path", "start_line", "end_line"],
        },
    },
    {
        "name": "codebase_list_files",
        "description": "List files matching a glob pattern.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "pattern": {"type": "string", "description": "Glob pattern (e.g., '**/*.rs')"},
            },
            "required": ["pattern"],
        },
    },
]


# All tools combined
ALL_TOOLS: list[Tool] = [
    *REPL_TOOLS,
    *AGENTFS_TOOLS,
    *INDEX_TOOLS,
    *VERIFICATION_TOOLS,
    *DST_TOOLS,
    *CODEBASE_TOOLS,
]

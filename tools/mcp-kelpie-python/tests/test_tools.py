"""
Tests for MCP tools module.

Tests cover:
- Tool definitions
- Handler routing
- Individual tool handlers
"""

import asyncio
import pytest
import tempfile
from pathlib import Path

from mcp_kelpie.tools import ALL_TOOLS, ToolHandlers
from mcp_kelpie.tools.definitions import (
    REPL_TOOLS,
    AGENTFS_TOOLS,
    INDEX_TOOLS,
    VERIFICATION_TOOLS,
    DST_TOOLS,
    CODEBASE_TOOLS,
)


# ==================== Tool Definitions Tests ====================


class TestToolDefinitions:
    """Test tool definition schemas."""

    def test_all_tools_count(self):
        """Verify total tool count."""
        expected = (
            len(REPL_TOOLS)
            + len(AGENTFS_TOOLS)
            + len(INDEX_TOOLS)
            + len(VERIFICATION_TOOLS)
            + len(DST_TOOLS)
            + len(CODEBASE_TOOLS)
        )
        assert len(ALL_TOOLS) == expected

    def test_repl_tools_names(self):
        """Verify REPL tool names."""
        names = {t["name"] for t in REPL_TOOLS}
        assert "repl_load" in names
        assert "repl_exec" in names
        assert "repl_query" in names
        assert "repl_state" in names
        assert "repl_clear" in names

    def test_vfs_tools_names(self):
        """Verify VFS/AgentFS tool names."""
        names = {t["name"] for t in AGENTFS_TOOLS}
        assert "vfs_init" in names
        assert "vfs_fact_add" in names
        assert "vfs_status" in names
        assert "vfs_tool_start" in names

    def test_index_tools_names(self):
        """Verify index tool names."""
        names = {t["name"] for t in INDEX_TOOLS}
        assert "index_symbols" in names
        assert "index_tests" in names
        assert "index_refresh" in names

    def test_verify_tools_names(self):
        """Verify verification tool names."""
        names = {t["name"] for t in VERIFICATION_TOOLS}
        assert "verify_claim" in names
        assert "verify_all_tests" in names
        assert "verify_clippy" in names
        assert "verify_fmt" in names

    def test_dst_tools_names(self):
        """Verify DST tool names."""
        names = {t["name"] for t in DST_TOOLS}
        assert "dst_coverage_check" in names
        assert "dst_gaps_report" in names
        assert "harness_check" in names

    def test_codebase_tools_names(self):
        """Verify codebase tool names."""
        names = {t["name"] for t in CODEBASE_TOOLS}
        assert "codebase_grep" in names
        assert "codebase_peek" in names
        assert "codebase_list_files" in names

    def test_tool_schema_format(self):
        """Verify all tools have required schema fields."""
        for tool in ALL_TOOLS:
            assert "name" in tool, f"Tool missing name: {tool}"
            assert "description" in tool, f"Tool missing description: {tool}"
            assert "inputSchema" in tool, f"Tool missing inputSchema: {tool}"
            assert tool["inputSchema"]["type"] == "object"


# ==================== Handler Routing Tests ====================


@pytest.fixture
def temp_codebase():
    """Create a temporary codebase for testing."""
    with tempfile.TemporaryDirectory() as tmpdir:
        root = Path(tmpdir)

        # Create a minimal Rust project structure
        src_dir = root / "src"
        src_dir.mkdir()

        # Create lib.rs
        (src_dir / "lib.rs").write_text("""
//! Test library

pub fn test_function() -> i32 {
    42
}

#[test]
fn test_it_works() {
    assert_eq!(test_function(), 42);
}
""")

        # Create Cargo.toml
        (root / "Cargo.toml").write_text("""
[package]
name = "test-crate"
version = "0.1.0"
edition = "2021"
""")

        yield root


class TestHandlerRouting:
    """Test handler routing logic."""

    def test_handlers_init(self, temp_codebase):
        """Test handlers initialization."""
        handlers = ToolHandlers(temp_codebase)
        # Resolve both paths to handle macOS /var -> /private/var symlink
        assert handlers.codebase_path.resolve() == temp_codebase.resolve()

    @pytest.mark.asyncio
    async def test_handle_unknown_tool(self, temp_codebase):
        """Test handling of unknown tool."""
        handlers = ToolHandlers(temp_codebase)

        with pytest.raises(ValueError, match="Unknown tool"):
            await handlers.handle_tool("nonexistent_tool", {})

    @pytest.mark.asyncio
    async def test_handle_repl_state(self, temp_codebase):
        """Test repl_state handler."""
        handlers = ToolHandlers(temp_codebase)
        result = await handlers.handle_tool("repl_state", {})

        assert "variables" in result
        assert "total_size_bytes" in result

    @pytest.mark.asyncio
    async def test_handle_vfs_init(self, temp_codebase):
        """Test vfs_init handler."""
        handlers = ToolHandlers(temp_codebase)
        result = await handlers.handle_tool("vfs_init", {"task": "Test task"})

        assert "session_id" in result
        assert result["task"] == "Test task"

    @pytest.mark.asyncio
    async def test_handle_index_status(self, temp_codebase):
        """Test index_status handler."""
        handlers = ToolHandlers(temp_codebase)
        result = await handlers.handle_tool("index_status", {})

        assert result["success"]
        assert "status" in result


# ==================== Codebase Tools Tests ====================


class TestCodebaseTools:
    """Test codebase-related tools."""

    @pytest.mark.asyncio
    async def test_codebase_list_files(self, temp_codebase):
        """Test codebase_list_files handler."""
        handlers = ToolHandlers(temp_codebase)
        result = await handlers.handle_tool("codebase_list_files", {"pattern": "**/*.rs"})

        assert result["success"]
        assert result["count"] >= 1
        assert any("lib.rs" in f for f in result["files"])

    @pytest.mark.asyncio
    async def test_codebase_peek(self, temp_codebase):
        """Test codebase_peek handler."""
        handlers = ToolHandlers(temp_codebase)
        result = await handlers.handle_tool("codebase_peek", {
            "path": "src/lib.rs",
            "lines": 5
        })

        assert result["success"]
        assert "Test library" in result["content"]

    @pytest.mark.asyncio
    async def test_codebase_grep(self, temp_codebase):
        """Test codebase_grep handler."""
        handlers = ToolHandlers(temp_codebase)
        result = await handlers.handle_tool("codebase_grep", {
            "pattern": "test_function",
            "glob": "**/*.rs"
        })

        assert result["success"]
        assert result["count"] >= 1


# ==================== REPL Tools Tests ====================


class TestReplTools:
    """Test REPL-related tools."""

    @pytest.mark.asyncio
    async def test_repl_load_and_query(self, temp_codebase):
        """Test repl_load and repl_query handlers."""
        handlers = ToolHandlers(temp_codebase)

        # Load files
        result = await handlers.handle_tool("repl_load", {
            "pattern": "**/*.rs",
            "var_name": "code"
        })
        assert result["success"]

        # Query loaded files
        result = await handlers.handle_tool("repl_query", {
            "expression": "len(code)"
        })
        assert result["success"]
        assert result["result"] >= 1

    @pytest.mark.asyncio
    async def test_repl_exec(self, temp_codebase):
        """Test repl_exec handler."""
        handlers = ToolHandlers(temp_codebase)

        # Load files first
        await handlers.handle_tool("repl_load", {
            "pattern": "**/*.rs",
            "var_name": "code"
        })

        # Execute code
        result = await handlers.handle_tool("repl_exec", {
            "code": "result = sum(len(c) for c in code.values())"
        })
        assert result["success"]
        assert result["result"] > 0

    @pytest.mark.asyncio
    async def test_repl_clear(self, temp_codebase):
        """Test repl_clear handler."""
        handlers = ToolHandlers(temp_codebase)

        # Load and clear
        await handlers.handle_tool("repl_load", {
            "pattern": "**/*.rs",
            "var_name": "code"
        })
        result = await handlers.handle_tool("repl_clear", {"var_name": "code"})

        assert result["success"]
        assert "freed" in result["message"]


# ==================== VFS Tools Tests ====================


class TestVfsTools:
    """Test VFS/AgentFS-related tools."""

    @pytest.mark.asyncio
    async def test_vfs_workflow(self, temp_codebase):
        """Test VFS workflow: init -> add fact -> check fact."""
        handlers = ToolHandlers(temp_codebase)

        # Initialize session
        result = await handlers.handle_tool("vfs_init", {"task": "Test workflow"})
        assert "session_id" in result

        # Add a fact
        result = await handlers.handle_tool("vfs_fact_add", {
            "claim": "Tests pass",
            "evidence": "cargo test output",
            "source": "test"
        })
        assert result["success"]

        # Check the fact
        result = await handlers.handle_tool("vfs_fact_check", {
            "claim_pattern": "Tests"
        })
        assert result["success"]
        assert result["count"] >= 1
        assert "facts" in result

    @pytest.mark.asyncio
    async def test_vfs_tool_tracking(self, temp_codebase):
        """Test VFS tool call tracking."""
        handlers = ToolHandlers(temp_codebase)

        # Initialize session
        await handlers.handle_tool("vfs_init", {"task": "Tool tracking test"})

        # Start a tool call
        result = await handlers.handle_tool("vfs_tool_start", {
            "name": "test_tool",
            "args": {"key": "value"}
        })
        assert "call_id" in result
        call_id = result["call_id"]

        # Mark success
        result = await handlers.handle_tool("vfs_tool_success", {
            "call_id": call_id,
            "result": "success"
        })
        assert result["success"]

        # List tool calls
        result = await handlers.handle_tool("vfs_tool_list", {})
        assert result["success"]
        assert "tools" in result
        assert len(result["tools"]) >= 1


# ==================== DST Tools Tests ====================


class TestDstTools:
    """Test DST-related tools."""

    @pytest.mark.asyncio
    async def test_harness_check(self, temp_codebase):
        """Test harness_check handler."""
        handlers = ToolHandlers(temp_codebase)

        result = await handlers.handle_tool("harness_check", {
            "fault_types": ["StorageWriteFail", "NetworkPartition", "UnknownFault"]
        })

        assert "results" in result
        assert result["supported_count"] == 2  # Two known faults
        assert result["total"] == 3

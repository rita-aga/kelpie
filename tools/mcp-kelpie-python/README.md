# Kelpie MCP Server

Single Python MCP server for Kelpie Repo OS, aligned with VDE (Verification-Driven Exploration) architecture.

## Architecture

This is a **single MCP server** combining:
- **RLM (Recursive Language Models)** - Context as variables, not tokens
- **AgentFS** - Persistent state across sessions (Turso AgentFS SDK)
- **Indexer** - Structural code analysis (tree-sitter)
- **Verification** - CLI execution tracking
- **DST** - Deterministic Simulation Testing coverage
- **Issues** - Persistent issue tracking

Based on QuickHouse VDE implementation (see `.progress/VDE.md`).

## Why Python?

1. **RLM requires Python** - Native REPL, dynamic execution, sub-LLM calls
2. **AgentFS SDK available** - Official Turso Python SDK
3. **State integration** - RLM + AgentFS in same process for tool tracking
4. **VDE proven** - QuickHouse uses Python MCP successfully

## Installation

```bash
cd tools/mcp-kelpie-python

# Install dependencies
pip install -e .

# Install dev dependencies
pip install -e ".[dev]"
```

## Usage

### Start MCP Server

```bash
mcp-kelpie
```

### Run Tests

```bash
pytest
```

## Tool Categories

### RLM Tools (6 tools)
- `repl_load` - Load files into server variable by glob
- `repl_exec` - Execute Python code on loaded variables
- `repl_query` - Evaluate expression and return result
- `repl_sub_llm` - Spawn sub-LLM to analyze variable
- `repl_state` - Show current variable names/sizes
- `repl_clear` - Clear variables to free memory

### VerificationFS Tools (10+ tools)
- `vfs_init` - Initialize session
- `vfs_fact_add/check/list` - Record and query verified facts
- `vfs_invariant_verify/status` - Track invariant verification
- `vfs_spec_read` - Record TLA+ spec reading
- `vfs_exploration_log` - Log exploration actions
- `vfs_status` - Session status
- `vfs_export` - Export session to JSON

### Tool Trajectory (AgentFS built-in)
- `vfs_tool_start` - Start tool call tracking
- `vfs_tool_success` - Mark tool call success
- `vfs_tool_error` - Mark tool call failure
- `vfs_tool_list` - List tool call history

### Index Tools (4 tools)
- `index_symbols` - Query symbols (functions, structs, traits)
- `index_tests` - Query test index
- `index_modules` - Query module hierarchy
- `index_deps` - Query dependency graph

### Verification Tools (4 tools)
- `verify_by_tests` - Run specific tests
- `verify_claim` - Verify arbitrary claim
- `verify_all_tests` - Full test suite
- `verify_clippy` - Linting check

### DST Tools (3 tools)
- `dst_coverage_check` - Verify critical path coverage
- `dst_gaps_report` - Find missing coverage
- `harness_check` - Validate harnesses

### Codebase Tools (3 tools)
- `codebase_grep` - Search without loading context
- `codebase_peek` - Sample file structure
- `codebase_read_section` - Focused reads

### Issue Tools (6 tools)
- `issue_record` - Record new issue
- `issue_update` - Update issue status
- `issue_query` - Query issues
- `issue_summary` - Get issue overview
- `examination_log` - Log what was examined
- `thoroughness_check` - Verify complete coverage

### Constraint Tools (2 tools)
- `constraint_check` - Check P0 constraints
- `constraint_list` - List all constraints

## Architecture

```
mcp_kelpie/
├── server.py              # Main MCP server
├── rlm/                   # RLM implementation
│   ├── repl.py            # Python REPL with state
│   ├── executor.py        # Safe code execution
│   └── llm_query.py       # Recursive LLM calls
├── agentfs/               # AgentFS wrapper
│   ├── wrapper.py         # VerificationFS
│   └── session.py         # Session management
├── indexer/               # Structural indexing
│   ├── symbols.py         # Symbol extraction
│   ├── dependencies.py    # Dependency graph
│   ├── tests.py           # Test discovery
│   └── modules.py         # Module hierarchy
└── tools/                 # Tool implementations
    ├── verify.py          # Verification
    ├── dst.py             # DST coverage
    ├── codebase.py        # Codebase operations
    ├── issues.py          # Issue tracking
    └── constraints.py     # Constraint checking
```

## Development

### Running Tests

```bash
# All tests
pytest

# Specific test file
pytest tests/test_rlm.py

# With coverage
pytest --cov=mcp_kelpie
```

### Code Formatting

```bash
# Format code
black mcp_kelpie/

# Lint
ruff check mcp_kelpie/
```

## Migration Status

This replaces:
- ❌ `tools/mcp-kelpie/` (TypeScript) → Python
- ❌ `tools/kelpie-indexer/` (Rust) → Python tree-sitter
- ❌ `tools/rlm-env/` (Python) → Integrated into MCP

See `.progress/VDE_CONSOLIDATION_PLAN.md` for details.

## References

- VDE Paper: `.progress/VDE.md`
- RLM Paper: https://arxiv.org/html/2512.24601v1
- AgentFS: https://docs.turso.tech/agentfs/introduction
- MCP Protocol: https://modelcontextprotocol.io

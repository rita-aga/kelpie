# Kelpie MCP Server

**MCP (Model Context Protocol) server for Kelpie Repo OS**

Provides tools for agents to:
- Query structural indexes (symbols, tests, dependencies, modules)
- Manage persistent state (AgentFS)
- Verify claims by execution (running tests, commands)
- Hard controls (freshness checks, evidence requirements)

## Installation

```bash
cd tools/mcp-kelpie
npm install
npm run build
```

## Usage

### Standalone Server

```bash
# Set environment variables
export KELPIE_CODEBASE_PATH=/path/to/kelpie
export KELPIE_INDEXES_PATH=/path/to/kelpie/.kelpie-index
export KELPIE_AGENTFS_PATH=/path/to/kelpie/.agentfs

# Run server
npm start
```

### MCP Configuration

Add to your MCP settings (e.g., Claude Desktop config):

```json
{
  "mcpServers": {
    "kelpie": {
      "command": "node",
      "args": [
        "/path/to/kelpie/tools/mcp-kelpie/dist/index.js"
      ],
      "env": {
        "KELPIE_CODEBASE_PATH": "/path/to/kelpie",
        "KELPIE_INDEXES_PATH": "/path/to/kelpie/.kelpie-index",
        "KELPIE_AGENTFS_PATH": "/path/to/kelpie/.agentfs"
      }
    }
  }
}
```

## Available Tools

### State Management Tools (Phase 4.2)

| Tool | Description | Arguments |
|------|-------------|-----------|
| `state_get` | Get value from agent state | `key: string` |
| `state_set` | Set value in agent state | `key: string, value: any` |
| `state_task_start` | Start a new task | `description: string` |
| `state_task_complete` | Mark task complete (requires proof) | `task_id: number, proof: string` |
| `state_verified_fact` | Store verified fact | `claim: string, method: string, result: string` |

### Index Query Tools (Phase 4.3)

| Tool | Description | Arguments |
|------|-------------|-----------|
| `index_symbols` | Find symbols matching pattern | `pattern: string, kind?: string` |
| `index_tests` | Find tests by topic or type | `topic?: string, type?: string` |
| `index_modules` | Get module hierarchy | `crate?: string` |
| `index_deps` | Get dependency graph | `crate?: string` |
| `index_status` | Get status of all indexes | (none) |

### Verification Tools (Phase 4.4)

| Tool | Description | Arguments |
|------|-------------|-----------|
| `verify_by_tests` | Run tests for a topic | `topic: string, type?: string` |
| `verify_claim` | Verify claim by execution | `claim: string, method: string` |
| `verify_all_tests` | Run all tests (cargo test --all) | `release?: boolean` |
| `verify_clippy` | Run clippy linter | (none) |

## Architecture

```
tools/mcp-kelpie/
├── package.json          # Dependencies and scripts
├── tsconfig.json         # TypeScript configuration
└── src/
    ├── index.ts          # MCP server entry point
    ├── audit.ts          # Audit logging (all tool calls)
    ├── state.ts          # AgentFS state management
    ├── indexes.ts        # Index query operations
    └── verify.ts         # Verification by execution
```

## Hard Controls

**TigerStyle: Hard controls enforce behavior that agents can't bypass**

### Freshness Checks

All index queries include freshness information. If indexes are stale (>1 hour old), a warning is returned.

### Evidence Requirements

`state_task_complete` requires proof parameter. Cannot mark task complete without verification evidence.

### Audit Trail

Every tool call is logged to `agent.db` audit_log table with:
- Timestamp
- Tool name
- Arguments
- Results (success/failure)

## Example Usage

### Query Symbols

```typescript
{
  "name": "index_symbols",
  "arguments": {
    "pattern": "FdbStorage",
    "kind": "struct"
  }
}
```

Returns:
```json
{
  "success": true,
  "matches": [
    {
      "file": "crates/kelpie-storage/src/fdb.rs",
      "name": "FdbStorage",
      "kind": "struct",
      "visibility": "pub",
      "line": 42
    }
  ],
  "count": 1,
  "freshness": {
    "fresh": true
  }
}
```

### Verify by Tests

```typescript
{
  "name": "verify_by_tests",
  "arguments": {
    "topic": "storage",
    "type": "dst"
  }
}
```

Returns:
```json
{
  "success": true,
  "topic": "storage",
  "tests_run": 8,
  "passed": 8,
  "failed": 0,
  "results": [...]
}
```

### Start and Complete Task

```typescript
// Start task
{
  "name": "state_task_start",
  "arguments": {
    "description": "Implement feature X"
  }
}

// Returns: { task_id: 1, ... }

// Complete task (requires proof!)
{
  "name": "state_task_complete",
  "arguments": {
    "task_id": 1,
    "proof": "cargo test passed: 74 tests, 0 failures"
  }
}
```

## Development

```bash
# Install dependencies
npm install

# Build TypeScript
npm run build

# Watch mode (rebuild on changes)
npm run dev

# Run server
npm start
```

## Status

- ✅ Phase 4.1: MCP Server Skeleton
- ✅ Phase 4.2: State Tools (AgentFS)
- ✅ Phase 4.3: Index Query Tools
- ✅ Phase 4.4: Verification Tools
- ❌ Phase 4.5: Index Management Tools (refresh, validate)
- ❌ Phase 4.6: Hard Control Gates (not yet implemented - future)
- ❌ Phase 4.7: Integrity Tools (mark_phase_complete, handoff verification - future)
- ❌ Phase 4.8: Slop Detection Tools (dead code, orphaned files - future)

## Next Steps

1. **Test MCP server** - Verify tools work end-to-end
2. **Phase 4.5-4.8** - Add remaining tools (optional, can be added later)
3. **Phase 5: RLM Skills** - Build agent skills that use RLM pattern

## References

- [Model Context Protocol](https://modelcontextprotocol.io/)
- [MCP SDK Documentation](https://github.com/modelcontextprotocol/typescript-sdk)
- [Kelpie Project](../../README.md)

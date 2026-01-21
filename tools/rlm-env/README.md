# RLM Environment

**RLM (Recursive Language Model) execution environment for Kelpie codebase**

## What is RLM?

RLM is an inference strategy where the LLM **never sees the full context directly**. Instead, context is stored as a variable in a REPL environment, and the LLM writes code to interact with it.

Reference: [alexzhang13.github.io/blog/2025/rlm](https://alexzhang13.github.io/blog/2025/rlm/)

## Architecture

```
┌─────────────────────────────────────┐
│  MCP Server (TypeScript)            │
│                                     │
│  Receives agent request to explore │
│  codebase                           │
└──────────────┬──────────────────────┘
               │
               │ spawn subprocess
               ▼
┌─────────────────────────────────────┐
│  rlm-env (Python)                   │
│                                     │
│  ┌─────────────────────────────┐   │
│  │ CodebaseContext             │   │
│  │ - grep(), peek(), read()    │   │
│  │ - Never loads full files    │   │
│  │ - Works with indexes        │   │
│  └─────────────────────────────┘   │
│                                     │
│  ┌─────────────────────────────┐   │
│  │ RLMEnvironment              │   │
│  │ - Sandboxed execution       │   │
│  │ - RestrictedPython          │   │
│  │ - 30s timeout               │   │
│  │ - Depth limit: 3            │   │
│  └─────────────────────────────┘   │
└─────────────────────────────────────┘
```

## Installation

```bash
cd tools/rlm-env
pip install -e .

# Or with dev dependencies
pip install -e ".[dev]"
```

## Usage

### CLI Interface

```bash
# Execute code directly
python -m rlm_env \
  --codebase /path/to/kelpie \
  --indexes /path/to/.kelpie-index \
  --execute "result = list_crates()"

# Read code from stdin
echo 'result = grep("FdbStorage")' | python -m rlm_env \
  --codebase /path/to/kelpie \
  --indexes /path/to/.kelpie-index \
  --stdin
```

### Python API

```python
from rlm_env import RLMEnvironment

# Initialize environment
env = RLMEnvironment(
    codebase_path="/path/to/kelpie",
    indexes_path="/path/to/.kelpie-index"
)

# Execute agent code
result = env.execute("""
# Find all FdbStorage references
matches = grep("FdbStorage", "**/*.rs")

# Get context around first match
if matches:
    context = read_context(matches[0].file, matches[0].line)
    result = context
else:
    result = "No matches found"
""")

print(result.success)  # True
print(result.result)   # Context around first match
print(result.execution_log)  # Execution trace
```

## Available Functions

Agent code has access to these functions via `CodebaseContext`:

### File Operations

```python
# List files matching glob pattern
files = list_files("**/*.rs")

# Peek at first N lines (default: 50)
header = peek("crates/kelpie-core/src/lib.rs", lines=30)

# Read specific line range
section = read_section("path/to/file.rs", start=10, end=20)

# Read context around a line (±10 lines by default)
context = read_context("path/to/file.rs", line=42, padding=10)
```

### Search Operations

```python
# Grep for pattern (returns GrepMatch objects)
matches = grep("fn.*actor", "**/*.rs", max_matches=50)

# Access match details
for match in matches:
    print(f"{match.file}:{match.line}: {match.content}")
```

### Index Operations

```python
# List all crates
crates = list_crates()

# List all modules (optionally filtered by crate)
modules = list_modules()
modules = list_modules(crate_name="kelpie-core")

# Get raw index data
symbols = get_index("symbols")
tests = get_index("tests")
deps = get_index("dependencies")

# List tests (with optional filters)
all_tests = list_tests()
storage_tests = list_tests(topic="storage")
dst_tests = list_tests(test_type="dst")
```

### Partitioning (for Map-Reduce)

```python
# Partition codebase by crate
crates = partition_by_crate()

for crate in crates:
    print(f"{crate.module_name}: {len(crate.files)} files")
```

## Sandboxing

The execution environment uses **RestrictedPython** to prevent dangerous operations:

### Allowed:
- ✅ Reading codebase via provided functions
- ✅ Accessing structural indexes
- ✅ Basic Python operations (list, dict, loops, etc.)
- ✅ Standard library functions (len, str, sorted, etc.)

### Blocked:
- ❌ Writing to filesystem
- ❌ Network requests
- ❌ Subprocess spawning
- ❌ Importing arbitrary modules
- ❌ Executing shell commands

### Limits:
- **Timeout:** 30 seconds per execution
- **Recursion:** Max depth of 3
- **Output:** Max 100KB
- **Grep matches:** Max 1000 results
- **File reads:** Max 500 lines per read

## Example Use Cases

### Find All Tests for a Feature

```python
# Find all storage-related tests
tests = list_tests(topic="storage")

# Get DST tests specifically
dst_tests = [t for t in tests if t["type"] == "dst"]

# Return commands to run them
result = [t["command"] for t in dst_tests]
```

### Map-Reduce Over Modules

```python
# Partition by crate
crates = partition_by_crate()

results = []
for crate in crates:
    # For each crate, search for TODO comments
    matches = grep("TODO", f"{crate.files[0]}/**/*.rs")
    if matches:
        results.append({
            "crate": crate.module_name,
            "todo_count": len(matches)
        })

result = results
```

### Find Dead Code Candidates

```python
# Find all public functions
symbols = get_index("symbols")
public_fns = []

for file_path, file_data in symbols["files"].items():
    for symbol in file_data["symbols"]:
        if symbol["kind"] == "fn" and symbol["visibility"] == "pub":
            public_fns.append({
                "name": symbol["name"],
                "file": file_path
            })

# Check which ones are never called
deps = get_index("dependencies")
# ... cross-reference with call graph

result = public_fns[:10]  # Return first 10 for analysis
```

## Testing

```bash
# Run tests
pytest

# Run with coverage
pytest --cov=rlm_env --cov-report=html

# Type checking
mypy rlm_env
```

## Integration with MCP Server

The MCP server will invoke this via subprocess:

```typescript
// tools/mcp-kelpie/src/rlm.ts
import { spawn } from "child_process";

export async function rlm_execute(code: string): Promise<RLMResult> {
  return new Promise((resolve, reject) => {
    const proc = spawn("python", [
      "-m", "rlm_env",
      "--codebase", CODEBASE_PATH,
      "--indexes", INDEXES_PATH,
      "--stdin"
    ]);

    proc.stdin.write(code);
    proc.stdin.end();

    let stdout = "";
    proc.stdout.on("data", (data) => stdout += data);
    proc.on("close", (code) => {
      if (code === 0) {
        resolve(JSON.parse(stdout));
      } else {
        reject(new Error(stdout));
      }
    });
  });
}
```

## Security

**TigerStyle: Defense in depth**

1. **RestrictedPython**: Prevents dangerous operations at Python level
2. **Timeout**: 30s limit prevents infinite loops
3. **Depth limit**: Prevents unbounded recursion
4. **Read-only**: No filesystem writes, only reads
5. **Subprocess isolation**: MCP server spawns fresh process per execution
6. **No network**: Cannot make external requests

## Status

- ✅ Package structure
- ✅ CodebaseContext (grep, peek, read, list operations)
- ✅ RLMEnvironment (sandboxed execution)
- ✅ CLI interface
- ✅ Index integration (symbols, tests, dependencies, modules)
- ✅ Tests (35+ tests for CodebaseContext and RLMEnvironment)
- ✅ Output size enforcement (100KB limit)
- ✅ FINAL() method for completion signaling
- ✅ _safe_print() for captured output
- ✅ map_reduce() for partition + map pattern
- ❌ Recursive LLM calls (requires Claude API integration)
- ❌ MCP server integration (Phase 4)

## Next Steps

1. **LLM integration** - Implement `spawn_recursive()` with Claude API
2. **MCP tool** - Add `rlm_execute` tool to MCP server (Phase 4)
3. **RLM skills** - Build agent skills that use RLM (Phase 5)

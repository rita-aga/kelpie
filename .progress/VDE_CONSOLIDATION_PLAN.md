# VDE Consolidation Plan: Python MCP Migration

**Created:** 2026-01-22
**Goal:** Consolidate all Repo OS infrastructure into single Python MCP server, aligned with VDE architecture

---

## Current State (Fragmented)

```
tools/
├── kelpie-indexer/          # 1,456 lines Rust (standalone binary)
├── mcp-kelpie/              # 4,300 lines TypeScript (MCP server)
└── rlm-env/                 # 450 lines Python (separate package)

.archive/                     # Old code (to be deleted)
```

**Problems:**
1. Three separate implementations (Rust, TypeScript, Python)
2. Not aligned with VDE's proven architecture
3. Archive directory taking up space
4. More complex for agents (multiple entry points)

---

## Target State (VDE-aligned)

```
tools/
└── mcp-kelpie/              # Single Python MCP server
    ├── server.py            # Main MCP server (entry point)
    ├── rlm.py               # RLM tools (repl_load, repl_exec, repl_sub_llm)
    ├── agentfs.py           # VerificationFS wrapper over Turso AgentFS SDK
    ├── indexes.py           # Indexer logic (tree-sitter Python)
    ├── verify.py            # Verification tools (CLI execution)
    ├── dst.py               # DST coverage checking
    ├── codebase.py          # Grep/peek/read operations
    ├── issues.py            # Issue tracking
    ├── constraints.py       # P0 constraint checking
    ├── audit.py             # Audit logging
    └── requirements.txt     # Python dependencies
```

**Benefits:**
1. Single language (Python) - easier to maintain
2. Matches QuickHouse VDE architecture exactly
3. All tools in one MCP server (simpler for agents)
4. Can reuse existing `rlm-env` code directly

---

## VDE Reference Architecture

From VDE.md section 4.2, QuickHouse's MCP server provides:

### Tool Categories (25 tools in 4 categories):

1. **RLM Tools** - Context as variables, not tokens
   ```python
   "repl_load"     # Load files into server variable by glob
   "repl_exec"     # Execute Python code on loaded variables
   "repl_query"    # Evaluate expression and return result
   "repl_sub_llm"  # Spawn sub-LLM to analyze variable IN SERVER
   "repl_state"    # Show current variable names/sizes
   "repl_clear"    # Clear variables to free memory
   ```

2. **VerificationFS Tools** - SQLite persistence via Turso AgentFS SDK
   ```python
   "vfs_init"              # Initialize session
   "vfs_fact_add"          # Record verified fact with evidence
   "vfs_fact_check"        # Query verified facts
   "vfs_fact_list"         # List all facts
   "vfs_invariant_verify"  # Mark invariant as verified
   "vfs_invariant_status"  # Check unverified invariants
   "vfs_spec_read"         # Record TLA+ spec reading
   "vfs_exploration_log"   # Log exploration actions
   "vfs_status"            # Session status
   "vfs_export"            # Export session to JSON
   ```

3. **Tool Trajectory** - Native AgentFS SDK
   ```python
   "vfs_tool_start"    # Start tool call tracking
   "vfs_tool_success"  # Mark tool call success
   "vfs_tool_error"    # Mark tool call failure
   "vfs_tool_list"     # List tool call history
   ```

4. **DDSQL Tool** - Production telemetry (Datadog SQL)
   ```python
   "ddsql_query"       # Execute SQL against Datadog Retriever
   ```

### Key VDE Patterns to Adopt:

1. **AgentFS SDK Usage:**
   ```python
   from agentfs import AgentFS, AgentFSOptions

   # Open AgentFS with SQLite backend
   afs = await AgentFS.open(AgentFSOptions(
       id=session_id,
       path=str(db_path)
   ))

   # Use KV store with namespaced keys
   await afs.kv.set(f"vfs:fact:{fact_id}", fact)

   # Tool call tracking built-in
   call_id = await afs.tools.start("tool_name", args)
   await afs.tools.success(call_id, result)
   ```

2. **VerificationFS Wrapper:**
   ```python
   class VerificationFS:
       """Extends AgentFS with verification-specific semantics."""
       PREFIX_FACT = "vfs:fact:"
       PREFIX_INVARIANT = "vfs:invariant:"
       PREFIX_SPEC = "vfs:spec:"
       PREFIX_CACHE = "vfs:cache:"
       PREFIX_EXPLORATION = "vfs:exploration:"

       def __init__(self, afs: AgentFS, session_id: str, task: str):
           self.afs = afs
           self.session_id = session_id
           self.task = task
   ```

3. **RLM Pattern:**
   ```python
   # Load codebase into server variable (NOT in LLM context)
   repl_load("**/*.rs", "code", "/path/to/crates")
   # → "Loaded 274 files (5.4MB)" (0 tokens in model context)

   # Execute code on the variable
   repl_exec("""
   import re
   for path, content in code.items():
       for match in re.findall(r'const.*BYTES_MAX.*', content):
           print(f"{path}: {match}")
   """)

   # Spawn sub-LLM to analyze IN THE SERVER
   repl_sub_llm("code", "Which limits could cause OOM?")
   # → Haiku analyzes in server, returns summary to main LLM
   ```

4. **CLI-First Verification:**
   - MCP does NOT wrap `cargo test` or `cargo clippy`
   - Agent runs them directly via CLI
   - MCP only tracks results in AgentFS

---

## Migration Plan

### Phase 1: Immediate Cleanup ✅
**Goal:** Remove archive, prepare for migration

**Actions:**
```bash
# 1. Delete archive completely
rm -rf .archive/

# 2. Commit deletion
git add .archive/
git commit -m "chore: Remove archived code completely

Deleted:
- .archive/specs.py, intelligence.py (shallow pattern matching)
- .archive/*.yaml (static spec files)
- .archive/skills/ (consolidated into CLAUDE.md)

These were archived in Phase 16.5. History preserved in git.
Next: VDE consolidation to Python MCP.

Related: .progress/026 Phase 16.5, VDE_CONSOLIDATION_PLAN.md"
```

### Phase 2: Create Python MCP Structure
**Goal:** Set up new Python MCP server scaffolding

**Actions:**
```bash
# 1. Create new directory structure
mkdir -p tools/mcp-kelpie-python
cd tools/mcp-kelpie-python

# 2. Initialize Python package
cat > pyproject.toml << 'EOF'
[project]
name = "mcp-kelpie"
version = "0.1.0"
description = "MCP server for Kelpie Repo OS - VDE-aligned"
requires-python = ">=3.11"
dependencies = [
    "mcp>=1.0.0",
    "agentfs-sdk>=0.5.3",
    "tree-sitter>=0.21.0",
    "tree-sitter-rust>=0.21.0",
    "anthropic>=0.34.0",
]

[project.scripts]
mcp-kelpie = "mcp_kelpie.server:main"
EOF

# 3. Create package structure
mkdir -p mcp_kelpie
touch mcp_kelpie/__init__.py
touch mcp_kelpie/server.py
touch mcp_kelpie/rlm.py
touch mcp_kelpie/agentfs.py
touch mcp_kelpie/indexes.py
touch mcp_kelpie/verify.py
touch mcp_kelpie/dst.py
touch mcp_kelpie/codebase.py
touch mcp_kelpie/issues.py
touch mcp_kelpie/constraints.py
touch mcp_kelpie/audit.py
```

### Phase 3: Port AgentFS Integration
**Goal:** Implement VerificationFS wrapper over Turso AgentFS SDK

**Source:** VDE.md section 4.4
**Target:** `mcp_kelpie/agentfs.py`

**Implementation:**
```python
"""
VerificationFS - AgentFS wrapper with verification semantics

Based on QuickHouse VDE implementation (VDE.md section 4.4)
"""
from agentfs import AgentFS, AgentFSOptions
from pathlib import Path
from datetime import datetime
from contextlib import asynccontextmanager
import hashlib
import time

class VerificationFS:
    """Verification-driven extension of Turso AgentFS."""

    # KV store prefixes for different verification entities
    PREFIX_SESSION = "vfs:session:"
    PREFIX_FACT = "vfs:fact:"
    PREFIX_INVARIANT = "vfs:invariant:"
    PREFIX_SPEC = "vfs:spec:"
    PREFIX_CACHE = "vfs:cache:"
    PREFIX_EXPLORATION = "vfs:exploration:"

    @classmethod
    @asynccontextmanager
    async def open(cls, session_id: str, task: str, project_root: str):
        """Open or resume a verification session."""
        db_path = Path(project_root) / ".agentfs" / f"agentfs-{session_id}.db"
        db_path.parent.mkdir(parents=True, exist_ok=True)

        # Open Turso AgentFS with SQLite backend
        afs = await AgentFS.open(AgentFSOptions(
            id=session_id,
            path=str(db_path)
        ))

        vfs = cls(afs, session_id, task)
        yield vfs
        # AgentFS handles cleanup

    def __init__(self, afs: AgentFS, session_id: str, task: str):
        self.afs = afs
        self.session_id = session_id
        self.task = task

    async def add_fact(self, claim: str, evidence: str, source: str,
                       command: str = None, query: str = None):
        """Record a verified fact with evidence."""
        fact_id = f"{int(time.time() * 1000)}"
        fact = {
            "id": fact_id,
            "claim": claim,
            "evidence": evidence,
            "source": source,
            "timestamp": datetime.utcnow().isoformat(),
            "command": command,
            "query": query
        }
        await self.afs.kv.set(f"{self.PREFIX_FACT}{fact_id}", fact)
        return fact_id

    async def verify_invariant(self, name: str, component: str,
                               method: str = "dst", evidence: str = None):
        """Mark an invariant as verified."""
        inv = {
            "name": name,
            "component": component,
            "method": method,
            "verified_at": datetime.utcnow().isoformat(),
            "evidence": evidence
        }
        key = f"{self.PREFIX_INVARIANT}{component}:{name}"
        await self.afs.kv.set(key, inv)

    async def cache_query(self, query: str, result: dict, ttl_minutes: int = 30):
        """Cache a query result with TTL."""
        cache_key = hashlib.sha256(query.encode()).hexdigest()[:16]
        entry = {
            "query": query,
            "result": result,
            "timestamp": datetime.utcnow().isoformat(),
            "ttl_minutes": ttl_minutes
        }
        await self.afs.kv.set(f"{self.PREFIX_CACHE}{cache_key}", entry)

    # ... additional methods from VDE ...
```

**Tests Required:**
- Session initialization and resumption
- Fact recording and retrieval
- Invariant tracking
- Cache TTL behavior
- Tool call trajectory

### Phase 4: Port RLM Tools
**Goal:** Move RLM environment into MCP

**Source:** `tools/rlm-env/rlm_env/` (existing working code)
**Target:** `mcp_kelpie/rlm.py`

**Implementation Strategy:**
1. Copy `rlm_env/codebase.py` → `rlm.py` (CodebaseContext class)
2. Copy `rlm_env/environment.py` → `rlm.py` (RLMEnvironment class)
3. Integrate with MCP tool interface
4. Add `repl_sub_llm` using Anthropic API (Haiku)

**Key RLM Tools:**
```python
async def repl_load(pattern: str, var_name: str, path: str = None):
    """Load files into server variable by glob pattern."""
    # Load files matching pattern into server-side variable
    # Return: "Loaded N files (X MB)" - NOT the files themselves
    pass

async def repl_exec(code: str):
    """Execute Python code on loaded variables."""
    # Execute in safe context with loaded variables
    # Return: stdout/stderr from execution
    pass

async def repl_sub_llm(var_name: str, query: str, model: str = "haiku"):
    """Spawn sub-LLM to analyze variable IN THE SERVER."""
    # Send variable content + query to Haiku
    # Return: Summary/answer (NOT full content)
    pass
```

**Tests Required:**
- Load files without consuming context
- Execute code on loaded variables
- Sub-LLM spawning and response
- Variable state management

### Phase 5: Port Indexer Logic
**Goal:** Replace Rust indexer with Python tree-sitter

**Source:** `tools/kelpie-indexer/src/main.rs` (1,456 lines)
**Target:** `mcp_kelpie/indexes.py`

**Dependencies:**
```bash
pip install tree-sitter tree-sitter-rust
```

**Implementation:**
```python
"""
Structural indexer using tree-sitter

Replaces Rust kelpie-indexer with Python implementation
Uses tree-sitter for fast, deterministic parsing
"""
from tree_sitter import Language, Parser
import tree_sitter_rust as tsrust
from pathlib import Path
import json
from dataclasses import dataclass
from typing import List, Dict

@dataclass
class Symbol:
    name: str
    kind: str  # "function", "struct", "trait", "impl"
    file: str
    line: int
    visibility: str  # "pub", "pub(crate)", "private"

class StructuralIndexer:
    """Parse Rust code and extract structural information."""

    def __init__(self, codebase_path: str):
        self.codebase_path = Path(codebase_path)
        self.parser = Parser()
        self.parser.set_language(Language(tsrust.language()))

    def build_symbol_index(self) -> List[Symbol]:
        """Extract all symbols from Rust files."""
        symbols = []
        for rs_file in self.codebase_path.rglob("*.rs"):
            symbols.extend(self._parse_file(rs_file))
        return symbols

    def _parse_file(self, file: Path) -> List[Symbol]:
        """Parse single Rust file."""
        content = file.read_bytes()
        tree = self.parser.parse(content)

        symbols = []
        # Walk tree and extract symbols
        # ... tree-sitter query logic ...
        return symbols
```

**Migration Strategy:**
1. Port symbol extraction (functions, structs, traits, impls)
2. Port dependency graph (via `cargo metadata` subprocess)
3. Port test discovery (regex + tree-sitter)
4. Port module hierarchy extraction
5. Verify output matches existing JSON format

**Tests Required:**
- Symbol extraction accuracy (compare with Rust version)
- Dependency graph correctness
- Test discovery completeness
- Module hierarchy accuracy

### Phase 6: Port Verification & DST Tools
**Goal:** Port verification and DST tooling from TypeScript

**Source:** `tools/mcp-kelpie/src/verify.ts`, `dst.ts`
**Target:** `mcp_kelpie/verify.py`, `dst.py`

**Implementation:**
```python
"""
Verification tools - CLI execution wrapper

Does NOT wrap cargo test/clippy in MCP tools (Phase 16.6)
Agent runs CLI directly, MCP tracks results in AgentFS
"""
import subprocess
from pathlib import Path

def run_tests(package: str = None, filter: str = None) -> dict:
    """Run cargo test and capture output."""
    cmd = ["cargo", "test"]
    if package:
        cmd.extend(["-p", package])
    if filter:
        cmd.append(filter)

    result = subprocess.run(cmd, capture_output=True, text=True)
    return {
        "success": result.returncode == 0,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "command": " ".join(cmd)
    }

def check_dst_coverage(critical_paths: List[str]) -> dict:
    """Check if critical paths have DST tests."""
    # Parse kelpie-dst crate for test functions
    # Match against critical paths
    # Return coverage report
    pass
```

**Tests Required:**
- CLI execution and output capture
- DST coverage detection accuracy
- Critical path mapping

### Phase 7: Port Remaining Tools
**Goal:** Port codebase, issues, constraints, slop detection

**Source:** TypeScript implementations
**Target:** Python equivalents

**Priority Order:**
1. `codebase.py` - grep, peek, read_section (HIGH - needed for RLM)
2. `issues.py` - issue tracking, examination logs (HIGH - for thoroughness)
3. `constraints.py` - P0 constraint checking (MEDIUM)
4. `audit.py` - audit logging (MEDIUM - AgentFS handles most)

**Tests Required:**
- Each tool category has test coverage
- Integration tests for workflows

### Phase 8: Update Documentation
**Goal:** Update all docs to reference Python MCP

**Files to Update:**
1. `CLAUDE.md` - Update tool references, commands
2. `.progress/026_20260120_repo_os_rlm_infrastructure.md` - Mark as migrated
3. `README.md` - Update setup instructions
4. `.kelpie-index/README.md` - Update indexer references

**Example CLAUDE.md changes:**
```markdown
## Repo OS Infrastructure

Kelpie includes a **Repo OS** infrastructure for AI agent-driven development.

### Quick Reference

```bash
# Build all indexes
python -m mcp_kelpie.indexes full

# Start MCP server
python -m mcp_kelpie.server

# Run tests
pytest tests/
```

### MCP Tools Available

See VDE.md for full reference. Key categories:
- RLM tools (repl_load, repl_exec, repl_sub_llm)
- VerificationFS tools (vfs_*)
- Index queries (index_*)
- Verification (CLI-first, not wrapped)
```

### Phase 9: Remove Old Implementations
**Goal:** Clean up TypeScript MCP and Rust indexer

**Actions:**
```bash
# 1. Move to archive (temporary backup)
mkdir -p .migration-backup
mv tools/mcp-kelpie .migration-backup/mcp-kelpie-typescript
mv tools/kelpie-indexer .migration-backup/kelpie-indexer-rust

# 2. Rename Python implementation
mv tools/mcp-kelpie-python tools/mcp-kelpie

# 3. Test thoroughly
pytest tools/mcp-kelpie/tests/

# 4. If all good, delete backup
rm -rf .migration-backup/

# 5. Commit
git add -A
git commit -m "refactor: Migrate to Python MCP (VDE-aligned)

Consolidated all Repo OS infrastructure into single Python MCP server:
- Merged RLM environment into MCP
- Ported indexer logic to Python (tree-sitter)
- Integrated AgentFS SDK (Turso)
- Aligned with QuickHouse VDE architecture

Benefits:
- Single language (Python) - easier to maintain
- Matches VDE proven architecture
- All tools in one MCP server
- Reused existing rlm-env code

Removed:
- tools/mcp-kelpie (TypeScript) → Python
- tools/kelpie-indexer (Rust) → Python tree-sitter
- tools/rlm-env → Integrated into MCP

Related: VDE_CONSOLIDATION_PLAN.md, VDE.md section 4.2"
```

---

## Testing Strategy

### Unit Tests (pytest)
```bash
# Test structure
tests/
├── test_agentfs.py       # VerificationFS wrapper
├── test_rlm.py           # RLM tools
├── test_indexes.py       # Indexer logic
├── test_verify.py        # Verification tools
├── test_dst.py           # DST coverage
└── integration/
    ├── test_workflow.py  # Full workflows
    └── test_handoff.py   # Multi-agent handoff
```

### Integration Tests
1. Full index build → query → verify flow
2. RLM load → exec → sub-llm flow
3. AgentFS session → fact recording → retrieval
4. Phase completion → verification → handoff

### Comparison Tests
1. Compare Python indexer output with Rust version
2. Verify structural index JSON format unchanged
3. Ensure MCP tool signatures match TypeScript version
4. Validate AgentFS schema compatibility

---

## Migration Checklist

### Phase 1: Cleanup ✅
- [ ] Delete `.archive/` directory
- [ ] Commit deletion

### Phase 2: Python MCP Structure
- [ ] Create `tools/mcp-kelpie-python/` directory
- [ ] Set up `pyproject.toml` with dependencies
- [ ] Create package structure (`mcp_kelpie/`)
- [ ] Set up test structure

### Phase 3: AgentFS
- [ ] Install `agentfs-sdk` Python package
- [ ] Implement `VerificationFS` wrapper
- [ ] Port fact/invariant/cache methods
- [ ] Write unit tests
- [ ] Verify SQLite schema compatibility

### Phase 4: RLM
- [ ] Copy code from `tools/rlm-env/`
- [ ] Implement `repl_load` tool
- [ ] Implement `repl_exec` tool
- [ ] Implement `repl_sub_llm` tool (Haiku API)
- [ ] Write unit tests
- [ ] Test with large codebase load

### Phase 5: Indexer
- [ ] Install tree-sitter Python
- [ ] Port symbol extraction
- [ ] Port dependency graph
- [ ] Port test discovery
- [ ] Port module hierarchy
- [ ] Write unit tests
- [ ] Compare output with Rust version

### Phase 6: Verification
- [ ] Port `verify.py` (CLI wrappers)
- [ ] Port `dst.py` (coverage checking)
- [ ] Write unit tests
- [ ] Verify CLI execution works

### Phase 7: Remaining Tools
- [ ] Port `codebase.py`
- [ ] Port `issues.py`
- [ ] Port `constraints.py`
- [ ] Port `audit.py`
- [ ] Write unit tests

### Phase 8: Documentation
- [ ] Update `CLAUDE.md`
- [ ] Update `.progress/026_*`
- [ ] Update `README.md`
- [ ] Update `.kelpie-index/README.md`
- [ ] Document Python MCP usage

### Phase 9: Cleanup
- [ ] Run full test suite
- [ ] Verify all workflows work
- [ ] Move old implementations to backup
- [ ] Rename Python MCP to `tools/mcp-kelpie`
- [ ] Delete backup after verification
- [ ] Final commit

---

## Success Criteria

1. **Functionality:** All existing MCP tools work in Python version
2. **Performance:** Indexer performance comparable to Rust version
3. **Tests:** All tests passing (unit + integration)
4. **Compatibility:** Index JSON format unchanged
5. **Documentation:** All docs updated
6. **VDE Alignment:** Architecture matches QuickHouse exactly

---

## Rollback Plan

If migration fails:
1. Restore from `.migration-backup/`
2. Keep Python MCP alongside TypeScript (temporarily)
3. Incrementally migrate one tool category at a time
4. Document issues in `.progress/VDE_CONSOLIDATION_ISSUES.md`

---

## Next Steps

1. Get approval on this plan
2. Start Phase 1 (delete archive)
3. Create Python MCP scaffolding (Phase 2)
4. Port AgentFS integration first (Phase 3) - foundation for everything else
5. Port RLM tools (Phase 4) - core capability
6. Incrementally port remaining components

Estimated time: 2-3 days for full migration with testing

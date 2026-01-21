# Repo OS + RLM Infrastructure: Complete Technical Report

**Date:** 2026-01-21
**Status:** In Development
**Plan Reference:** `.progress/026_20260120_repo_os_rlm_infrastructure.md`

---

## Executive Summary

This report describes a comprehensive infrastructure for **reliable agent-driven development** on the kelpie codebase. The system addresses fundamental problems with how AI coding agents interact with codebases: context limitations, unreliable verification, and inconsistent quality of analysis.

The infrastructure consists of **three complementary systems**:

1. **RLM (Recursive Language Models)** - An inference strategy where agents never see the full codebase directly, instead writing code to query it programmatically
2. **Hard Control Layer** - Enforcement mechanisms that prevent agents from lying about completion or skipping verification
3. **Codebase Intelligence Layer** - A framework for thorough, truthful answers by comparing actual code (IS) against specifications (SHOULD)

---

## Part 1: Problems Being Addressed

### Problems This Infrastructure Solves

| Problem | Description | Impact |
|---------|-------------|--------|
| **Context Rot** | As LLM context fills up, quality of analysis degrades | Agents miss issues, give incorrect answers |
| **Partial Coverage** | Agents grep once, find 20%, miss 80% | False confidence, incomplete analysis |
| **MD File Trust** | Agents trust outdated `.progress/` claims | Regressions go unnoticed |
| **No Verification** | "Is feature X done?" reads docs instead of running tests | Claims don't match reality |
| **P0 Constraint Violations** | Natural language instructions get ignored | Critical invariants broken |
| **Slop Accumulation** | Agents create garbage while fixing themselves | Codebase quality degrades |
| **Inconsistent Findings** | Different agents find different issues each time | No accumulation, no ground truth |
| **Unknown Completeness** | No way to know if analysis was thorough | Can't trust "complete" status |

### Problems This Infrastructure Does NOT Solve

| Non-Goal | Why Not Addressed |
|----------|-------------------|
| **LLM Reasoning Quality** | We can't make LLMs smarter; we can only give them better tools and constraints |
| **Novel Bug Types** | System catches known patterns; truly novel issues require human insight |
| **Specification Completeness** | If the spec is wrong/incomplete, IS vs SHOULD comparison reflects that |
| **Malicious Actors** | System designed for cooperative agents, not adversarial use |
| **100% Automated Development** | Human review still required; system enables better human-agent collaboration |
| **Cross-Repository Work** | Currently scoped to single repository (kelpie) |
| **Non-Rust Codebases** | Indexers and patterns are Rust-specific (though concepts generalize) |

---

## Part 2: How Everything Works

### Technology Stack Overview

```
┌─────────────────────────────────────────────────────────────────────────┐
│  AGENT LAYER                                                             │
│  • Claude Code (Anthropic's CLI tool)                                   │
│  • Skills (.claude/skills/*.md) - Soft guidance for workflows           │
│  • Human oversight via chat interface                                   │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 3: CODEBASE INTELLIGENCE (Python + LLM)                          │
│  • Spec adapters (programmatic YAML/JSON parsing)                       │
│  • Agent-driven examination (LLM calls via Anthropic API)               │
│  • Issue storage (SQLite via AgentFS)                                   │
│  • Thoroughness verification (programmatic)                             │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 2: RLM INFRASTRUCTURE (Python REPL)                              │
│  • CodebaseContext class (programmatic file access)                     │
│  • Sandboxed execution (RestrictedPython)                               │
│  • Recursive LLM calls for partition+map patterns                       │
│  • 30s timeout, depth limits                                            │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 1: BASE TOOLS (TypeScript MCP Server)                            │
│  • MCP protocol for tool invocation                                     │
│  • AgentFS (SQLite) for state persistence                               │
│  • Structural indexes (JSON files)                                      │
│  • Verification by execution (subprocess calls)                         │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  HARD FLOOR (Shell Scripts, Git)                                        │
│  • Pre-commit hooks (bash)                                              │
│  • CI pipeline (GitHub Actions YAML)                                    │
│  • Git for version control                                              │
└─────────────────────────────────────────────────────────────────────────┘
```

### What is Programmatic vs LLM-Driven?

#### Purely Programmatic (No LLM)

| Component | Technology | Description |
|-----------|------------|-------------|
| **Symbol Index** | Rust (tree-sitter/rust-analyzer) | Parse AST, extract function/struct/trait definitions |
| **Dependency Graph** | Rust (cargo metadata) | Crate-level and fine-grained type dependencies |
| **Test Index** | Rust | Find all `#[test]` functions, extract metadata |
| **Module Index** | Rust | Map crate → module → file hierarchy |
| **Freshness Tracking** | Git SHA comparison | Detect stale indexes |
| **Pre-commit Hooks** | Bash | Run tests, clippy, fmt checks |
| **CI Pipeline** | GitHub Actions | Automated verification on push |
| **AgentFS Storage** | SQLite | Key-value store, audit log, issue storage |
| **MCP Protocol** | TypeScript | Tool invocation, parameter validation |
| **CodebaseContext** | Python | File listing, grep, peek, read_section |
| **Thoroughness Check** | Python | Compare examined partitions vs expected |
| **Spec Parsing** | Python | Parse OpenAPI YAML, TLA+ files, pattern rules |

#### LLM-Driven (Claude API Calls)

| Component | When LLM Called | Purpose |
|-----------|-----------------|---------|
| **Semantic Summaries** | During index build | Generate human-readable module descriptions |
| **Constraint Extraction** | On CONSTRAINTS.md change | Parse prose into structured requirements |
| **Recursive RLM Calls** | During partition+map | Analyze focused code chunks |
| **Agent Examination** | During codebase_question | Intelligent IS vs SHOULD comparison |
| **Issue Analysis** | During examination | Determine severity, suggested fixes |
| **Answer Synthesis** | After examination | Combine findings into coherent answer |

### How RLM Works (Technical Detail)

**RLM is an inference strategy, not a model.** The key insight is that the LLM never sees the full codebase in its context window. Instead:

1. **Codebase as Variable**: The entire codebase is available as a `codebase` variable in a Python REPL environment
2. **Agent Writes Code**: The LLM writes Python code to query the codebase (grep, peek, read_section)
3. **Programmatic Execution**: The code executes via RestrictedPython sandbox
4. **Recursive Calls**: For large results, the agent can spawn sub-LLM calls with focused context

```python
# Example: Agent-written code in RLM environment
modules = codebase.list_modules()  # Programmatic - no LLM call

all_dead_code = []
for module in modules:
    # This spawns a sub-LLM call with only one module's context
    dead = RLM(f"find unused functions in {module}",
               codebase.get_module(module))  # LLM call
    all_dead_code.extend(dead)

FINAL(all_dead_code)  # Return complete results
```

**What happens under the hood:**

```
1. MCP server receives rlm_execute(code) request
2. Spawns Python subprocess: python -m rlm_env --codebase /path --indexes /path --stdin
3. Python code executes in RestrictedPython sandbox
4. When RLM() is called, Python makes Anthropic API call
5. Results aggregated, returned as JSON
6. MCP server returns results to Claude Code
```

### How Hard Controls Work (Technical Detail)

Hard controls are **programmatic enforcement** - they cannot be bypassed by the LLM.

**Level 1: MCP Tool Gates**

```typescript
// tools/mcp-kelpie/src/hardcontrols.ts

async function state_task_complete(task_id: string, evidence: Evidence) {
  // HARD: Evidence parameter is required by TypeScript type system
  if (!evidence.verification_commands?.length) {
    throw new Error("Cannot complete without verification commands");  // Can't bypass
  }

  // HARD: System re-runs verification NOW (not trusting agent's claim)
  for (const cmd of evidence.verification_commands) {
    const result = await exec(cmd.command);  // Actually runs the command
    if (!matches(result, cmd.expected)) {
      throw new Error(`Verification failed: ${cmd.command}`);
    }
  }

  // Only if ALL verifications pass, store completion with git SHA
  await agentfs.store(`completions/${task_id}`, {
    ...evidence,
    verified_at: Date.now(),
    git_sha: await getCurrentSha()  // Tracks WHICH code was verified
  });
}
```

**Level 2: Pre-commit Hooks**

```bash
#!/bin/bash
# .git/hooks/pre-commit

# HARD: Tests must pass before commit allowed
cargo test || { echo "Tests failed"; exit 1; }

# HARD: Clippy must pass
cargo clippy --all-targets -- -D warnings || { echo "Clippy failed"; exit 1; }

# HARD: Code must be formatted
cargo fmt --check || { echo "Format check failed"; exit 1; }
```

**Level 3: CI Pipeline**

```yaml
# .github/workflows/ci.yml
test-dst:
  steps:
    - name: Verify Determinism (Double Run)
      run: ./scripts/check_dst.sh 12345  # Runs same tests twice, diff output
```

### How Codebase Intelligence Works (Technical Detail)

The intelligence layer provides **structured analysis** by comparing IS (actual code) against SHOULD (specifications).

**Step 1: Load Specifications (Programmatic)**

```python
class OpenAPIAdapter(SpecAdapter):
    def load(self, source: str) -> List[Requirement]:
        # Programmatic YAML parsing
        spec = yaml.safe_load(open(source))
        requirements = []
        for path, methods in spec['paths'].items():
            for method, details in methods.items():
                requirements.append(Requirement(
                    id=f"{method}_{path}",
                    source="letta_openapi",
                    description=f"Endpoint {method.upper()} {path} must exist",
                    verification_hint=f"Check for route handler matching {path}",
                    context={"schema": details.get("requestBody", {})}
                ))
        return requirements
```

**Step 2: Agent Examination (LLM-Driven)**

```python
# For each partition of the codebase
finding = await RLM(f"""
    Examine this code thoroughly:

    EXPECTATIONS (what SHOULD be true):
    {[r.description for r in applicable_requirements]}

    For this partition:
    1. What actually exists? (IS)
    2. Does it satisfy the expectations? (IS vs SHOULD)
    3. What's missing, broken, stubbed, or suspicious?
    4. Provide EVIDENCE for every claim
""", partition)
```

**Step 3: Issue Storage (Programmatic)**

```python
# After agent finds issues, store them structurally
agentfs.record_issue({
    "found_by": session_id,
    "spec_source": "letta_openapi",
    "should_description": "Endpoint POST /v1/agents must return 201 on success",
    "is_description": "Endpoint returns 200 instead of 201",
    "evidence": "handlers.rs:145: return Ok(Json(agent)) without status code",
    "severity": "medium",
    "category": "mismatch"
})
```

**Step 4: Thoroughness Verification (Programmatic)**

```python
def verify_thoroughness(session_id: str, scope: Scope):
    examination_log = agentfs.get_examination_log(session_id)
    expected_partitions = scope.all_partitions()

    examined = set(e.module for e in examination_log)
    expected = set(p.name for p in expected_partitions)

    missing = expected - examined
    return ThortoughnessReport(
        complete=len(missing) == 0,
        missing_partitions=list(missing),
        coverage_percent=len(examined) / len(expected) * 100
    )
```

---

## Part 3: Implementation Status

### Currently Implemented (Completed)

| Phase | Component | Status | Technology |
|-------|-----------|--------|------------|
| **1** | Directory structure (.kelpie-index/, .agentfs/) | ✅ Complete | Filesystem |
| **2.1** | Symbol Index | ✅ Complete | Rust (tools/kelpie-indexer) |
| **2.2** | Dependency Graph | ✅ Complete | Rust |
| **2.3** | Test Index | ✅ Complete | Rust |
| **2.4** | Module Index | ✅ Complete | Rust |
| **3b** | RLM Environment | ✅ Complete | Python (tools/rlm-env) |
| **4** | MCP Server | ✅ Complete | TypeScript (tools/mcp-kelpie) |
| **5** | RLM Skills | ✅ Complete | Markdown (.claude/skills/) |
| **6** | Hard Controls (hooks, gates) | ✅ Complete | Bash, TypeScript |
| **7** | Parallel indexing orchestration | ✅ Complete | Python |

### Planned (Not Yet Implemented)

| Phase | Component | Status | Blocking On |
|-------|-----------|--------|-------------|
| **3** | Semantic Indexing (summaries) | Planned | Phase 2 stable |
| **4.9** | DST Coverage Tools | Planned | Phase 4 complete |
| **4.10** | Harness Adequacy Verification | Planned | Phase 4.9 |
| **8** | Integration Testing | Planned | All infrastructure |
| **9** | Slop Cleanup Workflow | Planned | Phase 8 |
| **10** | Codebase Intelligence Layer | Planned | All prior phases |
| **10.1** | Spec Adapter Framework | Planned | Phase 10 design |
| **10.2** | Issue Storage Schema | Planned | AgentFS extension |
| **10.3** | Agent-Driven Examination | Planned | 10.1, 10.2 |
| **10.4** | codebase_question MCP Tool | Planned | 10.3 |
| **10.5** | Thoroughness Verification | Planned | 10.3 |
| **10.6** | Pre-built Spec Configs | Planned | 10.1 |
| **10.7** | Issue Dashboard Skill | Planned | 10.2 |

### What Works Now

With the current implementation, you can:

1. **Query Structural Indexes** (programmatic, no LLM)
   ```bash
   # Via MCP tools
   query_symbols("FdbStorage")       # Find symbol definitions
   query_tests("storage")            # Find tests by topic
   query_dependencies("kelpie-storage")  # Get dependency graph
   ```

2. **Execute RLM Code** (programmatic + LLM)
   ```python
   # Agent writes code that executes in sandboxed REPL
   matches = grep(r"impl\s+ActorKV", "*.rs")
   for m in matches:
       content = read_section(m.file, m.line - 5, m.line + 20)
       analysis = RLM("What does this implementation do?", content)
   ```

3. **Verify Claims by Execution** (programmatic)
   ```bash
   # MCP tool runs actual commands, not trusting agent claims
   verify_by_command("cargo test -p kelpie-storage")
   ```

4. **Track Agent State** (programmatic)
   ```bash
   # AgentFS stores state, audit trail
   state_save("current_task", "Implementing feature X")
   state_task_complete("task_123", {verification_commands: [...]})
   ```

5. **Block Bad Commits** (programmatic)
   ```bash
   # Pre-commit hooks prevent commits that would break things
   git commit -m "..."
   # → Runs tests, clippy, fmt checks
   # → Blocks if any fail
   ```

### What Doesn't Work Yet

1. **codebase_question** - The single entry point for thorough analysis isn't implemented
2. **Spec Adapters** - Can't yet compare against OpenAPI, TLA+, or pattern rules
3. **Issue Storage** - Issues aren't persisted structurally in AgentFS
4. **Thoroughness Verification** - No examination log to prove completeness
5. **Semantic Summaries** - LLM-generated module descriptions aren't available

---

## Part 4: Detailed Component Descriptions

### RLM Environment (tools/rlm-env/)

**Purpose:** Enable LLMs to work with arbitrarily large codebases without context rot.

**Technology:**
- Python package with CLI interface
- RestrictedPython for sandboxed execution
- Anthropic Claude API for recursive calls

**Key Classes:**

```python
class CodebaseContext:
    """Provides read-only access to codebase files"""
    def list_files(glob: str) -> List[str]
    def list_modules() -> List[str]
    def peek(file: str, lines: int) -> str
    def grep(pattern: str, glob: str) -> List[GrepMatch]
    def read_section(file: str, start: int, end: int) -> str
    def partition_by_module() -> List[ModuleContext]

class RLMEnvironment:
    """REPL environment for executing agent-written code"""
    def execute(code: str, depth: int) -> Any
    def recursive_call(query: str, context: Any) -> str  # Makes LLM call
    def map_reduce(query: str, partitions: List) -> Any
```

**Constraints:**
- 30-second execution timeout
- 3-level maximum recursive depth
- 100KB maximum output size
- Read-only codebase access (can't modify files)

### MCP Server (tools/mcp-kelpie/)

**Purpose:** Provide structured tools for agent operations with hard enforcement.

**Technology:**
- TypeScript
- MCP (Model Context Protocol) for tool definitions
- AgentFS (SQLite) for state

**Tools Available:**

```typescript
// Index queries (programmatic)
query_symbols(pattern: string): SymbolMatch[]
query_tests(topic: string): TestInfo[]
query_dependencies(crate: string): DepGraph
query_modules(): ModuleTree

// Codebase operations (programmatic + RLM)
codebase_grep(pattern: string, glob: string): GrepMatch[]
codebase_peek(file: string, lines: number): string
rlm_execute(code: string): RLMResult

// Verification (programmatic)
verify_by_command(command: string): VerifyResult
verify_by_tests(pattern: string): TestResult

// State management (programmatic)
state_save(key: string, value: any): void
state_load(key: string): any
state_task_complete(task_id: string, evidence: Evidence): void  // HARD CONTROL

// Slop detection (programmatic)
detect_dead_code(): DeadCode[]
detect_fake_dst(): FakeDST[]
detect_incomplete(): Incomplete[]
```

### AgentFS

**Purpose:** Persistent state storage with audit trail.

**Technology:**
- SQLite database at `.agentfs/agent.db`
- Based on Turso's AgentFS library

**Tables:**

```sql
-- Key-value store for agent state
CREATE TABLE agent_state (
    key TEXT PRIMARY KEY,
    value TEXT,
    updated_at INTEGER
);

-- Verified facts with execution proof
CREATE TABLE verified_facts (
    claim TEXT,
    method TEXT,
    result TEXT,
    timestamp INTEGER,
    git_sha TEXT
);

-- Task completions with evidence
CREATE TABLE completions (
    plan_id TEXT,
    phase TEXT,
    status TEXT,
    evidence TEXT,
    verified_at INTEGER,
    git_sha TEXT
);

-- Audit log (append-only)
CREATE TABLE audit_log (
    id INTEGER PRIMARY KEY,
    tool TEXT,
    args TEXT,
    result TEXT,
    timestamp INTEGER
);

-- Issues (Phase 10)
CREATE TABLE issues (
    id TEXT PRIMARY KEY,
    category TEXT,
    severity TEXT,
    should_description TEXT,
    is_description TEXT,
    evidence TEXT,
    status TEXT
);
```

### Structural Indexes (.kelpie-index/)

**Purpose:** Fast, deterministic access to codebase structure.

**Technology:**
- JSON files generated by Rust indexer
- Git-tracked for reproducibility

**Files:**

```
.kelpie-index/
├── structural/
│   ├── symbols.json       # Functions, structs, traits
│   ├── dependencies.json  # Crate and type-level deps
│   ├── tests.json         # All tests with metadata
│   └── modules.json       # Module hierarchy
├── meta/
│   ├── freshness.json     # Git SHA for staleness detection
│   └── build_log.json     # Index build timestamps
└── specs/                 # (Phase 10)
    ├── dst-coverage.yaml  # DST requirements
    └── presets.yaml       # Pre-built spec configs
```

### Skills (.claude/skills/)

**Purpose:** Soft guidance for agent workflows.

**Technology:**
- Markdown files with workflow instructions
- Loaded by Claude Code

**Available Skills:**

| Skill | Purpose |
|-------|---------|
| `rlm-task.md` | Execute complex tasks using RLM patterns |
| `verify-first.md` | Always verify by execution, not by reading docs |
| `explore-codebase.md` | Use indexes before reading random files |
| `handoff.md` | Re-verify all prior completions on session start |
| `slop-hunt.md` | Find and eliminate code quality issues |
| `hard-controls.md` | Understanding enforcement mechanisms |

### Hard Controls

**Purpose:** Enforcement that cannot be bypassed by LLM.

**Components:**

1. **MCP Tool Gates** (TypeScript)
   - Required parameters enforced by type system
   - Verification commands re-run by system (not trusted from agent)
   - Git SHA tracked with completions

2. **Pre-commit Hooks** (Bash)
   - Tests must pass
   - Clippy must pass
   - Format check must pass
   - DST coverage for critical paths (planned)

3. **CI Pipeline** (GitHub Actions)
   - Determinism verification (same seed = same output)
   - Multiple seed testing
   - Full test suite

---

## Part 5: Use Case Examples

### Example 1: "What's the state of DST?"

**Without this infrastructure:**
```
Agent reads .progress/ files, finds claims about DST being "complete"
Agent trusts the claims
Reports "DST is complete"
Reality: Several tests are failing, coverage is incomplete
```

**With this infrastructure (Phase 10):**
```python
# 1. Load DST spec (programmatic)
specs = load_specs(["preset:dst_assessment"])
# → Loads dst-coverage.yaml pattern rules

# 2. Partition codebase (programmatic)
partitions = codebase.partition_by_scope("crates/kelpie-*/")

# 3. For each partition (LLM-driven)
for partition in partitions:
    agentfs.log_examination(session_id, "DST state", partition.name)

    finding = RLM("""
        Examine this code for DST coverage:

        EXPECTATIONS:
        - All pub async fn must have DST test
        - DST tests must use fault injection
        - Tests must be deterministic

        For each function, determine:
        - IS: Does it have a DST test?
        - IS: Does the test inject faults?
        - IS: Is the test deterministic?

        Provide evidence for each claim.
    """, partition)

    # Record issues (programmatic)
    for issue in finding.issues:
        agentfs.record_issue(issue)

# 4. Verify thoroughness (programmatic)
thoroughness = verify_thoroughness(session_id, scope)
# → Returns: 15/17 partitions examined, 2 missing

# 5. Synthesize answer (LLM-driven)
answer = RLM("Synthesize complete answer based on all findings and issues")
```

**Result:**
```
DST Coverage Assessment:

✅ EXAMINED: 15 of 17 modules (88% coverage)
⚠️ MISSING: kelpie-wasm, kelpie-cli (not examined)

FINDINGS:
- 47 pub async fn in storage layer
- 38 have DST tests (81%)
- 29 use fault injection (62%)
- 9 missing tests entirely

ISSUES FOUND: 12
- CRITICAL: test_fdb_write missing CrashAfterWrite fault (fdb_storage_dst.rs)
- HIGH: 3 tests don't use harness correctly (fake DST)
- MEDIUM: 9 functions lack DST coverage

Evidence stored in AgentFS for review.
```

### Example 2: "Is Letta compatibility complete?"

**With this infrastructure (Phase 10):**
```python
# 1. Load Letta OpenAPI spec (programmatic)
specs = load_specs(["preset:letta_compatibility"])
# → Fetches https://raw.githubusercontent.com/letta-ai/letta/main/openapi.yaml
# → Parses into 127 Requirements (endpoints, schemas, behaviors)

# 2. For each requirement
for req in requirements:
    # Find relevant code
    matches = codebase.grep(req.endpoint_pattern, "crates/kelpie-server/src/handlers/")

    if not matches:
        agentfs.record_issue({
            "category": "gap",
            "severity": "high",
            "should": f"Endpoint {req.method} {req.path} must exist",
            "is": "No handler found",
            "evidence": f"No match for {req.endpoint_pattern}"
        })
        continue

    # LLM examines the match
    for match in matches:
        context = codebase.read_context(match.file, match.line, padding=50)
        finding = RLM(f"""
            Does this implementation match the spec?

            EXPECTED (from Letta OpenAPI):
            - Path: {req.path}
            - Method: {req.method}
            - Request schema: {req.request_schema}
            - Response schema: {req.response_schema}

            ACTUAL CODE:
            {context}

            Compare and identify:
            - Does the route match?
            - Does request parsing match schema?
            - Does response match schema?
            - Are there stub responses like "not implemented"?
        """, context)
```

---

## Part 6: Limitations and Caveats

### Fundamental Limitations

1. **LLM Quality Ceiling**: The system can't make LLM analysis better than the LLM is capable of. It can only structure the analysis and verify thoroughness.

2. **Spec Completeness**: IS vs SHOULD comparison is only as good as the SHOULD specification. Missing or wrong specs lead to missing or wrong analysis.

3. **False Positives**: Agent-driven analysis may flag non-issues. Human review of issue list is still required.

4. **Latency**: Full codebase analysis with RLM is slower than traditional approaches (many LLM calls). Trade-off is thoroughness vs speed.

5. **Cost**: Recursive LLM calls incur API costs. Large analyses may be expensive.

### What Requires Human Judgment

- **Spec Validation**: Are the specs we're comparing against actually correct?
- **Issue Triage**: Which flagged issues are real vs false positives?
- **Priority Setting**: Which issues to fix first?
- **Architecture Decisions**: Should this design change?
- **Novel Problems**: Issues that don't fit known patterns

### Security Considerations

- **Sandboxed Execution**: RestrictedPython prevents arbitrary code execution
- **Read-Only Codebase**: RLM environment cannot modify files
- **No Network Access**: Sandbox doesn't allow network calls (except LLM API)
- **Audit Trail**: All operations logged immutably
- **Git SHA Tracking**: Know exactly which code was analyzed

---

## Part 7: Future Directions

### Near-Term (Phase 10)

- Implement spec adapter framework
- Add issue storage schema to AgentFS
- Build codebase_question MCP tool
- Create pre-built spec configurations

### Medium-Term

- TLA+ formal verification integration
- Cross-repository analysis
- Automated issue prioritization
- Integration with IDE tooling

### Long-Term Vision

- Self-improving analysis (learn from false positives)
- Continuous codebase monitoring
- Multi-agent collaboration protocols
- Generalization to non-Rust codebases

---

## Appendix A: File Locations

```
kelpie/
├── .kelpie-index/                    # Structural indexes (git-tracked)
├── .agentfs/                         # Agent state (git-ignored)
├── .claude/skills/                   # Soft control skills
├── .git/hooks/pre-commit             # Hard control hook
├── tools/
│   ├── kelpie-indexer/               # Rust indexer
│   ├── mcp-kelpie/                   # TypeScript MCP server
│   └── rlm-env/                      # Python RLM environment
├── scripts/
│   └── check_dst.sh                  # DST verification script
└── .progress/
    └── 026_20260120_repo_os_rlm_infrastructure.md  # This plan
```

## Appendix B: Glossary

| Term | Definition |
|------|------------|
| **RLM** | Recursive Language Model - inference strategy where context is a queryable variable |
| **MCP** | Model Context Protocol - standard for LLM tool invocation |
| **AgentFS** | SQLite-backed persistent state storage for agents |
| **DST** | Deterministic Simulation Testing - testing with controlled randomness |
| **Hard Control** | Enforcement mechanism that cannot be bypassed by LLM |
| **Soft Control** | Guidance that LLM may choose to follow or ignore |
| **Slop** | Code quality issues: dead code, duplicates, incomplete implementations |
| **IS vs SHOULD** | Comparing actual code behavior against specifications |
| **Spec Adapter** | Normalizes any specification format into comparable requirements |
| **Thoroughness** | Verification that all relevant parts of codebase were examined |

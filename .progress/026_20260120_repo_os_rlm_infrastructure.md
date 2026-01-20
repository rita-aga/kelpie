# Task: Repo OS + RLM Infrastructure for Agent-Driven Development

**Created:** 2026-01-20 10:30:00
**State:** IMPLEMENTING

---

## Vision Alignment

**Vision files read:** CONSTRAINTS.md, CLAUDE.md

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - The Repo OS itself should be testable
- TigerStyle safety principles (CONSTRAINTS.md §3) - Hard controls, explicit assertions
- No placeholders in production (CONSTRAINTS.md §4) - Verification-first, not trust-MD
- Changes are traceable (CONSTRAINTS.md §7) - Audit trail via AgentFS

---

## Problem Statement

When coding agents work on kelpie:

1. **MD files become stale** - Agents read .progress/ or docs, trust outdated claims
2. **Context fills up** - Random exploration wastes tokens, misses things
3. **Partial coverage** - "Find all dead code" finds 20%, misses 80%
4. **Slop accumulation** - Agents create garbage while fixing themselves
5. **P0 constraints ignored** - Natural language instructions get skipped
6. **No verification** - "Is feature X done?" reads MD instead of running tests

## Solution: Repo OS + RLM

Build an infrastructure layer that:
- **Indexes the codebase** deterministically (structural) and semantically (summaries)
- **Persists agent state** in AgentFS (not scattered MD files)
- **Extracts constraints** from .vision/ via LLM, structures them for injection
- **Enforces verification** via hard controls (hooks, gates)
- **Guides agents** via RLM controller pattern with soft controls
- **Cross-validates** via multi-agent index building

---

## Options & Decisions

### Decision 1: Index Storage Backend

**Context:** Where do we store the auto-generated indexes?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: AgentFS | SQLite-backed, Turso's library | Built-in audit, KV, snapshots | External dependency, learning curve |
| B: SQLite (custom) | Roll our own SQLite schema | Full control, no dependency | More work, reinvent audit/snapshots |
| C: JSON files in .kelpie-index/ | Simple file-based storage | Easy to inspect, git-trackable | No transactions, no audit trail |

**Decision:** **Hybrid A+C** - Use AgentFS for agent state (current task, verified facts, audit log) and JSON files for indexes (easy to inspect, can be git-ignored or tracked). AgentFS handles ephemeral agent memory; JSON handles structural data that should be inspectable.

**Trade-offs accepted:**
- Two storage mechanisms to maintain
- JSON indexes aren't transactional (acceptable - they're derived/rebuildable)

---

### Decision 2: Constraint Extraction Method

**Context:** How do we turn .vision/CONSTRAINTS.md into structured, injectable constraints?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Human writes YAML | Manual structured format | No drift, deterministic | Humans won't maintain it |
| B: LLM extracts on hook | Parse MD → structured on commit | Auto-maintained | May hallucinate, drift |
| C: LLM extracts + human reviews | Extract, human approves diff | Best of both | Adds friction |
| D: LLM extracts + validation | Extract, validate by running checks | Auto + verified | Complex, but robust |

**Decision:** **Option D** - LLM extracts constraints from .vision/CONSTRAINTS.md, but each constraint must include a verification command. On extraction, we run the verification to confirm it works. If verification fails, flag for human review.

**Trade-offs accepted:**
- LLM might miss nuance in prose
- Verification commands need to exist for each constraint
- Some constraints (soft guidelines) may not be verifiable → marked as "soft"

---

### Decision 3: Index Types and Build Strategy

**Context:** What types of indexes do we need and how do we build them?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Single-agent sequential | One agent builds all indexes | Simple | Slow, single point of failure |
| B: Multi-agent parallel | Dispatch agents per index type | Fast, cross-validation | Coordination complexity |
| C: Tool-based (no LLM) | tree-sitter, cargo metadata only | Deterministic | No semantic understanding |
| D: Hybrid multi-agent | Tools for structural, LLM for semantic | Best coverage | Most complex |

**Decision:** **Option D** - Structural indexes (symbols, deps, tests) via tools (deterministic). Semantic indexes (summaries, constraint extraction) via LLM agents. Cross-validation by comparing structural vs semantic (e.g., summary says "unused" but call graph shows refs → flag).

**Trade-offs accepted:**
- Complex architecture
- Must handle LLM failures gracefully
- Semantic indexes may have some drift (acceptable - they're for navigation, not truth)

---

### Decision 4: RLM Controller Implementation

**Context:** How do we implement the RLM pattern?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Claude Code + MCP | Use existing infrastructure | Already works, familiar | MCP overhead, limited control |
| B: Custom Rust binary | Full control, native | Performance, integration | Significant work |
| C: Claude Code + Skills + MCP | Extend existing with skills | Incremental, flexible | Relies on model following skills |

**Decision:** **Option C** - Build on Claude Code. Create MCP server for state/index operations. Create Skills for RLM workflows. Add hard controls via MCP tool wrappers and git hooks.

**Trade-offs accepted:**
- Dependent on Claude Code behavior
- Skills are soft controls (model might ignore)
- Mitigated by hard control layer around MCP tools

---

### Decision 5: Verification-First Enforcement

**Context:** How do we ensure agents verify by execution, not by trusting MD?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Prompt injection only | Tell agent to verify | Simple | Agent might ignore |
| B: MCP gates | Tools refuse to return "done" without test pass | Hard enforcement | May block legitimate cases |
| C: Two-phase completion | Claim done → system runs verification → confirms | Clear separation | Adds latency |
| D: All of above | Layered enforcement | Most robust | Complex |

**Decision:** **Option D** - Layer all three:
1. Prompt injection (soft) - "verify by execution"
2. MCP gates (hard) - `mark_complete` tool requires test pass proof
3. Two-phase (hard) - system runs verification before accepting completion

**Trade-offs accepted:**
- More ceremony for completing tasks
- May slow down trivial fixes (acceptable - we prefer correctness)

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-20 10:30 | Hybrid AgentFS + JSON | Best of both: audit + inspectable | Two systems to maintain |
| 2026-01-20 10:35 | LLM extracts + validation | Humans won't maintain YAML | Need verification commands |
| 2026-01-20 10:40 | Multi-agent parallel indexing | Speed + cross-validation | Coordination complexity |
| 2026-01-20 10:45 | Claude Code + MCP + Skills | Incremental, leverages existing | Relies on model compliance |
| 2026-01-20 10:50 | Layered verification enforcement | Defense in depth | More ceremony |
| 2026-01-20 11:00 | Enhanced Layer 1 with imports/exports_to | Match Aider's repo map approach | More parsing complexity |
| 2026-01-20 11:00 | Enhanced Layer 2 with implements/uses edges | Fine-grained dependency tracking | Requires rust-analyzer, not just cargo |
| 2026-01-20 11:00 | Added target schemas for all indexes | Clear spec for implementation | More upfront design |

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           RLM Controller Layer                              │
│                    (Claude Code + Skills + MCP)                             │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                        HARD SHELL                                   │    │
│  │  • Git hooks (pre-commit: constraints, tests)                       │    │
│  │  • MCP gates (freshness, verification proof)                        │    │
│  │  • Index staleness detection (Merkle-style hashes)                  │    │
│  │  • Audit logging (every tool call)                                  │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │                        SOFT CORE                                    │    │
│  │  • Constraint injection (P0s in every prompt)                       │    │
│  │  • Skill instructions (RLM workflows)                               │    │
│  │  • Planning guidance (read/write/new lists)                         │    │
│  │  • Verification suggestions                                         │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│  ┌─────────────────────────────────▼───────────────────────────────────┐    │
│  │                        HARD FLOOR                                   │    │
│  │  • Tests must pass before commit                                    │    │
│  │  • Clippy must pass before commit                                   │    │
│  │  • DST required for critical paths                                  │    │
│  │  • Verification proof required for completion claims                │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────────────────┘
                                     │
         ┌───────────────────────────┼───────────────────────────┐
         ▼                           ▼                           ▼
┌─────────────────┐        ┌─────────────────┐        ┌─────────────────┐
│    AgentFS      │        │   Index Layer   │        │   Execution     │
│  (Agent State)  │        │  (Knowledge)    │        │  (Ground Truth) │
│                 │        │                 │        │                 │
│ • current_task  │        │ • structural/   │        │ • cargo test    │
│ • verified_facts│        │   symbols.json  │        │ • cargo clippy  │
│ • findings      │        │   deps.json     │        │ • DST tests     │
│ • plan          │        │   tests.json    │        │ • rust-analyzer │
│ • audit_log     │        │ • semantic/     │        │ • tree-sitter   │
│                 │        │   summaries.json│        │                 │
│ (SQLite-backed) │        │   embeddings/   │        │ (Real execution)│
│                 │        │ • constraints/  │        │                 │
│                 │        │   extracted.json│        │                 │
│                 │        │                 │        │                 │
│                 │        │ (JSON files)    │        │                 │
└─────────────────┘        └─────────────────┘        └─────────────────┘
         │                           │                           │
         └───────────────────────────┼───────────────────────────┘
                                     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Git Repository                                     │
│  • crates/           (actual code - source of truth)                        │
│  • docs/adr/         (human documentation)                                  │
│  • .vision/          (constraints in prose - input to extraction)           │
│  • .progress/        (human-readable plans - not source of truth)           │
│  • .kelpie-index/    (auto-generated indexes - git-ignored or tracked)      │
│  • .agentfs/         (agent state - git-ignored)                            │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Implementation Plan

### Phase 1: Foundation - Directory Structure & AgentFS Setup

**Goal:** Establish the physical structure and agent state storage.

- [ ] Create `.kelpie-index/` directory structure
  ```
  .kelpie-index/
  ├── structural/           # Deterministic, tool-generated
  │   ├── symbols.json      # Functions, types, traits (tree-sitter/LSP)
  │   ├── dependencies.json # Crate graph (cargo metadata)
  │   ├── tests.json        # All tests, what they verify
  │   └── modules.json      # Module hierarchy
  ├── semantic/             # LLM-generated, for navigation not truth
  │   ├── summaries/        # Per-module summaries
  │   └── embeddings/       # Vector embeddings (optional)
  ├── constraints/          # Extracted from .vision/
  │   └── extracted.json    # Structured constraints with verification commands
  └── meta/
      ├── freshness.json    # Git SHA, file hashes for staleness detection
      └── build_log.json    # When indexes were last built
  ```
- [ ] Initialize AgentFS or SQLite for agent state
  ```
  .agentfs/
  ├── agent.db              # SQLite database
  └── README.md             # What this is, how to inspect
  ```
- [ ] Add to .gitignore: `.agentfs/`, optionally `.kelpie-index/semantic/`
- [ ] Create initial freshness tracking (store current git SHA)

**Verification:**
```bash
ls -la .kelpie-index/
ls -la .agentfs/
```

---

### Phase 2: Structural Indexing (Deterministic, Tool-Based)

**Goal:** Build indexes derived directly from code, no LLM interpretation.

- [ ] **2.1: Symbol Index** (tree-sitter or rust-analyzer)
  - Parse all .rs files
  - Extract: functions, structs, traits, impls, with signatures
  - Store in `structural/symbols.json`
  - Include file path, line numbers, visibility
  - **Include imports**: What modules/crates each file uses
  - **Include exports_to**: Which other files/crates reference symbols from this file

  **Target schema:**
  ```json
  {
    "crates/kelpie-storage/src/fdb.rs": {
      "symbols": [
        {"name": "FdbStorage", "kind": "struct", "line": 45, "visibility": "pub"},
        {"name": "get", "kind": "fn", "line": 67, "signature": "async fn get(&self, key: &[u8]) -> Result<Option<Bytes>>"},
        {"name": "put", "kind": "fn", "line": 89, "signature": "async fn put(&self, key: &[u8], value: &[u8]) -> Result<()>"}
      ],
      "imports": ["foundationdb", "kelpie_core", "bytes::Bytes"],
      "exports_to": ["kelpie-server", "kelpie-agent"]
    }
  }
  ```
  **Trust level: HIGH** - derived deterministically from code.

- [ ] **2.2: Dependency Graph** (cargo metadata + rust-analyzer)
  - Run `cargo metadata --format-version=1` for crate-level deps
  - Use rust-analyzer for fine-grained type relationships
  - Build multi-level graph with nodes and edges
  - Store in `structural/dependencies.json`
  - **Include fine-grained nodes**: structs, traits, functions (not just crates)
  - **Include implements edges**: What traits each struct implements
  - **Include uses edges**: What types each function/struct uses

  **Target schema:**
  ```json
  {
    "nodes": [
      {"id": "kelpie-storage", "type": "crate"},
      {"id": "kelpie-server", "type": "crate"},
      {"id": "FdbStorage", "type": "struct", "crate": "kelpie-storage", "file": "src/fdb.rs"},
      {"id": "ActorKV", "type": "trait", "crate": "kelpie-storage", "file": "src/lib.rs"},
      {"id": "get", "type": "fn", "crate": "kelpie-storage", "parent": "FdbStorage"}
    ],
    "edges": [
      {"from": "kelpie-server", "to": "kelpie-storage", "type": "depends"},
      {"from": "FdbStorage", "to": "ActorKV", "type": "implements"},
      {"from": "FdbStorage", "to": "foundationdb::Database", "type": "uses"},
      {"from": "get", "to": "Bytes", "type": "returns"}
    ]
  }
  ```
  **Trust level: HIGH** - derived from cargo and LSP.

- [ ] **2.3: Test Index** (parse test files)
  - Find all `#[test]` and `#[tokio::test]` functions
  - Infer topics from file names and test names
  - Categorize: unit, integration, DST, chaos
  - Store in `structural/tests.json`
  - Include command to run each test

  **Target schema:**
  ```json
  {
    "tests": [
      {
        "name": "test_fdb_storage_fault_injection",
        "file": "tests/fdb_storage_dst.rs",
        "line": 45,
        "type": "dst",
        "topics": ["storage", "fdb", "faults"],
        "command": "cargo test -p kelpie-server --test fdb_storage_dst test_fdb_storage_fault_injection"
      },
      {
        "name": "test_actor_lifecycle",
        "file": "tests/actor_lifecycle_dst.rs",
        "line": 23,
        "type": "dst",
        "topics": ["actor", "lifecycle"],
        "command": "cargo test -p kelpie-server --test actor_lifecycle_dst"
      }
    ],
    "by_topic": {
      "storage": ["test_fdb_storage_fault_injection", "test_memory_storage"],
      "actor": ["test_actor_lifecycle", "test_actor_activation"]
    },
    "by_type": {
      "dst": ["test_fdb_storage_fault_injection", "test_actor_lifecycle"],
      "unit": ["test_actor_id_valid"],
      "integration": ["test_api_endpoint"]
    }
  }
  ```
  **Trust level: HIGH** - test names/files are facts.

- [ ] **2.4: Module Index** (cargo + file structure)
  - Map crate → module → file hierarchy
  - Store in `structural/modules.json`

- [ ] **2.5: Freshness Tracking**
  - For each indexed file, store:
    - File path
    - Git SHA at index time
    - File content hash
  - On query, check if file changed since indexing
  - If changed, re-index before returning

**Tools to use:**
- `cargo metadata` for crate info
- `tree-sitter` (via tree-sitter-rust) or `rust-analyzer` CLI for symbols
- Custom Rust script for test parsing

**Verification:**
```bash
# After building indexes
cat .kelpie-index/structural/symbols.json | jq '.["crates/kelpie-core/src/lib.rs"]'
cat .kelpie-index/structural/tests.json | jq '.tests | length'
cargo metadata --format-version=1 | jq '.packages | map(select(.name | startswith("kelpie"))) | length'
```

---

### Phase 3: Semantic Indexing (LLM-Generated, Multi-Agent)

**Goal:** Build summaries and semantic understanding via LLM agents.

- [ ] **3.1: Hierarchical Summary Agent**
  - For each module, generate summary (bottom-up):
    - Function level → File level → Module level → Crate level
  - Use HCGS approach (Hierarchical Code Graph Summarization)
  - Store in `semantic/summaries/{crate}/{module}.json`

  **Target schema (hierarchical):**
  ```json
  {
    "kelpie-storage": {
      "summary": "Per-actor key-value storage abstraction with multiple backend support",
      "key_traits": ["ActorKV", "StorageBackend"],
      "modules": {
        "fdb": {
          "summary": "FoundationDB storage backend with ACID transactions",
          "files": {
            "fdb.rs": {
              "summary": "FdbStorage struct implementing ActorKV trait",
              "functions": {
                "get": "Retrieves value by key from FoundationDB",
                "put": "Stores key-value pair with transaction support",
                "delete": "Removes key from storage"
              }
            }
          }
        },
        "memory": {
          "summary": "In-memory storage backend for testing",
          "files": {...}
        }
      }
    }
  }
  ```
  **Trust level: LOW for claims** - LLM-generated, use for navigation not truth.

- [ ] **3.2: Constraint Extraction Agent**
  - Read `.vision/CONSTRAINTS.md`
  - Extract structured constraints:
    ```json
    {
      "id": "simulation-first",
      "category": "P0",
      "rule": "Every feature must be DST tested before complete",
      "verification": {
        "type": "test",
        "command": "cargo test -p kelpie-dst",
        "pass_criteria": "all tests pass"
      },
      "enforcement": "hard",
      "source_line": 17
    }
    ```
  - Validate each by running verification command
  - Store in `constraints/extracted.json`

- [ ] **3.3: Cross-Validation Agent**
  - Compare structural vs semantic:
    - Summary says "function X is unused" → check call graph
    - Summary says "module Y handles Z" → check if Z appears in symbols
  - Flag inconsistencies for review
  - Store in `semantic/validation_issues.json`

- [ ] **3.4: Embeddings (Optional)**
  - Generate embeddings for code chunks
  - Store in `semantic/embeddings/`
  - Use for semantic search

**Multi-Agent Orchestration:**
```
Coordinator Agent:
├── Dispatch Symbol Agent → structural/symbols.json
├── Dispatch Dependency Agent → structural/dependencies.json
├── Dispatch Test Agent → structural/tests.json
├── Dispatch Summary Agent → semantic/summaries/
├── Dispatch Constraint Agent → constraints/extracted.json
└── Dispatch Validation Agent → semantic/validation_issues.json

Cross-validation after all complete.
```

**Verification:**
```bash
# Check constraint extraction
cat .kelpie-index/constraints/extracted.json | jq '.[] | select(.category == "P0")'

# Check summaries exist
ls .kelpie-index/semantic/summaries/

# Check for validation issues
cat .kelpie-index/semantic/validation_issues.json | jq '. | length'
```

---

### Phase 4: MCP Server for Index/State Operations

**Goal:** Provide tools for agents to query indexes and manage state.

- [ ] **4.1: Create MCP Server Skeleton**
  ```
  tools/mcp-kelpie/
  ├── package.json
  ├── tsconfig.json
  └── src/
      ├── index.ts           # MCP server entry
      ├── state.ts           # AgentFS/SQLite operations
      ├── index.ts           # Index query operations
      ├── constraints.ts     # Constraint operations
      ├── verify.ts          # Verification operations
      └── audit.ts           # Audit logging
  ```

- [ ] **4.2: State Tools (AgentFS)**
  - `state_get(key)` → Get from agent state
  - `state_set(key, value)` → Set in agent state
  - `state_task_start(description)` → Start task, log to audit
  - `state_task_complete(proof)` → Complete task, requires verification proof
  - `state_verified_fact(claim, method, result)` → Store verified fact

- [ ] **4.3: Index Tools (Query)**
  - `index_query(query)` → Semantic search across indexes
  - `index_symbols(pattern)` → Find symbols matching pattern
  - `index_tests(topic)` → Find tests for topic
  - `index_modules(path)` → Get module info
  - `index_deps(crate)` → Get dependencies
  - `index_constraints()` → Get all P0 constraints

- [ ] **4.4: Verification Tools (Execution)**
  - `verify_by_tests(topic)` → Find tests, run them, return results
  - `verify_constraint(id)` → Run specific constraint's verification
  - `verify_all_constraints()` → Run all P0 checks
  - `verify_claim(claim)` → Determine how to verify, execute, return result

- [ ] **4.5: Index Management Tools**
  - `index_status()` → Check freshness of all indexes
  - `index_refresh(scope?)` → Rebuild indexes (all or specific)
  - `index_validate()` → Run cross-validation

- [ ] **4.6: Hard Control Gates**
  - Before returning index results, check freshness
  - Before accepting `state_task_complete`, require verification proof
  - Log every tool call to audit trail

**Verification:**
```bash
# Test MCP server
cd tools/mcp-kelpie && npm test

# Manual test
echo '{"tool": "index_constraints"}' | node src/index.js
```

---

### Phase 5: RLM Skills and Soft Controls

**Goal:** Create skills that guide agent behavior in RLM pattern.

- [ ] **5.1: RLM Task Skill**
  ```markdown
  # .claude/skills/rlm-task.md

  When starting any task:
  1. Call mcp.index_constraints() → inject P0s into reasoning
  2. Call mcp.index_query() → understand scope from index
  3. Create plan with explicit read/write/new lists
  4. Store: mcp.state_task_start(description)
  5. For each phase, verify by execution not by reading docs
  6. Update indexes after changes: mcp.index_refresh(changed_files)
  7. Final: mcp.verify_all_constraints()
  8. Complete: mcp.state_task_complete(proof)
  ```

- [ ] **5.2: RLM Verify Skill**
  ```markdown
  # .claude/skills/rlm-verify.md

  When asked if something is true about the code:
  1. NEVER trust MD files for factual claims
  2. Call mcp.index_tests(topic) → find relevant tests
  3. Call mcp.verify_by_tests(topic) → run them
  4. Report actual results, not documentation claims
  5. Store verified fact: mcp.state_verified_fact(...)
  ```

- [ ] **5.3: RLM Explore Skill**
  ```markdown
  # .claude/skills/rlm-explore.md

  When exploring the codebase:
  1. Start with mcp.index_modules() → hierarchical view
  2. Drill down via mcp.index_symbols(pattern)
  3. Check mcp.index_deps() for relationships
  4. Use semantic summaries for navigation, not truth
  5. For claims, always verify by execution
  ```

- [ ] **5.4: Constraint Injection Prompt**
  - Create system prompt prefix that always includes:
    - Current P0 constraints
    - Reminder to verify by execution
    - Link to verification tools

**Verification:**
```bash
# Check skills are registered
cat .claude/skills/rlm-task.md
```

---

### Phase 6: Hard Controls - Hooks and Gates

**Goal:** Enforce constraints via code, not just prompts.

- [ ] **6.1: Pre-commit Hook**
  ```bash
  #!/bin/bash
  # .git/hooks/pre-commit

  # Load extracted constraints
  CONSTRAINTS=".kelpie-index/constraints/extracted.json"

  if [ -f "$CONSTRAINTS" ]; then
    # Run each hard enforcement check
    jq -r '.[] | select(.enforcement == "hard") | .verification.command' "$CONSTRAINTS" | while read cmd; do
      echo "Running: $cmd"
      eval "$cmd"
      if [ $? -ne 0 ]; then
        echo "BLOCKED: Constraint check failed"
        exit 1
      fi
    done
  fi

  # Always run basic checks
  cargo test || exit 1
  cargo clippy --all-targets -- -D warnings || exit 1
  cargo fmt --check || exit 1
  ```

- [ ] **6.2: Index Freshness Gate**
  - In MCP tools, before returning index data:
    - Check if git SHA changed since index build
    - If stale, either:
      - Auto-rebuild (for small changes)
      - Return error with "index stale, run index_refresh"

- [ ] **6.3: Completion Verification Gate**
  - `state_task_complete` requires:
    - Proof of test execution (test output or SHA)
    - All P0 constraint checks passed
    - If missing, reject with "verification required"

- [ ] **6.4: Audit Trail**
  - Every MCP tool call logged:
    ```json
    {
      "timestamp": "2026-01-20T10:30:00Z",
      "tool": "verify_by_tests",
      "args": {"topic": "streaming"},
      "result": {"passed": true, "tests": 23},
      "git_sha": "82244509"
    }
    ```

**Verification:**
```bash
# Test pre-commit hook
git stash && git commit --allow-empty -m "test hook" # Should run checks

# Check audit log
cat .agentfs/audit.jsonl | tail -5
```

---

### Phase 7: Multi-Agent Index Build Orchestration

**Goal:** Parallelize index building with cross-validation.

- [ ] **7.1: Coordinator Script**
  ```rust
  // tools/kelpie-indexer/src/main.rs

  async fn build_all_indexes() {
      // Parallel structural indexing (deterministic)
      let (symbols, deps, tests, modules) = join!(
          build_symbol_index(),
          build_dependency_index(),
          build_test_index(),
          build_module_index(),
      );

      // Parallel semantic indexing (LLM agents)
      let (summaries, constraints) = join!(
          spawn_summary_agent(),
          spawn_constraint_agent(),
      );

      // Cross-validation
      let issues = cross_validate(&symbols, &deps, &summaries);

      // Write all indexes
      write_indexes(...);
  }
  ```

- [ ] **7.2: Incremental Rebuild**
  - On commit, detect changed files
  - Only rebuild indexes for changed files
  - Update freshness tracking

- [ ] **7.3: Git Hook for Auto-Index**
  ```bash
  # .git/hooks/post-commit
  ./tools/kelpie-indexer --incremental $(git diff --name-only HEAD~1 -- '*.rs')
  ```

**Verification:**
```bash
# Full rebuild
./tools/kelpie-indexer --full

# Incremental
./tools/kelpie-indexer --incremental crates/kelpie-core/src/lib.rs

# Check timing
time ./tools/kelpie-indexer --full
```

---

### Phase 8: Integration and Testing

**Goal:** Verify the complete system works end-to-end.

- [ ] **8.1: Unit Tests for Indexer**
  - Test symbol extraction
  - Test dependency graph building
  - Test test index building
  - Test freshness detection

- [ ] **8.2: Integration Test: Full Flow**
  ```
  1. Build indexes
  2. Start task via MCP
  3. Query indexes
  4. Make changes
  5. Verify by execution
  6. Complete task with proof
  7. Check audit trail
  ```

- [ ] **8.3: DST for Index Consistency**
  - Simulate index corruption
  - Simulate stale index
  - Verify gates catch issues

- [ ] **8.4: Documentation**
  - Update CLAUDE.md with new workflow
  - Create .claude/skills/ with RLM skills
  - Document MCP tools

**Verification:**
```bash
cargo test -p kelpie-indexer
./scripts/test_repo_os_e2e.sh
```

---

## Checkpoints

- [x] Codebase understood
- [x] Plan approved
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained**
- [x] **Phase 1: Foundation complete** ✅
- [ ] Phase 2: Structural indexing complete
- [ ] Phase 3: Semantic indexing complete
- [ ] Phase 4: MCP server complete
- [ ] Phase 5: RLM skills complete
- [ ] Phase 6: Hard controls complete
- [ ] Phase 7: Multi-agent orchestration complete
- [ ] Phase 8: Integration testing complete
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [ ] **DST coverage added** (for indexer and gates)
- [ ] **What to Try section updated**
- [ ] Committed

---

## Test Requirements

**Unit tests:**
- tools/kelpie-indexer - symbol extraction, dependency parsing, test discovery
- tools/mcp-kelpie - tool handlers, gates, audit logging

**DST tests (if critical path):**
- [ ] Index freshness detection under concurrent updates
- [ ] Verification gates under fault injection
- [ ] Audit logging under crashes

**Integration tests:**
- [ ] Full index build → query → verify flow
- [ ] Constraint extraction → enforcement flow
- [ ] Multi-agent coordination

**Commands:**
```bash
# Run indexer tests
cargo test -p kelpie-indexer

# Run MCP server tests
cd tools/mcp-kelpie && npm test

# Run E2E test
./scripts/test_repo_os_e2e.sh

# Run DST
cargo test -p kelpie-dst index
```

---

## Dependencies and Prerequisites

1. **tree-sitter-rust** or **rust-analyzer CLI** for symbol extraction
2. **SQLite** for AgentFS (or the agentfs npm package)
3. **jq** for JSON processing in scripts
4. **Node.js** for MCP server

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| LLM constraint extraction hallucinates | P0 constraints wrong | Validate by running verification command |
| Index goes stale silently | Agent trusts wrong info | Merkle-style freshness checks, git SHA tracking |
| Semantic summaries drift | Navigation misleads | Use for navigation only, always verify claims by execution |
| MCP server becomes bottleneck | Slow agent operations | Cache aggressively, parallel tool calls |
| Agent ignores soft controls | Workflow not followed | Hard floor catches via pre-commit hooks |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| | | | |

---

## Findings

### Phase 1: Foundation (Completed 2026-01-20)

**Directory Structure:**
- Created `.kelpie-index/` with 4 subdirectories (structural, semantic, constraints, meta)
- Created `.agentfs/` for SQLite-backed agent state
- All directories include README.md for self-documentation

**AgentFS Database:**
- SQLite schema with 3 tables: agent_state (KV store), verified_facts (execution proofs), audit_log (tool calls)
- Indexes on timestamp columns for efficient queries
- Initial state includes "initialized" and "current_task" entries

**Git Tracking Strategy:**
- `.agentfs/` git-ignored (ephemeral)
- `.kelpie-index/semantic/` git-ignored (LLM-generated, may vary)
- `.kelpie-index/structural/` git-tracked (deterministic, useful for review)
- `.kelpie-index/meta/` git-tracked (freshness tracking is critical)

**Freshness Tracking:**
- Initialized with current git SHA: 53f582a041bb5092cd1462c18673397e466495a3
- Placeholder for file_hashes map (will be populated during index building)

**Key Insight:**
The separation between structural (deterministic, tracked) and semantic (LLM-generated, ignored) indexes is working well. This allows us to version control the deterministic parts while keeping the variable parts out of git.

---

## What to Try [UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Plan exists | Read this file | Understanding of architecture |
| Directory structure | `ls -la .kelpie-index/` | See structural/, semantic/, constraints/, meta/ subdirectories |
| Index placeholders | `cat .kelpie-index/structural/symbols.json` | See empty index structure with version, git_sha fields |
| AgentFS database | `sqlite3 .agentfs/agent.db "SELECT * FROM agent_state;"` | See initialized=true and current_task |
| Database schema | `sqlite3 .agentfs/agent.db ".schema"` | See agent_state, verified_facts, audit_log tables |
| Git ignore | `git status` | .agentfs/ not tracked, .kelpie-index/structural/ tracked |
| Freshness tracking | `cat .kelpie-index/meta/freshness.json` | See current git SHA: 53f582a0 |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| Index building | Not implemented | Phase 2 |
| Semantic summaries | Not implemented | Phase 3 |
| MCP server | Not implemented | Phase 4 |
| RLM skills | Not implemented | Phase 5 |
| Hard controls | Not implemented | Phase 6 |

### Known Limitations ⚠️
- Phase 1 only creates the structure, indexes are empty
- AgentFS database has schema but no real data yet
- .gitignore patterns will only take effect after committing
- Semantic embeddings directory exists but is optional

---

## Open Questions - RESOLVED

1. **AgentFS vs roll-our-own SQLite** - ✅ Use AgentFS (Turso's package)
2. **Embeddings** - ✅ Skip for now, can add later
3. **Index storage** - ✅ Git-track `.kelpie-index/` (structural is deterministic, useful for review)
4. **Rust vs TypeScript** - ✅ Rust for indexer (consistent with kelpie, performant)
5. **Implementation order** - ✅ All phases, in order

---

## Completion Notes

**Verification Status:**
- Tests: [pending]
- Clippy: [pending]
- Formatter: [pending]
- /no-cap: [pending]
- Vision alignment: [pending]

**Commit:** [pending]

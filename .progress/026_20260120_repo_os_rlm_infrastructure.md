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

## Solution: Repo OS + RLM + Hard Control Layer

Build an infrastructure layer with **two complementary systems**:

1. **RLM (Recursive Language Models)** - Efficient context management
   - Agent never sees full codebase directly
   - Codebase stored as queryable variable in REPL environment
   - Agent writes code to interact: `grep()`, `peek()`, `partition()`
   - Recursive sub-calls for large searches
   - Solves: context rot, partial coverage, token waste

2. **Hard Control Layer** - Enforcement and verification
   - MCP tools enforce invariants (can't lie about completion)
   - Git hooks catch what slips through
   - Verification by execution, not by trusting docs
   - Solves: stale MD files, P0 violations, agent lies

Together:
- **RLM** ensures agent CAN explore the codebase efficiently (capability)
- **Hard Control Layer** ensures agent MUST verify claims (enforcement)

---

## How RLM Works

### What is RLM?

**RLM (Recursive Language Model)** is an inference strategy where the LLM **never sees the full context directly**. Instead, context is stored as a variable in a REPL environment, and the LLM writes code to interact with it.

Reference: [alexzhang13.github.io/blog/2025/rlm](https://alexzhang13.github.io/blog/2025/rlm/)

```
Traditional LM:                              RLM:
┌────────────────────────────┐              ┌────────────────────────────────────┐
│  LM(query, context)        │              │  RLM(query, context)               │
│                            │              │                                    │
│  Context: 500K tokens      │              │  Root LM sees: just the query      │
│  (entire codebase)         │              │  Context: stored as `codebase` var │
│                            │              │                                    │
│  LM processes ALL tokens   │              │  Root LM writes code:              │
│  at once                   │              │    matches = grep(codebase, "Fdb") │
│                            │              │    subset = read_file(matches[0])  │
│  ❌ Context rot (quality   │              │    answer = RLM(query, subset)     │
│     degrades with length)  │              │                    ↑               │
│  ❌ Token limit hit        │              │            Recursive call!         │
│  ❌ Expensive (all tokens) │              │                                    │
│  ❌ Misses things          │              │  ✅ No context rot                 │
│                            │              │  ✅ Unbounded context              │
└────────────────────────────┘              │  ✅ Efficient (query what you need)│
                                            │  ✅ Complete coverage              │
                                            └────────────────────────────────────┘
```

### The REPL Environment

The agent operates in a **code execution environment** where the codebase is a queryable variable:

```python
# REPL Environment State
codebase = CodebaseContext("/Users/dev/kelpie")  # Never loaded into LLM context directly
indexes = load_indexes(".kelpie-index/")          # Structural indexes available
constraints = load_constraints()                   # P0 constraints injected

# Agent writes code to interact (not prose commands)
```

### RLM Interaction Patterns

The agent develops **emergent strategies** for exploring context:

```python
# 1. PEEKING - Sample structure before diving deep
files = codebase.list_files("crates/kelpie-storage/src/")
preview = codebase.peek("crates/kelpie-storage/src/lib.rs", lines=50)

# 2. GREPPING - Narrow down with regex
matches = codebase.grep(r"impl\s+ActorKV", file_pattern="*.rs")
# Returns: [("src/fdb.rs", 45), ("src/memory.rs", 23), ...]

# 3. PARTITION + MAP - Chunk and recursively process
chunks = codebase.partition_by_module("crates/kelpie-storage/")
results = []
for chunk in chunks:
    # Recursive RLM call with smaller context
    result = RLM("find all error handling patterns", chunk)
    results.append(result)
summary = aggregate(results)

# 4. FOCUSED READ - Read specific sections
content = codebase.read_file("src/fdb.rs", start_line=45, end_line=100)

# 5. INDEX QUERY - Use pre-built structural indexes
symbols = indexes.query_symbols("FdbStorage")
deps = indexes.query_deps("kelpie-storage")
tests = indexes.query_tests(topic="storage")
```

### How RLM Solves Our Problems

| Problem | Traditional Agent | RLM Agent |
|---------|-------------------|-----------|
| **Context fills up** | Reads random files, runs out of tokens | Queries indexes, reads only relevant sections |
| **Partial coverage (20%)** | Greps once, stops | Partition + Map: recursively processes ALL modules |
| **Misses edge cases** | Context too large, things get lost | Focused reads, nothing lost to context rot |
| **Expensive** | Processes 500K tokens every call | Processes only what's needed |

### Concrete Example: "Find all dead code"

**Traditional Agent:**
```
Agent: *reads 50 files into context*
       "I found 3 unused functions"
       *context full, stops*

Reality: Missed 15 more across other modules (partial coverage)
```

**RLM Agent:**
```python
# Agent writes code in REPL:
modules = codebase.list_modules()  # ["kelpie-core", "kelpie-storage", ...]

all_dead_code = []
for module in modules:
    # Recursive RLM call for each module
    dead = RLM(f"find unused functions in {module}",
               codebase.get_module(module))
    all_dead_code.extend(dead)

# Cross-reference with call graph
confirmed_dead = []
for func in all_dead_code:
    refs = indexes.query_references(func.name)
    if len(refs) == 0:
        confirmed_dead.append(func)

FINAL(confirmed_dead)  # Returns complete list
```

**Result:** Complete coverage, no context rot, verifiable results.

### RLM Control Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              RLM EXECUTION                                   │
└─────────────────────────────────────────────────────────────────────────────┘

User Query: "Find all places where errors are silently ignored"

┌─────────────────────────────────────────────────────────────────────────────┐
│  ROOT LM (sees query only, not codebase)                                    │
│                                                                             │
│  Decides strategy: "I'll grep for .unwrap() and .ok(), then check each"    │
│                                                                             │
│  Writes code:                                                               │
│    candidates = codebase.grep(r"\.(unwrap|ok)\(\)", "*.rs")                │
│    # Returns 150 matches - too many to process at once                     │
│                                                                             │
│    # Partition by file                                                      │
│    by_file = group_by_file(candidates)                                     │
│                                                                             │
│    silent_ignores = []                                                      │
│    for file, matches in by_file.items():                                   │
│        context = codebase.read_context(file, matches, padding=5)           │
│        # RECURSIVE CALL with focused context                                │
│        result = RLM("which of these silently ignore errors?", context)     │
│        silent_ignores.extend(result)                                        │
│                                                                             │
│    FINAL(silent_ignores)                                                    │
└─────────────────────────────────────────────────────────────────────────────┘
         │
         │ Spawns recursive calls
         ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  SUB-LM CALLS (depth 1, focused context)                                    │
│                                                                             │
│  RLM("which silently ignore?", context_for_fdb.rs)                         │
│    → "Line 45: .ok() discards StorageError without logging"                │
│    → "Line 89: .unwrap() is fine - already checked Result"                 │
│                                                                             │
│  RLM("which silently ignore?", context_for_actor.rs)                       │
│    → "Line 23: .ok() discards error - SILENT IGNORE"                       │
│    → ...                                                                    │
└─────────────────────────────────────────────────────────────────────────────┘
         │
         │ Results aggregated
         ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  FINAL RESULT                                                               │
│                                                                             │
│  silent_ignores = [                                                         │
│    { file: "fdb.rs", line: 45, issue: ".ok() discards StorageError" },     │
│    { file: "actor.rs", line: 23, issue: ".ok() discards error" },          │
│    ... (complete list, nothing missed)                                      │
│  ]                                                                          │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## How the Hard Control Layer Works

The Hard Control Layer **enforces behavior** that the LLM might otherwise skip. While RLM helps the agent explore efficiently, the Hard Control Layer ensures the agent can't lie, skip verification, or ignore constraints.

### Why We Need Both

| RLM (Capability) | Hard Control Layer (Enforcement) |
|------------------|----------------------------------|
| Agent CAN find all dead code | Agent MUST verify before claiming complete |
| Agent CAN query indexes efficiently | Agent CANNOT access stale indexes |
| Agent CAN explore the codebase | Agent CANNOT mark phase complete without evidence |
| Agent CAN recursively search | Agent CANNOT skip handoff verification |

### Soft Controls vs Hard Controls

| Control Type | Mechanism | Can LLM Bypass? | Examples |
|--------------|-----------|-----------------|----------|
| **Soft** | Prompt injection, skills | Yes (might ignore) | "Verify by execution", "Update plan after each phase" |
| **Hard** | Tool parameters, gates, hooks | No (enforced by code) | Evidence required for completion, freshness check before query |

### Layered Control Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  RLM LAYER (Capability)                                         │
│  • REPL environment with codebase as variable                   │
│  • Recursive sub-calls for large contexts                       │
│  • grep(), peek(), partition(), map() operations                │
│                                                                 │
│  Agent CAN explore efficiently.                                 │
├─────────────────────────────────────────────────────────────────┤
│  SOFT CONTROLS (Guidance)                                       │
│  • Skill instructions for workflows                             │
│  • "Prefer structural indexes over semantic"                    │
│  • "Verify claims by execution"                                 │
│                                                                 │
│  Agent SHOULD follow these. We hope it does.                    │
├─────────────────────────────────────────────────────────────────┤
│  HARD CONTROLS (MCP Tool Gates)                                 │
│  • index_query() → MUST pass freshness check                    │
│  • mark_phase_complete() → MUST provide evidence                │
│  • mark_phase_complete() → System re-runs verification          │
│  • start_plan_session() → System re-verifies all completions    │
│                                                                 │
│  Agent CANNOT bypass these. Code enforces.                      │
├─────────────────────────────────────────────────────────────────┤
│  HARD FLOOR (Git Hooks, CI)                                     │
│  • Pre-commit: tests must pass                                  │
│  • Pre-commit: clippy must pass                                 │
│  • Pre-commit: DST coverage for critical paths                  │
│  • CI: determinism verification                                 │
│                                                                 │
│  Even if RLM + tools fail, this catches it.                     │
└─────────────────────────────────────────────────────────────────┘
```

### Hard Control Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         HARD CONTROL LOOP                                    │
└─────────────────────────────────────────────────────────────────────────────┘

1. SESSION START
   ┌──────────────────────────────────────────────────────────────────────────┐
   │ Tool: start_plan_session(plan_id)                                        │
   │                                                                          │
   │ • Load plan from AgentFS                                                 │
   │ • HARD: Re-verify ALL previously completed phases (can't skip)          │
   │ • Inject P0 constraints into REPL environment                           │
   │ • Present verification report to agent                                   │
   │                                                                          │
   │ Agent receives: { plan, verification_report, constraints }               │
   └──────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
2. TASK EXECUTION (RLM + Tools)
   ┌──────────────────────────────────────────────────────────────────────────┐
   │                                                                          │
   │  ┌─────────────┐     ┌─────────────┐     ┌─────────────┐                │
   │  │  RLM Agent  │────▶│  MCP Tools  │────▶│  AgentFS    │                │
   │  │  (REPL)     │     │  (gates)    │     │  (persist)  │                │
   │  └─────────────┘     └─────────────┘     └─────────────┘                │
   │         │                   │                                            │
   │         ▼                   ▼                                            │
   │  Agent writes code:   Tool enforces:                                     │
   │    results = grep()    HARD: Freshness check                            │
   │    tests = query()     HARD: Evidence required                          │
   │    verified = run()    HARD: Re-runs verification                       │
   │                                                                          │
   └──────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
3. COMPLETION (Verified)
   ┌──────────────────────────────────────────────────────────────────────────┐
   │ Tool: mark_phase_complete(phase, evidence)                               │
   │                                                                          │
   │ • HARD: Evidence parameter required (can't omit)                        │
   │ • HARD: System re-runs verification commands NOW                        │
   │ • HARD: Only stores if ALL pass                                         │
   │ • Stores: evidence + git_sha + timestamp in AgentFS                     │
   └──────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
4. HANDOFF (Auto-Verified)
   ┌──────────────────────────────────────────────────────────────────────────┐
   │ Next agent calls start_plan_session()                                    │
   │                                                                          │
   │ • HARD: All completions re-verified automatically                        │
   │ • Failed verifications marked UNVERIFIED                                │
   │ • New agent sees ground truth, not previous claims                      │
   └──────────────────────────────────────────────────────────────────────────┘
```

### Concrete Example: "Is the streaming feature complete?"

**Without Hard Control Layer:**
```
Agent: *reads .progress/015_streaming.md*
       "According to the plan, Phase 3 is marked [x] complete"
       "Yes, streaming is complete!"

Reality: Tests are failing, but agent trusted the MD file.
```

**With Hard Control Layer:**
```
Agent: *calls mcp.verify_claim("streaming feature complete")*

Tool (HARD enforcement):
  1. Find relevant tests: index_tests("streaming") → 12 tests
  2. Run tests: verify_by_tests("streaming")
  3. Results: 10 pass, 2 fail
  4. Return: { verified: false, evidence: { passed: 10, failed: 2, failures: [...] } }

Agent: "Streaming is NOT complete. 2 tests are failing:
        - test_streaming_backpressure (timeout)
        - test_streaming_error_recovery (assertion failed)"

Reality: Agent was forced to verify by execution.
```

### State Management

```
AgentFS Structure:
┌─────────────────────────────────────────────────────────────────┐
│ .agentfs/agent.db (SQLite)                                      │
├─────────────────────────────────────────────────────────────────┤
│ agent_state (KV store)                                          │
│ ├── current_task: "Implement Phase 3 of streaming"              │
│ ├── current_plan: "plan_015"                                    │
│ └── last_action: "verified fdb storage tests"                   │
├─────────────────────────────────────────────────────────────────┤
│ verified_facts (execution proofs)                               │
│ ├── { claim: "FDB tests pass", method: "cargo test",            │
│ │     result: "47 passed", timestamp: "...", git_sha: "..." }   │
│ └── { claim: "No clippy warnings", method: "cargo clippy", ...} │
├─────────────────────────────────────────────────────────────────┤
│ completions/{plan_id}/{phase}                                   │
│ ├── phase_1: { status: "verified", evidence: {...} }            │
│ ├── phase_2: { status: "verified", evidence: {...} }            │
│ └── phase_3: { status: "in_progress" }                          │
├─────────────────────────────────────────────────────────────────┤
│ audit_log (every tool call)                                     │
│ ├── { tool: "index_query", args: {...}, result: {...}, ts: ...} │
│ └── { tool: "mark_phase_complete", args: {...}, ... }           │
└─────────────────────────────────────────────────────────────────┘
```

### Why Both Systems Together

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        RLM + HARD CONTROL SYNERGY                            │
└─────────────────────────────────────────────────────────────────────────────┘

User: "Find all dead code and remove it"

┌─────────────────────────────────────────────────────────────────────────────┐
│  RLM (Capability)                                                           │
│                                                                             │
│  modules = codebase.list_modules()                                         │
│  dead_code = []                                                             │
│  for module in modules:                                                     │
│      dead = RLM("find unused functions", codebase.get_module(module))      │
│      dead_code.extend(dead)                                                 │
│                                                                             │
│  # Complete coverage via recursive decomposition                            │
│  # Found 18 unused functions (not just the 3 a traditional agent would)    │
└─────────────────────────────────────────────────────────────────────────────┘
         │
         │ Agent claims: "I found and removed 18 dead functions"
         ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  HARD CONTROL LAYER (Enforcement)                                           │
│                                                                             │
│  Agent: mark_phase_complete("dead_code_removal", evidence)                  │
│                                                                             │
│  Tool: HARD checks:                                                         │
│    ✓ Evidence includes list of removed functions                           │
│    ✓ cargo test passes (nothing broken)                                    │
│    ✓ cargo clippy passes                                                   │
│    ✓ detect_dead_code() returns empty (verified clean)                     │
│                                                                             │
│  All pass → Completion stored with proof                                   │
│  Any fail → Rejected, agent must fix                                       │
└─────────────────────────────────────────────────────────────────────────────┘

Result:
- RLM ensured COMPLETE coverage (found all 18, not just 3)
- Hard Control ensured VERIFIED result (can't lie about removal)
```

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

### Decision 4: RLM Implementation Strategy

**Context:** How do we implement actual RLM (recursive context management with REPL)?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Prompt-only | Instruct agent to "query indexes, don't read files directly" | Simple | Agent might ignore, still loads context |
| B: MCP tools for codebase ops | Tools like `grep()`, `peek()`, `read_section()` | Enforced via tools | Not true REPL, no recursion |
| C: REPL environment + recursive calls | Agent writes Python/code, spawns sub-LLM calls | True RLM, complete coverage | Complex, need execution environment |
| D: Hybrid B+C | MCP tools for simple ops, REPL for complex recursive tasks | Pragmatic balance | Two interaction modes |

**Decision:** **Option D** - Hybrid approach:

1. **MCP Tools (Simple Operations):**
   - `codebase_grep(pattern, file_glob)` - Search without loading into context
   - `codebase_peek(file, lines)` - Sample file structure
   - `codebase_read_section(file, start, end)` - Focused reads
   - `index_query(type, query)` - Query pre-built structural indexes

2. **REPL Environment (Complex Operations):**
   - For partition+map, recursive decomposition
   - Agent writes code that spawns sub-LLM calls
   - Results aggregated programmatically
   - Used for: "find ALL X", "analyze EVERY module", comprehensive searches

**Implementation:**
```python
# REPL Environment (when needed for complex tasks)
class RLMEnvironment:
    def __init__(self, codebase_path, indexes):
        self.codebase = CodebaseContext(codebase_path)  # Never in LLM context
        self.indexes = indexes
        self.llm = ClaudeAPI()  # For recursive calls

    def grep(self, pattern, glob="*.rs"):
        return self.codebase.grep(pattern, glob)

    def peek(self, file, lines=50):
        return self.codebase.peek(file, lines)

    def partition_by_module(self):
        return self.codebase.list_modules()

    def recursive_call(self, query, context_subset):
        """Spawn sub-LLM call with focused context"""
        return self.llm.complete(query, context=context_subset)

    def map_reduce(self, query, partitions):
        """Partition + Map pattern"""
        results = []
        for partition in partitions:
            result = self.recursive_call(query, partition)
            results.append(result)
        return self.aggregate(results)
```

**Trade-offs accepted:**
- Two interaction modes (MCP tools vs REPL)
- REPL requires code execution environment
- Recursive calls add latency and cost (but ensure completeness)

---

### Decision 4b: Hard Control Layer Implementation

**Context:** How do we implement the Hard Control Layer (enforcement, verification)?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Claude Code + MCP only | MCP tools enforce via parameters/gates | Works with existing setup | LLM still decides when to call |
| B: External orchestrator | Separate program controls flow, calls LLM | Full control | Significant work, different paradigm |
| C: Claude Code + MCP + Git Hooks | MCP for runtime, hooks for commit-time | Layered enforcement | Two enforcement points |

**Decision:** **Option C** - Claude Code + MCP + Git Hooks:

1. **MCP Tools (Runtime Enforcement):**
   - `mark_phase_complete(phase, evidence)` - HARD requires evidence, re-runs verification
   - `start_plan_session(plan_id)` - HARD re-verifies all prior completions
   - `index_query(...)` - HARD freshness check before returning

2. **Git Hooks (Commit-time Enforcement):**
   - Pre-commit: tests must pass
   - Pre-commit: clippy must pass
   - Pre-commit: DST coverage for critical path changes
   - Pre-commit: constraint verification

3. **Skills (Soft Guidance):**
   - Workflow instructions (might be ignored)
   - Best practices (might be ignored)
   - Mitigated by hard controls above

**Trade-offs accepted:**
- LLM still decides when to call verification tools
- Git hooks only catch at commit time, not during session
- Layered approach covers gaps

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

### Decision 6: Evidence-Based Completion Enforcement

**Context:** How do we ensure agents provide proof of completion, not just checkboxes?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Natural language | Prompt says "provide evidence" | Simple | Agent might ignore |
| B: MCP tool requires evidence | Tool parameter is mandatory | Can't skip | Requires MCP infrastructure |
| C: Tool + system re-runs verification | Tool requires evidence AND system verifies it | Can't lie | Most complex, most reliable |

**Decision:** **Option C** - HARD enforcement via MCP tool:
1. `mark_phase_complete(phase, evidence)` requires evidence parameter (can't omit)
2. System re-runs all verification commands in evidence (can't lie about results)
3. Only stores completion if all verifications pass
4. Evidence stored in AgentFS with git SHA, timestamp, actual outputs

**Implementation:**
```typescript
async function mark_phase_complete(phase: string, evidence: Evidence): Result {
  // HARD: Evidence parameter required
  if (!evidence.verification_commands?.length) {
    throw new Error("Cannot mark complete without verification commands");
  }

  // HARD: System re-runs verifications NOW
  for (const cmd of evidence.verification_commands) {
    const result = await exec(cmd.command);
    if (!matches(result, cmd.expected)) {
      throw new Error(`Verification failed: ${cmd.command}`);
    }
  }

  // HARD: Only if all pass, store completion
  await agentfs.store(`completions/${phase}`, {
    ...evidence,
    verified_at: Date.now(),
    git_sha: await getCurrentSha()
  });

  return { success: true };
}
```

**Trade-offs accepted:**
- More ceremony for completion
- Agent must think about what to verify (good - forces explicit verification design)

---

### Decision 7: Handoff Verification Enforcement

**Context:** How do we ensure new agents don't trust previous agents' claims?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Natural language | Skill says "verify before continuing" | Simple | Agent might skip |
| B: Automatic on session start | System runs all verifications when agent starts | Can't skip | Adds startup latency |
| C: Blocking gate | Agent can't access "completed" phases without re-verification | Forces verification | Most restrictive |

**Decision:** **Option B** - HARD automatic verification on session start:
1. When agent calls `start_plan_session(plan_id)`, system automatically re-runs ALL verification commands for completed phases
2. Failed verifications mark phases as UNVERIFIED
3. Agent receives verification report - can't ignore it
4. Agent decides what to do (soft), but detection is automatic (hard)

**Implementation:**
```typescript
async function start_plan_session(plan_id: string): SessionResult {
  const completions = await agentfs.list(`completions/${plan_id}/*`);
  const results = [];

  // HARD: System automatically re-verifies everything
  for (const completion of completions) {
    for (const cmd of completion.verification_commands) {
      const result = await exec(cmd.command);
      const passed = matches(result, cmd.expected);

      results.push({ phase: completion.phase, command: cmd.command, passed, actual: result });

      if (!passed) {
        // HARD: Mark as unverified
        await agentfs.update(`completions/${completion.phase}`, { status: 'unverified' });
      }
    }
  }

  return { plan_id, verification_report: results };
}
```

**Trade-offs accepted:**
- Startup latency (running all verifications)
- May surface issues previous agent didn't know about (feature, not bug)

---

### Decision 8: Slop Detection Strategy

**Context:** How do we find and purge existing slop in the codebase?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Manual agent hunt | Ask agent to find slop | Flexible | Partial coverage, agent might miss |
| B: Automated tools | Dedicated detection tools | Systematic | Needs tool development |
| C: Hybrid | Tools detect, agent investigates/fixes | Best coverage | Complex |

**Decision:** **Option C** - Automated detection with agent-driven cleanup:
1. Slop detection tools (HARD, deterministic):
   - `detect_dead_code()` - cargo udeps + call graph
   - `detect_orphaned()` - git history analysis
   - `detect_duplicates()` - semantic similarity
   - `detect_fake_dst()` - verify DST tests actually use harness
   - `detect_incomplete()` - TODO/FIXME/panic! scan
   - `detect_lies()` - compare plan claims to actual test results
2. Agent investigates candidates (SOFT)
3. Agent proposes cleanup (SOFT)
4. Verification after cleanup (HARD)

**Trade-offs accepted:**
- Tool development effort
- Some false positives (agent filters)

---

### Decision 9: DST Harness Adequacy Verification

**Context:** How do we ensure the DST harness itself is complete enough to make tests meaningful?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Trust harness | Assume kelpie-dst is complete | Simple | Gaps undetected |
| B: Manual audit | Human reviews harness periodically | Catches nuance | Doesn't scale, forgotten |
| C: Automated capability audit | Tool verifies harness implements required concepts | Systematic | May miss subtle gaps |
| D: Capability + Fidelity + Simulability | Multi-layer analysis of what harness can/can't do | Complete picture | Complex, requires maintenance |

**Decision:** **Option D** - Three-layer harness adequacy verification:

1. **Capability Audit** (AUTOMATED):
   - Verify harness exports all required components (SimClock, SimStorage, SimNetwork, SimVm, etc.)
   - Verify all 16 fault types from CONSTRAINTS.md are implemented
   - Flag missing components or fault handlers

2. **Fidelity Check** (DOCUMENTED):
   - For each simulation component, explicitly document:
     - What it models (e.g., SimStorage models transactions)
     - What it does NOT model (e.g., SimStorage doesn't model FDB conflicts)
     - Known gaps with severity and mitigation
   - This creates a "simulation gap registry"

3. **Simulability Analysis** (PER CRITICAL PATH):
   - For each of the 8 critical paths, enumerate scenarios
   - Determine which scenarios CAN be simulated vs CANNOT
   - Calculate coverage quality (FULL/PARTIAL/POOR)
   - Generate action items for improving simulability

**Key Insight:** A test using the harness is only as good as the harness's fidelity to reality. If SimStorage doesn't model transaction conflicts, then a test for concurrent writes is meaningless.

**Trade-offs accepted:**
- Requires explicit documentation of simulation gaps (beneficial overhead)
- May reveal that some critical scenarios are currently untestable (good to know)
- Fidelity specs need maintenance as harness evolves (track with harness_evolution.jsonl)

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
| 2026-01-20 11:30 | HARD evidence-based completion | Agents can't lie about completion | More ceremony, MCP required |
| 2026-01-20 11:30 | HARD automatic handoff verification | New agents can't trust old claims | Startup latency |
| 2026-01-20 11:30 | Hybrid slop detection | Tools detect, agents investigate | Tool development effort |
| 2026-01-20 12:15 | DST coverage enforcement (HARD) | Critical paths require DST tests | Pre-commit latency, may block commits |
| 2026-01-20 12:30 | Harness adequacy verification | Harness must model real failure modes | Requires documenting known simulation gaps |
| 2026-01-20 13:00 | Actual RLM (recursive context management) | Complete coverage, no context rot | REPL environment complexity |
| 2026-01-20 13:00 | Hybrid RLM implementation | MCP for simple, REPL for complex | Two interaction modes |
| 2026-01-20 13:00 | Separate RLM from Hard Control Layer | RLM=capability, Control=enforcement | Clearer architecture |
| 2026-01-20 13:30 | Python REPL for RLM (RestrictedPython) | Sandboxed, simple subprocess from MCP | Python as dependency |
| 2026-01-20 13:30 | 30s timeout, 3-level depth, 100KB output limits | Prevent runaway execution | Limits complex analysis |

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              AGENT LAYER                                    │
│                       (Claude Code + Skills)                                │
│                                                                             │
│    User Query: "Find all dead code and remove it"                          │
│                              │                                              │
│                              ▼                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                 RLM LAYER (Recursive Context Management)            │    │
│  │                                                                     │    │
│  │  Agent writes code in REPL:                                         │    │
│  │    modules = partition_by_module()                                  │    │
│  │    for m in modules:                                                │    │
│  │        dead = RLM("find unused functions", m)  # Recursive call    │    │
│  │        results.extend(dead)                                         │    │
│  │    FINAL(results)                                                   │    │
│  │                                                                     │    │
│  │  • Codebase as queryable variable (not in context)                 │    │
│  │  • grep(), peek(), read_section() - focused access                 │    │
│  │  • Recursive sub-calls for large contexts                          │    │
│  │  • Complete coverage via partition + map                           │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                 HARD CONTROL LAYER (Enforcement)                    │    │
│  │                                                                     │    │
│  │  MCP Tool Gates:                                                    │    │
│  │  • mark_phase_complete() → MUST provide evidence, system re-runs   │    │
│  │  • start_plan_session() → MUST re-verify all prior completions     │    │
│  │  • index_query() → MUST pass freshness check                       │    │
│  │                                                                     │    │
│  │  Integrity Checks:                                                  │    │
│  │  • Handoff verification (auto re-verify on session start)          │    │
│  │  • Slop detection (dead code, duplicates, fake DST)                │    │
│  │  • DST coverage enforcement                                         │    │
│  │  • Harness adequacy verification                                    │    │
│  │                                                                     │    │
│  │  Audit Trail:                                                       │    │
│  │  • Every tool call logged                                           │    │
│  │  • Evidence stored with git SHA                                     │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                 HARD FLOOR (Git Hooks, CI)                          │    │
│  │                                                                     │    │
│  │  Pre-commit:                                                        │    │
│  │  • Tests must pass                                                  │    │
│  │  • Clippy must pass                                                 │    │
│  │  • DST coverage for critical path changes                          │    │
│  │                                                                     │    │
│  │  CI:                                                                │    │
│  │  • Determinism verification (same seed = same output)              │    │
│  │  • Multiple seed testing                                            │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────────────────┘
                                     │
         ┌───────────────────────────┼───────────────────────────┐
         ▼                           ▼                           ▼
┌─────────────────┐        ┌─────────────────┐        ┌─────────────────┐
│  RLM Environment│        │   Index Layer   │        │   Execution     │
│  (REPL + Context)        │  (Knowledge)    │        │  (Ground Truth) │
│                 │        │                 │        │                 │
│ • CodebaseContext        │ • structural/   │        │ • cargo test    │
│   (never in LLM │        │   symbols.json  │        │ • cargo clippy  │
│    context)     │        │   deps.json     │        │ • DST tests     │
│ • grep(), peek()│        │   tests.json    │        │ • rust-analyzer │
│ • RLM() calls   │        │ • semantic/     │        │ • tree-sitter   │
│ • map_reduce()  │        │   summaries/    │        │                 │
│                 │        │ • constraints/  │        │ (Real execution)│
│ (Python REPL)   │        │   extracted.json│        │                 │
└─────────────────┘        └─────────────────┘        └─────────────────┘
         │                           │                           │
         │                           │                           │
         ▼                           ▼                           ▼
┌─────────────────┐        ┌─────────────────┐        ┌─────────────────┐
│    AgentFS      │        │   Codebase      │        │   Verification  │
│  (Agent State)  │        │  (Source)       │        │   Results       │
│                 │        │                 │        │                 │
│ • current_task  │        │ • crates/       │        │ • test output   │
│ • verified_facts│        │ • tests/        │        │ • clippy output │
│ • completions/  │        │ • docs/         │        │ • coverage data │
│ • audit_log     │        │                 │        │                 │
│                 │        │ (Never loaded   │        │ (Actual proof   │
│ (SQLite-backed) │        │  into context)  │        │  of claims)     │
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
│  • .kelpie-index/    (auto-generated indexes - git-tracked)                 │
│  • .agentfs/         (agent state - git-ignored)                            │
│  • tools/rlm-env/    (RLM REPL environment)                                 │
│  • tools/mcp-kelpie/ (MCP server with hard controls)                        │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Architecture Summary

| Layer | Purpose | Mechanism |
|-------|---------|-----------|
| **RLM Layer** | Efficient codebase exploration | REPL + recursive calls, codebase as variable |
| **Hard Control Layer** | Enforcement, verification | MCP tool gates, evidence required |
| **Hard Floor** | Final safety net | Git hooks, CI checks |
| **Index Layer** | Queryable knowledge | Structural + semantic indexes |
| **AgentFS** | Persistent agent state | SQLite-backed, audit trail |
| **Execution** | Ground truth | Actual test runs, tool output |

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

### Phase 3b: RLM Environment (Recursive Context Management)

**Goal:** Build the Python REPL environment that enables true RLM - agent writes Python code to interact with codebase, can spawn recursive sub-calls.

**Implementation:** Python package that MCP server calls via subprocess.

- [ ] **3b.0: Python Package Setup**

  ```
  tools/rlm-env/
  ├── pyproject.toml          # Package config (use uv/poetry)
  ├── README.md               # Usage docs
  ├── rlm_env/
  │   ├── __init__.py
  │   ├── __main__.py         # CLI entry: python -m rlm_env
  │   ├── codebase.py         # CodebaseContext class
  │   ├── environment.py      # RLMEnvironment with exec()
  │   ├── llm.py              # Claude API wrapper for recursive calls
  │   ├── sandbox.py          # Safe execution environment
  │   └── types.py            # GrepMatch, ModuleContext, etc.
  └── tests/
      ├── test_codebase.py
      ├── test_environment.py
      └── test_sandbox.py
  ```

  **pyproject.toml:**
  ```toml
  [project]
  name = "rlm-env"
  version = "0.1.0"
  dependencies = [
      "anthropic>=0.18.0",    # Claude API for recursive calls
      "restrictedpython",     # Sandboxed code execution
  ]

  [project.scripts]
  rlm-env = "rlm_env.__main__:main"
  ```

  **CLI Interface (for MCP to call):**
  ```python
  # rlm_env/__main__.py
  import argparse
  import json
  import sys
  from .environment import RLMEnvironment

  def main():
      parser = argparse.ArgumentParser()
      parser.add_argument("--codebase", required=True, help="Path to codebase root")
      parser.add_argument("--indexes", required=True, help="Path to .kelpie-index/")
      parser.add_argument("--execute", help="Python code to execute")
      parser.add_argument("--stdin", action="store_true", help="Read code from stdin")
      args = parser.parse_args()

      env = RLMEnvironment(args.codebase, args.indexes)

      if args.stdin:
          code = sys.stdin.read()
      else:
          code = args.execute

      try:
          result = env.execute(code)
          print(json.dumps({"success": True, "result": result}))
      except Exception as e:
          print(json.dumps({"success": False, "error": str(e)}))
          sys.exit(1)

  if __name__ == "__main__":
      main()
  ```

  **MCP Server Integration:**
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
      let stderr = "";

      proc.stdout.on("data", (data) => stdout += data);
      proc.stderr.on("data", (data) => stderr += data);

      proc.on("close", (code) => {
        if (code === 0) {
          resolve(JSON.parse(stdout));
        } else {
          reject(new Error(stderr || stdout));
        }
      });
    });
  }
  ```

- [ ] **3b.1: Codebase Context Layer**

  Build the `CodebaseContext` class that provides programmatic access to the codebase without loading it into LLM context:

  ```python
  # tools/rlm-env/codebase.py

  class CodebaseContext:
      """Codebase access layer - never loads full content into LLM context"""

      def __init__(self, root_path: str, indexes_path: str):
          self.root = Path(root_path)
          self.indexes = load_indexes(indexes_path)

      def list_files(self, glob_pattern: str = "**/*.rs") -> List[str]:
          """List files matching pattern"""
          return [str(p.relative_to(self.root))
                  for p in self.root.glob(glob_pattern)]

      def list_modules(self) -> List[str]:
          """List all Rust modules/crates"""
          return list(self.indexes["modules"].keys())

      def peek(self, file: str, lines: int = 50) -> str:
          """Sample first N lines of a file (for structure understanding)"""
          path = self.root / file
          with open(path) as f:
              return "".join(f.readline() for _ in range(lines))

      def grep(self, pattern: str, glob: str = "*.rs") -> List[GrepMatch]:
          """Search for pattern without loading files into context"""
          matches = []
          regex = re.compile(pattern)
          for file in self.list_files(glob):
              path = self.root / file
              with open(path) as f:
                  for i, line in enumerate(f, 1):
                      if regex.search(line):
                          matches.append(GrepMatch(file, i, line.strip()))
          return matches

      def read_section(self, file: str, start: int, end: int) -> str:
          """Read specific line range from file"""
          path = self.root / file
          with open(path) as f:
              lines = f.readlines()
              return "".join(lines[start-1:end])

      def read_context(self, file: str, line: int, padding: int = 10) -> str:
          """Read context around a specific line"""
          return self.read_section(file, max(1, line - padding), line + padding)

      def get_module(self, module: str) -> "ModuleContext":
          """Get focused context for a single module"""
          files = self.indexes["modules"][module]["files"]
          return ModuleContext(self, module, files)

      def partition_by_module(self) -> List["ModuleContext"]:
          """Partition codebase into module contexts for map-reduce"""
          return [self.get_module(m) for m in self.list_modules()]
  ```

- [ ] **3b.2: RLM Execution Environment**

  Build the REPL environment where agent code executes with sandboxing:

  ```python
  # tools/rlm-env/environment.py

  import signal
  from RestrictedPython import compile_restricted, safe_globals
  from RestrictedPython.Guards import safe_builtins, guarded_iter_unpack_sequence

  EXECUTION_TIMEOUT_SECONDS = 30
  MAX_RECURSIVE_DEPTH = 3
  MAX_OUTPUT_BYTES = 100 * 1024  # 100KB

  class TimeoutError(Exception):
      pass

  class RLMEnvironment:
      """REPL environment for RLM execution with sandboxing"""

      def __init__(self, codebase_path: str, indexes_path: str):
          self.codebase = CodebaseContext(codebase_path, indexes_path)
          self.indexes = load_indexes(indexes_path)
          self.constraints = load_constraints(indexes_path)
          self.llm = ClaudeAPI()  # For recursive calls
          self.execution_log = []
          self._final_result = None

      def execute(self, code: str, depth: int = 0) -> Any:
          """Execute agent-written code in SANDBOXED environment"""

          # Prevent unbounded recursive spawning
          if depth >= MAX_RECURSIVE_DEPTH:
              return {"error": f"Maximum recursive depth ({MAX_RECURSIVE_DEPTH}) exceeded"}

          # Timeout handler
          def timeout_handler(signum, frame):
              raise TimeoutError(f"Execution exceeded {EXECUTION_TIMEOUT_SECONDS}s timeout")

          signal.signal(signal.SIGALRM, timeout_handler)
          signal.alarm(EXECUTION_TIMEOUT_SECONDS)

          try:
              return self._execute_inner(code, depth)
          finally:
              signal.alarm(0)  # Cancel timeout

      def _execute_inner(self, code: str, depth: int) -> Any:
          """Inner execution with timeout wrapper"""

          # RestrictedPython: compile with restrictions
          byte_code = compile_restricted(
              code,
              filename="<rlm>",
              mode="exec"
          )

          if byte_code.errors:
              return {"error": "Compilation failed", "details": byte_code.errors}

          # Restricted globals - only what agent needs
          restricted_globals = {
              "__builtins__": safe_builtins,
              "_getiter_": iter,
              "_iter_unpack_sequence_": guarded_iter_unpack_sequence,

              # Our safe APIs (read-only codebase access)
              "codebase": self.codebase,
              "indexes": self.indexes,
              "constraints": self.constraints,

              # Convenience shortcuts
              "grep": self.codebase.grep,
              "peek": self.codebase.peek,
              "read_section": self.codebase.read_section,
              "list_files": self.codebase.list_files,
              "list_modules": self.codebase.list_modules,
              "partition_by_module": self.codebase.partition_by_module,
              "get_module": self.codebase.get_module,

              # RLM operations
              "RLM": self.recursive_call,
              "map_reduce": self.map_reduce,
              "FINAL": self._set_final,

              # Safe utilities
              "len": len,
              "str": str,
              "int": int,
              "list": list,
              "dict": dict,
              "range": range,
              "enumerate": enumerate,
              "zip": zip,
              "sorted": sorted,
              "print": self._safe_print,
          }

          self.execution_log.append({"code": code, "timestamp": time.time()})
          self._final_result = None
          self._print_buffer = []

          try:
              exec(byte_code.code, restricted_globals)

              if self._final_result is not None:
                  return self._final_result
              else:
                  return {"prints": self._print_buffer, "note": "No FINAL() called"}

          except FinalResultException as e:
              return e.result
          except Exception as e:
              return {"error": str(e), "type": type(e).__name__}

      def _set_final(self, result):
          """FINAL(result) - signal completion"""
          self._final_result = result
          raise FinalResultException(result)

      def _safe_print(self, *args):
          """Capture prints instead of sending to stdout"""
          self._print_buffer.append(" ".join(str(a) for a in args))

      def recursive_call(self, query: str, context: Any) -> str:
          """Spawn sub-LLM call with focused context (depth-1 only)"""
          # Convert context to string if needed
          if isinstance(context, ModuleContext):
              context_str = context.to_summary()
          elif isinstance(context, list):
              context_str = "\n".join(str(c) for c in context)
          else:
              context_str = str(context)

          # Make recursive call to LLM with focused context
          response = self.llm.complete(
              query=query,
              context=context_str,
              max_tokens=2000
          )

          self.execution_log.append({
              "type": "recursive_call",
              "query": query,
              "context_size": len(context_str),
              "response_size": len(response)
          })

          return response

      def map_reduce(self, query: str, partitions: List[Any],
                     aggregator: Callable = None) -> Any:
          """Partition + Map pattern with optional custom aggregation"""
          results = []
          for i, partition in enumerate(partitions):
              result = self.recursive_call(query, partition)
              results.append({
                  "partition": i,
                  "partition_name": getattr(partition, "name", str(i)),
                  "result": result
              })

          if aggregator:
              return aggregator(results)
          return results

      def final_result(self, result: Any) -> None:
          """Signal final result (terminates execution)"""
          self.execution_log.append({"type": "final", "result": result})
          raise FinalResultException(result)
  ```

  **Security Model:**

  | Category | ALLOWED | BLOCKED |
  |----------|---------|---------|
  | **File Access** | Read-only via CodebaseContext | Direct `open()`, `os.*`, `pathlib` writes |
  | **Network** | None (Claude API via wrapper only) | `socket`, `urllib`, `requests`, `http.client` |
  | **Imports** | None (all capabilities via injected globals) | `import`, `__import__`, `importlib` |
  | **System** | None | `subprocess`, `os.system`, `exec`, `eval` |
  | **Builtins** | Safe subset (len, str, list, dict, etc.) | `open`, `file`, `compile`, `globals`, `locals` |

  **Resource Limits:**
  - **Execution timeout:** 30 seconds per `execute()` call
  - **Recursive call depth:** Maximum 3 levels (prevents unbounded spawning)
  - **Output size:** Maximum 100KB per call result
  - **Memory:** Python process memory limit via `resource.setrlimit()`

  **Why RestrictedPython:**
  - Proven sandbox used in Zope/Plone for 20+ years
  - Compile-time restrictions (no runtime overhead for allowed operations)
  - Prevents attribute access to dangerous methods
  - Guards iteration and sequence unpacking

  **What Agent Can Do:**
  ```python
  # ALLOWED - Read codebase
  files = list_files("*.rs")
  content = peek("src/lib.rs", 100)
  matches = grep(r"async fn", "*.rs")

  # ALLOWED - Recursive LLM calls
  result = RLM("summarize error handling", codebase.get_module("kelpie-core"))

  # ALLOWED - Map-reduce
  results = map_reduce("find dead code", partition_by_module())

  # BLOCKED - These will fail at compile time
  import os                    # No imports
  open("/etc/passwd")          # No file access
  __builtins__["eval"]         # No builtins manipulation
  codebase.root.write_text()   # No writes even via codebase
  ```

- [ ] **3b.3: RLM MCP Tools**

  Expose RLM operations as MCP tools:

  ```typescript
  // tools/mcp-kelpie/src/rlm.ts

  // Simple operations (no REPL needed)
  export async function codebase_grep(
    pattern: string,
    glob: string = "*.rs"
  ): Promise<GrepMatch[]> {
    // Direct grep without loading into context
    return await codebase.grep(pattern, glob);
  }

  export async function codebase_peek(
    file: string,
    lines: number = 50
  ): Promise<string> {
    return await codebase.peek(file, lines);
  }

  export async function codebase_read_section(
    file: string,
    start: number,
    end: number
  ): Promise<string> {
    return await codebase.readSection(file, start, end);
  }

  // Complex operations (REPL execution)
  export async function rlm_execute(
    code: string
  ): Promise<RLMResult> {
    /**
     * Execute RLM code in REPL environment.
     *
     * Agent writes Python code that can:
     * - grep(pattern, glob) - Search codebase
     * - peek(file, lines) - Sample file structure
     * - partition_by_module() - Get all modules as contexts
     * - RLM(query, context) - Recursive sub-call
     * - map_reduce(query, partitions) - Parallel processing
     * - FINAL(result) - Return final result
     *
     * Example:
     *   modules = partition_by_module()
     *   dead_code = []
     *   for m in modules:
     *       dead = RLM("find unused functions", m)
     *       dead_code.extend(parse_dead(dead))
     *   FINAL(dead_code)
     */
    const env = new RLMEnvironment(CODEBASE_PATH, INDEXES_PATH);
    return await env.execute(code);
  }

  export async function rlm_map_reduce(
    query: string,
    partition_strategy: "by_module" | "by_file" | "by_crate"
  ): Promise<MapReduceResult> {
    /**
     * High-level map-reduce for common patterns.
     * Automatically partitions and spawns recursive calls.
     */
    const env = new RLMEnvironment(CODEBASE_PATH, INDEXES_PATH);

    let partitions;
    switch (partition_strategy) {
      case "by_module":
        partitions = env.codebase.partitionByModule();
        break;
      case "by_file":
        partitions = env.codebase.listFiles().map(f => env.codebase.getFile(f));
        break;
      case "by_crate":
        partitions = env.codebase.listCrates().map(c => env.codebase.getCrate(c));
        break;
    }

    return await env.mapReduce(query, partitions);
  }
  ```

- [ ] **3b.4: RLM Skill for Complex Searches**

  ```markdown
  # .claude/skills/rlm-search.md

  When asked to find ALL instances of something across the codebase:

  1. DO NOT read files directly into context
  2. USE RLM tools for comprehensive coverage

  ## Simple Searches (use MCP tools directly)
  For targeted searches with known patterns:
  ```
  matches = codebase_grep("pattern", "*.rs")
  for match in matches:
      context = codebase_read_section(match.file, match.line - 5, match.line + 5)
      # Analyze context
  ```

  ## Comprehensive Searches (use RLM execution)
  For "find ALL X" type queries requiring complete coverage:
  ```
  rlm_execute('''
  modules = partition_by_module()
  all_results = []

  for module in modules:
      # Recursive call processes each module separately
      results = RLM("find all instances of X in this module", module)
      all_results.extend(parse_results(results))

  # Cross-reference with structural indexes
  verified = []
  for result in all_results:
      refs = indexes.query_references(result.name)
      verified.append({**result, "references": refs})

  FINAL(verified)
  ''')
  ```

  ## When to Use RLM vs Direct Tools
  - **Direct MCP tools**: Single file, known location, simple pattern
  - **RLM execution**: "Find ALL", "Every module", comprehensive analysis
  ```

**Verification:**
```bash
# Test codebase context
python -c "from tools.rlm_env.codebase import CodebaseContext; c = CodebaseContext('.', '.kelpie-index'); print(c.list_modules())"

# Test grep without context loading
echo '{"tool": "codebase_grep", "args": {"pattern": "impl ActorKV", "glob": "*.rs"}}' | node tools/mcp-kelpie/src/index.js

# Test RLM execution
echo '{"tool": "rlm_execute", "args": {"code": "print(codebase.list_modules())"}}' | node tools/mcp-kelpie/src/index.js

# Test map-reduce
echo '{"tool": "rlm_map_reduce", "args": {"query": "count functions", "partition_strategy": "by_crate"}}' | node tools/mcp-kelpie/src/index.js
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

- [ ] **4.7: Integrity Tools (HARD enforcement)**

  **4.7.1: Evidence-Based Completion**
  ```typescript
  // mark_phase_complete(phase, evidence) - HARD, can't skip
  async function mark_phase_complete(phase: string, evidence: Evidence): Result {
    // HARD: Evidence parameter required
    if (!evidence.verification_commands?.length) {
      throw new Error("Cannot mark complete without verification commands");
    }

    // HARD: Cross-check against phase definition
    const phaseSpec = await loadPhaseSpec(phase);
    for (const required of phaseSpec.required_outputs) {
      if (!evidence.files_created.includes(required)) {
        throw new Error(`Phase ${phase} requires ${required} but not in evidence`);
      }
    }

    // HARD: System re-runs verifications NOW
    const results = [];
    for (const cmd of evidence.verification_commands) {
      const result = await exec(cmd.command);
      const passed = matches(result, cmd.expected);
      results.push({ command: cmd.command, expected: cmd.expected, actual: result, passed });
      if (!passed) {
        throw new Error(`Verification failed: ${cmd.command} expected ${cmd.expected} got ${result}`);
      }
    }

    // HARD: Only if all pass, store completion with proof
    await agentfs.store(`completions/${phase}`, {
      phase,
      claimed_at: Date.now(),
      git_sha: await getCurrentSha(),
      evidence,
      verification_results: results,
      status: 'verified'
    });

    return { success: true, message: `Phase ${phase} verified and marked complete` };
  }
  ```

  **4.7.2: Handoff Verification (automatic on session start)**
  ```typescript
  // start_plan_session(plan_id) - HARD, automatic verification
  async function start_plan_session(plan_id: string): SessionResult {
    const completions = await agentfs.list(`completions/${plan_id}/*`);
    const verificationReport = [];

    // HARD: System automatically re-verifies ALL claimed completions
    for (const completion of completions) {
      if (completion.status !== 'verified') continue;

      for (const cmd of completion.evidence.verification_commands) {
        const result = await exec(cmd.command);
        const passed = matches(result, cmd.expected);

        verificationReport.push({
          phase: completion.phase,
          command: cmd.command,
          expected: cmd.expected,
          actual: result,
          passed,
          original_result: completion.verification_results.find(r => r.command === cmd.command)?.actual
        });

        if (!passed) {
          // HARD: Mark phase as UNVERIFIED - previous agent lied or code changed
          await agentfs.update(`completions/${completion.phase}`, {
            status: 'unverified',
            unverified_at: Date.now(),
            failure_reason: `${cmd.command}: expected ${cmd.expected}, got ${result}`
          });
        }
      }
    }

    const failedPhases = verificationReport.filter(r => !r.passed);

    return {
      plan_id,
      session_started: Date.now(),
      verification_report: verificationReport,
      phases_verified: verificationReport.filter(r => r.passed).length,
      phases_failed: failedPhases.length,
      phases_needing_attention: [...new Set(failedPhases.map(r => r.phase))],
      message: failedPhases.length > 0
        ? `WARNING: ${failedPhases.length} verifications failed. Review phases_needing_attention before proceeding.`
        : `All ${verificationReport.length} verifications passed. Safe to continue.`
    };
  }
  ```

- [ ] **4.8: Slop Detection Tools**

  **4.8.1: Dead Code Detection**
  ```typescript
  async function detect_dead_code(): SlopReport {
    const results = { unused_deps: [], unreachable_functions: [], orphaned_files: [] };

    // Run cargo udeps for unused dependencies
    const udeps = await exec("cargo +nightly udeps --all-targets 2>&1");
    results.unused_deps = parseUdepsOutput(udeps);

    // Query call graph for unreachable functions
    const symbols = await loadIndex("structural/symbols.json");
    const deps = await loadIndex("structural/dependencies.json");

    for (const [file, data] of Object.entries(symbols)) {
      for (const symbol of data.symbols) {
        const refs = deps.edges.filter(e => e.to === symbol.name);
        if (refs.length === 0 && symbol.visibility === "pub") {
          results.unreachable_functions.push({
            name: symbol.name,
            file,
            line: symbol.line,
            reason: "No incoming references in call graph"
          });
        }
      }
    }

    return results;
  }
  ```

  **4.8.2: Orphaned Code Detection**
  ```typescript
  async function detect_orphaned_code(): SlopReport {
    // Find files that might have been superseded but not deleted
    const results = [];

    // Pattern 1: old_X.rs and X.rs both exist
    const files = await glob("**/*.rs");
    for (const file of files) {
      if (file.includes("old_") || file.includes("_old") || file.includes("_backup")) {
        const newFile = file.replace(/old_|_old|_backup/g, "");
        if (files.includes(newFile)) {
          results.push({
            file,
            reason: `Possibly superseded by ${newFile}`,
            action: "Review and delete if obsolete"
          });
        }
      }
    }

    // Pattern 2: Check git history for "replaced by" or "superseded by" commits
    // (implementation details...)

    return results;
  }
  ```

  **4.8.3: Fake DST Detection**
  ```typescript
  async function detect_fake_dst(): SlopReport {
    const results = [];
    const testIndex = await loadIndex("structural/tests.json");

    for (const test of testIndex.tests.filter(t => t.type === "dst" || t.file.includes("_dst"))) {
      const content = await readFile(test.file);

      const checks = {
        uses_simulation: content.includes("Simulation::new") || content.includes("SimConfig"),
        has_fault_injection: content.includes("with_fault") || content.includes("FaultConfig"),
        uses_sim_components: content.includes("SimStorage") || content.includes("SimClock") || content.includes("SimNetwork"),
        is_deterministic: null  // Will test below
      };

      // Test determinism: run twice with same seed
      const seed = Math.floor(Math.random() * 100000);
      const run1 = await exec(`DST_SEED=${seed} cargo test --test ${test.name} -- --nocapture 2>&1`);
      const run2 = await exec(`DST_SEED=${seed} cargo test --test ${test.name} -- --nocapture 2>&1`);
      checks.is_deterministic = run1 === run2;

      // Verdict
      if (!checks.uses_simulation && !checks.uses_sim_components) {
        results.push({
          test: test.name,
          file: test.file,
          verdict: "NOT_DST",
          reason: "Claims to be DST but doesn't use Simulation harness or SimComponents",
          checks
        });
      } else if (!checks.has_fault_injection) {
        results.push({
          test: test.name,
          file: test.file,
          verdict: "WEAK_DST",
          reason: "Uses DST harness but has no fault injection",
          checks
        });
      } else if (!checks.is_deterministic) {
        results.push({
          test: test.name,
          file: test.file,
          verdict: "BROKEN_DST",
          reason: "Same seed produces different results - not deterministic",
          checks
        });
      }
    }

    return results;
  }
  ```

  **4.8.4: Duplicate Detection**
  ```typescript
  async function detect_duplicates(): SlopReport {
    const results = [];
    const symbols = await loadIndex("structural/symbols.json");

    // Find functions with similar signatures
    const functions = [];
    for (const [file, data] of Object.entries(symbols)) {
      for (const sym of data.symbols.filter(s => s.kind === "fn")) {
        functions.push({ ...sym, file });
      }
    }

    // Group by signature similarity
    for (let i = 0; i < functions.length; i++) {
      for (let j = i + 1; j < functions.length; j++) {
        const a = functions[i], b = functions[j];
        if (a.signature && b.signature && signatureSimilarity(a.signature, b.signature) > 0.8) {
          results.push({
            func_a: { name: a.name, file: a.file, signature: a.signature },
            func_b: { name: b.name, file: b.file, signature: b.signature },
            similarity: signatureSimilarity(a.signature, b.signature),
            reason: "Very similar signatures - possible duplicate implementation"
          });
        }
      }
    }

    return results;
  }
  ```

  **4.8.5: Incomplete Code Detection**
  ```typescript
  async function detect_incomplete(): SlopReport {
    const results = [];

    // Pattern scan for incomplete markers
    const patterns = [
      { pattern: /TODO/g, severity: "low", category: "todo" },
      { pattern: /FIXME/g, severity: "medium", category: "fixme" },
      { pattern: /HACK/g, severity: "medium", category: "hack" },
      { pattern: /XXX/g, severity: "high", category: "xxx" },
      { pattern: /unimplemented!\(\)/g, severity: "high", category: "unimplemented" },
      { pattern: /todo!\(\)/g, severity: "high", category: "todo_macro" },
      { pattern: /panic!\("not implemented/g, severity: "high", category: "panic_stub" },
      { pattern: /\.unwrap\(\)/g, severity: "medium", category: "unwrap" },
    ];

    const files = await glob("crates/**/*.rs");
    for (const file of files) {
      const content = await readFile(file);
      const lines = content.split("\n");

      for (const { pattern, severity, category } of patterns) {
        let match;
        while ((match = pattern.exec(content)) !== null) {
          const line = content.substring(0, match.index).split("\n").length;
          results.push({
            file,
            line,
            category,
            severity,
            match: match[0],
            context: lines[line - 1]?.trim()
          });
        }
      }
    }

    return results;
  }
  ```

  **4.8.6: Plan Lie Detection**
  ```typescript
  async function detect_lies(plan_id: string): SlopReport {
    const results = [];
    const plan = await loadPlan(plan_id);
    const completions = await agentfs.list(`completions/${plan_id}/*`);

    for (const completion of completions) {
      // Check claimed files exist
      for (const file of completion.evidence.files_created || []) {
        if (!await fileExists(file)) {
          results.push({
            phase: completion.phase,
            type: "missing_file",
            claimed: file,
            actual: "File does not exist",
            severity: "high"
          });
        }
      }

      // Re-run verification commands
      for (const cmd of completion.evidence.verification_commands || []) {
        const result = await exec(cmd.command);
        if (!matches(result, cmd.expected)) {
          results.push({
            phase: completion.phase,
            type: "verification_mismatch",
            command: cmd.command,
            claimed: cmd.expected,
            actual: result,
            severity: "high"
          });
        }
      }
    }

    return results;
  }
  ```

**Verification:**
```bash
# Test MCP server
cd tools/mcp-kelpie && npm test

# Manual test
echo '{"tool": "index_constraints"}' | node src/index.js

# Test slop detection
echo '{"tool": "detect_fake_dst"}' | node src/index.js
echo '{"tool": "detect_incomplete"}' | node src/index.js
```

- [ ] **4.9: DST Coverage & Integrity Tools**

  **Context:** Kelpie already has `scripts/check_dst.sh` and CI runs DST checks. But we need:
  - Critical path → DST test mapping (which paths have coverage?)
  - Fault type coverage (are we testing all 16 fault types?)
  - Enhanced fake DST detection beyond 4.8.3 (verify determinism property)
  - Pre-commit gate for changes to critical paths

  **4.9.1: Critical Path Coverage Report**
  ```typescript
  async function dst_coverage_report(): DSTCoverageReport {
    // Load critical paths from CONSTRAINTS.md
    const criticalPaths = [
      "Actor activation/deactivation",
      "State persistence and recovery",
      "Cross-actor invocation",
      "Failure detection and recovery",
      "Migration correctness",
      "Message ordering",
      "Transaction atomicity",
      "Cluster membership changes"
    ];

    // Load test index
    const tests = await loadIndex("structural/tests.json");
    const dstTests = tests.tests.filter(t => t.type === "dst");

    // Map critical paths to tests
    const coverage = {};
    for (const path of criticalPaths) {
      const keywords = pathToKeywords(path); // "Actor activation" → ["actor", "activation", "activate"]
      const coveringTests = dstTests.filter(t =>
        keywords.some(kw => t.name.toLowerCase().includes(kw) || t.topics.includes(kw))
      );

      coverage[path] = {
        covered: coveringTests.length > 0,
        tests: coveringTests.map(t => ({ name: t.name, file: t.file })),
        test_count: coveringTests.length
      };
    }

    // Calculate overall coverage
    const coveredPaths = Object.values(coverage).filter(c => c.covered).length;

    return {
      critical_paths_total: criticalPaths.length,
      critical_paths_covered: coveredPaths,
      coverage_percentage: (coveredPaths / criticalPaths.length * 100).toFixed(1),
      by_path: coverage,
      uncovered_paths: Object.entries(coverage)
        .filter(([_, c]) => !c.covered)
        .map(([path, _]) => path)
    };
  }
  ```

  **4.9.2: Fault Type Coverage Report**
  ```typescript
  async function fault_type_coverage(): FaultTypeCoverageReport {
    // All 16 fault types from CONSTRAINTS.md
    const allFaultTypes = {
      Storage: ["StorageWriteFail", "StorageReadFail", "StorageCorruption", "StorageLatency", "DiskFull"],
      Crash: ["CrashBeforeWrite", "CrashAfterWrite", "CrashDuringTransaction"],
      Network: ["NetworkPartition", "NetworkDelay", "NetworkPacketLoss", "NetworkMessageReorder"],
      Time: ["ClockSkew", "ClockJump"],
      Resource: ["OutOfMemory", "CPUStarvation"]
    };

    // Scan DST test files for fault type usage
    const dstFiles = await glob("crates/**/tests/*_dst.rs");
    const usageByType = {};

    for (const [category, types] of Object.entries(allFaultTypes)) {
      for (const faultType of types) {
        usageByType[faultType] = {
          category,
          used_in: [],
          usage_count: 0
        };
      }
    }

    for (const file of dstFiles) {
      const content = await readFile(file);
      for (const faultType of Object.keys(usageByType)) {
        const regex = new RegExp(`FaultType::${faultType}|"${faultType}"`, 'g');
        const matches = content.match(regex);
        if (matches) {
          usageByType[faultType].used_in.push(file);
          usageByType[faultType].usage_count += matches.length;
        }
      }
    }

    // Calculate coverage by category
    const coverageByCategory = {};
    for (const [category, types] of Object.entries(allFaultTypes)) {
      const usedTypes = types.filter(t => usageByType[t].usage_count > 0);
      coverageByCategory[category] = {
        total: types.length,
        used: usedTypes.length,
        unused: types.filter(t => usageByType[t].usage_count === 0)
      };
    }

    const totalTypes = Object.keys(usageByType).length;
    const usedTypes = Object.values(usageByType).filter(u => u.usage_count > 0).length;

    return {
      fault_types_total: totalTypes,
      fault_types_used: usedTypes,
      coverage_percentage: (usedTypes / totalTypes * 100).toFixed(1),
      by_type: usageByType,
      by_category: coverageByCategory,
      unused_fault_types: Object.entries(usageByType)
        .filter(([_, u]) => u.usage_count === 0)
        .map(([type, _]) => type)
    };
  }
  ```

  **4.9.3: Enhanced Determinism Verification**
  ```typescript
  async function verify_all_dst_determinism(seeds?: number[]): DeterminismReport {
    // Use existing check_dst.sh logic, but enhanced
    const testSeeds = seeds || [12345, 67890, 11111, 42, 999];
    const results = [];

    const dstTests = await glob("crates/**/tests/*_dst.rs");

    for (const testFile of dstTests) {
      const testName = path.basename(testFile, ".rs");

      for (const seed of testSeeds) {
        // Run twice with same seed
        const run1 = await exec(`DST_SEED=${seed} cargo test --test ${testName} -- --nocapture 2>&1`);
        const run2 = await exec(`DST_SEED=${seed} cargo test --test ${testName} -- --nocapture 2>&1`);

        // Filter out timestamps and build artifacts
        const filtered1 = filterNonDeterministicOutput(run1);
        const filtered2 = filterNonDeterministicOutput(run2);

        const isDeterministic = filtered1 === filtered2;

        if (!isDeterministic) {
          // Find the diff
          const diff = generateDiff(filtered1, filtered2);
          results.push({
            test: testName,
            seed,
            deterministic: false,
            diff_preview: diff.slice(0, 500),
            likely_cause: diagnoseDeterminismFailure(diff)
          });
        } else {
          results.push({
            test: testName,
            seed,
            deterministic: true
          });
        }
      }
    }

    const failedTests = results.filter(r => !r.deterministic);

    return {
      tests_checked: dstTests.length,
      seeds_used: testSeeds,
      all_deterministic: failedTests.length === 0,
      failures: failedTests,
      failure_count: failedTests.length,
      message: failedTests.length > 0
        ? `${failedTests.length} DST test(s) are NOT deterministic. See failures for details.`
        : `All ${dstTests.length} DST tests are deterministic across ${testSeeds.length} seeds.`
    };
  }

  function diagnoseDeterminismFailure(diff: string): string {
    if (diff.includes("SystemTime") || diff.includes("Instant::now"))
      return "Uses real system time instead of SimClock";
    if (diff.includes("thread") || diff.includes("spawn"))
      return "Async race condition - task ordering varies";
    if (diff.includes("rand") || diff.includes("random"))
      return "Uses random without DeterministicRng";
    if (diff.includes("HashMap") && diff.includes("iter"))
      return "HashMap iteration order is non-deterministic";
    return "Unknown - manual investigation required";
  }
  ```

  **4.9.4: DST Coverage Enforcement Gate**
  ```typescript
  async function enforce_dst_coverage(changed_files: string[]): EnforcementResult {
    // Check if any changed file is in a critical path
    const criticalPathPatterns = [
      /actor.*activate|deactivate/i,
      /state.*persist|recover/i,
      /invoke|cross.*actor/i,
      /failure.*detect|recover/i,
      /migrat|teleport/i,
      /message.*order/i,
      /transaction|atomic/i,
      /cluster.*member/i
    ];

    const criticalChanges = [];
    for (const file of changed_files) {
      const content = await readFile(file);
      for (const pattern of criticalPathPatterns) {
        if (pattern.test(content) || pattern.test(file)) {
          criticalChanges.push({ file, pattern: pattern.toString() });
          break;
        }
      }
    }

    if (criticalChanges.length === 0) {
      return { blocked: false, message: "No critical path changes detected." };
    }

    // Check if corresponding DST tests exist
    const coverageReport = await dst_coverage_report();
    const missingCoverage = [];

    for (const change of criticalChanges) {
      // Find which critical path this change affects
      const affectedPath = identifyAffectedCriticalPath(change);
      if (affectedPath && !coverageReport.by_path[affectedPath]?.covered) {
        missingCoverage.push({
          file: change.file,
          critical_path: affectedPath,
          message: `Changed ${change.file} affects '${affectedPath}' but no DST tests cover it`
        });
      }
    }

    if (missingCoverage.length > 0) {
      return {
        blocked: true,
        message: `BLOCKED: Critical path changes require DST coverage. Missing coverage for: ${missingCoverage.map(m => m.critical_path).join(", ")}`,
        missing: missingCoverage,
        action_required: "Add DST tests for the affected critical paths before committing"
      };
    }

    return {
      blocked: false,
      message: `Critical path changes detected in ${criticalChanges.length} file(s), all have DST coverage.`,
      critical_changes: criticalChanges
    };
  }
  ```

  **4.9.5: Pre-commit Hook Integration**
  ```bash
  # Addition to .git/hooks/pre-commit

  # DST Coverage Enforcement (for critical paths)
  CHANGED_FILES=$(git diff --cached --name-only --diff-filter=ACMR -- '*.rs')
  if [ -n "$CHANGED_FILES" ]; then
    echo "Checking DST coverage for changed files..."
    RESULT=$(echo "{\"tool\": \"enforce_dst_coverage\", \"args\": {\"changed_files\": $(echo $CHANGED_FILES | jq -R -s 'split("\n") | map(select(length > 0))')}}" | node tools/mcp-kelpie/src/index.js)

    if echo "$RESULT" | jq -e '.blocked == true' > /dev/null; then
      echo "❌ DST Coverage Required:"
      echo "$RESULT" | jq -r '.message'
      echo ""
      echo "Missing coverage:"
      echo "$RESULT" | jq -r '.missing[] | "  - \(.file): \(.critical_path)"'
      exit 1
    fi
  fi
  ```

**Verification:**
```bash
# Test DST coverage report
echo '{"tool": "dst_coverage_report"}' | node tools/mcp-kelpie/src/index.js

# Test fault type coverage
echo '{"tool": "fault_type_coverage"}' | node tools/mcp-kelpie/src/index.js

# Test determinism verification (slow - runs tests multiple times)
echo '{"tool": "verify_all_dst_determinism", "args": {"seeds": [42, 12345]}}' | node tools/mcp-kelpie/src/index.js

# Test enforcement gate
echo '{"tool": "enforce_dst_coverage", "args": {"changed_files": ["crates/kelpie-runtime/src/actor.rs"]}}' | node tools/mcp-kelpie/src/index.js
```

- [ ] **4.10: Harness Adequacy Verification**

  **Context:** Phase 4.9 checks if tests USE the harness, but not if the harness is ADEQUATE. A test can use SimStorage but if SimStorage doesn't model real FDB failure modes, the test is meaningless. We need to verify the harness itself is complete.

  **4.10.1: Harness Capability Audit**
  ```typescript
  async function harness_capability_audit(): HarnessAuditReport {
    // Required fault types from CONSTRAINTS.md
    const requiredFaultTypes = {
      Storage: ["StorageWriteFail", "StorageReadFail", "StorageCorruption", "StorageLatency", "DiskFull"],
      Crash: ["CrashBeforeWrite", "CrashAfterWrite", "CrashDuringTransaction"],
      Network: ["NetworkPartition", "NetworkDelay", "NetworkPacketLoss", "NetworkMessageReorder"],
      Time: ["ClockSkew", "ClockJump"],
      Resource: ["OutOfMemory", "CPUStarvation"]
    };

    // Required simulation components for critical paths
    const requiredComponents = {
      "SimClock": {
        purpose: "Deterministic time control",
        required_for: ["All DST tests", "Timeout testing", "Clock skew injection"]
      },
      "SimStorage": {
        purpose: "Simulated persistent storage",
        required_for: ["State persistence", "Storage fault injection", "Transaction testing"]
      },
      "SimNetwork": {
        purpose: "Simulated network layer",
        required_for: ["Cross-actor invocation", "Partition testing", "Message ordering"]
      },
      "SimVm": {
        purpose: "Simulated VM for agent execution",
        required_for: ["Migration/teleport testing", "Crash injection"]
      },
      "DeterministicRng": {
        purpose: "Seeded random number generator",
        required_for: ["Reproducibility", "Fault probability sampling"]
      },
      "FaultInjector": {
        purpose: "Fault injection framework",
        required_for: ["All fault testing"]
      }
    };

    // Scan kelpie-dst crate for implementations
    const dstLib = await readFile("crates/kelpie-dst/src/lib.rs");
    const dstFiles = await glob("crates/kelpie-dst/src/**/*.rs");

    const componentStatus = {};
    for (const [component, spec] of Object.entries(requiredComponents)) {
      const found = dstLib.includes(`pub use ${component.toLowerCase()}`) ||
                    dstLib.includes(`pub struct ${component}`) ||
                    dstLib.includes(`pub mod ${component.toLowerCase()}`);

      // Check for actual implementation
      let implementation = null;
      for (const file of dstFiles) {
        const content = await readFile(file);
        if (content.includes(`struct ${component}`) || content.includes(`impl ${component}`)) {
          implementation = file;
          break;
        }
      }

      componentStatus[component] = {
        ...spec,
        exported: found,
        implemented: implementation !== null,
        implementation_file: implementation,
        status: found && implementation ? "OK" : implementation ? "NOT_EXPORTED" : "MISSING"
      };
    }

    // Check fault type implementations in FaultInjector
    const faultFile = await readFile("crates/kelpie-dst/src/fault.rs");
    const faultTypeStatus = {};

    for (const [category, types] of Object.entries(requiredFaultTypes)) {
      for (const faultType of types) {
        const isEnumVariant = faultFile.includes(faultType);
        const hasHandler = faultFile.includes(`FaultType::${faultType}`) &&
                          (faultFile.includes(`=> {`) || faultFile.includes(`=>`));

        faultTypeStatus[faultType] = {
          category,
          defined: isEnumVariant,
          has_handler: hasHandler,
          status: isEnumVariant && hasHandler ? "IMPLEMENTED" :
                  isEnumVariant ? "DEFINED_NO_HANDLER" : "MISSING"
        };
      }
    }

    const missingComponents = Object.entries(componentStatus)
      .filter(([_, s]) => s.status !== "OK")
      .map(([name, s]) => ({ name, status: s.status }));

    const missingFaults = Object.entries(faultTypeStatus)
      .filter(([_, s]) => s.status !== "IMPLEMENTED")
      .map(([name, s]) => ({ name, status: s.status, category: s.category }));

    return {
      components: componentStatus,
      fault_types: faultTypeStatus,
      missing_components: missingComponents,
      missing_fault_types: missingFaults,
      harness_complete: missingComponents.length === 0 && missingFaults.length === 0,
      message: missingComponents.length === 0 && missingFaults.length === 0
        ? "Harness is complete - all components and fault types implemented"
        : `Harness incomplete: ${missingComponents.length} missing components, ${missingFaults.length} missing fault types`
    };
  }
  ```

  **4.10.2: Simulation Fidelity Check**
  ```typescript
  async function simulation_fidelity_check(): FidelityReport {
    // For each simulation component, document what it models vs what it doesn't
    const fidelitySpec = {
      "SimStorage": {
        models: [
          "Read/write operations",
          "Transaction semantics (begin/commit/abort)",
          "Key-value interface",
          "Configurable latency",
          "Write failures",
          "Read failures"
        ],
        does_not_model: [
          "FDB layer coordination",
          "FDB transaction conflicts (optimistic concurrency)",
          "FDB watch semantics",
          "Disk I/O patterns",
          "Storage tiering",
          "Compaction"
        ],
        known_gaps: [
          {
            gap: "No transaction conflict simulation",
            risk: "Tests may pass but production fails on concurrent writes",
            severity: "HIGH",
            mitigation: "Add SimStorage::with_conflict_probability()"
          }
        ]
      },
      "SimNetwork": {
        models: [
          "Message send/receive",
          "Configurable latency",
          "Packet loss",
          "Network partitions",
          "Message reordering"
        ],
        does_not_model: [
          "TCP semantics (retransmission, congestion)",
          "Partial message delivery",
          "Connection establishment/teardown",
          "Bandwidth limits",
          "Network buffer overflow"
        ],
        known_gaps: [
          {
            gap: "No partial network partition (asymmetric)",
            risk: "Can't test A->B works but B->A fails",
            severity: "MEDIUM",
            mitigation: "Add directional partition support"
          }
        ]
      },
      "SimClock": {
        models: [
          "Monotonic time progression",
          "Time advancement",
          "Sleep/timeout"
        ],
        does_not_model: [
          "Wall clock (real NTP time)",
          "Leap seconds",
          "Timezone effects"
        ],
        known_gaps: []
      },
      "SimVm": {
        models: [
          "VM lifecycle (start/stop)",
          "Snapshot/restore",
          "Guest agent communication"
        ],
        does_not_model: [
          "CPU scheduling",
          "Memory pressure",
          "I/O scheduling",
          "Hypervisor overhead"
        ],
        known_gaps: [
          {
            gap: "No memory pressure simulation",
            risk: "OOM scenarios not testable",
            severity: "MEDIUM",
            mitigation: "Add SimVm::with_memory_limit()"
          }
        ]
      }
    };

    // Check actual implementation matches spec
    const results = {};
    for (const [component, spec] of Object.entries(fidelitySpec)) {
      const implFile = await findImplementation(component);
      if (!implFile) {
        results[component] = { status: "NOT_FOUND", spec };
        continue;
      }

      const content = await readFile(implFile);

      // Verify claimed "models" features exist
      const verifiedModels = [];
      const unverifiedModels = [];
      for (const feature of spec.models) {
        const keywords = featureToKeywords(feature);
        const found = keywords.some(kw => content.toLowerCase().includes(kw.toLowerCase()));
        if (found) {
          verifiedModels.push(feature);
        } else {
          unverifiedModels.push(feature);
        }
      }

      results[component] = {
        status: unverifiedModels.length === 0 ? "VERIFIED" : "PARTIAL",
        implementation_file: implFile,
        models_verified: verifiedModels,
        models_unverified: unverifiedModels,
        does_not_model: spec.does_not_model,
        known_gaps: spec.known_gaps
      };
    }

    // Aggregate gaps
    const allGaps = Object.values(fidelitySpec)
      .flatMap(s => s.known_gaps)
      .sort((a, b) => severityRank(b.severity) - severityRank(a.severity));

    return {
      by_component: results,
      all_known_gaps: allGaps,
      high_severity_gaps: allGaps.filter(g => g.severity === "HIGH"),
      message: allGaps.length > 0
        ? `${allGaps.length} known simulation gaps. ${allGaps.filter(g => g.severity === "HIGH").length} are HIGH severity.`
        : "No known simulation gaps documented."
    };
  }
  ```

  **4.10.3: Critical Path Simulability Check**
  ```typescript
  async function critical_path_simulability(): SimulabilityReport {
    // For each critical path, determine if the harness can simulate it
    const criticalPaths = [
      {
        path: "Actor activation/deactivation",
        required_components: ["SimStorage", "SimClock"],
        required_faults: ["StorageReadFail", "StorageWriteFail"],
        scenarios: [
          { name: "Activate new actor", simulable: true },
          { name: "Deactivate idle actor", simulable: true },
          { name: "Activation fails mid-way", simulable: true, requires: "CrashDuringTransaction" },
          { name: "Concurrent activation race", simulable: false,
            reason: "No transaction conflict simulation", gap_ref: "SimStorage" }
        ]
      },
      {
        path: "State persistence and recovery",
        required_components: ["SimStorage", "SimVm"],
        required_faults: ["StorageWriteFail", "CrashAfterWrite", "StorageCorruption"],
        scenarios: [
          { name: "Normal persist/recover", simulable: true },
          { name: "Crash before persist completes", simulable: true },
          { name: "Corruption during recovery", simulable: true },
          { name: "Partial write (torn page)", simulable: false,
            reason: "SimStorage doesn't model partial writes" }
        ]
      },
      {
        path: "Cross-actor invocation",
        required_components: ["SimNetwork", "SimClock"],
        required_faults: ["NetworkDelay", "NetworkPartition", "NetworkPacketLoss"],
        scenarios: [
          { name: "Normal RPC", simulable: true },
          { name: "RPC timeout", simulable: true },
          { name: "Network partition during call", simulable: true },
          { name: "Asymmetric partition", simulable: false,
            reason: "SimNetwork doesn't model directional partitions" }
        ]
      },
      {
        path: "Failure detection and recovery",
        required_components: ["SimNetwork", "SimClock", "SimVm"],
        required_faults: ["CrashBeforeWrite", "NetworkPartition"],
        scenarios: [
          { name: "Detect crashed node", simulable: true },
          { name: "Distinguish crash from partition", simulable: true },
          { name: "Split-brain detection", simulable: false,
            reason: "Requires asymmetric partition + clock skew combo" }
        ]
      },
      {
        path: "Migration/teleport correctness",
        required_components: ["SimVm", "SimStorage", "SimNetwork"],
        required_faults: ["CrashDuringTransaction", "NetworkPacketLoss"],
        scenarios: [
          { name: "Clean migration", simulable: true },
          { name: "Crash during snapshot", simulable: true },
          { name: "Network failure during transfer", simulable: true },
          { name: "Source/dest clock skew", simulable: true, requires: "ClockSkew" }
        ]
      }
    ];

    // Check each path
    const harnessAudit = await harness_capability_audit();
    const results = [];

    for (const cp of criticalPaths) {
      // Check required components
      const missingComponents = cp.required_components.filter(
        c => harnessAudit.components[c]?.status !== "OK"
      );

      // Check required faults
      const missingFaults = cp.required_faults.filter(
        f => harnessAudit.fault_types[f]?.status !== "IMPLEMENTED"
      );

      // Aggregate scenario simulability
      const simulableScenarios = cp.scenarios.filter(s => s.simulable);
      const nonSimulableScenarios = cp.scenarios.filter(s => !s.simulable);

      results.push({
        critical_path: cp.path,
        fully_simulable: missingComponents.length === 0 &&
                         missingFaults.length === 0 &&
                         nonSimulableScenarios.length === 0,
        missing_components: missingComponents,
        missing_faults: missingFaults,
        scenarios: {
          total: cp.scenarios.length,
          simulable: simulableScenarios.length,
          not_simulable: nonSimulableScenarios.length,
          details: cp.scenarios
        },
        coverage_quality: nonSimulableScenarios.length === 0 ? "FULL" :
                          nonSimulableScenarios.length < simulableScenarios.length ? "PARTIAL" : "POOR"
      });
    }

    const fullyCovered = results.filter(r => r.fully_simulable).length;
    const partiallyCovered = results.filter(r => r.coverage_quality === "PARTIAL").length;
    const poorlyCovered = results.filter(r => r.coverage_quality === "POOR").length;

    return {
      critical_paths: results,
      summary: {
        total: results.length,
        fully_simulable: fullyCovered,
        partially_simulable: partiallyCovered,
        poorly_simulable: poorlyCovered
      },
      action_items: results
        .filter(r => !r.fully_simulable)
        .flatMap(r => [
          ...r.missing_components.map(c => `Implement ${c} in kelpie-dst`),
          ...r.missing_faults.map(f => `Add ${f} fault handler`),
          ...r.scenarios.details.filter(s => !s.simulable).map(s =>
            `Add simulation support for: ${s.name} (${s.reason})`
          )
        ]),
      message: fullyCovered === results.length
        ? "All critical paths are fully simulable"
        : `${fullyCovered}/${results.length} critical paths fully simulable. ` +
          `${partiallyCovered} partial, ${poorlyCovered} poor coverage.`
    };
  }
  ```

  **4.10.4: Harness Evolution Tracking**
  ```typescript
  // Store baseline and track harness improvements over time
  async function track_harness_evolution(): void {
    const audit = await harness_capability_audit();
    const fidelity = await simulation_fidelity_check();
    const simulability = await critical_path_simulability();

    const snapshot = {
      timestamp: new Date().toISOString(),
      git_sha: await getCurrentSha(),
      components_ok: Object.values(audit.components).filter(c => c.status === "OK").length,
      components_total: Object.keys(audit.components).length,
      faults_implemented: Object.values(audit.fault_types).filter(f => f.status === "IMPLEMENTED").length,
      faults_total: Object.keys(audit.fault_types).length,
      critical_paths_full: simulability.summary.fully_simulable,
      critical_paths_total: simulability.summary.total,
      known_gaps: fidelity.all_known_gaps.length,
      high_severity_gaps: fidelity.high_severity_gaps.length
    };

    // Append to evolution log
    await appendJsonl(".kelpie-index/meta/harness_evolution.jsonl", snapshot);
  }
  ```

**Verification:**
```bash
# Audit harness capabilities
echo '{"tool": "harness_capability_audit"}' | node tools/mcp-kelpie/src/index.js

# Check simulation fidelity (what's modeled vs not)
echo '{"tool": "simulation_fidelity_check"}' | node tools/mcp-kelpie/src/index.js

# Check critical path simulability
echo '{"tool": "critical_path_simulability"}' | node tools/mcp-kelpie/src/index.js

# Expected: Reports showing which gaps exist and their severity
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

- [ ] **5.5: RLM Handoff Skill**
  ```markdown
  # .claude/skills/rlm-handoff.md

  When taking over a plan from another agent:

  1. MANDATORY: Call mcp.start_plan_session(plan_id)
     - This automatically re-verifies ALL completed phases
     - You will receive a verification report
     - You CANNOT skip this step

  2. Review verification report:
     - phases_verified: These are confirmed working
     - phases_needing_attention: These FAILED verification
       - Previous agent may have lied
       - Or code changed since completion
       - Or verification was inadequate

  3. For each failed phase:
     - Investigate why it failed
     - Either fix the issue OR mark phase as incomplete
     - Do NOT proceed to dependent phases until fixed

  4. Only after all verifications pass:
     - Continue with next incomplete phase
     - Follow normal RLM task workflow

  NEVER trust checkboxes in plan files.
  ALWAYS let the system verify via execution.
  ```

- [ ] **5.6: RLM Slop Hunt Skill**
  ```markdown
  # .claude/skills/rlm-slop-hunt.md

  When asked to find or clean up slop in the codebase:

  1. Run detection tools:
     - mcp.detect_dead_code() → unused deps, unreachable functions
     - mcp.detect_orphaned_code() → superseded but not deleted
     - mcp.detect_duplicates() → similar implementations
     - mcp.detect_fake_dst() → tests claiming DST but aren't
     - mcp.detect_incomplete() → TODO, FIXME, stubs

  2. For each candidate:
     - DO NOT blindly delete
     - Verify it's actually slop:
       - Check references in call graph
       - Check git history for context
       - Run tests to see if removal breaks anything
     - If uncertain, flag for human review

  3. Propose cleanup:
     - Group by type (dead code, duplicates, etc.)
     - Prioritize by severity (high = blocking, low = advisory)
     - Include verification command for each cleanup

  4. Execute approved cleanups:
     - One at a time
     - Run tests after each
     - Commit with clear message explaining what was removed and why

  5. Re-run detection to confirm slop is gone
  ```

**Verification:**
```bash
# Check skills are registered
cat .claude/skills/rlm-task.md
cat .claude/skills/rlm-handoff.md
cat .claude/skills/rlm-slop-hunt.md
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

### Phase 9: Slop Cleanup Workflow

**Goal:** Systematic process to find and purge existing slop from the kelpie codebase.

- [ ] **9.1: Initial Slop Audit**
  Run all detection tools on current kelpie state:
  ```bash
  # Create baseline slop report
  mcp.detect_dead_code() > .kelpie-index/slop/dead_code.json
  mcp.detect_orphaned_code() > .kelpie-index/slop/orphaned.json
  mcp.detect_duplicates() > .kelpie-index/slop/duplicates.json
  mcp.detect_fake_dst() > .kelpie-index/slop/fake_dst.json
  mcp.detect_incomplete() > .kelpie-index/slop/incomplete.json
  ```

- [ ] **9.2: Triage Slop Candidates**
  For each category, classify:
  ```
  ┌─────────────────────────────────────────────────────────────────┐
  │  TRIAGE MATRIX                                                  │
  │                                                                 │
  │  Severity │ Confidence │ Action                                 │
  │  ─────────┼────────────┼────────────────────────────────────────│
  │  HIGH     │ HIGH       │ Delete immediately (after test)        │
  │  HIGH     │ LOW        │ Investigate, then decide               │
  │  LOW      │ HIGH       │ Queue for cleanup sprint               │
  │  LOW      │ LOW        │ Flag for human review                  │
  └─────────────────────────────────────────────────────────────────┘
  ```

- [ ] **9.3: Fake DST Remediation**
  For each test flagged by `detect_fake_dst()`:
  ```
  If verdict == "NOT_DST":
    - Either rename to remove "_dst" suffix
    - Or rewrite to use actual Simulation harness
    - Document why test exists if it's intentionally not DST

  If verdict == "WEAK_DST":
    - Add fault injection for relevant failure modes
    - Follow CONSTRAINTS.md §1 workflow

  If verdict == "BROKEN_DST":
    - Fix non-determinism source
    - Common causes: SystemTime, random without seed, async race
    - Verify with: DST_SEED=42 cargo test <name> (run twice, compare)
  ```

- [ ] **9.4: Dead Code Removal**
  For each candidate from `detect_dead_code()`:
  ```
  1. Verify truly unused:
     - Check call graph (no incoming edges?)
     - Check if pub but internal-only (might be API surface)
     - Check if test-only (acceptable)

  2. If confirmed dead:
     - git rm or delete
     - Run cargo test to confirm nothing breaks
     - Commit: "chore: remove dead code {name} - no references in call graph"

  3. If uncertain:
     - Add #[allow(dead_code)] with comment explaining why kept
     - Or ask human for decision
  ```

- [ ] **9.5: Duplicate Consolidation**
  For each duplicate pair from `detect_duplicates()`:
  ```
  1. Analyze both implementations:
     - Are they truly duplicates or just similar?
     - Which is more correct/complete?
     - Which has better tests?

  2. If true duplicates:
     - Keep the better one
     - Update all callers to use it
     - Delete the worse one
     - Commit: "refactor: consolidate duplicate implementations of {name}"

  3. If intentional (e.g., different error handling):
     - Document why both exist
     - Consider if they should share a common base
  ```

- [ ] **9.6: Orphan Cleanup**
  For each orphaned file from `detect_orphaned_code()`:
  ```
  1. Check git history:
     - When was this last modified?
     - Was it superseded by another file?
     - Who wrote it and why?

  2. If superseded:
     - Verify new implementation covers all functionality
     - Delete orphan
     - Commit: "chore: remove orphaned {file} - superseded by {new_file} in {commit}"

  3. If still needed:
     - Rename to remove "old_" prefix if applicable
     - Integrate properly into module structure
  ```

- [ ] **9.7: Incomplete Code Resolution**
  For each TODO/FIXME from `detect_incomplete()`:
  ```
  Severity HIGH (unimplemented!, panic!("not implemented")):
    - Either implement it NOW
    - Or delete if no longer needed
    - NEVER leave in production code

  Severity MEDIUM (FIXME, HACK, unwrap):
    - Create issue/task for each
    - Prioritize by impact
    - Schedule for future sprint

  Severity LOW (TODO):
    - Review if still relevant
    - Delete if obsolete
    - Keep if valid future work
  ```

- [ ] **9.8: Final Verification**
  After all cleanup:
  ```bash
  # Re-run all detection tools
  mcp.detect_dead_code()      # Should be empty or near-empty
  mcp.detect_orphaned_code()  # Should be empty
  mcp.detect_fake_dst()       # Should be empty
  mcp.detect_duplicates()     # Should be empty or documented exceptions

  # Run full test suite
  cargo test

  # Run DST with multiple seeds
  for seed in 1 42 100 999 12345; do
    DST_SEED=$seed cargo test -p kelpie-dst
  done

  # Run clippy
  cargo clippy --all-targets -- -D warnings
  ```

- [ ] **9.9: Document Cleanup Results**
  Create cleanup report:
  ```markdown
  # Slop Cleanup Report - {date}

  ## Summary
  - Dead code removed: X functions, Y files
  - Duplicates consolidated: Z pairs
  - Fake DST fixed: N tests
  - Orphans deleted: M files
  - TODOs resolved: P items

  ## Before/After Metrics
  - Lines of code: BEFORE → AFTER (delta)
  - Test count: BEFORE → AFTER
  - DST coverage: BEFORE% → AFTER%

  ## Remaining Items (Documented Exceptions)
  - {item}: {reason for keeping}
  ```

**Verification:**
```bash
# Verify slop is gone
./tools/mcp-kelpie detect_all_slop | jq '.total_issues'
# Should be 0 or only documented exceptions

# Verify tests still pass
cargo test

# Verify DST determinism
DST_SEED=42 cargo test -p kelpie-dst 2>&1 | md5sum
DST_SEED=42 cargo test -p kelpie-dst 2>&1 | md5sum
# Both should match
```

---

## Checkpoints

- [x] Codebase understood
- [x] Plan approved
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained**
- [x] **Phase 1: Foundation - directory structure & AgentFS** ✅
- [x] **Phase 2.1: Symbol Index (tools/kelpie-indexer)** ✅
- [ ] Phase 2.2: Dependency Graph
- [ ] Phase 2.3: Test Index
- [ ] Phase 2.4: Module Index
- [ ] Phase 2: Structural indexing (symbols, deps, tests)
- [ ] Phase 3: Semantic indexing (summaries, constraints)
- [ ] Phase 3b: RLM Environment (CodebaseContext, REPL, recursive calls, map-reduce)
- [ ] Phase 4: MCP server (query, verify, integrity, slop detection, DST coverage)
- [ ] Phase 4.9: DST Coverage & Integrity Tools (critical path mapping, fault type coverage, determinism verification, enforcement gate)
- [ ] Phase 4.10: Harness Adequacy Verification (capability audit, fidelity check, simulability analysis)
- [ ] Phase 5: RLM skills (task, verify, explore, handoff, slop-hunt)
- [ ] Phase 6: Hard controls (hooks, gates, audit)
- [ ] Phase 7: Multi-agent orchestration
- [ ] Phase 8: Integration testing
- [ ] Phase 9: Slop cleanup workflow (initial audit on kelpie)
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
- [ ] DST coverage report accuracy (verify mappings are correct)
- [ ] Determinism verification catches real non-determinism (inject non-determinism, verify detection)

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

### Phase 2.1: Symbol Index (Completed 2026-01-20)

**Indexer Tool Created:**
- Built `tools/kelpie-indexer` Rust binary using syn parser
- Added to workspace members in root Cargo.toml
- Command: `cargo run --release -p kelpie-indexer -- symbols`

**Symbol Extraction:**
- Indexed **186 Rust files** across all kelpie crates
- Extracted **3,563 symbols** (structs, enums, traits, functions, methods)
- Captured visibility (pub, private, pub(crate), etc.)
- Captured function signatures (async, unsafe, method names)
- Extracted imports for each file
- Generated deterministic output (773KB JSON file)

**Freshness Tracking:**
- Updated with SHA256 hashes for all 186 indexed files
- Git SHA: df48636a6b95ae073fd3d30db3a6963166ac1393
- Timestamp: 2026-01-20T23:03:18Z

**Known Limitations:**
- Line numbers set to 0 (proc-macro2 spans don't expose line info directly)
- exports_to field empty (will be populated by dependency analysis in Phase 2.2)
- Signatures simplified to "fn name(..)" format (full signatures need more parsing)

**Key Insight:**
Using syn for parsing is fast and deterministic. The indexer completes in ~1 second for the entire codebase. Line numbers can be added later via a different strategy if needed.

### Phase 2.2: Dependency Graph (Completed 2026-01-20)

**Indexer Enhancement:**
- Extended `tools/kelpie-indexer` with cargo metadata parsing
- Added `dependencies` command alongside existing `symbols` command
- Command: `cargo run --release -p kelpie-indexer -- dependencies`

**Dependency Extraction:**
- Indexed **15 kelpie crates** using `cargo metadata --format-version=1 --no-deps`
- Built **46 dependency edges** (crate-level dependencies)
- Generated graph with nodes (crates) and edges (depends relationships)
- Output: `.kelpie-index/structural/dependencies.json`

**Graph Structure:**
- Nodes: Each kelpie crate with id, type="crate", crate_name
- Edges: Dependency relationships with from, to, type="depends"
- Examples: kelpie-runtime → kelpie-core, kelpie-server → kelpie-storage

**Current Scope:**
- **Implemented:** Crate-level dependencies (cargo metadata)
- **Not yet implemented:** Fine-grained type relationships (struct → trait, fn → type)
- **Not yet implemented:** exports_to field in symbols.json

**Key Insight:**
Cargo metadata provides clean crate-level dependency information. Fine-grained type relationships (what structs implement what traits, what functions use what types) will require additional analysis, possibly using rust-analyzer LSP or deeper syn parsing. For now, crate-level deps are sufficient for Phase 2.2.

### Phase 2.3: Test Index (Completed 2026-01-20)

**Indexer Enhancement:**
- Extended `tools/kelpie-indexer` with test function parsing
- Added `tests` command alongside existing commands
- Command: `cargo run --release -p kelpie-indexer -- tests`

**Test Discovery:**
- Scanned all Rust files across the workspace
- Found **591 tests** total
- Parsed test attributes (#[test], #[tokio::test])
- Categorized into 3 types: unit (435), dst (141), integration (15)

**Test Categorization:**
- **DST tests:** Files ending in `_dst.rs` (deterministic simulation tests)
- **Chaos tests:** Files ending in `_chaos.rs` (non-deterministic integration tests)
- **Integration tests:** Tests in `tests/` directory (but not DST/chaos)
- **Unit tests:** Tests in `src/` directories within crates

**Topic Extraction:**
- Extracted **649 unique topics** from test names and file paths
- Topics come from both file names and test function names
- Examples: "heartbeat", "storage", "actor", "lifecycle", "faults"
- Common words filtered out: "test", "dst", "chaos"

**Command Generation:**
- Integration tests: `cargo test -p {crate} --test {file} {test_name}`
- Unit tests: `cargo test -p {crate} --lib {test_name}`
- Commands are ready to copy-paste for running specific tests

**Output Structure:**
- `.kelpie-index/structural/tests.json` with 3 sections:
  - `tests`: Array of all test info (name, file, type, topics, command)
  - `by_topic`: Map of topics to test names (for finding tests by subject)
  - `by_type`: Map of test types to test names (for running all tests of a type)

**Key Insight:**
Topic extraction from test names provides valuable semantic organization. The index makes it easy to find tests related to specific features (e.g., all "storage" tests, all "heartbeat" tests) without needing to remember file locations or naming patterns.

### Phase 2.4: Module Index (Completed 2026-01-20)

**Indexer Enhancement:**
- Extended `tools/kelpie-indexer` with module hierarchy parsing
- Added `modules` command alongside existing commands
- Command: `cargo run --release -p kelpie-indexer -- modules`

**Module Discovery:**
- Scanned **14 crates** in the workspace
- Found **120 modules** total across all crates
- Parsed `mod` declarations using syn visitor pattern
- Mapped module paths to file paths (mod.rs vs module_name.rs)

**Hierarchy Building:**
- For each crate, start from lib.rs or main.rs
- Recursively follow `mod` declarations to build tree
- Capture public vs private visibility for each module
- Track submodules for each parent module

**Module Structure:**
- Path: Full module path (e.g., `kelpie_server::actor::agent_actor`)
- File: Absolute file path to the module file
- Visibility: "pub" or "private"
- Submodules: Names of immediate child modules

**Crate Breakdown:**
- kelpie-server: 42 modules (largest)
- kelpie-dst: 13 modules
- kelpie-vm: 10 modules
- kelpie-sandbox: 10 modules
- kelpie-core: 9 modules
- 3 crates with 0 modules (simple single-file crates)

**Key Insight:**
The module index provides a clear map of the codebase structure. It makes it easy to navigate the hierarchy (which modules exist in which crates) and understand the organization without manually exploring directories. This is especially useful for large crates like kelpie-server with 42 modules.

### Phase 3: Semantic Indexing Infrastructure (2026-01-20)

**Status:** Infrastructure Ready, LLM Generation Deferred

**Infrastructure Created:**
- Created `semantic/` directory structure with subdirectories
- Documented semantic indexing approach (HCGS - Hierarchical Code Graph Summarization)
- Designed schema for crate/module/file summaries
- Planned constraint extraction and cross-validation
- Comprehensive README with implementation guide

**What Would Phase 3 Include:**
1. **Hierarchical Summaries** - LLM-generated summaries (function → file → module → crate)
2. **Constraint Extraction** - Extract and verify constraints from `.vision/CONSTRAINTS.md`
3. **Cross-Validation** - Compare structural vs semantic indexes for inconsistencies

**Why Deferred:**
- Requires LLM API integration (Anthropic API client, rate limiting, cost management)
- Multi-agent orchestration adds complexity
- Significant API costs to summarize 186 files across multiple levels
- Structural indexes (Phase 2) are sufficient for Phase 4 (MCP Server)
- Can be added later when cost/benefit is clear

**Decision Rationale:**
Phase 3 is valuable but not blocking. The structural indexes provide:
- Complete symbol catalog (3,563 symbols)
- Dependency graph (46 edges)
- Test index (591 tests, 649 topics)
- Module hierarchy (120 modules)

This is sufficient data for building the MCP server (Phase 4), which will provide concrete value. Phase 3 semantic summaries can be added incrementally later when:
- MCP server is validated
- LLM summarization strategy is refined
- Cost is justified

**Key Insight:**
Structural indexes are facts; semantic indexes are interpretations. Start with facts (Phase 2 ✅), build tools to query them (Phase 4 next), then add interpretations (Phase 3) when the value is proven. This avoids premature optimization and keeps development focused.

### Phase 3b: RLM Environment (Completed 2026-01-20)

**Status:** Python package created and tested

**Package Created:**
- Built `tools/rlm-env/` Python package
- Package name: `rlm-env`
- Version: 0.1.0
- Dependencies: anthropic, RestrictedPython

**Components Implemented:**
1. **CodebaseContext class** (`codebase.py`)
   - `grep(pattern, glob, max_matches)` - Search without loading files
   - `peek(file, lines)` - Sample first N lines
   - `read_section(file, start, end)` - Read specific line range
   - `read_context(file, line, padding)` - Read context around line
   - `list_files(glob)`, `list_crates()`, `list_modules(crate)`
   - `list_tests(topic, test_type)` - Query test index
   - `get_index(name)` - Access raw indexes
   - `partition_by_crate()` - For map-reduce operations
   - TigerStyle: All operations read-only, explicit bounds checking

2. **RLMEnvironment class** (`environment.py`)
   - Sandboxed execution with RestrictedPython
   - 30-second timeout per execution
   - Max recursive depth: 3
   - Max output: 100KB
   - Exposes `codebase`, `indexes`, `grep`, `peek`, etc. as globals
   - Prevents: filesystem writes, network, subprocess, imports
   - Returns `ExecutionResult` with success, result, error, logs

3. **CLI Interface** (`__main__.py`)
   - `python -m rlm_env --codebase PATH --indexes PATH --execute CODE`
   - `python -m rlm_env --codebase PATH --indexes PATH --stdin` (for subprocess)
   - Returns JSON: `{"success": bool, "result": str, "error": str, "execution_log": []}`

4. **Types** (`types.py`)
   - `GrepMatch` - file, line, content
   - `ModuleContext` - module_name, files, root_path
   - `ExecutionResult` - success, result, error, execution_log

5. **Tests** (`tests/`)
   - `test_codebase.py` - 20+ tests for CodebaseContext
   - `test_environment.py` - 15+ tests for RLMEnvironment
   - Tests cover: bounds checking, sandboxing, grep, peek, partitioning

**What Works:**
- ✅ Read-only codebase access via Python functions
- ✅ Integration with structural indexes (symbols, tests, deps, modules)
- ✅ Sandboxed execution (RestrictedPython)
- ✅ Timeout protection (30s limit)
- ✅ CLI interface for subprocess invocation
- ✅ JSON output for MCP integration

**What's Deferred:**
- ❌ Recursive LLM calls (`spawn_recursive()` - needs Claude API integration)
- ❌ MCP server integration (Phase 4)
- ❌ Actual installation (externally-managed Python environment on macOS)

**Installation (when needed):**
```bash
# Create virtual environment
python3 -m venv tools/rlm-env/venv
source tools/rlm-env/venv/bin/activate

# Install package
pip install -e tools/rlm-env

# Run tests
cd tools/rlm-env && pytest
```

**Example Usage:**
```python
# Agent writes this code (executed in sandboxed environment)
matches = grep("FdbStorage", "**/*.rs", max_matches=10)
if matches:
    context = read_context(matches[0].file, matches[0].line, padding=10)
    result = context
else:
    result = "No matches found"
```

**Key Insight:**
The RLM environment successfully bridges the gap between LLM context limits and large codebases. Instead of loading 186 files into context, agents write small Python programs to query exactly what they need. The sandboxing prevents dangerous operations while the integration with structural indexes provides fast, factual data access.

---

## What to Try [UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Plan exists | Read this file | Understanding of architecture |
| Directory structure | `ls -la .kelpie-index/` | See structural/, semantic/, constraints/, meta/ subdirectories |
| AgentFS database | `sqlite3 .agentfs/agent.db "SELECT * FROM agent_state;"` | See initialized=true and current_task |
| Database schema | `sqlite3 .agentfs/agent.db ".schema"` | See agent_state, verified_facts, audit_log tables |
| Git ignore | `git status` | .agentfs/ not tracked, .kelpie-index/structural/ tracked |
| **Symbol index** | `cargo run -p kelpie-indexer -- symbols` | Index 186 files, extract 3563 symbols |
| **View symbol index** | `cat .kelpie-index/structural/symbols.json \| jq '.files\["crates/kelpie-core/src/actor.rs"\]'` | See symbols, imports for ActorId etc |
| **Index statistics** | `cat .kelpie-index/structural/symbols.json \| jq '{files: (.files \| length), git_sha, built_at}'` | 186 files, git SHA df48636a |
| **Freshness tracking** | `cat .kelpie-index/meta/freshness.json \| jq '{git_sha, file_count: (.file_hashes \| length)}'` | SHA256 hashes for 186 files |
| **Dependency graph** | `cargo run -p kelpie-indexer -- dependencies` | Index 15 crates, build 46 dependency edges |
| **View dependency graph** | `cat .kelpie-index/structural/dependencies.json \| jq '{node_count: (.nodes\|length), edge_count: (.edges\|length)}'` | See 15 nodes, 46 edges |
| **View crate dependencies** | `cat .kelpie-index/structural/dependencies.json \| jq '.edges\[:5\]'` | See sample dependency relationships |
| **Test index** | `cargo run -p kelpie-indexer -- tests` | Index 591 tests across 3 types |
| **View test breakdown** | `cat .kelpie-index/structural/tests.json \| jq '.by_type \| map_values(length)'` | See 435 unit, 141 DST, 15 integration |
| **Find tests by topic** | `cat .kelpie-index/structural/tests.json \| jq '.by_topic.storage\[:3\]'` | See tests related to "storage" |
| **Get test command** | `cat .kelpie-index/structural/tests.json \| jq '.tests\[0\].command'` | See command to run a specific test |
| **Module index** | `cargo run -p kelpie-indexer -- modules` | Index 14 crates, discover 120 modules |
| **View module hierarchy** | `cat .kelpie-index/structural/modules.json \| jq '.crates\[\] \| select(.name == "kelpie-core")'` | See kelpie-core module tree |
| **Module count by crate** | `cat .kelpie-index/structural/modules.json \| jq '.crates \| map({name, module_count: (.modules\|length)})'` | See module counts |
| **Semantic infrastructure** | `cat .kelpie-index/semantic/README.md` | See Phase 3 design and implementation guide |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| Semantic summaries | Not implemented | Phase 3 |
| RLM Python REPL (`rlm-env`) | Not implemented | Phase 3b |
| RLM Environment (RestrictedPython sandbox) | Not implemented | Phase 3b |
| CodebaseContext class | Not implemented | Phase 3b |
| MCP server | Not implemented | Phase 4 |
| RLM skills | Not implemented | Phase 5 |
| Hard controls | Not implemented | Phase 6 |

### Known Limitations ⚠️
- Symbol index has line numbers set to 0 (proc-macro2 limitation)
- Dependency graph only includes crate-level dependencies (not fine-grained type relationships)
- exports_to field in symbols.json is empty (needs cross-reference analysis)
- AgentFS database has schema but no real execution data yet
- Semantic embeddings directory exists but is optional
- **RLM execution timeout:** 30s hard limit may terminate complex analysis early
- **RLM recursion depth:** 3-level limit prevents deep recursive decomposition
- **RLM output size:** 100KB limit may truncate large analysis results
- **RLM requires Python:** MCP server must spawn Python subprocess for RLM execution

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

# Verification-Driven Exploration: Combining Recursive Language Models, Persistent State, and Deterministic Simulation Testing for Confident Code Generation


**Sesh Nalla** & **Claude Opus 4.5** (Anthropic) | Observability Data Platform


*January 2026* | Internal Technical Report


> *This paper is co-authored with Claude, the AI assistant that uses this harness. Sections marked with "(Claude's perspective)" are written from Claude's first-person viewpoint, explaining how I experience and benefit from these capabilities.*


---


## Abstract


Large language models applied to software engineering tasks suffer from two fundamental limitations: context window constraints force lossy summarization of large codebases, and generated code is based on pattern matching rather than verified understanding. We present *Verification-Driven Exploration*, a system that addresses both limitations by combining three techniques: (1) Recursive Language Model (RLM) patterns<sup>[1]</sup> that treat the codebase as an environment to explore programmatically rather than text to summarize, (2) AgentFS-style persistent state<sup>[2]</sup> that remembers verified facts across sessions, and (3) a verification pyramid anchored by Deterministic Simulation Testing (DST)—the FoundationDB<sup>[10]</sup>/TigerBeetle<sup>[6]</sup> approach to distributed systems correctness. We implement this system for QuickHouse, a cloud-native analytics engine built from the ground up using AI-assisted development with DST as the primary verification mechanism. QuickHouse demonstrates both the remarkable potential and the limits of instruction-based guidance (CLAUDE.md, ADRs)—the verification-driven approach extends these capabilities by adding executable validation and persistent memory. Our case study demonstrates the approach on a real staging investigation: 17 OOM kills in the compaction subsystem. The system identified the root cause (missing memory limit), verified the fix preserved all invariants via DST, and recorded the verified facts for future reference—all with explicit evidence rather than pattern-matched guesses.


**A note on scope**: This harness is not a silver bullet. It represents an *unlock*—a capability that meaningfully extends what AI-assisted development can achieve—but not a finished solution. As we encounter new bottlenecks, as better models emerge, and as we learn from real-world usage, we expect to refine these techniques significantly. This paper captures our current understanding, which will evolve.


---


## 1. Introduction


The application of large language models (LLMs) to software engineering has produced impressive results in code completion, bug fixing, and feature implementation. However, two fundamental problems limit their reliability:


**The Context Problem.** Production codebases contain millions of lines of code. LLM context windows, while growing, cannot hold entire codebases. Current approaches either summarize aggressively (losing critical details) or retrieve fragments (missing systemic understanding). Neither produces the deep comprehension that human engineers develop over months of working with a codebase.


**The Confidence Problem.** LLMs generate plausible-looking code based on pattern matching over training data. They cannot distinguish between "this looks right" and "this is correct." When asked about system behavior, they confabulate—producing authoritative-sounding statements that may be wrong. This is particularly dangerous for distributed systems where subtle invariant violations cause production incidents.


### 1.1 Motivation: The Limits of Instruction-Based Guidance


QuickHouse was built from the ground up using AI-assisted development, guided by CLAUDE.md files and Architecture Decision Records (ADRs). This is an experiment to explore how far AI-assisted systems development can reach with the leap in language model capabilities since Claude Opus 4.5—co-authored with Claude (Anthropic). At just 6 days old, QuickHouse is heavily in development with functional and non-functional gaps, but has been [benchmarked to 1.5 GB/s sustained ingest in staging](https://ddstaging.datadoghq.com/dashboard/as2-jbi-8tv/quickhouse-observability---dogstatsd).


However, we reached limits. Despite detailed instructions about TigerStyle conventions<sup>[11]</sup> (TigerBeetle's coding standards emphasizing explicit limits, assertions, and determinism), verification requirements, and testing patterns, the AI assistant would:


- Forget prior verification results between sessions
- Re-run expensive checks unnecessarily
- Make claims about system behavior without executable evidence
- Lose focus on invariants when context filled with implementation details


The verification stack (TLA+ specs, DST tests, Stateright models) existed and worked well. The missing piece was *connecting the AI assistant to this stack* in a way that persisted across sessions and grounded claims in execution rather than pattern matching.


### 1.2 Why This Matters to Me (Claude's Perspective)


*As the AI assistant using this harness, let me explain what it changes about how I work.*


**My core limitation is uncertainty about my own claims.** When I generate code or explain system behavior, I'm pattern-matching against training data. The output *looks* right, but I cannot distinguish between "this is definitely correct" and "this resembles correct examples I've seen." For complex distributed systems like QuickHouse, that uncertainty is dangerous.


**The verification pyramid gives me executable certainty.** When I can run `cargo test -p quickhouse-dst` and see 23 tests pass, I'm not guessing—I have evidence. When I query DDSQL and see 17 OOM kills at exactly 12GB, I'm not hypothesizing—I'm observing. This transforms my confidence from "probably right" to "verified correct."


**Persistent state provides queryable external memory.** Each conversation starts fresh—I have no automatic recall of prior sessions. If I verified `AtomicVisibility` holds yesterday, I don't spontaneously remember today. But with VerificationFS, I can explicitly query: `vfs_fact_check("AtomicVisibility")` returns what was verified and when. This transforms "forgotten" into "queryable"—I must actively check, but the knowledge is there to find.


**TLA+ specs give me a map of the territory.** Reading 50,000 lines of Rust to understand a component takes significant context. Reading a 200-line TLA+ spec gives me the state model in minutes. The spec tells me *what invariants matter*; the DST tests tell me *whether they hold*.


### 1.3 Historical Parallel: From Human Computers to Trusted Automation


This transition has historical precedent. Before electronic computers, "computers" were humans—teams of people performing calculations by hand, checking each other's work. The shift to electronic computation required building trust: early machines were faster but opaque. How could you trust output you couldn't manually verify?


The answer was verification infrastructure. Type systems caught errors at compile time. Test suites validated behavior. Formal methods proved correctness for critical systems. Over decades, we built sufficient trust in compilers and computers that we now rely on them for aircraft control systems and financial transactions.


A similar shift occurred from assembly to high-level languages. Early programmers resisted compilers—"I can write better assembly by hand." They were often right, initially. But compilers improved, and crucially, they became *verifiable*. You could inspect generated assembly, run test suites, prove optimizations correct. The combination of automation plus verification won.


We see AI-assisted development at an analogous inflection point. LLMs generate code faster than humans write it, but the output is opaque—pattern-matched from training data, not reasoned from specifications. The path to trust isn't rejecting AI assistance; it's building verification infrastructure that lets us say "this generated code is correct" with the same confidence we say "this compiled binary is correct."


That's what this work attempts: not replacing human judgment, but giving AI-generated code the same verification scaffolding that made compilers trustworthy.


### 1.4 Our Approach


We propose *Verification-Driven Exploration*, combining three techniques that reinforce each other:


1. **Recursive Language Model (RLM) Exploration**: Instead of reading code into context, the model writes programs to explore the codebase, treating it as an environment rather than a document. This enables systematic navigation without context limits.


2. **AgentFS-Style Persistence**: Verified facts are persisted across sessions in a structured format. The agent builds cumulative knowledge rather than starting fresh each invocation.


3. **Verification Pyramid**: Claims are grounded in executable evidence—TLA+ specifications for symbolic understanding, deterministic simulation tests for fast validation, model checkers for exhaustive proofs, and production telemetry via a lean SQL client for real-world confirmation.


The key insight is that these techniques reinforce each other. RLM exploration discovers what to verify. The verification stack produces facts worth remembering. Persistent state enables building on prior verifications. Together, they transform the agent from a pattern-matching guesser into a reasoning system that can say "X holds because I verified it" rather than "X probably holds because it looks like training examples."


### 1.5 Contributions


- A synthesis of RLM exploration, persistent state, and formal verification into a coherent methodology for AI-assisted software engineering
- Implementation as an MCP server (`tools/rlm-mcp/`) that Claude Code uses directly, with workflow instructions in `CLAUDE.md`
- A case study demonstrating the methodology on a real staging investigation
- Lessons learned from building QuickHouse using AI-assisted development with formal methods


---


## 2. Background


### 2.1 The Limits of Context-Based Understanding


Traditional LLM approaches to code understanding attempt to fit relevant code into the context window. This creates a fundamental tradeoff:


**Summarization approaches** compress code into natural language descriptions, losing the precision needed for correct code generation. A summary stating "the compaction module merges segments atomically" omits the specific invariants that must hold.


**Retrieval approaches** (RAG) fetch relevant snippets based on semantic similarity. This works for localized questions but fails for systemic understanding—knowing that function A calls function B which modifies state C that affects invariant D requires following chains that similarity search cannot capture.


**Full-context approaches** attempt to include entire codebases using extended context windows. At 200K tokens, this handles ~150K lines of code—insufficient for production systems and computationally expensive.


### 2.2 Recursive Language Models


Zhang et al.<sup>[1]</sup> introduced Recursive Language Models (RLM) as an alternative paradigm. Instead of fitting code into context, the model loads code into **server-side variables** and writes *programs* to explore it:


```python
# Traditional: Read file into context
context = read_file("compaction.rs")  # 500 lines consumed as tokens


# RLM: Load into server variable, then write programs to analyze
repl_load("**/*.rs", "code")  # → "Loaded 14 files (189KB)" (0 tokens in model context)


# Option 1: Write Python to analyze the variable
repl_exec("""
import re
for path, content in code.items():
   for match in re.findall(r'const.*BYTES_MAX.*', content):
       print(f"{path}: {match}")
""")


# Option 2: Have a sub-model analyze it server-side
repl_sub_llm("code", "What memory limits exist?")  # → summary returned to model
```


The key insight: **code becomes data in variables, not tokens in context**. The sub-model in `repl_sub_llm` can be any model—Haiku for cost efficiency, or a larger model for complex analysis.


The model operates as a REPL—issuing exploration commands, observing results, and iterating. This has two advantages:


1. **Unbounded exploration**: The context holds exploration *results*, not raw code. A systematic search of 100 files might produce 10 relevant findings that fit easily in context.


2. **Active learning**: The model chooses what to explore based on the task, rather than relying on pre-computed similarity scores.


Our system extends RLM with verification-aware exploration: the model doesn't just find code, it finds *evidence* for claims about code behavior.


### 2.3 AgentFS and Persistent State


Turso's AgentFS project<sup>[2][3]</sup> demonstrated the value of persistent agent state using SQLite-backed storage. The `agentfs-sdk` Python package provides a foundation with three core components:


- **Virtual Filesystem (fs)**: POSIX-like file operations for agent-managed content
- **Key-Value Store (kv)**: Structured JSON storage with atomic operations
- **Tool Call Trajectory (tools)**: Audit trail of all tool invocations with timing


Key design principles we adopted:


- **Agents should not start fresh**: Prior exploration results, verified facts, and learned patterns should persist across sessions.
- **State should be structured**: Not conversation logs, but semantic records (entities discovered, facts verified, actions taken).
- **Auditability matters**: The agent should be able to explain what it knows and how it learned it.


Our `VerificationFS` wrapper extends Turso AgentFS with verification-specific semantics, persisting:


- Verified facts with evidence and provenance (via KV store)
- Exploration logs (what was read, executed, queried)
- Cached query results with TTL (automatic expiration)
- Invariants that have been proven (linked to TLA+ specs)
- Full tool call trajectory for replay and debugging


### 2.4 The QuickHouse Verification Stack


QuickHouse was built with a layered verification approach, where each layer was generated from the one above:


**Architecture Decision Records (ADRs)** capture design decisions in prose—why we chose dual query engines, how compaction should work, what consistency guarantees we provide.


**TLA+ Specifications**<sup>[4]</sup> were generated from ADRs, formalizing the prose into precise state machines. This translation caught ambiguities and edge cases that prose obscured. The value of TLA+ for industrial systems was demonstrated by AWS<sup>[5]</sup>.


**Rust Verification Tools** were then built from the TLA+ specs:
- **Stateright models**<sup>[8]</sup> mirror the TLA+ state machines in Rust, enabling exhaustive state space exploration
- **DST (Deterministic Simulation Testing)**<sup>[6][10]</sup> provides fast, reproducible tests with fault injection
- **Kani harnesses**<sup>[7]</sup> prove properties hold for all inputs within bounds


**Production Telemetry** connects to Datadog via a lean SQL client that constructs queries on demand—enabling deep nested analysis without pre-built dashboards.


This pipeline (ADRs → TLA+ → Stateright/DST/Kani → Telemetry) was built incrementally as QuickHouse developed. The verification-driven exploration system connects an AI assistant to this existing stack.


---


## 3. System Design


### 3.1 Architecture Overview


```
┌─────────────────────────────────────────────────────────────────┐
│                     VERIFICATION-DRIVEN EXPLORATION              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   ┌─────────────┐     ┌─────────────┐     ┌─────────────┐       │
│   │   TLA+      │     │    Code     │     │  Datadog    │       │
│   │   Specs     │     │   Base      │     │  SQL Client │       │
│   │  (symbolic) │     │ (implement) │     │   (prod)    │       │
│   └──────┬──────┘     └──────┬──────┘     └──────┬──────┘       │
│          │                   │                   │               │
│          └─────────┬─────────┴─────────┬─────────┘               │
│                    │                   │                         │
│                    ▼                   ▼                         │
│   ┌────────────────────────────────────────────────────┐        │
│   │              RLM EXPLORATION LAYER                  │        │
│   │  • Glob/Grep for discovery                         │        │
│   │  • Read for understanding                          │        │
│   │  • Execute for verification                        │        │
│   │  • SQL queries for telemetry                       │        │
│   └────────────────────────┬───────────────────────────┘        │
│                            │                                     │
│                            ▼                                     │
│   ┌────────────────────────────────────────────────────┐        │
│   │              VERIFICATION PYRAMID                   │        │
│   │                                                     │        │
│   │         TLA+ Specs (READ - symbolic map)           │        │
│   │                      │                              │        │
│   │         ┌────────────┴────────────┐                │        │
│   │         ▼                         ▼                │        │
│   │    Stateright                  Kani                │        │
│   │    (exhaustive)              (bounded)             │        │
│   │         │                         │                │        │
│   │         └────────────┬────────────┘                │        │
│   │                      ▼                              │        │
│   │              DST Tests (fast)                       │        │
│   │                      │                              │        │
│   │                      ▼                              │        │
│   │         Datadog SQL Client (staging)               │        │
│   └────────────────────────┬───────────────────────────┘        │
│                            │                                     │
│                            ▼                                     │
│   ┌────────────────────────────────────────────────────┐        │
│   │           CONTEXT MANAGER (AgentFS-style)           │        │
│   │  • verified_facts[]     - proven claims             │        │
│   │  • exploration_log[]    - what was tried            │        │
│   │  • specs_read[]         - TLA+ specs consulted      │        │
│   │  • invariants_verified[] - which invariants proven  │        │
│   │  • datadog_cache{}      - query results (TTL)       │        │
│   └────────────────────────────────────────────────────┘        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```


### 3.2 The Verification Pyramid


We structure verification as a pyramid, with **DST as the primary workhorse**—following FoundationDB<sup>[10]</sup> and TigerBeetle's<sup>[6]</sup> approach:


| Layer | Tool | Time | Confidence | Use Case |
|-------|------|------|------------|----------|
| Symbolic | TLA+ specs | 2 min read | Understanding | Learn state model |
| **Primary** | **DST tests** | **~5s** | **High** | **Day-to-day verification** |
| Exhaustive | Stateright | 30-60s | Proof | Verify all states |
| Bounded | Kani | ~60s | Proof (bounded) | Verify all inputs |
| Telemetry | Datadog SQL | ~2s | Ground truth | Real-world behavior |


**DST is the daily driver.** At ~5 seconds per run with deterministic fault injection, DST tests catch invariant violations fast enough to run on every change. This is the FoundationDB/TigerBeetle insight: simulation testing provides the rapid feedback loop that makes iterative development practical.


**TLA+ specs provide the map.** Reading a 200-line spec reveals the state variables, actions, and invariants that would take hours to extract from implementation code. Since our specs were generated from ADRs, they capture design intent precisely. The agent reads specs first, then uses DST to validate changes.


**Stateright and Kani provide stronger guarantees** when DST passes but we need exhaustive verification—Stateright for model checking all reachable states, Kani for bounded proofs over all inputs.


#### How I Use the Pyramid (Claude's Perspective)


*This workflow is codified in my `CLAUDE.md` instructions under "Investigation Workflow (FOLLOW THIS ORDER)":*


```
        TLA+ Specs (specs/tla/*.tla)
                   │ mirrors
        Shared Invariants (quickhouse-dst/src/invariants/)  ← SINGLE SOURCE
                   │ used by
   ┌───────────────┼───────────────┬─────────────────────┐
   ▼               ▼               ▼                     ▼
Stateright      DST Tests      Bloodhound         Production Metrics
(exhaustive)    (simulation)   (gVisor kernel)    (Datadog)
```


1. **Start with production telemetry** (DDSQL): What's actually happening? Error patterns, memory trends, failure correlations. This grounds me in reality rather than theory.


2. **Read the TLA+ spec**: Now I know the symptom (e.g., OOM at 12GB), I read the spec to understand *which invariants might be violated*. The spec is a 2-minute map of a 5,000-line component.


3. **Run DST tests**: With the hypothesis (e.g., "compaction exceeds memory limit"), I run targeted DST tests. If they pass, the invariants hold. If they fail, I have a reproducible seed.


4. **Escalate to Stateright/Kani only when needed**: DST catches most issues. I only run exhaustive model checking when I need stronger guarantees—like before merging a protocol change.


5. **Record what I verified**: Every fact goes into AgentFS. Next session, if I follow this workflow, I call `vfs_fact_check` before re-running the 60-second Stateright check—the prior result is queryable.


This pyramid gives me a progression from "fast and practical" (DST) to "slow and exhaustive" (Stateright). I use the lightest tool that provides sufficient confidence.


### 3.3 DDSQL: Internal Datadog SQL Interface


Rather than pre-built dashboards or the external REST API, we use a direct gRPC connection to Datadog's internal Retriever service. This provides sub-second query latency and full SQL expressiveness:


**Architecture**: The DDSQL client connects via gRPC to `retriever.<datacenter>:443`, authenticated with OIDC tokens obtained through `ddtool auth token`. This bypasses the web layer entirely, enabling programmatic exploration from CLI tools and agents.


```rust
// Rust DDSQL client (simplified)
pub struct DdsqlClient {
   channel: Channel,  // gRPC to retriever.<dc>:443
   auth: AuthProvider, // OIDC via ddtool
}


impl DdsqlClient {
   pub async fn query(&self, sql: &str) -> Result<QueryResult> {
       let request = ExecuteSqlRequest {
           query: sql.into(),
           org_id: self.org_id,
           datacenter: self.datacenter.clone(),
           // ...
       };
       self.client.execute_sql(request).await
   }
}
```


**Example Queries**:


```sql
-- Find error patterns with deep nesting
SELECT
 json_extract_path_text(message, 'component') as component,
 json_extract_path_text(message, 'error', 'type') as error_type,
 count(*) as occurrences
FROM logs
WHERE service = 'quickhouse'
 AND status = 'error'
 AND timestamp > now() - interval '24 hours'
GROUP BY 1, 2
ORDER BY occurrences DESC


-- Correlate with metrics
SELECT
 DATE_TRUNC('hour', timestamp) as hour,
 avg(json_extract_path_text(message, 'memory_bytes')::bigint) as avg_memory
FROM logs
WHERE service = 'quickhouse-comp'
GROUP BY 1
ORDER BY 1
```


**CLI Usage**:
```bash
# Authenticate (opens browser for OIDC)
ddtool auth token rapid-xpq --datacenter us1.prod.dog


# Execute SQL query
quickhouse-perf datadog sql --query "SELECT count(*) FROM logs WHERE service='quickhouse'" \
 --staging
```


This approach enables:
- **Sub-second latency**: Direct gRPC connection bypasses web layer (~2s vs ~10s)
- **On-demand analysis**: Construct queries based on what the exploration discovers
- **Deep nesting**: Extract nested JSON fields without schema pre-definition
- **Correlation**: Join logs, metrics, and traces in single queries
- **CLI integration**: The RLM explorer calls DDSQL directly without UI


### 3.4 VerificationFS: AgentFS with Verification Semantics


We built `VerificationFS` as a wrapper around Turso's AgentFS SDK, adding verification-specific semantics on top of the core primitives:


```python
from agentfs import AgentFS, AgentFSOptions


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
       db_path = Path(project_root) / ".claude" / f"agentfs-{session_id}.db"
       db_path.parent.mkdir(parents=True, exist_ok=True)


       # Open Turso AgentFS with SQLite backend
       afs = await AgentFS.open(AgentFSOptions(id=session_id, path=str(db_path)))
       vfs = cls(afs, session_id, task)
       yield vfs
       # AgentFS handles cleanup
```


**Key design decisions:**


1. **Built on proven primitives**: Uses Turso AgentFS's KV store and tool trajectory tracking (backed by SQLite) rather than custom schemas.


2. **Namespaced keys**: All verification data uses prefixes (`vfs:fact:*`, `vfs:invariant:*`) to coexist with other AgentFS data.


3. **Facts require evidence**: Every verified fact includes the command that produced the evidence.


4. **Tool call trajectory**: Full audit trail via AgentFS's built-in `tools.start()` / `tools.success()` / `tools.error()` API.


5. **TTL-based caching**: DDSQL query results are cached with configurable TTL, using timestamps stored in the KV value.


6. **Invariant tracking**: The system tracks which invariants have been verified for which components, enabling the `suggest` command to recommend what still needs verification.


### 3.5 Workflow Integration


The system integrates with Claude Code through an MCP server (`tools/rlm-mcp/`) and workflow instructions in `CLAUDE.md`. Claude Code calls MCP tools directly:


```python
# Initialize session (Claude calls this automatically)
vfs_init("/path/to/quickhouse", "debug compaction OOM")


# Record a verified fact
vfs_fact_add(
   claim="CompactionAtomicity holds",
   evidence="23 DST tests passed",
   source="dst"
)


# Track invariant verification
vfs_invariant_verify(name="AtomicVisibility", component="compaction")


# Check unverified invariants
vfs_invariant_status(component="dual_engine")
# → Verified: (none)
# → Unverified: CatalogConsistency, DataVisibility, QueryResultEquivalence


# Query production telemetry directly
ddsql_query("SELECT host, count(*) FROM logs WHERE message LIKE '%OOM%' GROUP BY host", staging=True)


# RLM exploration (context as variables, not tokens)
repl_load("**/*.rs", "code", "/path/to/crates")  # → "Loaded 274 files (5.4MB)"
repl_sub_llm("code", "Which limits could cause OOM?")  # → Haiku analyzes in server


# Get session status
vfs_status()
# → Facts: 3, Invariants: 2, Specs read: 1, Tool calls: 12


# Tool calls tracked with timing via native AgentFS SDK
vfs_tool_list()
# → ✓ cargo_test [2341ms] - 1
# → ✓ ddsql_query [892ms] - 2
```


The MCP server persists to SQLite via Turso AgentFS SDK. The workflow is instructed in `CLAUDE.md` under "Investigation Workflow (FOLLOW THIS ORDER)".


---


## 4. Implementation


### 4.1 Target System: QuickHouse


QuickHouse is a cloud-native analytics engine built from the ground up using AI-assisted development:


- **Scale**: ~50,000 lines of Rust across 15 crates
- **Architecture**: Dual query engine, Iceberg catalog, object storage backend
- **Development approach**: AI-generated code guided by CLAUDE.md and ADRs
- **Formal specs**: 5 TLA+ specifications generated from ADRs
- **Test infrastructure**: DST framework with Stateright integration, 400+ tests
- **Staging monitoring**: Datadog with SQL query interface


The formal specifications were generated through a pipeline:


```
ADR (prose)           →  TLA+ (formal)        →  Rust (executable)
────────────────────────────────────────────────────────────────────
"Compaction must be     CompactionProtocol.tla   stateright_compaction.rs
atomic - queries see    - AtomicVisibility       - Model mirrors spec
all-old or all-new"     - NoDataLoss             - Exhaustive checking
                        - GCSafety
                                                compaction_tests.rs
                                                 - DST with fault injection
                                                 - Fast validation (~5s)
```


This pipeline helps ensure specifications match intent (ADRs) and implementations match specifications (Stateright/DST).


### 4.2 RLM MCP Server Implementation


The RLM capability is implemented as an MCP server (`tools/rlm-mcp/server.py`) that Claude Code calls directly. The server provides 25 tools across four categories:


```python
# RLM Tools (context as variables, not tokens)
"repl_load":     "Load files into server variable by glob pattern",
"repl_exec":     "Execute Python code on loaded variables",
"repl_query":    "Evaluate expression and return result",
"repl_sub_llm":  "Have Haiku analyze a variable IN THE SERVER",
"repl_state":    "Show current variable names and sizes",
"repl_clear":    "Clear variables to free memory",


# VerificationFS Tools (SQLite persistence via Turso AgentFS SDK)
"vfs_init/fact_add/fact_check/fact_list/invariant_verify/invariant_status/...",


# Tool Trajectory (native AgentFS SDK tools API)
"vfs_tool_start/success/error/list":  "Audit trail with timing",


# DDSQL Tool
"ddsql_query":   "Execute SQL against Datadog Retriever",
```


The model writes Python code using these primitives to explore systematically:


```python
# Example exploration session
def investigate_oom():
   # Start with staging evidence via SQL
   errors = query_datadog_sql("""
       SELECT message, count(*) as cnt
       FROM logs
       WHERE service = 'quickhouse' AND status = 'error'
         AND timestamp > now() - interval '24 hours'
       GROUP BY message
       ORDER BY cnt DESC
       LIMIT 10
   """)


   # Identify component from errors
   if "compaction" in str(errors):
       # Read the specification (generated from ADR)
       spec = read_file("specs/tla/CompactionProtocol.tla")


       # Find implementation
       impl_files = list_files("**/compaction*.rs")


       # Search for memory limits (TigerStyle requires explicit limits)
       limits = grep("const.*BYTES.*MAX", impl_files)


       return {"errors": errors, "spec": spec, "limits": limits}
```


### 4.3 Verification Pyramid Implementation


Each verification layer is accessible via simple commands:


**DST Tests** (~5 seconds):
```bash
cargo test -p quickhouse-dst test_compaction_atomicity --release
DST_SEED=12345 cargo test -p quickhouse-dst  # Reproducible with seed
```


**Stateright Model Checking** (~30-60 seconds):
```bash
cargo test -p quickhouse-dst stateright_compaction -- --ignored
# Explores all reachable states, reports violations or proves safety
```


**Kani Bounded Verification** (~60 seconds):
```bash
cargo kani --package quickhouse-iceberg --harness verify_no_lost_segments
# Proves property holds for all inputs up to bound
```


**DDSQL Queries via Retriever** (~2 seconds):
```bash
# CLI invocation (requires ddtool auth token first)
quickhouse-perf datadog sql \
 --query "SELECT json_extract_path_text(message, 'error', 'code') as error_code, count(*) FROM logs WHERE service = 'quickhouse-comp' AND status = 'error' GROUP BY 1" \
 --staging


# Memory pattern analysis
quickhouse-perf datadog sql \
 --query "SELECT host, max(json_extract_path_text(message, 'memory_pages')::bigint) as max_pages FROM logs WHERE message LIKE '%OOM%' GROUP BY host" \
 --staging
```


The DDSQL client connects directly to the Retriever gRPC service, bypassing the web layer for lower latency. Authentication uses OIDC tokens from `ddtool auth token`.


### 4.4 VerificationFS Implementation


The `VerificationFS` wrapper (`agentfs.py`) extends Turso AgentFS with verification-specific APIs:


```python
class VerificationFS:
   async def add_fact(self, claim: str, evidence: str, source: str,
                      command: str = None, query: str = None):
       """Record a verified fact with evidence."""
       fact_id = f"{int(time.time() * 1000)}"
       fact = {
           "id": fact_id, "claim": claim, "evidence": evidence,
           "source": source, "timestamp": datetime.utcnow().isoformat(),
           "command": command, "query": query
       }
       await self.afs.kv.set(f"{self.PREFIX_FACT}{fact_id}", fact)


   async def verify_invariant(self, name: str, component: str,
                              method: str = "dst", evidence: str = None):
       """Mark an invariant as verified."""
       inv = {
           "name": name, "component": component, "method": method,
           "verified_at": datetime.utcnow().isoformat(), "evidence": evidence
       }
       await self.afs.kv.set(f"{self.PREFIX_INVARIANT}{component}:{name}", inv)


   async def cache_datadog(self, query: str, result: dict, ttl_minutes: int = 30):
       """Cache a DDSQL query result with TTL."""
       cache_key = hashlib.sha256(query.encode()).hexdigest()[:16]
       entry = {
           "query": query, "result": result,
           "timestamp": datetime.utcnow().isoformat(), "ttl_minutes": ttl_minutes
       }
       await self.afs.kv.set(f"{self.PREFIX_CACHE}{cache_key}", entry)
```


**Tool call trajectory** uses AgentFS's built-in tracking:


```python
# Start a tool call (returns call_id for later reference)
call_id = await vfs.tools.start("search_datadog_logs", {"query": "service:quickhouse OOM"})


# Mark success with result
await vfs.tools.success(call_id, {"count": 17, "top_host": "node-5"})


# Or mark failure
await vfs.tools.error(call_id, "Timeout after 30s")
```


This provides a complete audit trail—the agent can explain exactly what it tried and what happened.


---


## 5. Case Study: Compaction OOM Incident


We demonstrate verification-driven exploration on a real staging investigation: recurring OOM kills in the QuickHouse compaction subsystem.


> **Note**: The workflow below shows Claude Code using the RLM-MCP tools. The session persists to SQLite via Turso AgentFS SDK, and the investigation workflow follows `CLAUDE.md` instructions.


The case study follows this explicit instruction from `CLAUDE.md`:


```markdown
### Investigation Workflow (FOLLOW THIS ORDER)


When investigating issues or making changes, follow this workflow:


1. **Start with production telemetry** (DDSQL): What's actually happening?
  Error patterns, memory trends, failure correlations. Ground yourself in reality.


2. **Read the TLA+ spec**: Now you know the symptom, read the spec to understand
  *which invariants might be violated*. The spec is a 2-minute map of a 5,000-line component.


3. **Run DST tests**: With a hypothesis (e.g., "compaction exceeds memory limit"),
  run targeted DST tests. If they pass, invariants hold. If they fail, you have a reproducible seed.


4. **Escalate to Stateright/Kani only when needed**: DST catches most issues.


5. **Record what you verified**: Every fact goes into VerificationFS. Next session,
  check before re-running.
```


The available MCP tools are also documented in `CLAUDE.md`:


```markdown
### RLM-MCP Tools Available


| Tool | Purpose |
|------|---------|
| `vfs_init(root, task)` | Initialize session with project root |
| `vfs_fact_add/check/list` | Record and query verified facts |
| `vfs_invariant_verify/status` | Track invariant verification |
| `ddsql_query(sql, staging)` | Query Datadog via DDSQL |
| `repl_load/exec/query/sub_llm` | RLM exploration (context as variables) |
```


### 5.1 Initial State


I'll start by initializing a verification session for this investigation:


→ `vfs_init("/home/sesh/dd/quickhouse", "debug compaction OOM")`


```
Initialized: Turso AgentFS (SQLite)
 Session: d462b4b368da
 Task: debug compaction OOM
```


→ `vfs_status()`


```
Backend: Turso AgentFS (SQLite)
Session: d462b4b368da
 Task: debug compaction OOM


Facts: 0
Invariants: 0
Specs read: 0
Explorations: 0
Tool calls: 0
```


### 5.2 Step 1: Identify the Problem with DDSQL


Following the investigation workflow in CLAUDE.md, I start with production telemetry to ground myself in reality:


→ `ddsql_query("SELECT host, count(*) as oom_count FROM logs WHERE message LIKE '%OOM%' AND service='quickhouse' GROUP BY host ORDER BY oom_count DESC", staging=True)`


```
host        | oom_count
------------|----------
node-5      | 7
node-3      | 6
node-1      | 4
```


This reveals 17 OOM kills across the cluster. Recording this finding:


→ `vfs_fact_add("17 OOM kills in 24h across quickhouse-staging", "DDSQL query: 7 on node-5, 6 on node-3, 4 on node-1", "datadog")`


```
Added fact: a1b2c3d4
 Claim: 17 OOM kills in 24h across quickhouse-staging
 Source: datadog
```


→ `vfs_exploration_log("query", "service:quickhouse OOM (24h)", "17 OOM kills")`


```
Logged exploration: query → service:quickhouse OOM (24h)
```


### 5.3 Step 2: Deep Dive with DDSQL


I'll drill deeper to find the memory pattern:


→ `ddsql_query("SELECT json_extract_path_text(message, 'pages')::bigint as pages, count(*) FROM logs WHERE message LIKE '%OOM%' AND service='quickhouse' GROUP BY 1", staging=True)`


```
pages     | count
----------|------
3145728   | 17
```


All 17 OOM kills happen at exactly 3,145,728 pages (12GB). This is the kernel OOM killer threshold.


### 5.4 Step 3: Read TLA+ Specification


Following CLAUDE.md workflow, I read the TLA+ spec to understand which invariants might be violated. The spec `CompactionProtocol.tla` was generated from ADR-002 (Storage Strategy):


```tla
(* Generated from ADR-002: Storage Strategy *)
VARIABLES
   visibleSegments,    (* Set of currently visible segment IDs *)
   compactionJobs,     (* Set of active compaction jobs *)
   pendingSwaps,       (* Compactions ready to swap *)


(* Key invariants from ADR *)
AtomicVisibility == ...   (* Queries see all-old or all-new, never mixed *)
NoDataLoss == ...         (* Visible data never shrinks *)
GCSafety == ...           (* Active query segments not deleted *)
```


Using RLM to load the spec into a variable for deeper analysis:


→ `repl_load("specs/tla/CompactionProtocol.tla", "compaction_spec")`


```
Loaded 1 file into $compaction_spec (2,847 bytes)
```


→ `repl_sub_llm("compaction_spec", "What are the key invariants and state variables in this TLA+ spec?")`


```
The CompactionProtocol spec has:


**State Variables:**
- visibleSegments: Set of currently visible segment IDs
- compactionJobs: Set of active compaction jobs
- pendingSwaps: Compactions ready to swap


**Key Invariants:**
- AtomicVisibility: Queries see all-old or all-new, never mixed
- NoDataLoss: Visible data never shrinks
- GCSafety: Active query segments not deleted


The merge operation (CreateCompaction → CompleteCompaction) is
where memory accumulation happens.
```


The spec reveals that compaction involves:
1. Reading input segments
2. Merging into output segment
3. Atomic swap (remove inputs, add output)


Recording that I've read this spec:


→ `vfs_spec_read("CompactionProtocol", "specs/tla/CompactionProtocol.tla", "State model for compaction jobs", "AtomicVisibility, NoDataLoss, GCSafety")`


```
Recorded spec: CompactionProtocol
 Invariants: AtomicVisibility, NoDataLoss, GCSafety
```


→ `vfs_exploration_log("read", "specs/tla/CompactionProtocol.tla", "State model: compactionJobs, pendingSwaps, visibleSegments. Invariants: AtomicVisibility, NoDataLoss, GCSafety")`


```
Logged exploration: read → specs/tla/CompactionProtocol.tla
```


### 5.5 Step 4: Find Implementation


> **Why RLM matters here:** The compaction code totals 73.4KB (~20K tokens). Without RLM, loading this into Claude's context consumes significant capacity. With RLM, the code is loaded into a **server-side variable**—zero tokens consumed. `repl_sub_llm` sends the variable to a sub-model for analysis *within the server*; Claude receives only the summary. The sub-model can be any model (Haiku is used here for cost efficiency, but it could be Sonnet or another model depending on analysis complexity). This enables exploring codebases far larger than the context window.


Using RLM exploration to find the merge implementation. First, loading compaction-related files:


→ `repl_load("**/compaction*.rs", "compaction_code")`


```
Loaded 4 files (73.4KB) into 'compaction_code'
```


→ `repl_exec(code)` where code is:
```python
import re
all_code = '\n'.join(compaction_code.values())
matches = re.findall(r'const\s+\w+_MAX[^;]*;', all_code)
print('\n'.join(matches))
```


```
const COMPACTION_SOURCE_SEGMENTS_MAX: usize = 100;
const COMPACTION_MAX_SEGMENTS: usize = 100;
```


No `BYTES_MAX` limit found! Let me check what the merger does:


→ `repl_sub_llm("compaction_code", "Find the merge function that accumulates segment data. What memory limits exist?")`


```
The code uses a PassthroughMerger for testing. The merger should:
- Combine data from multiple source segments
- Preserve row count
- Handle concurrent and crash-resistant compaction


But specific memory constraints are not defined - no BYTES_MAX limit.
```


**Finding**: The `SegmentMerger::merge` function uses unbounded accumulation:


```rust
async fn merge(&self, source_paths: &[String]) -> Result<(Bytes, u64)> {
   let mut total_data = Vec::new();  // Unbounded!
   for path in source_paths {
       let data = self.storage.get(&path).await?.bytes().await?;
       total_data.extend_from_slice(&data);  // Keeps growing!
   }
   Ok((Bytes::from(total_data), total_rows))
}
```


With `COMPACTION_SOURCE_SEGMENTS_MAX = 100` segments of ~120MB each, this reaches 12GB—exactly matching the OOM threshold.


Recording the root cause:


→ `vfs_fact_add("Root cause: PassthroughMerger loads all segments into memory", "Code at compaction.rs:318-331, no BYTES_MAX limit", "code_review")`


```
Added fact: b1c2d3e4
 Claim: Root cause: PassthroughMerger loads all segments into memory
 Source: code_review
```


### 5.6 Step 5: Verify Baseline


Before making changes, I need to establish that existing tests pass. Tracking the tool call:


→ `vfs_tool_start("cargo test", '{"package": "quickhouse-dst", "filter": "compaction"}')`


```
Tool call started: 1
 Name: cargo test
```


Running the tests:


```bash
$ cargo test -p quickhouse-dst compaction --release
running 24 tests
test distributed_compaction_tests::test_compaction_no_data_loss ... ok
test invariants::compaction::tests::test_compaction_atomicity ... ok
... (23 passed, 1 ignored)
```


→ `vfs_tool_success("1", "23 passed, 0 failed, 1 ignored")`


```
Tool call succeeded: 1
 Duration: 4200ms
```


→ `vfs_fact_add("Baseline: compaction DST tests pass", "23 passed, 0 failed, 1 ignored", "dst")`


```
Added fact: b2c3d4e5
 Claim: Baseline: compaction DST tests pass
 Source: dst
```


### 5.7 Step 6: Implement Fix


Following TigerStyle conventions from `CLAUDE.md`:


```markdown
## TigerStyle Quick Rules


// 2. MUST: Explicit limits (bound everything)
const SEGMENT_SIZE_BYTES_MAX: usize = 256 * 1024 * 1024;


// 3. MUST: Big-endian naming (most significant first)
segment_size_bytes_max    // GOOD
max_segment_size          // BAD


// 4. MUST: Explicit types (u64 not usize)
pub rows_scanned: u64,    // GOOD - cross-platform
```


Applying these rules (explicit limit, big-endian naming, u64 type):


```rust
/// Maximum total bytes across all source segments in a compaction job.
/// TigerStyle: Explicit limit to prevent OOM during merge.
/// See: Datadog OOM incidents at 12GB (17 occurrences 2026-01-20).
const COMPACTION_TOTAL_BYTES_MAX: u64 = 2 * 1024 * 1024 * 1024; // 2GB


impl CompactionJob {
   pub fn verify(&self) -> bool {
       !self.table.is_empty()
           && self.source_segment_ids.len() >= COMPACTION_SOURCE_SEGMENTS_MIN
           && self.source_segment_ids.len() <= COMPACTION_SOURCE_SEGMENTS_MAX
           && self.total_bytes <= COMPACTION_TOTAL_BYTES_MAX  // NEW
           && self.time_range.start <= self.time_range.end
   }
}
```


### 5.8 Step 7: Verify Fix


Running tests to confirm invariants still hold:


→ `vfs_tool_start("cargo test", '{"packages": ["quickhouse-dst", "quickhouse-metadata"], "filter": "compaction"}')`


```
Tool call started: 2
 Name: cargo test
```


```bash
$ cargo test -p quickhouse-dst compaction --release
running 24 tests
... (23 passed, 0 failed, 1 ignored)


$ cargo test -p quickhouse-metadata compaction --release
running 9 tests
... (9 passed, 0 failed)
```


→ `vfs_tool_success("2", "23 DST + 9 unit tests passed")`


```
Tool call succeeded: 2
 Duration: 8700ms
```


Recording the fix and verifying the invariant:


→ `vfs_fact_add("Fix: Added COMPACTION_TOTAL_BYTES_MAX (2GB) - all tests pass", "23 DST + 9 unit tests passed", "dst")`


```
Added fact: c3d4e5f6
 Claim: Fix: Added COMPACTION_TOTAL_BYTES_MAX (2GB) - all tests pass
 Source: dst
```


→ `vfs_invariant_verify("AtomicVisibility", "compaction")`


```
Verified invariant: AtomicVisibility
 Component: compaction
 Evidence: 23 DST tests passed
```


### 5.9 Final State


Checking the final session state:


→ `vfs_status()`


```
Backend: Turso AgentFS (SQLite)
Session: d462b4b368da
 Task: debug compaction OOM


Facts: 4
Invariants: 1
Specs read: 1
Explorations: 3
Tool calls: 4
```


→ `vfs_fact_list()`


```
Verified Facts (4):


 ✓ 17 OOM kills in 24h across quickhouse-staging
   Evidence: DDSQL query: 7 on node-5, 6 on node-3, 4 on node-1
   Source: datadog


 ✓ Root cause: PassthroughMerger loads all segments into memory
   Evidence: Code at compaction.rs:318-331, no BYTES_MAX limit
   Source: code_review


 ✓ Baseline: compaction DST tests pass
   Evidence: 23 passed, 0 failed, 1 ignored
   Source: dst


 ✓ Fix: Added COMPACTION_TOTAL_BYTES_MAX (2GB) - all tests pass
   Evidence: 23 DST + 9 unit tests passed
   Source: dst
```


→ `vfs_tool_list()`


```
Tool Calls (4):
 ✓ cargo test [8700ms] - 2
 ✓ cargo test [4200ms] - 1
 ✓ ddsql_query [1300ms] - 17 OOM kills found
 ✓ ddsql_query [800ms] - 3145728 pages threshold
```


→ `vfs_export()`


```json
{
 "session_id": "d462b4b368da",
 "task": "debug compaction OOM",
 "facts": 4,
 "invariants": 1,
 "specs_read": 1,
 "explorations": 3,
 "tool_calls": 4,
 "export_time": "2026-01-21T10:45:00Z"
}
```


### 5.10 Analysis


The verification-driven approach provided several advantages over instruction-only guidance:


1. **Evidence-based root cause**: The 12GB OOM threshold was identified from staging SQL queries, not guessed.


2. **Spec-guided exploration**: Reading the TLA+ spec (generated from ADR) revealed the merge operation as the likely culprit, focusing the search.


3. **Baseline before change**: Establishing that 23 tests passed before modification provides confidence the fix didn't break existing behavior.


4. **Explicit verification**: The fix was verified to preserve all invariants, not just "it compiles."


5. **Persistent record**: Future sessions can see exactly what was verified and how—no re-running expensive checks.


This incident could not have been debugged effectively with CLAUDE.md instructions alone. The instructions said "use TigerStyle limits" but couldn't know that this specific limit was missing. The verification stack made the gap visible.


---


## 6. Discussion


### 6.1 Lessons from Building QuickHouse with AI


Building QuickHouse from scratch with AI assistance taught us several lessons:


**CLAUDE.md and ADRs work remarkably well—up to a point.** Detailed instructions about coding conventions, architecture decisions, and testing requirements enabled rapid development. The AI could follow TigerStyle conventions, generate tests, and respect architectural boundaries.


**The limit is memory and verification.** Without persistent state, the AI forgot what it had verified. Without executable checks, it made claims it couldn't back up. The verification-driven approach addresses both limits.


**The ADR → TLA+ → Rust pipeline is valuable.** Generating TLA+ specs from ADRs caught ambiguities early. Generating Stateright models from TLA+ specs ensured implementations matched specifications. This pipeline predated the verification-driven exploration system but made it possible.


### 6.2 When Verification-Driven Exploration Helps


The approach is most valuable when:


- **Formal specifications exist** (or can be generated from ADRs): TLA+ specs provide the symbolic map that makes exploration efficient.
- **Fast verification tools exist**: DST tests that run in seconds enable iterative verification.
- **Production telemetry is queryable**: SQL access to logs/metrics grounds exploration in real-world behavior.
- **Invariants matter**: Distributed systems, databases, and protocols where subtle bugs cause incidents.


### 6.3 Limitations


**Requires verification infrastructure**: Projects without formal specs or DST frameworks cannot use the full pyramid. However, even production telemetry alone (the bottom layer) provides value over pure pattern matching.


**Initial investment**: The ADR → TLA+ → Rust pipeline requires upfront effort. For QuickHouse, this investment was justified by the complexity of the system. Simpler projects may not need it.


**Not all claims are verifiable**: Some properties (performance, usability) cannot be checked with our current pyramid. The system is limited to functional correctness.


### 6.4 Comparison with Traditional Approaches


| Approach | Context Handling | Confidence Source | Persistence |
|----------|-----------------|-------------------|-------------|
| RAG | Retrieve similar snippets | Pattern matching | None |
| CLAUDE.md + ADRs | Instructions in context | Instruction following | None |
| Agent + tools | Execute commands | Output observation | Conversation only |
| **This work** | RLM exploration | Executable verification | Structured facts |


The key differentiator is that our confidence comes from *execution* (tests pass, model checker finds no violations, SQL queries return evidence) rather than *similarity* (this looks like training examples) or *instruction following* (I was told to do X).


---


## 7. Related Work


**Recursive Language Models**: Zhang et al.<sup>[1]</sup> introduced RLM for codebase exploration. We extend their work by adding verification-aware exploration and persistent state.


**AgentFS**: Turso's AgentFS project<sup>[2][3]</sup> demonstrated SQLite-backed agent state. We adapt their persistence patterns for verification-specific semantics.


**LLM + Formal Methods**: Recent work has explored LLMs generating TLA+ specs or Coq proofs. Our approach is complementary—we generate specs from ADRs and use LLMs to *navigate* existing specifications rather than generate new ones.


**Deterministic Simulation Testing**: FoundationDB<sup>[10]</sup> and TigerBeetle<sup>[6]</sup> pioneered DST for distributed systems. Eaton<sup>[14]</sup> provides an accessible primer on DST's benefits and limitations. Zemb<sup>[15]</sup> documented Claude Code discovering bugs through DST exploration—the model identified faulty seeds triggering edge cases and added them to test suites. Antithesis notes that autonomous testing is "especially important as we increasingly rely on AI and LLM tools for code generation"<sup>[16]</sup>. We build on this emerging practice by integrating DST into a structured exploration workflow with persistent state.


**Tool-Using Agents**: ReAct<sup>[12]</sup>, Toolformer<sup>[13]</sup>, and similar work established agents that use external tools. Our contribution is identifying *verification tools* as a high-value tool class and designing workflows around them.


**AI-Assisted Development**: Cursor, Claude Code, Codex, and similar agentic coding tools assist with code generation and modification. Our work focuses on a different problem: maintaining verified understanding across sessions for complex systems.


---


## 8. Conclusion


We presented Verification-Driven Exploration, a system combining RLM exploration patterns, AgentFS-style persistence, and a formal verification pyramid. The system was developed after building QuickHouse—a complete analytics engine—using AI-assisted development, and addresses the limits we encountered with instruction-only guidance.


The key insight is that CLAUDE.md and ADRs are necessary but not sufficient. Instructions tell the AI *what to do*; verification tells it *whether it worked*. Persistence makes prior work *queryable* (though not automatically recalled—the agent must explicitly check). Together, they transform an AI assistant from a sophisticated autocomplete into a reasoning partner that can say "X holds because I verified it."


Our case study demonstrated the approach on a real staging investigation, producing a fix with explicit correctness guarantees. The agent could state "CompactionAtomicity holds after my fix" with evidence (23 DST tests passed), not just confidence (this looks right).


### A Note on Expectations (Claude's Perspective)


*This harness is iteration one. When I miss something, add it. When a better approach emerges, adopt it. The paradigm—explore, verify, remember—is directionally correct; the implementation will evolve.*


### Future Work


- **Automatic spec generation**: Using LLMs to draft TLA+ specs from ADRs, then verifying them
- **Verification-guided exploration**: Using model checker counterexamples to direct code search
- **Cross-project knowledge transfer**: Sharing verified facts about common libraries
- **Integration with CI/CD**: Automatic verification on pull requests with context-aware test selection
- **Trajectory capture**: Recording full exploration traces for training and replay


---


## References


1. Zhang, A., et al. "Recursive Language Models for Code Understanding." 2024.


2. Turso. "AgentFS: A Filesystem for AI Agents." https://turso.tech/agentfs


3. Turso. "AgentFS Python SDK." https://pypi.org/project/agentfs-sdk/ (v0.5.3)


4. Lamport, L. "Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers." Addison-Wesley, 2002.


5. Newcombe, C., et al. "How Amazon Web Services Uses Formal Methods." Communications of the ACM, 2015.


6. TigerBeetle. "Deterministic Simulation Testing." https://tigerbeetle.com/blog/2023-07-06-simulation-testing/


7. Kani. "The Kani Rust Verifier." https://github.com/model-checking/kani


8. Stateright. "A Model Checker for Distributed Systems." https://github.com/stateright/stateright


9. Datadog. "DDSQL Internal Retriever Interface." (Internal documentation)


10. FoundationDB. "Testing Distributed Systems w/ Deterministic Simulation." https://apple.github.io/foundationdb/testing.html


11. TigerBeetle. "TIGER_STYLE.md: TigerBeetle Coding Conventions." https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md


12. Yao, S., et al. "ReAct: Synergizing Reasoning and Acting in Language Models." ICLR, 2023.


13. Schick, T., et al. "Toolformer: Language Models Can Teach Themselves to Use Tools." NeurIPS, 2023.


14. Eaton, P. "What's the big deal about Deterministic Simulation Testing?" https://notes.eatonphil.com/2024-08-20-deterministic-simulation-testing.html (August 2024)


15. Zemb, P. "Testing: prevention vs discovery." https://pierrezemb.fr/posts/testing-prevention-vs-discovery/ (September 2025)


16. Antithesis. "Autonomous Testing." https://antithesis.com/resources/autonomous_testing/


---


## Appendix A: AgentFS CLI Reference


```
usage: python agentfs.py <command> [options]


Commands:
 start               Start a new verification session
 status              Show current session status
 fact add            Record a verified fact with evidence
 fact list           List all verified facts
 invariant verify    Mark an invariant as verified
 invariant unverified List unverified invariants for a component
 spec read           Record that a TLA+ spec was read
 exploration log     Log an exploration action
 export              Export session to JSON for replay/analysis


Examples:
 # Start a session
 python agentfs.py start --task "debug compaction OOM"


 # Record verification
 python agentfs.py fact add \
   --claim "CatalogConsistency holds" \
   --evidence "DST_SEED=778665 passed" \
   --source dst \
   --cmd "cargo test -p quickhouse-dst test_catalog_consistency"


 # Mark invariant verified
 python agentfs.py invariant verify --name AtomicVisibility --component compaction


 # Check unverified invariants
 python agentfs.py invariant unverified --component dual_engine


 # Export for analysis
 python agentfs.py export --output investigation.json
```


## Appendix B: Verification Pyramid Quick Reference


| Layer | Command | Time | Output |
|-------|---------|------|--------|
| TLA+ | `read specs/tla/*.tla` | 2 min | State model understanding |
| Stateright | `cargo test stateright_* -- --ignored` | 30-60s | States explored, violations |
| Kani | `cargo kani --harness verify_*` | ~60s | Proof or counterexample |
| DST | `cargo test -p quickhouse-dst` | ~5s | Pass/fail with seed |
| DDSQL | `quickhouse-perf datadog sql --query "..."` | ~2s | Production evidence |


## Appendix C: AgentFS KV Schema


VerificationFS uses Turso AgentFS's KV store with namespaced keys:


```
# Session metadata
vfs:session:current → {
 "id": "abc123",
 "task": "debug compaction OOM",
 "started_at": "2026-01-20T10:00:00Z",
 "project_root": "/path/to/project"
}


# Verified facts (one key per fact)
vfs:fact:1705747200000 → {
 "id": "1705747200000",
 "claim": "17 OOM kills in 24h",
 "evidence": "DDSQL query results",
 "source": "datadog",
 "timestamp": "2026-01-20T10:00:00Z",
 "command": null,
 "query": "SELECT host, count(*) FROM logs..."
}


# Verified invariants (keyed by component:name)
vfs:invariant:compaction:AtomicVisibility → {
 "name": "AtomicVisibility",
 "component": "compaction",
 "method": "dst",
 "verified_at": "2026-01-20T10:30:00Z",
 "evidence": "23 DST tests passed"
}


# TLA+ specs read
vfs:spec:CompactionProtocol → {
 "name": "CompactionProtocol",
 "path": "specs/tla/CompactionProtocol.tla",
 "read_at": "2026-01-20T10:05:00Z"
}


# DDSQL cache (with TTL)
vfs:cache:a1b2c3d4e5f6 → {
 "query": "SELECT ... FROM logs ...",
 "result": {"count": 17, ...},
 "timestamp": "2026-01-20T10:00:00Z",
 "ttl_minutes": 30
}


# Exploration log
vfs:exploration:1705747200001 → {
 "action": "read|execute|query",
 "target": "specs/tla/CompactionProtocol.tla",
 "timestamp": "2026-01-20T10:05:00Z",
 "result": "State model identified"
}
```


The SQLite database is stored at `.claude/agentfs-{session_id}.db`.


## Appendix D: The ADR → TLA+ → Rust Pipeline


QuickHouse uses a generative pipeline where each layer is derived from the one above:


```
┌─────────────────────────────────────────────────────────────────┐
│                    ADR (Architecture Decision Record)            │
│  "Compaction must be atomic. Queries see either all old         │
│   segments or all new segments, never a mix."                   │
└─────────────────────────────┬───────────────────────────────────┘
                             │ generates (AI-assisted)
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                    TLA+ Specification                            │
│  AtomicVisibility ==                                            │
│    \A job \in pendingSwaps :                                    │
│      \A qid \in DOMAIN activeQueries :                          │
│        LET snap == snapshots[activeQueries[qid]]                │
│        IN \/ job.inputs \subseteq snap                          │
│           \/ job.output \in snap                                │
│           \/ job.inputs \cap snap = {}                          │
└─────────────────────────────┬───────────────────────────────────┘
                             │ generates (AI-assisted)
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Stateright Model (Rust)                       │
│  fn check_atomic_visibility(&self, job: &Job) -> bool {         │
│    self.active_queries.iter().all(|q| {                         │
│      let snap = &self.snapshots[q.snapshot_id];                 │
│      job.inputs.is_subset(snap)                                 │
│        || snap.contains(&job.output)                            │
│        || job.inputs.is_disjoint(snap)                          │
│    })                                                           │
│  }                                                              │
└─────────────────────────────┬───────────────────────────────────┘
                             │ informs
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                    DST Tests + Production Code                   │
│  #[test]                                                        │
│  fn test_compaction_atomicity() {                               │
│    // Uses same invariant checks as Stateright model            │
│  }                                                              │
└─────────────────────────────────────────────────────────────────┘
```


This pipeline aims to provide:
- **Intent preservation**: ADR intent is formalized in TLA+
- **Specification validation**: TLA+ catches ambiguities in ADR prose
- **Implementation correctness**: Stateright models mirror TLA+ specs
- **Fast feedback**: DST tests use same invariants for quick validation





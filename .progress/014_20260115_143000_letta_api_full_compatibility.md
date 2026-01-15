# Task: 100% Complete Letta API Compatibility

**Created:** 2026-01-15 14:30:00
**Updated:** 2026-01-15 14:55:00 (Revised for 100% implementation)
**State:** PLANNING

---

## Vision Alignment

**Vision files read:**
- CONSTRAINTS.md
- CLAUDE.md
- LETTA_REPLACEMENT_GUIDE.md

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - All new tools need DST coverage
- TigerStyle safety principles (CONSTRAINTS.md §3) - 2+ assertions, explicit error handling
- No placeholders in production (CONSTRAINTS.md §4) - Full implementation, not stubs
- MCP server communication requires DST coverage (CONSTRAINTS.md §287)
- Tool execution with sandbox isolation requires DST coverage (CONSTRAINTS.md §285)
- Quality over speed (CONSTRAINTS.md §6) - Do it right, not fast

---

## Task Description

Currently Kelpie has ~90% Letta API compatibility (verified via testing and LETTA_REPLACEMENT_GUIDE.md). This task achieves **100% complete compatibility** with ZERO deferred features, allowing Kelpie to be a perfect drop-in replacement for Letta.

**Goals - ALL IMPLEMENTED:**
1. Fix the path difference for memory block updates
2. Add ALL missing built-in tools (`send_message`, `conversation_search_date`)
3. Add ALL missing prebuilt tools (`web_search`, `run_code`)
4. Implement custom tool execution for Python SDK compatibility (sandbox + source storage)
5. Complete MCP client execution wiring for ALL transports (stdio, HTTP, SSE)
6. Add ALL missing API endpoints (import/export, summarization, scheduling, projects, batch, agent groups)
7. Ensure all new features have full DST coverage per CONSTRAINTS.md
8. Achieve 100% API parity - NOTHING deferred

**Why this matters:**
- Kelpie can replace Letta in existing projects with ZERO code changes
- Full compatibility unlocks the entire Letta ecosystem
- No feature gaps - users get everything Letta offers plus Kelpie's advantages
- Demonstrates Kelpie's value proposition: "Same API, better foundation, nothing missing"

**Python SDK Compatibility Model:**

When a user uses the Letta Python SDK:
```python
from letta import LettaClient

# Point to Kelpie instead of Letta
client = LettaClient(base_url="http://localhost:8283")

# Define custom tool in Python
def weather(city: str) -> str:
    return f"Weather in {city}: Sunny"

# Register tool (sends schema + source code to server)
tool = client.tools.create(weather)

# Create agent with tool
agent = client.agents.create(
    name="weather-bot",
    tools=["weather", "web_search"]  # Mix custom + prebuilt
)
```

**How Kelpie handles this:**
1. **Tool Registration:** `POST /v1/tools` receives schema + Python source code
2. **Storage:** Store source code in FDB (keyed by tool name)
3. **Execution:** When agent calls tool:
   - Load source code from storage
   - Spawn ProcessSandbox with Python runtime
   - Inject environment (LETTA_AGENT_ID, LETTA_API_KEY, pre-initialized client)
   - Execute Python function with args
   - Return result to agent
4. **Sandboxing:** Per-tool isolation (NOT per-agent) with resource limits

**Key insight:** Letta runs as a **service** that executes user-defined Python code server-side in sandboxes. Kelpie must do the same for compatibility.

---

## Options & Decisions [REQUIRED]

### Decision 1: Path Compatibility Strategy

**Context:** Letta uses `/v1/agents/{id}/blocks/{label}` but Kelpie uses `/v1/agents/{id}/core-memory/blocks/{label}` for memory updates by label.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Alias Route | Add route alias for `/blocks/{label}` pointing to same handler | - Zero breaking changes<br>- Both paths work<br>- Simple change (5 lines) | - Two paths for same thing<br>- Slightly more routes |
| B: Rename Route | Change Kelpie's path to match Letta exactly | - Single canonical path<br>- Pure compatibility | - BREAKING CHANGE for existing users<br>- Need migration guide |
| C: Smart Router | Route based on parameter type (UUID=ID, string=label) | - Single path<br>- Auto-detect intent | - Magic behavior<br>- Harder to document<br>- Error-prone |

**Decision:** Option A - Alias Route

**Reasoning:**
1. Zero breaking changes - existing Kelpie users unaffected
2. Letta clients work immediately with no modifications
3. Simple implementation (one route definition)
4. Clear separation: `/blocks/{id}` for IDs, `/blocks/{label}` for labels, `/core-memory/blocks/{label}` for explicit memory ops
5. Can document both paths in API guide

**Trade-offs accepted:**
- Route duplication (minor - common pattern for API versioning)
- Slightly larger route table (negligible performance impact)
- Two ways to do the same thing (acceptable for backward compatibility)

---

### Decision 2: `send_message` Tool Implementation

**Context:** Letta has a `send_message` tool that agents use to send responses to users. Kelpie currently uses the LLM's direct response.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Intercept Tool | Add `send_message` as builtin that captures output | - Full Letta compatibility<br>- Agents control messaging<br>- Matches Letta semantics | - Changes response flow<br>- Need to handle multi-send<br>- More complex |
| B: Auto-wrapper | Automatically wrap LLM response as if `send_message` was called | - Transparent to agents<br>- No flow changes<br>- Simpler | - Not true compatibility<br>- May confuse agents expecting tool<br>- Less control |
| C: Dual Mode | Support both - tool if agent uses it, direct response otherwise | - Best of both worlds<br>- Flexible<br>- Gradual migration | - More complex<br>- Need clear docs<br>- Two code paths |

**Decision:** Option C - Dual Mode

**Reasoning:**
1. Kelpie agents that don't use `send_message` continue working (no breaking changes)
2. Letta agents migrating to Kelpie work exactly as expected
3. Agents can mix approaches (use tool for structured responses, direct for simple ones)
4. Clear upgrade path: start simple, add tool usage as needed
5. Aligns with "progressive enhancement" philosophy

**Trade-offs accepted:**
- More complex implementation (need to detect tool usage vs direct response)
- Two code paths to maintain (acceptable for compatibility)
- Need clear documentation on when to use which approach
- Slightly more testing surface area

---

### Decision 3: MCP Execution - ALL Transports

**Context:** MCP client architecture exists but `execute_mcp()` returns "not yet implemented". Letta supports 3 transports: stdio, HTTP (SSE), and HTTP (streaming).

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Full Implementation | Implement ALL 3 transports (stdio, HTTP, SSE) | - Complete feature<br>- Production ready<br>- ALL transports work<br>- 100% Letta parity | - Large scope<br>- 4-5 days work<br>- Complex HTTP handling |
| B: Stdio First | Implement stdio only, stub others | - Quick win<br>- Covers 80% use case | - NOT 100% compatible<br>- Incomplete feature<br>- REJECTED per user requirements |
| C: SimMcp Only | Keep DST-only, add to Phase 2/3 | - Focus on other features | - No real MCP support<br>- REJECTED per user requirements |

**Decision:** Option A - Full Implementation (ALL Transports)

**Reasoning:**
1. User requirement: "No deferring, 100% properly and fully implemented"
2. All 3 transports are needed for true Letta compatibility
3. Stdio: Local MCP servers (tools, scripts)
4. HTTP: Remote MCP servers with REST endpoints
5. SSE: Server-Sent Events for streaming/long-running operations
6. Existing architecture supports all 3 (just needs wiring)
7. DST coverage already exists via SimMcpClient

**Trade-offs accepted:**
- Larger scope (4-5 days vs 1 day)
- More complex implementation (HTTP client, SSE parsing)
- More test surface area (3x transport tests)
- Worth it for 100% compatibility

---

### Decision 4: API Endpoints - ALL Features

**Context:** Letta has several endpoints Kelpie lacks. User requires 100% implementation.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: ALL Endpoints | Implement EVERY missing endpoint | - 100% compatibility<br>- Nothing deferred<br>- Complete feature set | - Large scope (15+ days)<br>- High complexity |
| B: Core Only | Focus on high-value features | - Reasonable scope | - NOT 100% compatible<br>- REJECTED per user requirements |
| C: Defer Some | Ship iteratively | - Faster first version | - NOT 100% compatible<br>- REJECTED per user requirements |

**Decision:** Option A - ALL Endpoints

**Reasoning:**
1. User requirement: "I want everything 100% properly and fully implemented"
2. Required for true drop-in replacement
3. Each endpoint adds value to different use cases
4. Comprehensive implementation demonstrates commitment to compatibility
5. Prevents users from discovering "missing features" later

**Trade-offs accepted:**
- Very large scope (10-15 days total)
- High complexity (multiple subsystems)
- More maintenance burden (more code to support)
- Worth it for 100% compatibility and user satisfaction

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 14:35 | Use alias route for `/blocks/{label}` | Zero breaking changes, immediate compat | Route duplication |
| 14:40 | Implement dual-mode `send_message` | Support both Kelpie and Letta agent patterns | Two code paths |
| 14:45 | Implement ALL MCP transports (stdio, HTTP, SSE) | User requirement: 100% implementation | Larger scope, more complexity |
| 14:50 | Implement ALL API endpoints (no deferring) | User requirement: everything properly done | Very large scope (15+ days) |
| 14:55 | Revise plan for 100% completion | User feedback: no prioritization, no deferring | Extended timeline, higher effort |
| 15:30 | Add prebuilt tools (web_search, run_code) | Research revealed missing Letta prebuilt tools | +3 days scope |
| 15:35 | Local sandbox for run_code (not E2B) | Self-hosted philosophy, no cloud dependencies | More implementation work, security responsibility |
| 15:40 | Add custom tool execution (Python SDK) | Required for Letta Python SDK compatibility | +4 days scope, sandbox complexity |

---

### Decision 5: Prebuilt Tools Implementation

**Context:** Research revealed Letta has 2 prebuilt tools beyond base tools: `web_search` and `run_code`. These are critical for 100% compatibility.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Implement Both | Add web_search + run_code | - Complete compatibility<br>- Unlock key use cases<br>- Users expect these | - +3 days scope<br>- External dependencies (Tavily, sandbox) |
| B: Skip Prebuilt | Focus on base tools only | - Smaller scope | - NOT 100% compatible<br>- REJECTED per user requirements |

**Decision:** Option A - Implement Both

**Reasoning:**
1. User requirement: 100% compatibility
2. `web_search` is high-value (agents can search the web)
3. `run_code` is essential (agents can execute code)
4. Both are documented as "built-in" in Letta
5. Users migrating from Letta expect these to work

**Trade-offs accepted:**
- +3 days to timeline
- Tavily API dependency (can be self-hosted alternative later)
- Sandbox security responsibility for code execution

---

### Decision 6: run_code Sandbox Provider

**Context:** Letta uses E2B (cloud sandbox service). Kelpie could use E2B or local ProcessSandbox.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: E2B API | Use E2B like Letta | - Exact Letta parity<br>- Less code<br>- Security handled | - Cloud dependency<br>- Requires E2B_API_KEY<br>- Cost per execution |
| B: Local ProcessSandbox | Use Kelpie's existing sandbox | - Self-hosted<br>- No external dependencies<br>- No per-execution cost<br>- More control | - More implementation work<br>- Security responsibility |
| C: Both (pluggable) | Support E2B + local | - User choice<br>- Best of both | - Most complex<br>- Two code paths |

**Decision:** Option B - Local ProcessSandbox

**Reasoning:**
1. Aligns with Kelpie's self-hosted philosophy
2. Kelpie already has robust ProcessSandbox infrastructure
3. No cloud dependencies or API keys required
4. Full control over security and resource limits
5. No per-execution costs
6. Can add E2B support later if demanded

**Trade-offs accepted:**
- More implementation work (language runtimes, security hardening)
- Security is our responsibility
- Need to support Python, JS, TS, R, Java

---

### Decision 7: Custom Tool Execution (Python SDK)

**Context:** Letta Python SDK users define tools in Python that run on the server. Kelpie needs to execute these Python tools.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Full Python Sandbox | Store + execute Python code in sandbox | - True SDK compatibility<br>- Agents can use custom tools<br>- Same workflow as Letta | - +4 days scope<br>- Sandbox complexity<br>- Security critical |
| B: MCP Only | Force users to wrap tools as MCP servers | - Simpler server<br>- Security boundary clear | - NOT Letta compatible<br>- Breaking change for users<br>- REJECTED |
| C: Defer | Implement later | - Smaller initial scope | - NOT 100% compatible<br>- REJECTED per user requirements |

**Decision:** Option A - Full Python Sandbox

**Reasoning:**
1. User requirement: 100% compatibility
2. Letta Python SDK is the PRIMARY way users interact with Letta
3. Breaking this breaks the entire "drop-in replacement" promise
4. Custom tools are essential for real-world agents
5. Kelpie already has sandbox infrastructure (ProcessSandbox)
6. Can extend existing `run_code` sandbox implementation

**Trade-offs accepted:**
- +4 days to timeline
- Complex sandbox integration (environment injection, client pre-initialization)
- Security critical (arbitrary user code execution)
- Need dependency management (pip install)
- Per-tool sandboxing overhead

---

## Implementation Plan

### Phase 0: Path Alias (Quick Win - 15 min)
- [ ] Add `/v1/agents/{id}/blocks/{label}` route alias
- [ ] Point to existing `update_block_by_label` handler
- [ ] Add integration test for both paths
- [ ] Update LETTA_REPLACEMENT_GUIDE.md (mark as ✅)
- [ ] Commit: "feat: Add Letta-compatible route alias for memory blocks"

### Phase 1: Missing Built-in Tools (2 days)

#### 1.1: `send_message` Tool (1 day)
- [ ] Create `tools/messaging.rs` module
- [ ] Implement dual-mode message handling:
  - [ ] Detect when agent calls `send_message` tool
  - [ ] Capture tool call output
  - [ ] Support multiple `send_message` calls in one turn
  - [ ] Fall back to direct LLM response if no tool calls
- [ ] Register in UnifiedToolRegistry
- [ ] Update AgentActor to route messages appropriately
- [ ] Write unit tests:
  - [ ] Single send_message call
  - [ ] Multiple send_message calls
  - [ ] Mixed tool calls + send_message
  - [ ] Direct response (no send_message)
  - [ ] Empty message content
  - [ ] Large message content (>10KB)
- [ ] Write DST tests:
  - [ ] send_message with StorageWriteFail (0.2 probability)
  - [ ] Multiple sends with CrashAfterWrite
  - [ ] Concurrent send_message from multiple agents
  - [ ] send_message during NetworkPartition (message queuing)
- [ ] Integration test with real LLM

#### 1.2: `conversation_search_date` Tool (1 day)
- [ ] Extend existing conversation search in `tools/memory.rs`
- [ ] Add date range parsing:
  - [ ] ISO 8601 format support (2024-01-15T10:00:00Z)
  - [ ] RFC 3339 format support
  - [ ] Unix timestamp support
  - [ ] Relative dates (e.g., "last 7 days")
  - [ ] Timezone handling (UTC, local, specified)
- [ ] Implement date filtering in message queries
- [ ] Register as separate tool (for Letta compatibility)
- [ ] Write unit tests:
  - [ ] Valid date formats
  - [ ] Invalid formats (error handling)
  - [ ] Edge cases (year 2038, leap seconds)
  - [ ] Timezone conversions
  - [ ] Date range validation (start < end)
- [ ] Write integration tests:
  - [ ] Search messages from last week
  - [ ] Search between specific dates
  - [ ] Search with timezone offset
  - [ ] Empty results (no messages in range)
- [ ] Update default agent tools list
- [ ] Verify all tools appear in `GET /v1/tools`

### Phase 1.5: Prebuilt Tools (web_search, run_code) (3 days)

#### 1.5.1: `web_search` Tool (1 day)
- [ ] Research Tavily API integration:
  - [ ] Review Tavily API docs (https://docs.tavily.com/)
  - [ ] Understand request/response format
  - [ ] API key management (`TAVILY_API_KEY` env var)
- [ ] Implement `tools/web_search.rs`:
  - [ ] Create WebSearchTool struct
  - [ ] HTTP client for Tavily API
  - [ ] Request building (query, num_results, search_depth)
  - [ ] Response parsing (title, url, content, score)
  - [ ] Error handling (rate limits, API errors)
  - [ ] Timeout handling (10s default)
- [ ] Tool definition matching Letta schema:
  - [ ] Parameters: query (required), num_results (optional), search_depth (optional)
  - [ ] Return format: JSON array of results
- [ ] Register in UnifiedToolRegistry as prebuilt tool
- [ ] Write unit tests:
  - [ ] Query parsing
  - [ ] Result formatting
  - [ ] Error handling
- [ ] Write DST tests:
  - [ ] web_search with NetworkTimeout (0.2)
  - [ ] web_search with NetworkPartition (0.1)
  - [ ] web_search with rate limiting (429 errors)
  - [ ] Concurrent web_search calls (10+ simultaneous)
- [ ] Integration test with real Tavily API
- [ ] Document in LETTA_REPLACEMENT_GUIDE.md

#### 1.5.2: `run_code` Tool (2 days)
- [ ] **Decision**: E2B API vs Local Sandbox
  - Option A: E2B API (like Letta) - requires `E2B_API_KEY`, cloud dependency
  - Option B: Local ProcessSandbox - no dependencies, more control, security responsibility
  - **Chosen**: Option B (Local ProcessSandbox) - aligns with Kelpie's self-hosted philosophy
- [ ] Extend `ProcessSandbox` for code execution:
  - [ ] Add language detection (Python, JavaScript, TypeScript, R, Java)
  - [ ] Create runtime executors for each language:
    - [ ] PythonExecutor: `python3 -c "code"`
    - [ ] JavaScriptExecutor: `node -e "code"`
    - [ ] TypeScriptExecutor: `ts-node -e "code"`
    - [ ] RExecutor: `Rscript -e "code"`
    - [ ] JavaExecutor: compile + execute .class
  - [ ] Capture stdout/stderr
  - [ ] Parse execution results
  - [ ] Timeout enforcement (30s default, configurable)
  - [ ] Resource limits (memory, CPU)
- [ ] Environment injection:
  - [ ] `LETTA_AGENT_ID` - current agent ID
  - [ ] `LETTA_PROJECT_ID` - project ID (if applicable)
  - [ ] `LETTA_API_KEY` - API key for calling back to server
  - [ ] Pre-initialize Letta client in sandbox (import letta library)
- [ ] Implement `tools/code_execution.rs`:
  - [ ] Tool definition matching Letta schema
  - [ ] Parameters: language, code
  - [ ] Execute via ProcessSandbox
  - [ ] Return: stdout, stderr, exit_code, execution_time
- [ ] Security hardening:
  - [ ] Network isolation (no external network access by default)
  - [ ] Filesystem isolation (read-only except /tmp)
  - [ ] Process limits (no fork bombs)
  - [ ] Kill child processes on timeout
- [ ] Register in UnifiedToolRegistry
- [ ] Write unit tests:
  - [ ] Language detection
  - [ ] Code execution for each runtime
  - [ ] Timeout enforcement
  - [ ] Resource limit enforcement
- [ ] Write DST tests:
  - [ ] run_code with ProcessTimeout (0.2)
  - [ ] run_code with ProcessCrash (0.1)
  - [ ] run_code with ResourceExhaustion (memory limit)
  - [ ] Concurrent code execution (5+ sandboxes)
  - [ ] Malicious code handling (infinite loops, fork bombs)
- [ ] Integration tests:
  - [ ] Execute simple Python script → verify output
  - [ ] Execute JavaScript with imports → verify works
  - [ ] Execute code that times out → verify cleanup
  - [ ] Execute code with Letta client → verify can call API
- [ ] Document in LETTA_REPLACEMENT_GUIDE.md

### Phase 2: MCP Execution - ALL Transports (5 days)

#### 2.1: Stdio Transport (1 day)
- [ ] Review existing MCP client code (`kelpie-tools/src/mcp.rs`)
- [ ] Implement stdio execution:
  - [ ] Spawn child process with command + args
  - [ ] Setup stdin/stdout pipes
  - [ ] Send JSON-RPC initialize request
  - [ ] Read initialization response
  - [ ] Send tool execution request
  - [ ] Read execution response
  - [ ] Handle process cleanup (kill on drop)
- [ ] Add timeout handling (30s default, configurable per server)
- [ ] Add error conversion (McpError → ToolError)
- [ ] Write unit tests:
  - [ ] Process spawn and communication
  - [ ] JSON-RPC request formatting
  - [ ] Response parsing
  - [ ] Error message extraction
- [ ] Write DST tests:
  - [ ] Normal MCP tool execution
  - [ ] MCP process crash during init
  - [ ] MCP process crash during execution
  - [ ] MCP timeout (process hangs)
  - [ ] MCP invalid JSON response
  - [ ] Concurrent MCP calls to same server
  - [ ] Process resource exhaustion (CPUStarvation)
- [ ] Integration test with real MCP server (weather/calculator example)

#### 2.2: HTTP Transport (2 days)
- [ ] Implement HTTP MCP client:
  - [ ] POST request to MCP endpoint
  - [ ] JSON-RPC request body
  - [ ] Authentication header support (Bearer token)
  - [ ] Custom header support (API keys, etc.)
  - [ ] Response parsing
  - [ ] Error handling (4xx, 5xx)
  - [ ] Retry logic with exponential backoff
  - [ ] Circuit breaker pattern (stop calling failing servers)
- [ ] Add connection pooling (reuse HTTP connections)
- [ ] Add timeout handling (separate connect/read timeouts)
- [ ] Write unit tests:
  - [ ] HTTP request building
  - [ ] Header injection
  - [ ] Response parsing
  - [ ] Error code handling
- [ ] Write DST tests:
  - [ ] HTTP execution under NetworkPartition
  - [ ] HTTP timeout (slow server)
  - [ ] HTTP 500 errors (server failure)
  - [ ] HTTP connection refused (server down)
  - [ ] HTTP retry with backoff
  - [ ] Circuit breaker activation after N failures
  - [ ] Concurrent HTTP requests (connection pooling)
- [ ] Integration test with mockito HTTP server
- [ ] Integration test with real HTTP MCP endpoint

#### 2.3: SSE Transport (2 days)
- [ ] Implement SSE (Server-Sent Events) client:
  - [ ] HTTP GET to SSE endpoint
  - [ ] Parse SSE event stream format
  - [ ] Handle multi-line events
  - [ ] Event ID tracking (for resume)
  - [ ] Automatic reconnection on disconnect
  - [ ] Keepalive handling (heartbeat events)
  - [ ] Send tool execution via POST (separate from SSE stream)
  - [ ] Match responses to requests (correlation ID)
- [ ] Add connection lifecycle management:
  - [ ] Initial connection
  - [ ] Keep connection alive
  - [ ] Graceful disconnect
  - [ ] Reconnection with last event ID
- [ ] Write unit tests:
  - [ ] SSE event parsing
  - [ ] Multi-line data handling
  - [ ] Event ID extraction
  - [ ] Correlation ID matching
- [ ] Write DST tests:
  - [ ] SSE execution under NetworkPartition (reconnection)
  - [ ] SSE disconnect during execution (resume)
  - [ ] SSE keepalive timeout (reconnect)
  - [ ] SSE server restart (clean reconnect)
  - [ ] Multiple concurrent SSE connections
  - [ ] Event ordering verification
- [ ] Integration test with SSE mock server
- [ ] Integration test with real SSE MCP endpoint

#### 2.4: MCP Integration & Testing (remainder of Phase 2)
- [ ] Wire all transports to UnifiedToolRegistry
- [ ] Add transport selection logic (config-based)
- [ ] Document MCP setup in README for all transports
- [ ] Create example MCP server configs for each transport
- [ ] End-to-end test: stdio + HTTP + SSE all working

### Phase 3: API Endpoints - Import/Export (2 days)

#### 3.1: Export Implementation (1 day)
- [ ] Design export format:
  - [ ] JSON structure: {version, agent, blocks, sessions, messages, tools, metadata}
  - [ ] Version field: "1.0" for future compatibility
  - [ ] Include all agent data (name, type, allowed_tools, etc.)
  - [ ] Include all memory blocks (label, value, limit)
  - [ ] Include all sessions (checkpoints, tool calls, context)
  - [ ] Include all messages (full conversation history)
  - [ ] Include timestamps, creation dates
- [ ] Implement `GET /v1/agents/{id}/export`:
  - [ ] Fetch agent metadata from storage
  - [ ] Fetch all blocks
  - [ ] Fetch all sessions
  - [ ] Fetch all messages (paginate if needed)
  - [ ] Serialize to JSON
  - [ ] Return as downloadable file (Content-Disposition: attachment)
  - [ ] Add compression support (gzip) for large exports
- [ ] Add integration tests:
  - [ ] Export small agent (< 10 messages)
  - [ ] Export large agent (1000+ messages)
  - [ ] Export with no messages (new agent)
  - [ ] Export with special characters in content
- [ ] Write DST tests:
  - [ ] Export during StorageReadFail (retry logic)
  - [ ] Export during NetworkPartition (completion or failure)
  - [ ] Export of very large agent (memory limits)
  - [ ] Concurrent exports (multiple agents)

#### 3.2: Import Implementation (1 day)
- [ ] Implement `POST /v1/agents/import`:
  - [ ] Parse import JSON
  - [ ] Validate format version (reject if incompatible)
  - [ ] Validate structure (all required fields present)
  - [ ] Check for agent ID conflict (already exists)
  - [ ] Handle conflict strategies:
    - [ ] Fail (default): return error if exists
    - [ ] Replace: delete existing, create new
    - [ ] Merge: combine data (advanced)
  - [ ] Create agent with all data atomically (transaction)
  - [ ] Restore blocks, sessions, messages in correct order
  - [ ] Return created agent ID
- [ ] Add validation:
  - [ ] Required fields check
  - [ ] Data type validation
  - [ ] Size limits (reject extremely large imports)
  - [ ] Sanitization (prevent injection attacks)
- [ ] Add integration tests:
  - [ ] Import valid export file
  - [ ] Import with ID conflict (fail strategy)
  - [ ] Import with ID conflict (replace strategy)
  - [ ] Import corrupted file (error handling)
  - [ ] Import missing fields (validation errors)
  - [ ] Import with very large content
- [ ] Write DST tests:
  - [ ] Import during StorageWriteFail (rollback)
  - [ ] Import with CrashDuringTransaction (atomicity)
  - [ ] Import large agent with resource exhaustion
  - [ ] Concurrent imports (different agents)
  - [ ] Concurrent import + export (same agent)

### Phase 4: API Endpoints - Summarization (2 days)

#### 4.1: Summarization Core (1 day)
- [ ] Design summarization approach:
  - [ ] Use LLM to generate summary
  - [ ] Prompt engineering for good summaries
  - [ ] Configurable summary length (short, medium, long)
  - [ ] Preserve key facts, decisions, context
  - [ ] Maintain chronological flow
- [ ] Implement `POST /v1/agents/{id}/summarize`:
  - [ ] Parse request params:
    - [ ] message_count (last N messages) OR
    - [ ] start_date/end_date (date range)
    - [ ] summary_length (enum: short, medium, long)
    - [ ] save_to_archival (bool, default true)
  - [ ] Fetch messages based on params
  - [ ] Build summarization prompt
  - [ ] Call LLM (reuse RealLlmAdapter)
  - [ ] Extract summary from LLM response
  - [ ] Optionally save to agent's archival memory
  - [ ] Return summary text + metadata (message count, time range)
- [ ] Add prompt templates for different summary lengths:
  - [ ] Short: "Summarize in 1-2 sentences"
  - [ ] Medium: "Summarize in 1 paragraph (3-5 sentences)"
  - [ ] Long: "Summarize with key points and decisions"
- [ ] Add rate limiting (expensive operation):
  - [ ] Max 1 request per minute per agent
  - [ ] Max 10 requests per hour per agent
  - [ ] Return 429 Too Many Requests if exceeded
- [ ] Integration test with real LLM

#### 4.2: Summarization Edge Cases & Testing (1 day)
- [ ] Handle edge cases:
  - [ ] Empty conversation (no messages)
  - [ ] Single message (just return it)
  - [ ] Very short conversation (< 3 messages)
  - [ ] Very long conversation (> 10,000 messages, needs chunking)
  - [ ] Mixed media messages (text, tool calls, etc.)
- [ ] Add chunking for large conversations:
  - [ ] Split into chunks of N messages
  - [ ] Summarize each chunk
  - [ ] Combine chunk summaries into final summary
- [ ] Write unit tests:
  - [ ] Prompt building
  - [ ] Parameter parsing
  - [ ] Length selection
  - [ ] Rate limit enforcement
- [ ] Write DST tests:
  - [ ] Summarization during LLM timeout (retry)
  - [ ] Summarization with LLM failure (error handling)
  - [ ] Summarization with StorageWriteFail (archival save)
  - [ ] Concurrent summarization requests (rate limiting)
  - [ ] Summarization of very large conversation (chunking)
- [ ] Integration tests:
  - [ ] End-to-end: create agent → chat → summarize → verify summary
  - [ ] Verify summary saved to archival memory
  - [ ] Verify rate limiting works

### Phase 5: API Endpoints - Scheduling (2 days)

#### 5.1: Message Scheduling Core (1 day)
- [ ] Design scheduling system:
  - [ ] Persistent scheduled jobs (survive restarts)
  - [ ] Use job queue or timer wheel
  - [ ] Support one-time and recurring schedules
  - [ ] Timezone-aware scheduling
- [ ] Implement `POST /v1/agents/{id}/schedule`:
  - [ ] Parse schedule request:
    - [ ] message (content to send)
    - [ ] schedule_type (one_time, recurring)
    - [ ] scheduled_time (ISO 8601 datetime)
    - [ ] recurrence_rule (cron-like syntax for recurring)
    - [ ] timezone (default: UTC)
  - [ ] Validate schedule parameters
  - [ ] Store schedule in persistent storage
  - [ ] Return schedule ID
- [ ] Implement `GET /v1/agents/{id}/schedule`:
  - [ ] List all scheduled messages for agent
  - [ ] Include schedule ID, next run time, recurrence info
  - [ ] Support pagination
- [ ] Implement `DELETE /v1/agents/{id}/schedule/{schedule_id}`:
  - [ ] Cancel scheduled message
  - [ ] Remove from storage
  - [ ] Return success confirmation
- [ ] Create scheduler service:
  - [ ] Background task that checks for due schedules
  - [ ] Run every minute (configurable)
  - [ ] Execute scheduled messages by calling agent message endpoint
  - [ ] Handle failures (retry, dead letter queue)
  - [ ] Update next run time for recurring schedules

#### 5.2: Scheduling Integration & Testing (1 day)
- [ ] Add scheduler lifecycle management:
  - [ ] Start scheduler on server startup
  - [ ] Graceful shutdown (finish in-flight jobs)
  - [ ] Crash recovery (reschedule missed jobs)
- [ ] Write unit tests:
  - [ ] Schedule parsing and validation
  - [ ] Cron expression parsing
  - [ ] Timezone conversion
  - [ ] Next run time calculation
- [ ] Write DST tests:
  - [ ] Scheduled message execution under StorageWriteFail
  - [ ] Scheduler crash recovery (reschedule)
  - [ ] Concurrent schedule creation
  - [ ] Schedule execution during NetworkPartition
  - [ ] Clock skew handling (ClockJump)
- [ ] Integration tests:
  - [ ] Schedule one-time message → wait → verify sent
  - [ ] Schedule recurring message → verify multiple sends
  - [ ] Cancel scheduled message → verify not sent
  - [ ] Reschedule (update scheduled time)

### Phase 6: API Endpoints - Projects (2 days)

#### 6.1: Projects Core (1 day)
- [ ] Design project system:
  - [ ] Projects group related agents
  - [ ] Project metadata (name, description, owner, tags)
  - [ ] Agent-project associations (many-to-many)
  - [ ] Project-level permissions (future: RBAC)
- [ ] Implement `POST /v1/projects`:
  - [ ] Create new project
  - [ ] Parameters: name, description, tags, owner_id
  - [ ] Return project ID
- [ ] Implement `GET /v1/projects`:
  - [ ] List all projects
  - [ ] Support filtering (by owner, tag)
  - [ ] Support pagination
  - [ ] Return project list with metadata
- [ ] Implement `GET /v1/projects/{id}`:
  - [ ] Get project details
  - [ ] Include associated agents
  - [ ] Return full project info
- [ ] Implement `PATCH /v1/projects/{id}`:
  - [ ] Update project metadata
  - [ ] Support partial updates
- [ ] Implement `DELETE /v1/projects/{id}`:
  - [ ] Delete project
  - [ ] Option: cascade delete agents or just unassociate
  - [ ] Confirmation required for cascade

#### 6.2: Project-Agent Associations (1 day)
- [ ] Implement `POST /v1/projects/{id}/agents`:
  - [ ] Add agent to project
  - [ ] Parameters: agent_id
  - [ ] Handle duplicate adds (idempotent)
- [ ] Implement `DELETE /v1/projects/{id}/agents/{agent_id}`:
  - [ ] Remove agent from project
  - [ ] Agent still exists (just unassociated)
- [ ] Implement `GET /v1/projects/{id}/agents`:
  - [ ] List all agents in project
  - [ ] Support pagination
- [ ] Update `GET /v1/agents` to support project filtering:
  - [ ] Query param: project_id
  - [ ] Returns only agents in that project
- [ ] Write unit tests:
  - [ ] Project CRUD operations
  - [ ] Agent association/dissociation
  - [ ] Filtering and pagination
- [ ] Write DST tests:
  - [ ] Project creation with StorageWriteFail
  - [ ] Concurrent project updates
  - [ ] Cascade delete with agent associations
  - [ ] Project query under high load
- [ ] Integration tests:
  - [ ] Create project → add agents → query → delete
  - [ ] Multi-project agent (agent in 2+ projects)

### Phase 7: API Endpoints - Batch Operations (2 days)

#### 7.1: Batch Message Creation (1 day)
- [ ] Design batch system:
  - [ ] Accept array of message requests
  - [ ] Execute in parallel (thread pool)
  - [ ] Collect results (success/failure per message)
  - [ ] Return batch results with individual status
- [ ] Implement `POST /v1/agents/{id}/messages/batch`:
  - [ ] Parse batch request: array of {role, content}
  - [ ] Validate all messages before execution
  - [ ] Execute messages in parallel (up to N concurrent)
  - [ ] Track progress (% complete)
  - [ ] Handle partial failures (some succeed, some fail)
  - [ ] Return batch ID + results array
- [ ] Add batch status endpoint `GET /v1/agents/{id}/messages/batch/{batch_id}`:
  - [ ] Return batch execution status
  - [ ] Include completion percentage
  - [ ] List successful/failed messages
- [ ] Add limits:
  - [ ] Max batch size: 100 messages
  - [ ] Max concurrent executions per agent: 5
- [ ] Write unit tests:
  - [ ] Batch parsing
  - [ ] Parallel execution
  - [ ] Partial failure handling
  - [ ] Status tracking

#### 7.2: Batch Testing & Other Batch Operations (1 day)
- [ ] Implement `POST /v1/agents/batch`:
  - [ ] Create multiple agents in one request
  - [ ] Return array of created agent IDs
  - [ ] Handle partial failures
- [ ] Implement `DELETE /v1/agents/batch`:
  - [ ] Delete multiple agents by ID array
  - [ ] Return array of deletion statuses
- [ ] Write DST tests:
  - [ ] Batch message creation with StorageWriteFail (partial rollback)
  - [ ] Batch during LLM timeout (some succeed, some timeout)
  - [ ] Batch with concurrent regular messages (no deadlock)
  - [ ] Very large batch (100 messages, stress test)
  - [ ] Batch during resource exhaustion (CPUStarvation)
- [ ] Integration tests:
  - [ ] Batch create 50 messages → verify all saved
  - [ ] Batch with some failures → verify partial success
  - [ ] Concurrent batch operations

### Phase 8: API Endpoints - Agent Groups (2 days)

#### 8.1: Agent Groups Core (1 day)
- [ ] Design agent groups:
  - [ ] Groups enable multi-agent coordination
  - [ ] Group-level message routing
  - [ ] Group conversations (all agents participate)
  - [ ] Group state (shared context)
- [ ] Implement `POST /v1/agent-groups`:
  - [ ] Create agent group
  - [ ] Parameters: name, description, agent_ids[], routing_policy
  - [ ] Routing policies: round_robin, broadcast, intelligent
  - [ ] Return group ID
- [ ] Implement `GET /v1/agent-groups`:
  - [ ] List all agent groups
  - [ ] Support filtering by name
  - [ ] Support pagination
- [ ] Implement `GET /v1/agent-groups/{id}`:
  - [ ] Get group details
  - [ ] Include member agents
  - [ ] Include group state
- [ ] Implement `PATCH /v1/agent-groups/{id}`:
  - [ ] Update group (name, description, routing policy)
  - [ ] Add/remove agents
- [ ] Implement `DELETE /v1/agent-groups/{id}`:
  - [ ] Delete group (agents remain)

#### 8.2: Group Messaging & Coordination (1 day)
- [ ] Implement `POST /v1/agent-groups/{id}/messages`:
  - [ ] Send message to group
  - [ ] Route based on group policy:
    - [ ] Round-robin: next agent in rotation
    - [ ] Broadcast: all agents respond
    - [ ] Intelligent: LLM selects best agent
  - [ ] Aggregate responses if broadcast
  - [ ] Return response(s)
- [ ] Implement group state management:
  - [ ] Shared context across group members
  - [ ] State updates from any agent visible to all
  - [ ] Conflict resolution (last-write-wins or merge)
- [ ] Write unit tests:
  - [ ] Group CRUD operations
  - [ ] Routing policy logic
  - [ ] State management
  - [ ] Agent membership changes
- [ ] Write DST tests:
  - [ ] Group message broadcast under NetworkPartition
  - [ ] Group state updates with concurrent writes
  - [ ] Group deletion while messages in flight
  - [ ] Large group (100+ agents) stress test
- [ ] Integration tests:
  - [ ] Create group → send message → verify routing
  - [ ] Broadcast message → verify all agents respond
  - [ ] State updates visible across agents

### Phase 9: Custom Tool Execution - Python SDK Compatibility (4 days)

**Goal:** Enable Letta Python SDK users to define custom tools that execute in Kelpie.

**Current Problem:**
- Letta Python SDK users define tools like:
  ```python
  def my_tool(arg: str) -> str:
      return f"Result: {arg}"

  client.tools.create(my_tool)  # Sends to server
  ```
- Kelpie receives tool **schema** but NOT source code
- When agent calls tool, Kelpie has no code to execute
- **Result:** Custom tools fail

**Solution Architecture:**
```
Letta Python SDK → POST /v1/tools {schema, source_code, runtime}
                → Kelpie stores schema + code
                → Agent calls tool
                → Kelpie loads code from storage
                → Execute in ProcessSandbox
                → Return result to agent
```

#### 9.1: Tool Registration Enhancement (1 day)
- [ ] Extend `POST /v1/tools` endpoint:
  - [ ] Accept `source_code` field (Python function as string)
  - [ ] Accept `runtime` field (python, javascript, etc.)
  - [ ] Accept `requirements` field (pip packages, npm packages)
  - [ ] Validate source code (syntax check)
  - [ ] Generate unique tool ID
- [ ] Extend storage schema:
  - [ ] `tools/{tool_name}/schema` → ToolDefinition (existing)
  - [ ] `tools/{tool_name}/source_code` → String (NEW)
  - [ ] `tools/{tool_name}/runtime` → String (NEW)
  - [ ] `tools/{tool_name}/requirements` → Vec<String> (NEW)
  - [ ] `tools/{tool_name}/metadata` → created_at, updated_at (NEW)
- [ ] Update `UnifiedToolRegistry`:
  - [ ] Add `source_code` field to `RegisteredTool`
  - [ ] Add `runtime` field (enum: Python, JavaScript, TypeScript, etc.)
  - [ ] Load source code when tool is requested
- [ ] Write unit tests:
  - [ ] Tool registration with source code
  - [ ] Schema validation
  - [ ] Source code storage/retrieval
  - [ ] Invalid syntax rejection
- [ ] Write DST tests:
  - [ ] Tool registration with StorageWriteFail
  - [ ] Concurrent tool registrations
  - [ ] Tool retrieval with StorageReadFail

#### 9.2: Python Runtime Sandbox Integration (2 days)
- [ ] Extend `ProcessSandbox` for tool execution:
  - [ ] Add `execute_python_tool()` method
  - [ ] Accept: tool_name, source_code, args (JSON)
  - [ ] Build Python execution environment:
    - [ ] Create temp directory for tool
    - [ ] Write source code to file
    - [ ] Write args as JSON file
    - [ ] Create wrapper script that:
      - [ ] Imports tool function
      - [ ] Loads args from JSON
      - [ ] Calls function
      - [ ] Prints result as JSON
  - [ ] Inject environment variables:
    - [ ] `LETTA_AGENT_ID` - from execution context
    - [ ] `LETTA_PROJECT_ID` - from execution context
    - [ ] `LETTA_API_KEY` - for calling back to Kelpie API
    - [ ] `LETTA_BASE_URL` - Kelpie server URL
  - [ ] Pre-initialize Letta client:
    - [ ] Install letta SDK in sandbox (`pip install letta`)
    - [ ] Create client with injected credentials
    - [ ] Make available in tool execution context
- [ ] Sandbox security:
  - [ ] Network isolation (no external access except Kelpie API)
  - [ ] Filesystem isolation (read-only except /tmp)
  - [ ] Memory limits (256MB default)
  - [ ] CPU limits (1 core, 80% max)
  - [ ] Execution timeout (30s default)
  - [ ] Process limits (no child processes)
- [ ] Dependency management:
  - [ ] Parse `requirements` from tool metadata
  - [ ] Install packages in isolated venv
  - [ ] Cache venvs per tool (avoid repeated installs)
  - [ ] Timeout for package installation (5 min max)
- [ ] Write unit tests:
  - [ ] Python tool execution with args
  - [ ] Environment variable injection
  - [ ] Client pre-initialization
  - [ ] Dependency installation
  - [ ] Timeout enforcement
- [ ] Write DST tests:
  - [ ] Tool execution with ProcessTimeout (0.2)
  - [ ] Tool execution with ProcessCrash (0.15)
  - [ ] Tool execution with OutOfMemory (memory limit)
  - [ ] Tool calling back to Kelpie API (with NetworkPartition 0.1)
  - [ ] Concurrent tool executions (10+ simultaneous)

#### 9.3: Tool Execution Wiring & Testing (1 day)
- [ ] Wire `UnifiedToolRegistry.execute_custom()`:
  - [ ] Load tool from storage (schema + source_code)
  - [ ] Create execution context (agent_id, project_id, api_key)
  - [ ] Acquire sandbox from pool
  - [ ] Execute tool via sandbox
  - [ ] Capture result (success/failure, output, duration)
  - [ ] Release sandbox back to pool
  - [ ] Return ToolExecutionResult
- [ ] Update `AgentActor` to handle custom tools:
  - [ ] Detect custom tool calls from LLM
  - [ ] Route to `execute_custom()` instead of builtin handler
  - [ ] Handle tool execution errors gracefully
  - [ ] Log execution metrics (duration, success rate)
- [ ] Implement tool execution caching (optional):
  - [ ] Cache tool execution results for deterministic tools
  - [ ] Cache key: tool_name + args hash
  - [ ] TTL: 5 minutes default
  - [ ] Skip cache for tools with side effects
- [ ] Write integration tests:
  - [ ] End-to-end: Register Python tool → Create agent → Agent calls tool → Verify result
  - [ ] Tool that calls Kelpie API → Verify can access agent memory
  - [ ] Tool with dependencies → Verify packages installed and work
  - [ ] Tool execution failure → Verify agent handles gracefully
  - [ ] Concurrent agents calling same tool → Verify no interference
- [ ] Write DST tests:
  - [ ] Full workflow with storage + process + network faults
  - [ ] Multiple agents executing different custom tools
  - [ ] Custom tool calling another agent via API
  - [ ] Sandbox pool exhaustion (all sandboxes busy)
- [ ] Update LETTA_REPLACEMENT_GUIDE.md:
  - [ ] Document custom tool usage with Python SDK
  - [ ] Example: Define tool → Register → Use in agent
  - [ ] Security considerations
  - [ ] Performance tips (caching, dependencies)

### Phase 10: Documentation & Testing (3 days)

#### 9.1: Comprehensive Testing (2 days)
- [ ] Run full test suite (`cargo test`)
- [ ] Run all DST tests with multiple seeds (10+ random seeds)
- [ ] Run stress tests (high load, large data):
  - [ ] 1000+ concurrent message requests
  - [ ] Agent with 100,000+ messages (pagination)
  - [ ] 100+ MCP servers connected
  - [ ] 1000+ scheduled messages
  - [ ] 50+ active agent groups
- [ ] Run integration tests with real services:
  - [ ] Real LLM (Anthropic, OpenAI)
  - [ ] Real MCP servers (stdio, HTTP, SSE)
  - [ ] Real FDB backend (persistence across restarts)
- [ ] Run compatibility test suite:
  - [ ] Update `/tmp/test_kelpie_rest_api.py` for new endpoints
  - [ ] Test EVERY endpoint for Letta compatibility
  - [ ] Verify response formats match Letta exactly
- [ ] Performance benchmarking:
  - [ ] Message throughput (messages/sec)
  - [ ] MCP execution latency
  - [ ] Import/export time for various sizes
  - [ ] Memory usage under load
- [ ] Run clippy (`cargo clippy --all-targets --all-features`)
- [ ] Run formatter (`cargo fmt`)
- [ ] Run `/no-cap` verification

#### 9.2: Documentation Update (1 day)
- [ ] Update LETTA_REPLACEMENT_GUIDE.md:
  - [ ] Mark ALL features as ✅ (100% compatible)
  - [ ] Update compatibility percentage (90% → 100%)
  - [ ] Document ALL new tools and endpoints
  - [ ] Add examples for every new feature:
    - [ ] send_message tool usage
    - [ ] conversation_search_date examples
    - [ ] MCP setup (stdio, HTTP, SSE)
    - [ ] Import/export workflow
    - [ ] Summarization usage
    - [ ] Scheduling examples (one-time, recurring)
    - [ ] Project management
    - [ ] Batch operations
    - [ ] Agent groups
  - [ ] Add troubleshooting section
- [ ] Update main README.md:
  - [ ] Add "100% Letta Compatible" badge
  - [ ] Link to compatibility guide
  - [ ] Add feature comparison table
  - [ ] Highlight Kelpie advantages (Rust, FDB, DST)
- [ ] Create comprehensive migration guide:
  - [ ] Letta → Kelpie step-by-step instructions
  - [ ] Export agents from Letta
  - [ ] Import into Kelpie
  - [ ] MCP server migration
  - [ ] Tool mapping table (if any differences)
  - [ ] Configuration examples
  - [ ] Common issues and solutions
  - [ ] Performance tuning tips
- [ ] Create API reference documentation:
  - [ ] OpenAPI/Swagger spec generation
  - [ ] Endpoint documentation for ALL routes
  - [ ] Request/response examples
  - [ ] Error code reference
  - [ ] Rate limiting documentation
- [ ] Add runbook for operators:
  - [ ] Installation guide
  - [ ] Configuration reference
  - [ ] Monitoring setup (metrics, logs)
  - [ ] Backup/restore procedures
  - [ ] Disaster recovery
  - [ ] Performance tuning
  - [ ] Troubleshooting guide

---

## Checkpoints

- [ ] Codebase understood
- [ ] Plan approved ← **USER APPROVAL NEEDED**
- [ ] **Options & Decisions filled in** ✅
- [ ] **Quick Decision Log maintained** ✅
- [ ] Phase 0 complete (path alias - 15 min)
- [ ] Phase 1 complete (base tools - 2 days)
- [ ] Phase 1.5 complete (prebuilt tools - 3 days)
- [ ] Phase 2 complete (MCP all transports - 5 days)
- [ ] Phase 3 complete (import/export - 2 days)
- [ ] Phase 4 complete (summarization - 2 days)
- [ ] Phase 5 complete (scheduling - 2 days)
- [ ] Phase 6 complete (projects - 2 days)
- [ ] Phase 7 complete (batch - 2 days)
- [ ] Phase 8 complete (agent groups - 2 days)
- [ ] Phase 9 complete (custom tool execution - 4 days)
- [ ] Phase 10 complete (docs & testing - 3 days)
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned (DST coverage for ALL features)
- [ ] **DST coverage added** for:
  - [ ] send_message + conversation_search_date (Phase 1)
  - [ ] web_search + run_code (Phase 1.5)
  - [ ] MCP stdio + HTTP + SSE (all transports) (Phase 2)
  - [ ] Import/export with storage faults (Phase 3)
  - [ ] Summarization with LLM failures (Phase 4)
  - [ ] Scheduling with clock skew (Phase 5)
  - [ ] Projects with concurrent updates (Phase 6)
  - [ ] Batch operations with partial failures (Phase 7)
  - [ ] Agent groups with network partitions (Phase 8)
  - [ ] Custom tool execution with sandbox faults (Phase 9)
- [ ] **What to Try section updated** (after each phase)
- [ ] Committed (incremental commits per phase)
- [ ] 100% Letta compatibility verified

---

## Test Requirements

**Unit tests (EXTENSIVE):**
- Every new function has 2+ test cases
- Edge cases covered (empty input, max size, invalid format)
- Error paths tested (validation failures, constraints)
- Concurrent access patterns tested

**DST tests (MANDATORY per CONSTRAINTS.md):**
- [ ] ALL tools with storage/network/LLM faults
- [ ] ALL MCP transports with process/network faults
- [ ] ALL API endpoints with storage/concurrent access
- [ ] Stress tests (1000+ operations, 100+ agents)
- [ ] Determinism verification for ALL operations
- [ ] Fault injection probability: 0.1-0.3 (find bugs)
- [ ] Multiple seeds tested (10+)

**CRITICAL: What DST-First ACTUALLY Means:**

DST-first does NOT mean:
- ❌ Writing unit tests with mocks (MockStorage, MockLlm, etc.)
- ❌ Integration tests disguised as "DST"
- ❌ Standalone tests that happen to use some simulated components

DST-first MEANS:
- ✅ Running the ENTIRE Kelpie system in `Simulation::new(config).run_async(|sim_env| { ... })`
- ✅ Using `sim_env.storage` (SimStorage), `sim_env.clock` (SimClock), `sim_env.faults` (FaultInjector)
- ✅ Injecting REAL faults that ACTUALLY trigger during execution
- ✅ Testing the FULL system behavior under chaos, not isolated units

Example of TRUE DST (from agent_integration_dst.rs):
```rust
let result = Simulation::new(config)
    .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
    .run_async(|sim_env| async move {
        // This is FULL SYSTEM - not mocks
        let llm = Arc::new(SimLlmClient::new(
            sim_env.fork_rng_raw(),
            sim_env.faults.clone(),  // Real fault injection
        ));
        let agent_env = SimAgentEnv::new(
            sim_env.storage.clone(),  // SimStorage, not MockStorage
            llm,
            sim_env.clock.clone(),    // SimClock for time control
            sim_env.faults.clone(),
            sim_env.fork_rng(),
        );

        // Test feature - it ACTUALLY experiences faults
        let agent_id = agent_env.create_agent(config)?;
        agent_env.send_message(&agent_id, "test").await?;

        Ok(())
    })
    .await;
```

vs WRONG approach (NOT DST-first):
```rust
// ❌ WRONG - Unit test with mocks (NOT DST)
#[test]
fn test_with_mock() {
    let mock_storage = MockStorage::new();  // This is NOT DST
    let mock_llm = MockLlm::new();
    // ... test logic with mocks
}
```

**Integration tests:**
- End-to-end workflows for every feature
- Real LLM integration (requires API keys)
- Real MCP servers (stdio, HTTP, SSE examples)
- Real FDB backend (persistence, crash recovery)
- Cross-feature integration (e.g., scheduled batch messages)

**Compatibility tests:**
- Updated Python test script covering ALL endpoints
- Response format validation (matches Letta exactly)
- Error message validation (same error codes)
- Header validation (same headers)

**Commands:**
```bash
# Run all tests
cargo test

# Run DST tests
cargo test -p kelpie-dst
cargo test -p kelpie-server --features dst --test '*_dst'
cargo test -p kelpie-tools --features dst

# Reproduce DST failure
DST_SEED=12345 cargo test -p kelpie-dst test_mcp_http_execution

# Run Letta compatibility test
python3 /tmp/test_kelpie_rest_api.py

# Stress test
cargo test --release stress -- --ignored

# Run clippy
cargo clippy --all-targets --all-features

# Format code
cargo fmt

# Verify no placeholders
/no-cap

# Run specific phase tests
cargo test -p kelpie-server test_send_message
cargo test -p kelpie-tools test_mcp_stdio
```

---

## TRUE DST-First Approach Per Phase

This section shows how EACH phase uses TRUE Simulation harness (not mocks).

### Phase 0: Path Alias - No DST Needed
**Why:** Simple route alias, no business logic to test under faults.
**Test approach:** Integration test only (verify both paths work).

---

### Phase 1: Tools (send_message + conversation_search_date) - TRUE DST

**What TRUE DST looks like:**

```rust
// crates/kelpie-server/tests/send_message_tool_dst.rs

#[tokio::test]
async fn test_send_message_tool_with_storage_faults() {
    let config = SimConfig::new(42);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.2))
        .with_fault(FaultConfig::new(FaultType::LlmTimeout, 0.1))
        .run_async(|sim_env| async move {
            // Create FULL system in simulation
            let llm = Arc::new(SimLlmClient::new(
                sim_env.fork_rng_raw(),
                sim_env.faults.clone(),
            ));

            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),  // Real SimStorage, not mocks
                llm,
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            // Create agent and register send_message tool
            let agent_id = agent_env.create_agent(AgentTestConfig {
                tools: vec!["send_message".to_string()],
                ..Default::default()
            })?;

            // Send message that triggers tool usage
            // This ACTUALLY experiences storage faults (20% of writes fail)
            let response = agent_env
                .send_message(&agent_id, "Please use send_message to reply")
                .await?;

            // Verify send_message was captured
            assert!(response.content.contains("sent via tool"));

            // Try multiple calls - some will fail due to StorageWriteFail
            let mut success_count = 0;
            for i in 0..10 {
                match agent_env
                    .send_message(&agent_id, &format!("Message {}", i))
                    .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        // Storage fault triggered - this is REAL fault injection
                        assert!(e.to_string().contains("storage") || e.to_string().contains("timeout"));
                    }
                }
            }

            // With 20% + 10% = 30% fault rate, expect some failures
            assert!(success_count < 10, "Expected some failures with fault injection");
            assert!(success_count > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

**NOT this (WRONG - mocks):**
```rust
// ❌ WRONG - Unit test with mocks (NOT DST-first)
#[test]
fn test_send_message_with_mock() {
    let mock_storage = MockStorage::new();  // NOT DST
    let agent = Agent::new(mock_storage);
    agent.register_tool("send_message");
    // ... this is NOT DST-first
}
```

**conversation_search_date DST:**
```rust
#[tokio::test]
async fn test_conversation_search_date_with_faults() {
    let config = SimConfig::new(12345);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.2))
        .with_fault(FaultConfig::new(FaultType::StorageLatency, 0.3))
        .run_async(|sim_env| async move {
            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                Arc::new(SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone())),
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            let agent_id = agent_env.create_agent(AgentTestConfig::default())?;

            // Create conversation history
            for i in 0..20 {
                agent_env.send_message(&agent_id, &format!("Msg {}", i)).await?;
                sim_env.clock.advance_ms(3600_000); // 1 hour between messages
            }

            // Search with date range - REAL storage faults trigger
            let tool_input = json!({
                "start_date": "2024-01-15T00:00:00Z",
                "end_date": "2024-01-15T12:00:00Z"
            });

            // This call experiences REAL StorageReadFail (20%) and Latency (30%)
            let result = agent_env
                .execute_tool(&agent_id, "conversation_search_date", &tool_input)
                .await;

            // May fail due to storage faults - that's the point
            match result {
                Ok(results) => {
                    // Success despite faults (or no fault triggered)
                    assert!(results.is_array());
                }
                Err(e) => {
                    // Storage fault triggered
                    assert!(e.to_string().contains("storage"));
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 2: MCP Execution (ALL Transports) - TRUE DST

**What TRUE DST looks like for MCP:**

```rust
// crates/kelpie-tools/tests/mcp_stdio_dst.rs

#[tokio::test]
async fn test_mcp_stdio_with_process_faults() {
    let config = SimConfig::new(999);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::ProcessCrash, 0.15))
        .with_fault(FaultConfig::new(FaultType::ProcessTimeout, 0.1))
        .run_async(|sim_env| async move {
            // Create MCP client in simulation
            let mcp_config = McpConfig {
                transport: McpTransport::Stdio {
                    command: "python3".to_string(),
                    args: vec!["-m", "mcp_server_example"].iter().map(|s| s.to_string()).collect(),
                },
                timeout_ms: 5000,
            };

            let mcp_client = McpClient::new(
                mcp_config,
                sim_env.faults.clone(),  // Real fault injection
                sim_env.clock.clone(),
            );

            // Execute tool - REAL process faults trigger
            let tool_result = mcp_client
                .execute_tool("weather", json!({"location": "SF"}))
                .await;

            // With 15% ProcessCrash + 10% ProcessTimeout = 25% failure rate
            match tool_result {
                Ok(result) => {
                    // Success despite fault risk
                    assert!(result.is_string());
                }
                Err(e) => {
                    // Process fault triggered - REAL fault
                    let err_msg = e.to_string();
                    assert!(
                        err_msg.contains("process crash") || err_msg.contains("timeout"),
                        "Expected process fault, got: {}",
                        err_msg
                    );
                }
            }

            // Try multiple calls - verify some fail, some succeed
            let mut success = 0;
            let mut crash = 0;
            let mut timeout = 0;

            for _ in 0..20 {
                match mcp_client.execute_tool("test", json!({})).await {
                    Ok(_) => success += 1,
                    Err(e) => {
                        if e.to_string().contains("crash") {
                            crash += 1;
                        } else if e.to_string().contains("timeout") {
                            timeout += 1;
                        }
                    }
                }
            }

            // Verify faults actually triggered
            assert!(crash > 0 || timeout > 0, "Expected some faults to trigger");
            assert!(success > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

**MCP HTTP with Network Faults:**
```rust
#[tokio::test]
async fn test_mcp_http_with_network_faults() {
    let config = SimConfig::new(888);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::NetworkPartition, 0.1))
        .with_fault(FaultConfig::new(FaultType::NetworkDelay { min_ms: 100, max_ms: 500 }, 0.3))
        .run_async(|sim_env| async move {
            // Setup HTTP MCP server in simulation
            let mcp_config = McpConfig {
                transport: McpTransport::Http {
                    url: "http://localhost:8080/mcp".to_string(),
                    headers: HashMap::new(),
                },
                timeout_ms: 10000,
            };

            let mcp_client = McpClient::new(
                mcp_config,
                sim_env.faults.clone(),
                sim_env.clock.clone(),
            );

            let start = sim_env.clock.now_ms();

            // Execute tool - REAL network faults trigger
            let result = mcp_client
                .execute_tool("calculate", json!({"expr": "2+2"}))
                .await;

            let elapsed = sim_env.clock.now_ms() - start;

            // Network faults affect execution
            match result {
                Ok(val) => {
                    // May have experienced NetworkDelay (30% chance)
                    if elapsed > 100 {
                        // Delay fault triggered
                    }
                }
                Err(e) => {
                    // NetworkPartition fault triggered (10% chance)
                    assert!(e.to_string().contains("network"));
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

**MCP SSE with Reconnection:**
```rust
#[tokio::test]
async fn test_mcp_sse_with_disconnect_faults() {
    let config = SimConfig::new(777);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::NetworkPartition, 0.2))
        .run_async(|sim_env| async move {
            let mcp_config = McpConfig {
                transport: McpTransport::Sse {
                    url: "http://localhost:8080/sse".to_string(),
                    headers: HashMap::new(),
                },
                timeout_ms: 15000,
            };

            let mcp_client = McpClient::new(
                mcp_config,
                sim_env.faults.clone(),
                sim_env.clock.clone(),
            );

            // Connect - may experience NetworkPartition
            let connection_result = mcp_client.connect().await;

            if let Ok(conn) = connection_result {
                // Execute tool - connection may drop mid-execution
                let result = mcp_client.execute_tool("stream_data", json!({})).await;

                match result {
                    Ok(_) => {
                        // Success (no partition or reconnected)
                    }
                    Err(e) => {
                        // Partition during execution - verify reconnect attempted
                        assert!(e.to_string().contains("network") || e.to_string().contains("reconnect"));
                    }
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 3: Import/Export - TRUE DST

```rust
// crates/kelpie-server/tests/import_export_dst.rs

#[tokio::test]
async fn test_agent_export_with_storage_faults() {
    let config = SimConfig::new(555);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.2))
        .with_fault(FaultConfig::new(FaultType::StorageLatency, 0.3))
        .run_async(|sim_env| async move {
            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                Arc::new(SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone())),
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            // Create agent with data
            let agent_id = agent_env.create_agent(AgentTestConfig::default())?;
            for i in 0..100 {
                agent_env.send_message(&agent_id, &format!("Message {}", i)).await?;
            }

            // Export - REAL storage faults trigger during reads
            let export_result = agent_env.export_agent(&agent_id).await;

            match export_result {
                Ok(export_data) => {
                    // Success despite fault risk
                    assert!(export_data.contains_key("messages"));
                    assert_eq!(export_data["messages"].as_array().unwrap().len(), 100);
                }
                Err(e) => {
                    // Storage fault during export
                    assert!(e.to_string().contains("storage"));
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_agent_import_atomicity_with_crash() {
    let config = SimConfig::new(444);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashDuringTransaction, 0.3))
        .run_async(|sim_env| async move {
            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                Arc::new(SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone())),
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            let import_data = json!({
                "version": "1.0",
                "agent": {"name": "test", "type": "default"},
                "blocks": [{"label": "persona", "value": "You are helpful"}],
                "messages": [{"role": "user", "content": "Hello"}]
            });

            // Import - may crash mid-transaction
            let import_result = agent_env.import_agent(import_data).await;

            match import_result {
                Ok(agent_id) => {
                    // Success - verify atomicity (all data present or none)
                    let agent = agent_env.get_agent(&agent_id).await?;
                    assert_eq!(agent.name, "test");

                    let blocks = agent_env.get_blocks(&agent_id).await?;
                    assert_eq!(blocks.len(), 1);

                    let messages = agent_env.get_messages(&agent_id).await?;
                    assert_eq!(messages.len(), 1);
                }
                Err(e) => {
                    // Crash during import - verify nothing was created (atomicity)
                    assert!(e.to_string().contains("crash") || e.to_string().contains("transaction"));

                    // Verify no partial state (critical for atomicity)
                    // If agent was created, blocks and messages must also exist
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 4: Summarization - TRUE DST

```rust
// crates/kelpie-server/tests/summarization_dst.rs

#[tokio::test]
async fn test_summarization_with_llm_faults() {
    let config = SimConfig::new(333);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::LlmTimeout, 0.25))
        .with_fault(FaultConfig::new(FaultType::LlmRateLimit, 0.15))
        .run_async(|sim_env| async move {
            let llm = Arc::new(SimLlmClient::new(
                sim_env.fork_rng_raw(),
                sim_env.faults.clone(),
            ));

            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                llm,
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            let agent_id = agent_env.create_agent(AgentTestConfig::default())?;

            // Create conversation to summarize
            for i in 0..50 {
                agent_env.send_message(&agent_id, &format!("Message {}", i)).await?;
            }

            // Summarize - REAL LLM faults trigger
            let summary_result = agent_env
                .summarize_conversation(&agent_id, 50, SummaryLength::Medium)
                .await;

            match summary_result {
                Ok(summary) => {
                    // Success despite fault risk
                    assert!(!summary.text.is_empty());
                    assert_eq!(summary.message_count, 50);
                }
                Err(e) => {
                    // LLM fault triggered
                    let err_msg = e.to_string();
                    assert!(
                        err_msg.contains("timeout") || err_msg.contains("rate limit"),
                        "Expected LLM fault, got: {}",
                        err_msg
                    );
                }
            }

            // Test retry logic - try multiple times
            let mut success_count = 0;
            for _ in 0..10 {
                match agent_env
                    .summarize_conversation(&agent_id, 10, SummaryLength::Short)
                    .await
                {
                    Ok(_) => success_count += 1,
                    Err(_) => {
                        // Fault triggered
                    }
                }
            }

            // With 25% + 15% = 40% fault rate, expect some successes and failures
            assert!(success_count < 10, "Expected some failures");
            assert!(success_count > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 5: Scheduling - TRUE DST

```rust
// crates/kelpie-server/tests/scheduling_dst.rs

#[tokio::test]
async fn test_scheduling_with_clock_skew() {
    let config = SimConfig::new(222);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::ClockSkew, 0.2))
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .run_async(|sim_env| async move {
            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                Arc::new(SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone())),
                sim_env.clock.clone(),  // Critical: use SimClock
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            let agent_id = agent_env.create_agent(AgentTestConfig::default())?;

            // Schedule message for future
            let scheduled_time = sim_env.clock.now_ms() + 3600_000; // +1 hour
            let schedule_id = agent_env
                .schedule_message(&agent_id, "Scheduled message", scheduled_time)
                .await?;

            // Advance simulated time
            sim_env.clock.advance_ms(3600_000); // Advance 1 hour

            // Scheduler should fire - but ClockSkew may affect timing
            let scheduler = Scheduler::new(
                agent_env.clone(),
                sim_env.clock.clone(),
                sim_env.storage.clone(),
            );

            // Run scheduler tick - REAL clock faults trigger
            scheduler.tick().await?;

            // Check if message was sent (may be affected by ClockSkew)
            let messages = agent_env.get_messages(&agent_id).await?;

            // With ClockSkew, timing may be off but message should eventually send
            let scheduled_msg = messages.iter().find(|m| m.content.contains("Scheduled"));

            // Verify robustness despite clock faults
            assert!(
                scheduled_msg.is_some() || sim_env.clock.now_ms() < scheduled_time,
                "Scheduled message handling should be robust to clock skew"
            );

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 6: Projects - TRUE DST

```rust
// crates/kelpie-server/tests/projects_dst.rs

#[tokio::test]
async fn test_project_concurrent_updates() {
    let config = SimConfig::new(111);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.15))
        .run_async(|sim_env| async move {
            let project_manager = ProjectManager::new(
                sim_env.storage.clone(),
                sim_env.clock.clone(),
            );

            // Create project
            let project_id = project_manager
                .create_project("Test Project", "Description")
                .await?;

            // Concurrent updates from multiple tasks
            let handles: Vec<_> = (0..10)
                .map(|i| {
                    let pm = project_manager.clone();
                    let pid = project_id.clone();
                    tokio::spawn(async move {
                        pm.update_project_description(
                            &pid,
                            &format!("Updated by task {}", i),
                        )
                        .await
                    })
                })
                .collect();

            // Wait for all updates
            let results = futures::future::join_all(handles).await;

            // Some may fail due to StorageWriteFail, some succeed
            let successes = results.iter().filter(|r| r.is_ok()).count();
            let failures = results.len() - successes;

            // Verify system handles concurrent updates with faults
            assert!(successes > 0, "Expected some updates to succeed");

            // Final state should be consistent (last write wins)
            let project = project_manager.get_project(&project_id).await?;
            assert!(project.description.starts_with("Updated by task"));

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 7: Batch Operations - TRUE DST

```rust
// crates/kelpie-server/tests/batch_operations_dst.rs

#[tokio::test]
async fn test_batch_messages_with_partial_failures() {
    let config = SimConfig::new(100);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::LlmTimeout, 0.2))
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .run_async(|sim_env| async move {
            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                Arc::new(SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone())),
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            let agent_id = agent_env.create_agent(AgentTestConfig::default())?;

            // Batch of 20 messages
            let messages: Vec<_> = (0..20)
                .map(|i| MessageRequest {
                    role: "user".to_string(),
                    content: format!("Batch message {}", i),
                })
                .collect();

            // Send batch - REAL faults trigger for individual messages
            let batch_result = agent_env
                .send_batch_messages(&agent_id, messages)
                .await?;

            // Verify partial success/failure handling
            let successes = batch_result.iter().filter(|r| r.success).count();
            let failures = batch_result.len() - successes;

            // With 20% + 10% = 30% fault rate, expect some failures
            assert!(failures > 0, "Expected some batch items to fail with 30% fault rate");
            assert!(successes > 0, "Expected some batch items to succeed");

            // Verify system doesn't deadlock or cascade fail
            assert_eq!(batch_result.len(), 20, "All results should be returned");

            // Verify individual failures are isolated (no cascade)
            for (i, result) in batch_result.iter().enumerate() {
                if !result.success {
                    assert!(
                        result.error.as_ref().unwrap().contains("timeout")
                            || result.error.as_ref().unwrap().contains("storage"),
                        "Error for item {} should be timeout or storage",
                        i
                    );
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 8: Agent Groups - TRUE DST

```rust
// crates/kelpie-server/tests/agent_groups_dst.rs

#[tokio::test]
async fn test_agent_group_broadcast_with_network_partition() {
    let config = SimConfig::new(50);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::NetworkPartition, 0.3))
        .run_async(|sim_env| async move {
            let agent_env = SimAgentEnv::new(
                sim_env.storage.clone(),
                Arc::new(SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone())),
                sim_env.clock.clone(),
                sim_env.faults.clone(),
                sim_env.fork_rng(),
            );

            // Create multiple agents
            let agent_ids: Vec<_> = futures::future::join_all(
                (0..5).map(|_| agent_env.create_agent(AgentTestConfig::default()))
            )
            .await
            .into_iter()
            .collect::<Result<_>>()?;

            // Create agent group
            let group_manager = AgentGroupManager::new(
                sim_env.storage.clone(),
                agent_env.clone(),
            );

            let group_id = group_manager
                .create_group("Test Group", agent_ids.clone(), RoutingPolicy::Broadcast)
                .await?;

            // Send message to group - REAL network faults trigger
            let broadcast_result = group_manager
                .send_to_group(&group_id, "Broadcast message")
                .await;

            match broadcast_result {
                Ok(responses) => {
                    // Some agents may not respond due to NetworkPartition
                    // With 30% partition rate, expect 2-5 responses (not all 5)
                    assert!(
                        responses.len() < 5,
                        "Expected some agents unreachable due to network partition"
                    );
                    assert!(
                        !responses.is_empty(),
                        "Expected at least one agent to respond"
                    );
                }
                Err(e) => {
                    // Complete partition or majority unreachable
                    assert!(e.to_string().contains("network") || e.to_string().contains("partition"));
                }
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}
```

---

### Phase 9: Documentation & Testing - No DST (Meta-Phase)
**Why:** This phase runs and verifies ALL previous DST tests, doesn't add new features.

---

## Summary: TRUE DST-First Checklist

For EACH feature implementation:

✅ **DO:**
- Use `Simulation::new(config).with_fault(...).run_async(|sim_env| { ... })`
- Use `sim_env.storage`, `sim_env.clock`, `sim_env.faults`, `sim_env.rng`
- Inject REAL faults (StorageWriteFail, NetworkPartition, ProcessCrash, etc.)
- Verify feature works DESPITE faults
- Test partial failures, retries, atomicity
- Run with multiple seeds to verify determinism

❌ **DON'T:**
- Create MockStorage, MockLlm, or any mocks
- Write "unit tests" that don't use Simulation harness
- Call integration tests "DST" when they don't use sim_env
- Test features in isolation without fault injection
- Skip DST because "it's just a simple feature"

**Every phase (1-8) MUST have TRUE DST tests as shown above.**

---

## Fault Types Needed

Based on CONSTRAINTS.md §267, verify/add these fault types:

**Existing (✅):**
- `StorageWriteFail`, `StorageReadFail`, `StorageCorruption`, `StorageLatency`, `DiskFull`
- `CrashBeforeWrite`, `CrashAfterWrite`, `CrashDuringTransaction`
- `NetworkPartition`, `NetworkDelay`, `NetworkPacketLoss`, `NetworkMessageReorder`
- `ClockSkew`, `ClockJump`
- `OutOfMemory`, `CPUStarvation`

**May Need to Add (check kelpie-dst):**
- `ProcessCrash` - For MCP child process failures
- `ProcessTimeout` - For MCP command hangs
- `ProcessResourceExhaustion` - For MCP hitting resource limits
- `LlmTimeout` - For LLM API timeouts
- `LlmRateLimit` - For LLM 429 errors

**Action:** Check kelpie-dst/src/fault.rs for these. If missing, extend harness per CONSTRAINTS.md §37-42 BEFORE implementing relevant phases.

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 14:30 | CONSTRAINTS.md, CLAUDE.md, LETTA_REPLACEMENT_GUIDE.md | Initial planning |
| 14:35 | tools/memory.rs, tools/registry.rs | Existing tool structure |
| 14:40 | kelpie-tools/src/mcp.rs | MCP client architecture |
| 14:55 | Plan revised | User requirement: 100% implementation |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| Need user approval on 100% scope | OPEN | Get confirmation on timeline (20+ days) |
| May need to extend DST harness for process/LLM faults | CHECK | Verify fault types in kelpie-dst before Phase 2/4 |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Instance 1 | Planning | ACTIVE | 2026-01-15 14:55 |

---

## Findings

**Key discoveries:**
1. User requirement: "No deferring, 100% properly and fully implemented"
2. Scope significantly larger than initial plan (4-5 days → 20+ days)
3. Need ALL MCP transports (stdio, HTTP, SSE)
4. Need ALL API endpoints (import/export, summarization, scheduling, projects, batch, agent groups)
5. Each feature requires comprehensive DST coverage
6. Quality over speed - do it right

**Code locations:**
- Route definitions: `crates/kelpie-server/src/api/agents.rs`
- Tool registration: `crates/kelpie-server/src/tools/memory.rs`
- MCP client: `crates/kelpie-tools/src/mcp.rs`
- Tool registry: `crates/kelpie-server/src/tools/registry.rs`
- Fault types: `crates/kelpie-dst/src/fault.rs`

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| 90% Letta API compatibility | Run `python3 /tmp/test_kelpie_rest_api.py` | Most endpoints pass except blocks path |
| Memory tools | Use `core_memory_append`, `archival_memory_search` | Tools execute successfully |
| MCP DST testing | Run `cargo test -p kelpie-dst` | SimMcpClient tests pass |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| `/v1/agents/{id}/blocks/{label}` path | Need alias route | Phase 0 (15 min) |
| `send_message` tool | Not implemented | Phase 1 (day 2) |
| `conversation_search_date` tool | Not implemented | Phase 1 (day 2) |
| `web_search` tool | Not implemented | Phase 1.5 (day 5) |
| `run_code` tool | Not implemented | Phase 1.5 (day 5) |
| Custom Python tool execution | No sandbox integration | Phase 9 (day 26) |
| Letta Python SDK tool registration | No source code storage | Phase 9 (day 26) |
| Real MCP execution (stdio) | execute_mcp() not wired | Phase 2 (day 10) |
| Real MCP execution (HTTP) | Not implemented | Phase 2 (day 12) |
| Real MCP execution (SSE) | Not implemented | Phase 2 (day 14) |
| Agent import endpoint | Not implemented | Phase 3 (day 16) |
| Agent export endpoint | Not implemented | Phase 3 (day 16) |
| Conversation summarization | Not implemented | Phase 4 (day 18) |
| Message scheduling | Not implemented | Phase 5 (day 20) |
| Projects API | Not implemented | Phase 6 (day 22) |
| Batch operations | Not implemented | Phase 7 (day 24) |
| Agent groups | Not implemented | Phase 8 (day 26) |
| 100% Letta compatibility | All features need implementation | After Phase 10 (day 33) |

### Known Limitations ⚠️
- This is a LARGE scope (20+ days of work)
- Requires extending DST harness for new fault types
- Requires real LLM/MCP testing infrastructure
- Requires comprehensive documentation updates

---

## Estimated Timeline

**Total: 27-33 days (5-7 weeks full-time)**

- Phase 0: 15 minutes (path alias)
- Phase 1: 2 days (tools: send_message, conversation_search_date + DST)
- Phase 1.5: 3 days (prebuilt tools: web_search, run_code + DST)
- Phase 2: 5 days (MCP all transports + DST)
- Phase 3: 2 days (import/export + DST)
- Phase 4: 2 days (summarization + DST)
- Phase 5: 2 days (scheduling + DST)
- Phase 6: 2 days (projects + DST)
- Phase 7: 2 days (batch + DST)
- Phase 8: 2 days (agent groups + DST)
- Phase 9: 4 days (custom tool execution - Python SDK compatibility + DST)
- Phase 10: 3 days (comprehensive testing + docs)

**Note:** This assumes:
- Full-time focused work
- No major blockers
- DST harness already supports needed fault types (or quick to add)
- Incremental delivery (ship after each phase)

---

## Completion Notes

[To be filled after implementation]

**Verification Status:**
- Tests: [pass/fail with command output]
- Clippy: [clean/warnings with details]
- Formatter: [pass/fail]
- /no-cap: [pass/fail]
- Vision alignment: [confirmed/concerns]
- 100% Letta compatibility: [verified]

**DST Coverage:**
- Fault types tested: [complete list]
- Seeds tested: [10+ random seeds]
- Determinism verified: [yes/no for each feature]

**Key Decisions Made:**
- Path alias for backward compatibility
- Dual-mode send_message
- ALL MCP transports implemented (stdio, HTTP, SSE)
- ALL API endpoints implemented (scheduling, projects, batch, groups)
- Comprehensive DST coverage for every feature

**What to Try (Final):**
[To be updated after completion - should show 100% compatibility]

**Commits:** [hashes for each phase - 9 major commits expected]
**PR:** [link if applicable]

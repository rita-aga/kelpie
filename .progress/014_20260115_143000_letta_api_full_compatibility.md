# Task: Complete Letta API Compatibility

**Created:** 2026-01-15 14:30:00
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

Currently Kelpie has ~90% Letta API compatibility (verified via testing and LETTA_REPLACEMENT_GUIDE.md). This task addresses the remaining 10% to achieve 100% compatibility, allowing Kelpie to be a true drop-in replacement for Letta.

**Goals:**
1. Fix the path difference for memory block updates (easy win)
2. Add missing built-in tools (`send_message`, `conversation_search_date`)
3. Complete MCP client execution wiring
4. Add missing API endpoints (import/export, summarization, etc.)
5. Ensure all new features have DST coverage per CONSTRAINTS.md

**Why this matters:**
- Kelpie can replace Letta in existing projects with zero code changes
- Full compatibility unlocks the entire Letta ecosystem
- Demonstrates Kelpie's value proposition: "Same API, better foundation"

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

**Context:** Letta has a `send_message` tool that agents use to send responses to users. Kelpie currently uses the LLM's direct response. Need to decide how to implement compatibility.

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

### Decision 3: MCP Execution Wiring Priority

**Context:** MCP client architecture exists but `execute_mcp()` returns "not yet implemented". Need to decide implementation approach and priority.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Full Implementation | Wire up real MCP client with all 3 transports (stdio, HTTP, SSE) | - Complete feature<br>- Production ready<br>- All transports work | - Large scope<br>- 2-3 days work<br>- Delays other features |
| B: Stdio First | Implement stdio transport only, stub others | - Quick win (1 day)<br>- Covers 80% use case<br>- Unblocks testing | - Incomplete feature<br>- Need to finish later<br>- May disappoint HTTP users |
| C: SimMcp Only | Keep DST-only, add to Phase 2/3 | - Focuses on high-value features first<br>- DST coverage ready<br>- No prod complexity yet | - No real MCP support<br>- Misleading to users<br>- Blocks MCP-dependent workflows |

**Decision:** Option B - Stdio First

**Reasoning:**
1. 80/20 rule: stdio covers most MCP server use cases (local tools, scripts, etc.)
2. Quick implementation (~1 day) unblocks users immediately
3. Existing code structure supports incremental transport addition
4. Can ship this phase without waiting for HTTP/SSE complexity
5. DST coverage already exists via SimMcpClient
6. HTTP/SSE can follow in Phase 3 without blocking core features

**Trade-offs accepted:**
- Incomplete MCP support initially (document clearly)
- Need to return "transport not supported" for HTTP/SSE temporarily
- HTTP/SSE users must wait (acceptable - less common use case)
- Will need Phase 3 to complete MCP feature

---

### Decision 4: API Endpoint Priority

**Context:** Letta has several endpoints Kelpie lacks: import/export, summarization, scheduling, projects, batch. Need to prioritize.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: All At Once | Implement all missing endpoints in this task | - Complete compatibility<br>- One big push<br>- Nothing left behind | - Huge scope (10+ days)<br>- High risk<br>- May never finish |
| B: Core Only | Focus on import/export, summarization (high value) | - Reasonable scope (2-3 days)<br>- High-value features<br>- 95%+ compat | - Some endpoints missing<br>- Need Phase 3 for rest |
| C: Defer All | Focus on tools/MCP, save API endpoints for later | - Smallest scope<br>- Tools more important<br>- Ship faster | - Still incomplete<br>- Users expect full API<br>- Delays parity |

**Decision:** Option B - Core Only (Import/Export + Summarization)

**Reasoning:**
1. Import/export enables agent portability (critical for migrations)
2. Summarization is frequently used for long conversations
3. Scheduling/projects/batch are "nice to have" not "must have"
4. Gets us to 95%+ compatibility (good enough for "drop-in replacement" claim)
5. Keeps scope manageable (3-4 days total for this task)
6. Can add remaining endpoints in Phase 4 based on user feedback

**Trade-offs accepted:**
- Scheduling, projects, batch endpoints deferred to Phase 4
- Users needing those features must wait (document in README)
- Not 100% compatible yet (95%+ is close enough for now)
- May need another pass based on user requests

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 14:35 | Use alias route for `/blocks/{label}` | Zero breaking changes, immediate compat | Route duplication |
| 14:40 | Implement dual-mode `send_message` | Support both Kelpie and Letta agent patterns | Two code paths |
| 14:45 | Prioritize stdio MCP transport | 80% use case, quick win | HTTP/SSE delayed |
| 14:50 | Focus on import/export + summarization APIs | High value, reasonable scope | Defer scheduling/batch |

---

## Implementation Plan

### Phase 0: Path Alias (Quick Win - 15 min)
- [ ] Add `/v1/agents/{id}/blocks/{label}` route alias
- [ ] Point to existing `update_block_by_label` handler
- [ ] Add integration test for both paths
- [ ] Update LETTA_REPLACEMENT_GUIDE.md (mark as ✅)
- [ ] Commit: "feat: Add Letta-compatible route alias for memory blocks"

### Phase 1: Missing Built-in Tools (1 day)
- [ ] Implement `send_message` builtin tool
  - [ ] Create `tools/messaging.rs` module
  - [ ] Register in UnifiedToolRegistry
  - [ ] Dual-mode: capture tool calls OR use direct response
  - [ ] Update AgentActor to handle `send_message`
  - [ ] Write unit tests
  - [ ] Write DST test with fault injection (StorageWriteFail during message save)
- [ ] Implement `conversation_search_date` builtin tool
  - [ ] Add date range filtering to existing conversation search
  - [ ] Parse date parameters (ISO 8601, RFC 3339)
  - [ ] Update `tools/memory.rs`
  - [ ] Write unit tests for date parsing edge cases
  - [ ] Write integration test with date queries
- [ ] Update default agent tools list
- [ ] Verify all tools appear in `GET /v1/tools`
- [ ] Update LETTA_REPLACEMENT_GUIDE.md tool comparison table

### Phase 2: MCP Execution - Stdio Transport (1 day)
- [ ] Review existing MCP client code (`kelpie-tools/src/mcp.rs`)
- [ ] Implement `execute_mcp()` for stdio transport
  - [ ] Start child process with command
  - [ ] Send JSON-RPC request via stdin
  - [ ] Read JSON-RPC response from stdout
  - [ ] Handle process errors (crash, timeout)
  - [ ] Clean up child process resources
- [ ] Add timeout handling (30s default, configurable)
- [ ] Add error conversion (McpError → ToolError)
- [ ] Return "transport not supported" for HTTP/SSE (with clear error message)
- [ ] Write DST tests:
  - [ ] Normal MCP tool execution
  - [ ] MCP process crash during execution
  - [ ] MCP timeout (process hangs)
  - [ ] MCP invalid JSON response
  - [ ] Concurrent MCP calls to same server
- [ ] Integration test with real MCP server (weather/calculator example)
- [ ] Document stdio MCP setup in README
- [ ] Note: HTTP/SSE transports deferred to Phase 3

### Phase 3: API Endpoints - Import/Export (1 day)
- [ ] Design agent import/export format
  - [ ] JSON structure: {agent, blocks, sessions, messages}
  - [ ] Version field for future compat
  - [ ] Include metadata (created_at, etc.)
- [ ] Implement `GET /v1/agents/{id}/export`
  - [ ] Gather all agent data (metadata, blocks, sessions, messages)
  - [ ] Serialize to JSON
  - [ ] Return as downloadable file
  - [ ] Add integration test
- [ ] Implement `POST /v1/agents/import`
  - [ ] Parse import JSON
  - [ ] Validate format/version
  - [ ] Create agent with all data
  - [ ] Handle conflicts (agent ID already exists)
  - [ ] Add integration test
- [ ] Write DST tests:
  - [ ] Export during storage fault (retry logic)
  - [ ] Import with corrupted data (error handling)
  - [ ] Import of large agent (1000+ messages)
  - [ ] Concurrent export/import operations
- [ ] Document export/import in API guide

### Phase 4: API Endpoints - Summarization (1 day)
- [ ] Design summarization approach
  - [ ] Use LLM to summarize conversation
  - [ ] Configurable summary length
  - [ ] Preserve key facts/decisions
- [ ] Implement `POST /v1/agents/{id}/summarize`
  - [ ] Gather recent messages (last N or by date range)
  - [ ] Call LLM with summarization prompt
  - [ ] Return summary text
  - [ ] Add to agent's archival memory (optional)
  - [ ] Add integration test with real LLM
- [ ] Add rate limiting (expensive operation)
- [ ] Write DST tests:
  - [ ] Summarization during LLM timeout
  - [ ] Summarization of empty conversation
  - [ ] Concurrent summarization requests
  - [ ] Storage fault during archival save
- [ ] Document summarization in API guide
- [ ] Note: Scheduling/projects/batch deferred based on user demand

### Phase 5: Testing & Documentation (1 day)
- [ ] Run full test suite (`cargo test`)
- [ ] Run DST stress tests with multiple seeds
- [ ] Run clippy (`cargo clippy --all-targets --all-features`)
- [ ] Run formatter (`cargo fmt`)
- [ ] Run `/no-cap` verification
- [ ] Update LETTA_REPLACEMENT_GUIDE.md
  - [ ] Mark all implemented features as ✅
  - [ ] Update compatibility percentage (90% → 95%+)
  - [ ] Document new tools and endpoints
  - [ ] Add examples for new features
- [ ] Update main README.md
  - [ ] Add "Letta Compatible" badge/section
  - [ ] Link to compatibility guide
  - [ ] Add migration examples
- [ ] Create migration guide for Letta → Kelpie
  - [ ] Step-by-step instructions
  - [ ] Export/import process
  - [ ] Tool mapping table
  - [ ] Common issues and solutions
- [ ] Verify end-to-end with `/tmp/test_kelpie_rest_api.py`

---

## Checkpoints

- [ ] Codebase understood
- [ ] Plan approved ← **USER APPROVAL NEEDED**
- [ ] **Options & Decisions filled in** ✅
- [ ] **Quick Decision Log maintained** ✅
- [ ] Phase 0 complete (path alias)
- [ ] Phase 1 complete (tools)
- [ ] Phase 2 complete (MCP stdio)
- [ ] Phase 3 complete (import/export)
- [ ] Phase 4 complete (summarization)
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned (DST coverage for all critical paths)
- [ ] **DST coverage added** for:
  - [ ] `send_message` tool with faults
  - [ ] MCP stdio execution with crashes/timeouts
  - [ ] Import/export with storage faults
  - [ ] Summarization with LLM failures
- [ ] **What to Try section updated** (after each phase)
- [ ] Committed (incremental commits per phase)

---

## Test Requirements

**Unit tests:**
- `send_message` tool: happy path, empty content, large content
- `conversation_search_date`: valid dates, invalid formats, timezone handling, edge cases
- MCP stdio: request formatting, response parsing, error handling
- Import/export: JSON serialization, validation, conflict handling
- Summarization: prompt building, response parsing, length limits

**DST tests (MANDATORY per CONSTRAINTS.md):**
- [ ] `send_message` with StorageWriteFail (0.2 probability) - verify retry logic
- [ ] MCP stdio with process crash (CrashDuringExecution) - verify cleanup
- [ ] MCP stdio with timeout (30s) - verify timeout handling
- [ ] Import with corrupted data + StorageWriteFail - verify rollback
- [ ] Export during NetworkPartition - verify completion or clear failure
- [ ] Summarization with LLM timeout - verify graceful degradation
- [ ] Concurrent tool execution with resource exhaustion (CPUStarvation)
- [ ] Determinism verification: same seed = same output for all operations

**Integration tests:**
- End-to-end: Create agent → use new tools → export → delete → import → verify
- Letta compatibility: Run `/tmp/test_kelpie_rest_api.py` with new endpoints
- MCP: Test with real MCP server (weather example from MCP repo)
- Real LLM: Test summarization with actual API calls (requires ANTHROPIC_API_KEY)

**Commands:**
```bash
# Run all tests
cargo test

# Run DST tests specifically
cargo test -p kelpie-dst
cargo test -p kelpie-server --features dst --test '*_dst'

# Reproduce specific DST failure
DST_SEED=12345 cargo test -p kelpie-dst test_send_message_with_faults

# Run Letta compatibility test
python3 /tmp/test_kelpie_rest_api.py

# Run clippy
cargo clippy --all-targets --all-features

# Format code
cargo fmt

# Verify no placeholders
/no-cap
```

---

## Fault Types Needed

Based on CONSTRAINTS.md §267, verify these fault types are available in kelpie-dst:

- ✅ `StorageWriteFail` - For send_message, import, export
- ✅ `StorageReadFail` - For export, search operations
- ✅ `NetworkPartition` - For MCP execution, LLM calls
- ✅ `CrashDuringTransaction` - For import operations
- ❓ `ProcessCrash` - For MCP child process crashes (check if exists)
- ❓ `ProcessTimeout` - For MCP command timeouts (check if exists)
- ✅ `CPUStarvation` - For concurrent execution tests

**Action required:** If ProcessCrash/ProcessTimeout don't exist, extend harness per CONSTRAINTS.md §37-42 BEFORE implementing Phase 2.

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 14:30 | CONSTRAINTS.md, CLAUDE.md, LETTA_REPLACEMENT_GUIDE.md | Initial planning |
| | tools/memory.rs, tools/registry.rs | Understand existing tool structure |
| | kelpie-tools/src/mcp.rs | Review MCP client architecture |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| Need user approval on plan priority/scope | OPEN | Get feedback on Options & Decisions |
| May need to extend DST harness for process faults | CHECK | Verify ProcessCrash/Timeout exist in kelpie-dst |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Instance 1 | Planning | ACTIVE | 2026-01-15 14:30 |

---

## Findings

**Key discoveries:**
1. Route alias is simplest path to compatibility (no breaking changes)
2. MCP architecture is solid, just needs execution wiring
3. Dual-mode send_message preserves backward compat while adding Letta support
4. Import/export is essential for migrations (must prioritize)
5. Summarization is high-value but requires LLM interaction
6. DST coverage exists for storage/network, may need process-specific faults

**Code locations:**
- Route definitions: `crates/kelpie-server/src/api/agents.rs`
- Tool registration: `crates/kelpie-server/src/tools/memory.rs`
- MCP client: `crates/kelpie-tools/src/mcp.rs`
- Tool registry: `crates/kelpie-server/src/tools/registry.rs`

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
| `send_message` tool | Not implemented | Phase 1 (day 1) |
| `conversation_search_date` | Not implemented | Phase 1 (day 1) |
| Real MCP execution | execute_mcp() not wired | Phase 2 (day 2) |
| Agent import/export | Endpoints missing | Phase 3 (day 3) |
| Conversation summarization | Endpoint missing | Phase 4 (day 4) |
| 100% Letta compatibility | Some endpoints deferred | 95%+ after Phase 4, 100% in future |

### Known Limitations ⚠️
- MCP HTTP/SSE transports will return "not supported" initially (stdio only in Phase 2)
- Scheduling, projects, batch endpoints deferred to future work (based on user demand)
- Summarization requires ANTHROPIC_API_KEY or OPENAI_API_KEY
- Process crash faults for MCP may require harness extension (Phase 2 prerequisite)

---

## Estimated Timeline

**Total: 4-5 days**

- Phase 0: 15 minutes (path alias)
- Phase 1: 1 day (tools + DST tests)
- Phase 2: 1 day (MCP stdio + DST tests)
- Phase 3: 1 day (import/export + DST tests)
- Phase 4: 1 day (summarization + DST tests)
- Phase 5: 1 day (testing, docs, verification)

**Incremental delivery:** Ship after each phase (path alias can ship immediately, tools after Phase 1, etc.)

---

## Completion Notes

[To be filled after implementation]

**Verification Status:**
- Tests: [pass/fail with command output]
- Clippy: [clean/warnings with details]
- Formatter: [pass/fail]
- /no-cap: [pass/fail]
- Vision alignment: [confirmed/concerns]

**DST Coverage:**
- Fault types tested: [list]
- Seeds tested: [list or "randomized"]
- Determinism verified: [yes/no]

**Key Decisions Made:**
- Path alias for backward compatibility
- Dual-mode send_message
- Stdio-first MCP approach
- Prioritize import/export over scheduling/batch

**What to Try (Final):**
[To be updated after completion]

**Commit:** [hashes for each phase]
**PR:** [link if applicable]

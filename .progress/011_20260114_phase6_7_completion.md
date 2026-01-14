# Task: Complete Phases 6 & 7 (Plan 011)

**Created:** 2026-01-14 (after Phase 7.1-7.4 partial completion)
**State:** IN PROGRESS - Phases 6.6-6.7 Complete
**Parent Plans:**
- 007_20260113_actor_based_agent_server.md (Phases 6-7)
- 009_20260114_http_handler_migration.md (Phase 6 partial)
- 010_20260114_message_streaming_architecture.md (Phase 7 partial)

---

## Vision Alignment

**Constraints Applied:**
- **DST-first development** (write failing tests FIRST for every change)
- **Full simulation testing** (run with fault injection, verify determinism)
- Incremental migration (no big-bang changes)
- TigerStyle: Safety > Performance > DX
- Explicit error handling (no unwrap in production)

**Prior Work:**
- Phase 6: 5/6 handlers migrated (83%) - CRUD operations work
- Phase 7: Streaming infrastructure exists, but uses synthetic events
- AppState has dual-mode pattern proven safe
- 110 tests passing (105 + 5 streaming)

---

## Task Description

**Current State:**

**Phase 6 Remaining:**
- `send_message` handler (~300 lines) uses HashMap directly
- Agent loop logic (LLM + tools + history) in HTTP layer
- Message storage in HashMap, not in AgentActorState
- HashMap fields still present in AppState

**Phase 7 Remaining:**
- `send_message_stream()` emits synthetic events (wraps send_message)
- No true LLM token streaming (no `LlmClient::stream_complete()`)
- SSE endpoint not wired to AgentService
- No real-time token streaming UX

**Target State:**

**Phase 6 Complete:**
- Agent loop logic moved into AgentActor
- Message history stored in AgentActorState
- `send_message` handler uses AgentService
- HashMap fields removed from AppState
- All 6 handlers through AgentService (100%)

**Phase 7 Complete:**
- LlmClient trait has `stream_complete()` method
- RealLlmAdapter implements true streaming
- SSE endpoint wired to AgentService streaming
- Users see tokens appear in real-time

---

## Options & Decisions

### Decision 1: Agent Loop Architecture

**Question:** Where should agent message processing logic live?

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: HTTP Handler | Keep logic in handler, call through wrapper | Simple migration | Logic not reusable, violates layering |
| B: AgentActor | Move all logic into actor's handle_message | Clean architecture, reusable | Large refactoring, complex state management |
| C: Service Layer | Logic in AgentService, actor is thin | Middle ground | Service becomes complex |

**Decision:** **Option B - AgentActor**

**Reasoning:**
- Agent message processing is core actor behavior
- Enables actor-to-actor messaging (future)
- State management (messages, iterations) belongs in actor
- Aligns with virtual actor model (self-contained state)
- Testable via AgentService without HTTP layer

**Trade-offs Accepted:**
- More complex actor implementation (~500 lines)
- Message history state management in actor
- Need to handle tool execution in actor context

### Decision 2: Message History Storage

**Question:** How to store message history in actor?

| Option | Approach | Pros | Cons |
|--------|----------|------|------|
| A: In-Memory Vector | `Vec<Message>` in AgentActorState | Simple, fast | Limited to working set size |
| B: KV Storage | Store each message with key `msg:{id}` | Persistent, scalable | More complex, slower |
| C: Hybrid | Recent N in memory, rest in KV | Best of both | Most complex |

**Decision:** **Option A - In-Memory Vector (for now)**

**Reasoning:**
- Simplest for initial migration
- Matches current HashMap behavior
- Can migrate to Option C in Phase 8 (FDB integration)
- AgentActorState already persisted to KV on deactivation

**Trade-offs Accepted:**
- Limited message history (will truncate to last N)
- Full history loaded on activation (could be slow)
- Will need Phase 8 migration for large history

### Decision 3: LLM Streaming Approach

**Question:** How to implement true LLM token streaming?

| Option | Approach | Pros | Cons |
|--------|----------|------|------|
| A: Callback | `stream_complete(messages, on_token: impl Fn(String))` | Simple | Hard to integrate with channels |
| B: Stream Trait | `stream_complete() -> impl Stream<Item=String>` | Idiomatic Rust | Requires async-stream dependency |
| C: Channel | `stream_complete(tx: mpsc::Sender<String>)` | Matches our pattern | Less idiomatic |

**Decision:** **Option B - Stream Trait**

**Reasoning:**
- Most idiomatic Rust async
- Easy to convert to mpsc channel at call site
- Aligns with Axum SSE patterns
- Backpressure built-in

**Implementation:**
```rust
#[async_trait]
pub trait LlmClient: Send + Sync {
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse>;

    // Phase 7: Streaming method
    async fn stream_complete(
        &self,
        messages: Vec<LlmMessage>
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>>;
}

pub enum StreamChunk {
    ContentDelta { delta: String },
    ToolCallStart { id: String, name: String },
    ToolCallDelta { id: String, delta: String },
    Done { stop_reason: String },
}
```

### Decision 4: DST Test Strategy

**Question:** How to test agent message handling with DST?

| Option | Coverage | Approach |
|--------|----------|----------|
| A: Unit Tests | Actor methods only | Fast, isolated |
| B: Integration Tests | Through AgentService | More realistic |
| C: End-to-End Tests | HTTP → Service → Actor | Complete, slow |

**Decision:** **Option B - Integration Tests (AgentService level)**

**Reasoning:**
- Tests the full actor integration path
- Can inject faults at storage/network layer
- Faster than E2E HTTP tests
- Still validates actor behavior
- HTTP handlers become thin wrappers (tested separately)

**DST Test Coverage:**
1. `test_dst_agent_message_basic` - Simple message, LLM response
2. `test_dst_agent_message_with_tool_call` - Tool execution loop
3. `test_dst_agent_message_with_storage_fault` - StorageWriteFail injection
4. `test_dst_agent_message_history` - Message history preserved
5. `test_dst_agent_message_concurrent` - Multiple agents, same time
6. `test_dst_agent_llm_token_streaming` - Real-time token stream
7. `test_dst_agent_streaming_with_tools` - Streaming + tool calls

---

## Implementation Phases

### Phase 6.6: Write Agent Message DST Tests (FIRST!)

**Objective:** Define agent message handling contract through failing tests.

**Files:**
- `crates/kelpie-server/tests/agent_message_handling_dst.rs` (new)

**Tests to Write:**

1. **test_dst_agent_message_basic**
   - Create agent via service
   - Send user message via service.send_message()
   - Assert: Response from LLM
   - Assert: Message history updated
   - Assert: State persisted

2. **test_dst_agent_message_with_tool_call**
   - Send message that triggers tool call
   - Assert: Tool executed
   - Assert: Tool result fed back to LLM
   - Assert: Final response includes tool output

3. **test_dst_agent_message_with_storage_fault**
   - Enable StorageWriteFail (0.3 probability)
   - Send message
   - Assert: Either succeeds or retries correctly
   - Assert: No data corruption

4. **test_dst_agent_message_history**
   - Send 3 messages sequentially
   - Deactivate actor (simulate restart)
   - Reactivate and send 4th message
   - Assert: LLM sees full history in context

5. **test_dst_agent_message_concurrent**
   - Create 10 agents
   - Send messages to all simultaneously
   - Assert: All get correct responses
   - Assert: No message mixing between agents

**Success Criteria:**
- All 5 tests compile
- All 5 tests FAIL (no implementation yet)
- Tests clearly define message handling contract

### Phase 6.7: Add Message History to AgentActorState

**Objective:** Extend actor state to store message history.

**Files:**
- `crates/kelpie-server/src/actor/state.rs`

**Changes:**
```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentActorState {
    /// Agent metadata and blocks
    pub agent: Option<AgentState>,

    /// Message history (recent N messages)
    pub messages: Vec<Message>,

    /// Maximum messages to keep in memory
    #[serde(default = "default_max_messages")]
    pub max_messages: usize,
}

fn default_max_messages() -> usize {
    100
}

impl AgentActorState {
    /// Add message to history
    pub fn add_message(&mut self, message: Message) {
        self.messages.push(message);

        // Truncate if exceeds max
        if self.messages.len() > self.max_messages {
            let start = self.messages.len() - self.max_messages;
            self.messages = self.messages[start..].to_vec();
        }
    }

    /// Get recent messages
    pub fn recent_messages(&self, limit: usize) -> &[Message] {
        let start = self.messages.len().saturating_sub(limit);
        &self.messages[start..]
    }
}
```

**Verification:**
- Code compiles
- State serializes/deserializes correctly
- Truncation works (test with 101 messages)

### Phase 6.8: Implement AgentActor::handle_message with Tools

**Objective:** Move agent loop logic into actor.

**Files:**
- `crates/kelpie-server/src/actor/agent_actor.rs`

**Changes:**
```rust
impl AgentActor {
    /// Handle message with full agent loop (LLM + tools)
    async fn handle_message_full(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        request: HandleMessageFullRequest,
    ) -> Result<HandleMessageFullResponse> {
        // 1. Get agent state
        let agent = ctx.state.agent().ok_or(...)?;

        // 2. Add user message to history
        let user_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            role: MessageRole::User,
            content: request.content.clone(),
            // ...
        };
        ctx.state.add_message(user_msg.clone());

        // 3. Build LLM prompt from agent blocks + history
        let mut llm_messages = Vec::new();

        // System prompt
        if let Some(system) = &agent.system {
            llm_messages.push(LlmMessage {
                role: "system".to_string(),
                content: system.clone(),
            });
        }

        // Memory blocks
        for block in &agent.blocks {
            llm_messages.push(LlmMessage {
                role: "system".to_string(),
                content: format!("[{}]\n{}", block.label, block.value),
            });
        }

        // Recent message history (last 20)
        for msg in ctx.state.recent_messages(20) {
            llm_messages.push(LlmMessage {
                role: msg.role.as_str().to_string(),
                content: msg.content.clone(),
            });
        }

        // 4. Call LLM
        let mut response = self.llm.complete(llm_messages.clone()).await?;
        let mut iterations = 0;
        let max_iterations = 5;

        // 5. Tool execution loop
        while !response.tool_calls.is_empty() && iterations < max_iterations {
            iterations += 1;

            // Execute each tool
            for tool_call in &response.tool_calls {
                let result = self.execute_tool(ctx, tool_call).await?;

                // Add tool result to message history
                let tool_msg = Message {
                    id: uuid::Uuid::new_v4().to_string(),
                    agent_id: ctx.id.id().to_string(),
                    role: MessageRole::Tool,
                    content: result,
                    tool_call_id: Some(tool_call.id.clone()),
                    // ...
                };
                ctx.state.add_message(tool_msg);
            }

            // Continue conversation with tool results
            // (rebuild llm_messages with tool results)
            response = self.llm.complete(llm_messages).await?;
        }

        // 6. Add assistant response to history
        let assistant_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            role: MessageRole::Assistant,
            content: response.content.clone(),
            // ...
        };
        ctx.state.add_message(assistant_msg.clone());

        // 7. Return response
        Ok(HandleMessageFullResponse {
            messages: vec![user_msg, assistant_msg],
            usage: UsageStats {
                prompt_tokens: response.prompt_tokens,
                completion_tokens: response.completion_tokens,
            },
        })
    }

    /// Execute a tool call
    async fn execute_tool(
        &self,
        ctx: &ActorContext<AgentActorState>,
        tool_call: &LlmToolCall,
    ) -> Result<String> {
        match tool_call.name.as_str() {
            "shell" => {
                let command = tool_call.input
                    .get("command")
                    .and_then(|v| v.as_str())
                    .ok_or(...)?;

                // TODO: Integrate with sandbox
                // For now, return placeholder
                Ok(format!("Shell command '{}' executed", command))
            }
            _ => Err(Error::Internal {
                message: format!("Unknown tool: {}", tool_call.name),
            }),
        }
    }
}
```

**Verification:**
- Code compiles
- `test_dst_agent_message_basic` → PASSES
- `test_dst_agent_message_with_tool_call` → PASSES
- `test_dst_agent_message_history` → PASSES

### Phase 6.9: Update AgentService for Message Handling

**Objective:** Add service method for full message handling.

**Files:**
- `crates/kelpie-server/src/service/mod.rs`

**Changes:**
```rust
impl AgentService {
    /// Send message with full agent loop (LLM + tools + history)
    pub async fn send_message_full(
        &self,
        agent_id: &str,
        content: String,
    ) -> Result<HandleMessageFullResponse> {
        let actor_id = ActorId::new("agents", agent_id)?;

        let request = HandleMessageFullRequest { content };
        let payload = serde_json::to_vec(&request)?;

        let response = self
            .dispatcher
            .invoke(actor_id, "handle_message_full".to_string(), Bytes::from(payload))
            .await?;

        serde_json::from_slice(&response).map_err(...)
    }
}
```

**Verification:**
- Service method works
- DST tests pass through service layer

### Phase 6.10: Migrate send_message HTTP Handler

**Objective:** Update HTTP handler to use AgentService.

**Files:**
- `crates/kelpie-server/src/api/messages.rs`

**Changes:**
```rust
async fn send_message_json(
    state: AppState,
    agent_id: String,
    request: CreateMessageRequest,
) -> Result<Response, ApiError> {
    let (role, content) = request.effective_content()
        .ok_or_else(|| ApiError::bad_request("message content cannot be empty"))?;

    // Use AgentService if available, otherwise fallback
    let response = if let Some(service) = state.agent_service() {
        // Actor-based path
        service.send_message_full(&agent_id, content).await?
    } else {
        // HashMap fallback (for backward compat during transition)
        // ... existing logic
    };

    Ok(Json(MessageResponse {
        messages: response.messages,
        usage: Some(response.usage),
        stop_reason: "end_turn".to_string(),
    }).into_response())
}
```

**Verification:**
```bash
# Manual test
curl -X POST http://localhost:8283/v1/agents/{id}/messages \
  -H "Content-Type: application/json" \
  -d '{"role":"user","content":"Hello!"}'
```

### Phase 6.11: Remove HashMap Fields from AppState

**Objective:** Clean up after all handlers migrated.

**Files:**
- `crates/kelpie-server/src/state.rs`

**Changes:**
```rust
pub struct AppStateInner {
    // REMOVE these:
    // agents: HashMap<String, AgentState>,
    // messages: HashMap<String, Vec<Message>>,

    // KEEP these:
    agent_service: Option<AgentService>,
    dispatcher_handle: Option<DispatcherHandle>,
    // ...
}
```

**Remove Methods:**
- `get_agent()` (sync HashMap lookup)
- `create_agent()` (sync HashMap insert)
- All sync HashMap-based methods

**Keep Methods:**
- `get_agent_async()` (calls service)
- `create_agent_async()` (calls service)
- All dual-mode async methods

**Verification:**
```bash
cargo test -p kelpie-server
# All 110+ tests must pass
# No clippy warnings about unused fields
```

### Phase 7.6: Write LLM Streaming DST Tests (FIRST!)

**Objective:** Define LLM streaming contract through tests.

**Files:**
- `crates/kelpie-server/tests/llm_token_streaming_dst.rs` (new)

**Tests to Write:**

1. **test_dst_llm_token_streaming_basic**
   - Call stream_complete() with SimLlmClient
   - Collect all chunks
   - Assert: Tokens arrive incrementally
   - Assert: Concatenated chunks == full response

2. **test_dst_llm_streaming_with_network_delay**
   - Enable NetworkDelay fault
   - Stream tokens
   - Assert: Stream completes despite delays
   - Assert: No tokens lost

3. **test_dst_llm_streaming_cancellation**
   - Start streaming
   - Drop stream consumer after 3 tokens
   - Assert: Stream stops cleanly
   - Assert: No panic or resource leak

**Success Criteria:**
- All 3 tests compile
- All 3 tests FAIL (no stream_complete yet)

### Phase 7.7: Extend LlmClient Trait for Streaming

**Objective:** Add streaming method to trait.

**Files:**
- `crates/kelpie-server/src/actor/llm_trait.rs`

**Changes:**
```rust
use futures::stream::Stream;
use std::pin::Pin;

#[async_trait]
pub trait LlmClient: Send + Sync {
    /// Complete a chat conversation (batch)
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse>;

    /// Complete with streaming (real-time tokens)
    async fn stream_complete(
        &self,
        messages: Vec<LlmMessage>,
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>> {
        // Default implementation: convert batch to stream
        let response = self.complete(messages).await?;
        let chunks = vec![
            StreamChunk::ContentDelta { delta: response.content },
            StreamChunk::Done { stop_reason: "end_turn".to_string() },
        ];
        Ok(Box::pin(futures::stream::iter(chunks.into_iter().map(Ok))))
    }
}

#[derive(Debug, Clone)]
pub enum StreamChunk {
    ContentDelta { delta: String },
    ToolCallStart { id: String, name: String, input: Value },
    ToolCallDelta { id: String, delta: String },
    Done { stop_reason: String },
}
```

**Verification:**
- Trait compiles with default implementation
- Existing LlmClient impls still work

### Phase 7.8: Implement Streaming in RealLlmAdapter

**Objective:** Connect to Anthropic/OpenAI streaming APIs.

**Files:**
- `crates/kelpie-server/src/actor/llm_trait.rs`

**Changes:**
```rust
#[async_trait]
impl LlmClient for RealLlmAdapter {
    async fn stream_complete(
        &self,
        messages: Vec<LlmMessage>,
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>> {
        // Convert actor LlmMessage to llm::ChatMessage
        let chat_messages: Vec<crate::llm::ChatMessage> = messages
            .into_iter()
            .map(|m| crate::llm::ChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();

        // Call real LLM with streaming
        let stream = self.client.stream_with_tools(chat_messages, vec![]).await?;

        // Convert LLM stream chunks to StreamChunk
        let converted_stream = stream.map(|chunk_result| {
            chunk_result.map(|chunk| {
                match chunk {
                    crate::llm::StreamChunk::ContentDelta { delta } => {
                        StreamChunk::ContentDelta { delta }
                    }
                    crate::llm::StreamChunk::Done { stop_reason } => {
                        StreamChunk::Done { stop_reason }
                    }
                    // ... other variants
                }
            })
        });

        Ok(Box::pin(converted_stream))
    }
}
```

**Note:** This assumes `crate::llm::LlmClient` already has streaming support. If not, we'll need to add it there first.

**Verification:**
- `test_dst_llm_token_streaming_basic` → PASSES
- Manual test with real API key shows streaming

### Phase 7.9: Wire SSE Endpoint to AgentService Streaming

**Objective:** Use AgentService.send_message_stream() in SSE endpoint.

**Files:**
- `crates/kelpie-server/src/api/streaming.rs`

**Changes:**
```rust
pub async fn send_message_stream(
    State(state): State<AppState>,
    Path(agent_id): Path<String>,
    Query(_query): Query<StreamQuery>,
    axum::Json(request): axum::Json<CreateMessageRequest>,
) -> Result<Sse<impl Stream<Item = Result<Event, Infallible>>>, ApiError> {
    let (role, content) = request.effective_content()
        .ok_or_else(|| ApiError::bad_request("message content cannot be empty"))?;

    // Create channel for streaming
    let (tx, rx) = mpsc::channel(32);

    // Use AgentService streaming if available
    if let Some(service) = state.agent_service() {
        tokio::spawn(async move {
            if let Err(e) = service.send_message_stream(&agent_id, content, tx.clone()).await {
                let _ = tx.send(StreamEvent::Error {
                    message: e.to_string(),
                }).await;
            }
        });
    } else {
        // Fallback to HashMap-based streaming (existing implementation)
        // ...
    }

    // Convert StreamEvent to SSE Event
    let stream = ReceiverStream::new(rx).map(|event| {
        let event_name = event.event_name();
        let json = serde_json::to_string(&event)?;
        Ok(Event::default().event(event_name).data(json))
    });

    Ok(Sse::new(stream).keep_alive(KeepAlive::default()))
}
```

**Verification:**
```bash
curl -N http://localhost:8283/v1/agents/{id}/messages/stream \
  -H "Content-Type: application/json" \
  -d '{"role":"user","content":"Count to 10"}'

# Should see tokens stream in real-time
```

### Phase 7.10: Verify All Streaming Tests Pass

**Objective:** Confirm streaming works end-to-end.

**Verification:**
```bash
# Run all streaming tests
cargo test -p kelpie-server test_dst_streaming
cargo test -p kelpie-server test_dst_llm_token_streaming

# Manual verification
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server
curl -N http://localhost:8283/v1/agents/{id}/messages/stream \
  -d '{"role":"user","content":"Write a haiku"}'
# Should see tokens appear one by one
```

---

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Message history memory bloat | Medium | Medium | Truncate to max 100 messages |
| Tool execution breaks actor isolation | Medium | High | Sandbox tool calls, async boundary |
| LLM streaming API changes | Low | High | Abstracted behind LlmClient trait |
| HashMap removal breaks existing code | Low | Critical | Comprehensive test coverage before removal |
| Agent loop regression | Medium | High | DST tests with fault injection |
| Performance degradation | Low | Medium | Benchmark before/after |

---

## Success Criteria

**Phase 6 Complete When:**
1. ✅ All 5 agent message DST tests written and passing
2. ✅ Message history in AgentActorState
3. ✅ Agent loop logic in AgentActor
4. ✅ send_message handler uses AgentService
5. ✅ HashMap fields removed from AppState
6. ✅ All 6 handlers use AgentService (100%)
7. ✅ Full test suite passes (115+ tests)
8. ✅ No clippy warnings

**Phase 7 Complete When:**
1. ✅ All 3 LLM streaming DST tests written and passing
2. ✅ LlmClient trait has stream_complete()
3. ✅ RealLlmAdapter implements true streaming
4. ✅ SSE endpoint wired to AgentService
5. ✅ Manual curl test shows real-time tokens
6. ✅ Full test suite passes (118+ tests)
7. ✅ No clippy warnings

**Final Verification:**
```bash
# All tests pass
cargo test -p kelpie-server
# 118+ tests passing

# Clippy clean
cargo clippy -p kelpie-server --all-targets
# 0 warnings

# Manual E2E test
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server
curl -X POST http://localhost:8283/v1/agents \
  -d '{"name":"test-agent"}'
curl -N http://localhost:8283/v1/agents/{id}/messages/stream \
  -d '{"role":"user","content":"Count to 10 slowly"}'
# Tokens stream in real-time
```

---

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-14 | Agent loop in actor (Option B) | Clean architecture, reusable | More complex state management |
| 2026-01-14 | In-memory message history (Option A) | Simplest for migration | Will need Phase 8 refactor for scale |
| 2026-01-14 | Stream trait (Option B) | Most idiomatic Rust | Requires async-stream |
| 2026-01-14 | DST integration tests (Option B) | Full path tested, fast enough | Not E2E HTTP |

---

## What to Try

**After Phase 6.6 (DST tests written):**
- Works Now: Tests compile
- Doesn't Work Yet: Tests FAIL (expected)
- Known Limitations: Need to implement agent loop

**After Phase 6.8 (Agent loop in actor):**
- Works Now: Actor handles messages with LLM
- Test Results: Basic DST tests passing
- Doesn't Work Yet: HTTP handler not migrated
- Known Limitations: Can only test via service directly

**After Phase 6.10 (HTTP handler migrated):**
- Works Now: Full message handling through actors
- Test Results: All agent message DST tests passing
- Manual Test: `curl POST /v1/agents/{id}/messages` works
- Doesn't Work Yet: HashMap still present
- Known Limitations: Dual-mode still active

**After Phase 6.11 (HashMap removed):**
- Works Now: All handlers through AgentService (100%)
- Test Results: 115+ tests passing
- Production Ready: HashMap-free AppState
- Known Limitations: LLM streaming still synthetic

**After Phase 7.8 (LLM streaming implemented):**
- Works Now: True token-by-token streaming
- Test Results: Streaming DST tests passing
- Manual Test: Tokens appear in real-time
- Doesn't Work Yet: SSE endpoint not wired
- Known Limitations: Only works through service directly

**After Phase 7.9 (SSE endpoint wired):**
- Works Now: Full streaming via HTTP SSE
- Test Results: 118+ tests passing
- Manual Test: `curl -N /messages/stream` shows real-time tokens
- Production Ready: Complete streaming UX
- Known Limitations: None - both phases complete!

---

---

## Progress Status (Session 1)

### ✅ Completed: Phases 6.6-6.7

**Phase 6.6: Agent Message DST Tests** ✅
- **File:** `crates/kelpie-server/tests/agent_message_handling_dst.rs` (new)
- **Tests Written:** 5 comprehensive DST tests
  - `test_dst_agent_message_basic` - User message → LLM response
  - `test_dst_agent_message_with_tool_call` - Tool execution loop
  - `test_dst_agent_message_with_storage_fault` - Storage fault injection
  - `test_dst_agent_message_history` - History preservation across restarts
  - `test_dst_agent_message_concurrent` - 5 agents, concurrent messages
- **Status:** All tests compile, all FAIL as expected (DST-first ✅)
- **Error:** Response doesn't contain "messages" field (expected - not implemented yet)

**Phase 6.7: Message History in AgentActorState** ✅
- **File:** `crates/kelpie-server/src/actor/state.rs` (modified)
- **Added Fields:**
  - `messages: Vec<Message>` - Message history storage
  - `max_messages: usize` - Truncation limit (default 100)
- **Added Methods:**
  - `add_message(&mut self, message: Message)` - Append with auto-truncation
  - `recent_messages(&self, limit: usize) -> &[Message]` - Get last N
  - `all_messages(&self) -> &[Message]` - Get all
  - `clear_messages(&mut self)` - Clear history
- **TigerStyle:**
  - Explicit truncation with assertion
  - Clear size limits documented
  - Default value function for serde
- **Status:** Compiles, tests pass, ready for use

### 🔄 In Progress: Phase 6.8

**Phase 6.8: Implement AgentActor::handle_message_full**
- **Status:** NOT STARTED
- **Estimated Effort:** 4-6 hours
- **Scope:**
  - ~500 lines of agent loop logic
  - LLM prompt building from blocks + history
  - Tool execution loop (max 5 iterations)
  - Message storage after each step
  - Usage tracking
  - Error handling

### 📋 Remaining Work

**Phase 6 Remaining (Estimated 8-10 hours):**
- Phase 6.8: Implement handle_message_full in AgentActor (~4-6 hours)
- Phase 6.9: Add AgentService.send_message_full (~30 mins)
- Phase 6.10: Migrate send_message HTTP handler (~1 hour)
- Phase 6.11: Remove HashMap fields (~2-3 hours, includes testing)

**Phase 7 Remaining (Estimated 4-6 hours):**
- Phase 7.6: Write LLM streaming DST tests (~1 hour)
- Phase 7.7: Extend LlmClient trait (~30 mins)
- Phase 7.8: Implement RealLlmAdapter streaming (~2-3 hours)
- Phase 7.9: Wire SSE endpoint to AgentService (~1 hour)

**Total Remaining:** 12-16 hours of focused implementation

### 🎯 Next Session Start Point

**Begin with Phase 6.8:** Implement AgentActor::handle_message_full

**Key Implementation Details:**
```rust
impl AgentActor {
    async fn handle_message_full(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        request: HandleMessageFullRequest,
    ) -> Result<HandleMessageFullResponse> {
        // 1. Add user message to history
        // 2. Build LLM prompt from agent.system + blocks + recent history
        // 3. Call self.llm.complete()
        // 4. Tool execution loop (while tool_calls && iterations < 5)
        // 5. Add assistant response to history
        // 6. Return messages + usage stats
    }
}
```

**Dependencies Needed:**
- HandleMessageFullRequest struct (content: String)
- HandleMessageFullResponse struct (messages: Vec<Message>, usage: UsageStats)
- Tool execution method (execute_tool)
- Message construction helpers

**Testing Strategy:**
- Implement incrementally
- Run DST tests after each step
- Verify: basic → tool_call → history → concurrent

### 📊 Current Test Status

**Total Tests:** 115 tests
- 110 passing (Phases 1-5, 7 partial)
- 5 failing (Phase 6 DST tests - expected)

**After Phase 6 Complete:** 120+ tests passing
**After Phase 7 Complete:** 123+ tests passing

---

## References

- Parent Plan: `.progress/007_20260113_actor_based_agent_server.md`
- Phase 6 Partial: `.progress/009_20260114_http_handler_migration.md`
- Phase 7 Partial: `.progress/010_20260114_message_streaming_architecture.md`
- AgentActor: `crates/kelpie-server/src/actor/agent_actor.rs`
- AgentService: `crates/kelpie-server/src/service/mod.rs`
- DST Tests: `crates/kelpie-server/tests/agent_message_handling_dst.rs` (new)

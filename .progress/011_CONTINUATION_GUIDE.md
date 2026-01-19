# Phase 6 & 7 Completion - Continuation Guide

**Plan:** 011_20260114_phase6_7_completion.md
**Status:** Phases 6.6-6.7 Complete (Foundation work done)
**Remaining:** Phases 6.8-6.11 + 7.6-7.9 (~12-16 hours)

---

## 📋 Quick Start

**To Continue:** Start with Phase 6.8 implementation

**Command to verify current state:**
```bash
# Current test status
cargo test -p kelpie-server --test agent_message_handling_dst
# Should show: 0 passed, 5 failed (expected)

# Verify message history added
grep -n "add_message\|recent_messages" crates/kelpie-server/src/actor/state.rs
# Should show new methods at lines ~90-130
```

---

## ✅ What's Complete

### Phase 6.6: Agent Message DST Tests
**File:** `crates/kelpie-server/tests/agent_message_handling_dst.rs`
- ✅ 5 comprehensive DST tests written (450 lines)
- ✅ All tests compile correctly
- ✅ All tests FAIL as expected (DST-first verified)
- ✅ Tests use SimLlmClient for deterministic behavior
- ✅ Fault injection configured (StorageWriteFail 30%)

**Test Coverage:**
1. `test_dst_agent_message_basic` - Basic LLM conversation
2. `test_dst_agent_message_with_tool_call` - Tool execution loop
3. `test_dst_agent_message_with_storage_fault` - Fault tolerance
4. `test_dst_agent_message_history` - History preservation
5. `test_dst_agent_message_concurrent` - Concurrent agents

**Current Failure Reason:** Response doesn't contain "messages" field (expected - not implemented yet)

### Phase 6.7: Message History Storage
**File:** `crates/kelpie-server/src/actor/state.rs`
- ✅ Added `messages: Vec<Message>` field
- ✅ Added `max_messages: usize` (default 100)
- ✅ Implemented `add_message()` with auto-truncation
- ✅ Implemented `recent_messages(limit)` accessor
- ✅ Implemented `all_messages()` accessor
- ✅ Implemented `clear_messages()` helper
- ✅ TigerStyle: Explicit assertions, clear limits, defaults

**Test Status:** Compiles, no regressions

---

## 🎯 Next: Phase 6.8 Implementation

**Objective:** Move agent loop logic from HTTP handlers into AgentActor

**Estimated Effort:** 4-6 hours

**File to Modify:** `crates/kelpie-server/src/actor/agent_actor.rs`

### Step 1: Define Request/Response Types

Add these structs to `agent_actor.rs`:

```rust
/// Request for full message handling (Phase 6.8)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleMessageFullRequest {
    pub content: String,
}

/// Response from full message handling (Phase 6.8)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleMessageFullResponse {
    pub messages: Vec<Message>,
    pub usage: UsageStats,
}

/// Usage statistics (Phase 6.8)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UsageStats {
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub total_tokens: u64,
}
```

### Step 2: Implement handle_message_full Method

**Template:**

```rust
impl AgentActor {
    /// Handle message with full agent loop (Phase 6.8)
    ///
    /// Implements complete agent behavior:
    /// 1. Add user message to history
    /// 2. Build LLM prompt from agent blocks + history
    /// 3. Call LLM with tools
    /// 4. Execute tool calls (loop up to 5 iterations)
    /// 5. Add assistant response to history
    /// 6. Return all messages + usage stats
    async fn handle_message_full(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        request: HandleMessageFullRequest,
    ) -> Result<HandleMessageFullResponse> {
        // TigerStyle: Validate preconditions
        let agent = ctx.state.agent().ok_or_else(|| Error::Internal {
            message: "Agent not created".to_string(),
        })?;

        // 1. Create and store user message
        let user_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: request.content.clone(),
            tool_call_id: None,
            tool_calls: None,
            created_at: chrono::Utc::now(),
        };
        ctx.state.add_message(user_msg.clone());

        // 2. Build LLM messages
        let mut llm_messages = Vec::new();

        // System prompt
        if let Some(system) = &agent.system {
            llm_messages.push(LlmMessage {
                role: "system".to_string(),
                content: system.clone(),
            });
        }

        // Memory blocks as system context
        for block in &agent.blocks {
            llm_messages.push(LlmMessage {
                role: "system".to_string(),
                content: format!("[{}]\n{}", block.label, block.value),
            });
        }

        // Recent message history (last 20)
        for msg in ctx.state.recent_messages(20) {
            let role = match msg.role {
                MessageRole::User => "user",
                MessageRole::Assistant => "assistant",
                MessageRole::System => "system",
                MessageRole::Tool => "tool",
            };
            llm_messages.push(LlmMessage {
                role: role.to_string(),
                content: msg.content.clone(),
            });
        }

        // 3. Call LLM
        let mut response = self.llm.complete(llm_messages.clone()).await?;
        let mut total_prompt_tokens = 0u64;
        let mut total_completion_tokens = 0u64;
        let mut iterations = 0;
        const MAX_ITERATIONS: u32 = 5;

        // 4. Tool execution loop
        while !response.tool_calls.is_empty() && iterations < MAX_ITERATIONS {
            iterations += 1;

            // Execute each tool
            for tool_call in &response.tool_calls {
                // TODO: Implement execute_tool method
                let result = self.execute_tool(ctx, tool_call).await?;

                // Store tool result message
                let tool_msg = Message {
                    id: uuid::Uuid::new_v4().to_string(),
                    agent_id: ctx.id.id().to_string(),
                    message_type: "tool_return_message".to_string(),
                    role: MessageRole::Tool,
                    content: result,
                    tool_call_id: Some(tool_call.id.clone()),
                    tool_calls: None,
                    created_at: chrono::Utc::now(),
                };
                ctx.state.add_message(tool_msg);
            }

            // Rebuild messages with tool results for next LLM call
            // ... (rebuild llm_messages from ctx.state.recent_messages())

            // Continue conversation
            response = self.llm.complete(llm_messages).await?;
        }

        // 5. Store assistant response
        let assistant_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            message_type: "assistant_message".to_string(),
            role: MessageRole::Assistant,
            content: response.content.clone(),
            tool_call_id: None,
            tool_calls: None,
            created_at: chrono::Utc::now(),
        };
        ctx.state.add_message(assistant_msg.clone());

        // 6. Return response
        Ok(HandleMessageFullResponse {
            messages: vec![user_msg, assistant_msg],
            usage: UsageStats {
                prompt_tokens: total_prompt_tokens,
                completion_tokens: total_completion_tokens,
                total_tokens: total_prompt_tokens + total_completion_tokens,
            },
        })
    }

    /// Execute a tool call (Phase 6.8)
    async fn execute_tool(
        &self,
        _ctx: &ActorContext<AgentActorState>,
        tool_call: &LlmToolCall,
    ) -> Result<String> {
        // For now, placeholder implementation
        // TODO: Integrate with kelpie-sandbox
        match tool_call.name.as_str() {
            "shell" => {
                let command = tool_call
                    .input
                    .get("command")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| Error::Internal {
                        message: "shell tool requires 'command' parameter".to_string(),
                    })?;

                // Placeholder - return simulated result
                Ok(format!("Executed: {}", command))
            }
            _ => Err(Error::Internal {
                message: format!("Unknown tool: {}", tool_call.name),
            }),
        }
    }
}
```

### Step 3: Register Operation in Actor Trait

Add to the `Actor` trait implementation:

```rust
#[async_trait]
impl Actor for AgentActor {
    // ... existing operations

    async fn invoke(
        &self,
        ctx: &mut ActorContext<Self::State>,
        operation: String,
        payload: Bytes,
    ) -> Result<Bytes> {
        match operation.as_str() {
            // ... existing operations
            "handle_message_full" => {
                let request: HandleMessageFullRequest = serde_json::from_slice(&payload)?;
                let response = self.handle_message_full(ctx, request).await?;
                Ok(Bytes::from(serde_json::to_vec(&response)?))
            }
            // ...
        }
    }
}
```

### Step 4: Verify Tests

```bash
# Run DST tests
cargo test -p kelpie-server --test agent_message_handling_dst

# Expected: test_dst_agent_message_basic should PASS
# Others may still fail until fully implemented
```

### Step 5: Iterate Until All Tests Pass

- Fix tool execution
- Fix message history in tool loop
- Fix concurrent handling
- Add missing imports

**Success:** All 5 DST tests passing

---

## 📊 Testing Checklist

After Phase 6.8 implementation:

```bash
# 1. Basic test passes
cargo test -p kelpie-server --test agent_message_handling_dst test_dst_agent_message_basic
# Expected: PASS ✅

# 2. Tool test passes
cargo test -p kelpie-server --test agent_message_handling_dst test_dst_agent_message_with_tool_call
# Expected: PASS ✅

# 3. All DST tests pass
cargo test -p kelpie-server --test agent_message_handling_dst
# Expected: 5 passed, 0 failed ✅

# 4. No regressions
cargo test -p kelpie-server
# Expected: 115+ passed (110 existing + 5 new) ✅

# 5. Clippy clean
cargo clippy -p kelpie-server
# Expected: 0 warnings ✅
```

---

## 🔄 Remaining Phases After 6.8

### Phase 6.9: AgentService Wrapper (~30 mins)

**File:** `crates/kelpie-server/src/service/mod.rs`

Add method:
```rust
impl AgentService {
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

### Phase 6.10: Migrate HTTP Handler (~1 hour)

**File:** `crates/kelpie-server/src/api/messages.rs`

Update `send_message_json` to use `AgentService::send_message_full`:
```rust
async fn send_message_json(...) -> Result<Response, ApiError> {
    let (role, content) = request.effective_content()?;

    // Use AgentService if available
    let response = if let Some(service) = state.agent_service() {
        service.send_message_full(&agent_id, content).await?
    } else {
        // Fallback to HashMap for backward compat
        // ... existing logic
    };

    Ok(Json(MessageResponse {
        messages: response.messages,
        usage: Some(response.usage),
        stop_reason: "end_turn".to_string(),
    }).into_response())
}
```

### Phase 6.11: Remove HashMap (~2-3 hours)

**File:** `crates/kelpie-server/src/state.rs`

Remove:
- `agents: HashMap<String, AgentState>`
- `messages: HashMap<String, Vec<Message>>`
- All sync HashMap methods

Keep:
- All `*_async()` dual-mode methods
- `agent_service: Option<AgentService>`

**Verification:** Full test suite passes

---

## 🌊 Phase 7: LLM Streaming

### Phase 7.6: Write LLM Streaming DST Tests (~1 hour)

**File:** `crates/kelpie-server/tests/llm_token_streaming_dst.rs` (new)

**Tests:**
1. `test_dst_llm_token_streaming_basic` - Tokens arrive incrementally
2. `test_dst_llm_streaming_with_network_delay` - NetworkDelay fault
3. `test_dst_llm_streaming_cancellation` - Drop stream consumer

**Status:** All FAIL (expected - DST-first)

### Phase 7.7: Extend LlmClient Trait (~30 mins)

**File:** `crates/kelpie-server/src/actor/llm_trait.rs`

Add:
```rust
#[async_trait]
pub trait LlmClient: Send + Sync {
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse>;

    // NEW: Streaming method
    async fn stream_complete(
        &self,
        messages: Vec<LlmMessage>,
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>>;
}

pub enum StreamChunk {
    ContentDelta { delta: String },
    ToolCallStart { id: String, name: String, input: Value },
    Done { stop_reason: String },
}
```

### Phase 7.8: Implement RealLlmAdapter Streaming (~2-3 hours)

**File:** `crates/kelpie-server/src/actor/llm_trait.rs`

Implement `stream_complete()` for `RealLlmAdapter` to call Anthropic/OpenAI streaming APIs.

### Phase 7.9: Wire SSE Endpoint (~1 hour)

**File:** `crates/kelpie-server/src/api/streaming.rs`

Update to use `AgentService::send_message_stream()` instead of HashMap.

---

## 🎯 Success Criteria

**Phase 6 Complete:**
- ✅ All 5 agent message DST tests passing
- ✅ send_message handler uses AgentService
- ✅ HashMap fields removed
- ✅ 120+ tests passing total
- ✅ No clippy warnings

**Phase 7 Complete:**
- ✅ All 3 LLM streaming DST tests passing
- ✅ Real-time token streaming working
- ✅ SSE endpoint wired to AgentService
- ✅ 123+ tests passing total
- ✅ Manual curl test shows streaming tokens

**Final Verification:**
```bash
cargo test -p kelpie-server
# 123+ tests passing

cargo clippy -p kelpie-server --all-targets
# 0 warnings

# Manual E2E streaming test
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server
curl -N http://localhost:8283/v1/agents/{id}/messages/stream \
  -d '{"role":"user","content":"Count to 10"}'
# Tokens appear in real-time
```

---

## 📚 References

**Plans:**
- Plan 011: `.progress/011_20260114_phase6_7_completion.md`
- Plan 009 (Phase 6 partial): `.progress/009_20260114_http_handler_migration.md`
- Plan 010 (Phase 7 partial): `.progress/010_20260114_message_streaming_architecture.md`
- Plan 007 (Overall): `.progress/007_20260113_actor_based_agent_server.md`

**Key Files:**
- AgentActor: `crates/kelpie-server/src/actor/agent_actor.rs`
- AgentActorState: `crates/kelpie-server/src/actor/state.rs`
- AgentService: `crates/kelpie-server/src/service/mod.rs`
- DST Tests: `crates/kelpie-server/tests/agent_message_handling_dst.rs`
- HTTP Handler: `crates/kelpie-server/src/api/messages.rs`
- SSE Streaming: `crates/kelpie-server/src/api/streaming.rs`

**TigerStyle Reminders:**
- Write tests FIRST (DST-first)
- Explicit error handling (no unwrap)
- Assertions for invariants (2+ per function)
- Clear boundaries between layers
- Run full test suite after each phase

---

## 💡 Tips

1. **Incremental Development:** Implement handle_message_full incrementally:
   - First: Basic message handling (no tools)
   - Then: Tool execution (single iteration)
   - Then: Tool loop (multiple iterations)
   - Finally: Message history integration

2. **Test-Driven:** Run DST tests after each step to verify progress

3. **Debugging:** Use `RUST_LOG=debug cargo test` to see detailed actor invocations

4. **Performance:** Don't worry about optimization yet - focus on correctness

5. **Tool Integration:** Placeholder tool execution is fine for now - sandbox integration is Phase 8

6. **Message IDs:** Use `uuid::Uuid::new_v4()` for deterministic IDs in tests

---

## 🚀 Quick Commands

```bash
# Start from Phase 6.8
cd /Users/seshendranalla/Development/kelpie

# Verify current state
cargo test -p kelpie-server --test agent_message_handling_dst
# Should show: 0 passed, 5 failed

# Edit actor
code crates/kelpie-server/src/actor/agent_actor.rs

# Run tests as you implement
cargo test -p kelpie-server --test agent_message_handling_dst test_dst_agent_message_basic

# Full verification
cargo test -p kelpie-server && cargo clippy -p kelpie-server
```

---

**Ready to continue!** Start with Phase 6.8 implementation using the template above.

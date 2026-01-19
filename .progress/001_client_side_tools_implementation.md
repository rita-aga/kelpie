# Kelpie: Client-Side Tools Implementation Plan

## Problem Statement

The Letta SDK expects servers to support client-side tool execution via:
1. `default_requires_approval: true` flag on tool registration
2. `client_tools` array in message requests
3. Server returning `approval_request_message` and `stop_reason: requires_approval` instead of executing tools

Currently, Kelpie has the **data structures** defined but the **runtime logic** is missing - tools are always executed server-side regardless of these flags.

## Current State

### What EXISTS:
- `CreateMessageRequest.client_tools: Vec<ClientTool>` (models.rs:365)
- `ClientTool { name, requires_approval }` (models.rs:370-376)
- `ToolInfo.default_requires_approval: bool` (state.rs:55)
- `SseMessage::ApprovalRequestMessage` (messages.rs:79-84)
- Client tools stored separately in `client_tools` HashMap (state.rs:1514-1531)

### What's MISSING:
- Checking these flags before tool execution
- Emitting `approval_request_message`
- Returning `stop_reason: requires_approval`
- Handling tool approval responses to continue the loop

---

## Implementation Plan

### File 1: `crates/kelpie-server/src/api/messages.rs`

#### Change 1A: Add helper function to check if tool requires approval

```rust
// Add near the top of the file, after the imports

/// Check if a tool requires client-side execution
/// Returns true if:
/// - Tool name is in the client_tools array from the request, OR
/// - Tool has default_requires_approval=true in its registration
fn tool_requires_approval(
    tool_name: &str,
    client_tools: &[ClientTool],
    state: &AppState,
) -> bool {
    // Check if tool is in client_tools array from request
    if client_tools.iter().any(|ct| ct.name == tool_name) {
        return true;
    }

    // Check if tool has default_requires_approval=true
    // Look up in client_tools registry (where approval-required tools are stored)
    if let Ok(tools) = state.inner.client_tools.read() {
        if let Some(tool_info) = tools.get(tool_name) {
            if tool_info.default_requires_approval {
                return true;
            }
        }
    }

    false
}
```

#### Change 1B: Modify non-streaming tool execution (handle_message_request)

Around lines 299-380 in the tool execution loop, add approval checking:

```rust
// In handle_message_request, inside the while loop that handles tool_use
// BEFORE: for tool_call in &response.tool_calls { ... execute tool ... }
// AFTER:

while response.stop_reason == "tool_use" && iterations < max_iterations {
    iterations += 1;

    // NEW: Check if any tools require client-side execution
    let mut approval_needed = Vec::new();
    let mut server_tools = Vec::new();

    for tool_call in &response.tool_calls {
        if tool_requires_approval(&tool_call.name, &request.client_tools, &state) {
            approval_needed.push(tool_call.clone());
        } else {
            server_tools.push(tool_call.clone());
        }
    }

    // If any tools need approval, return approval_request and stop
    if !approval_needed.is_empty() {
        // Return early with approval request
        // The client will execute these tools and send results back
        return Ok(MessageResponse {
            messages: vec![stored_user_msg],
            usage: Some(UsageStats {
                prompt_tokens,
                completion_tokens,
                total_tokens: prompt_tokens + completion_tokens,
            }),
            stop_reason: "requires_approval".to_string(),
            // NEW: Add approval_requests field to MessageResponse
            approval_requests: Some(approval_needed.iter().map(|tc| ApprovalRequest {
                tool_call_id: tc.id.clone(),
                tool_name: tc.name.clone(),
                tool_arguments: tc.input.clone(),
            }).collect()),
        });
    }

    // Execute server-side tools as before
    let mut tool_results = Vec::new();
    for tool_call in &server_tools {
        // ... existing tool execution code ...
    }

    // ... rest of the loop ...
}
```

#### Change 1C: Modify streaming tool execution (generate_sse_events)

Around lines 755-812, add same approval checking:

```rust
// In generate_sse_events, inside the while loop
while response.stop_reason == "tool_use" && iterations < AGENT_LOOP_ITERATIONS_MAX {
    iterations += 1;

    // NEW: Check for client-side tools
    let mut approval_needed = Vec::new();
    let mut server_tools = Vec::new();

    for tool_call in &response.tool_calls {
        if tool_requires_approval(&tool_call.name, &client_tools, state) {
            approval_needed.push(tool_call.clone());
        } else {
            server_tools.push(tool_call.clone());
        }
    }

    // If any tools need approval, emit approval_request_message and stop
    if !approval_needed.is_empty() {
        for tool_call in &approval_needed {
            let approval_msg = SseMessage::ApprovalRequestMessage {
                id: Uuid::new_v4().to_string(),
                tool_call_id: tool_call.id.clone(),
                tool_call: ToolCallInfo {
                    name: tool_call.name.clone(),
                    arguments: tool_call.input.clone(),
                },
            };
            if let Ok(json) = serde_json::to_string(&approval_msg) {
                events.push(Ok(Event::default().data(json)));
            }
        }

        // Set stop reason and break
        final_stop_reason = "requires_approval".to_string();
        break;
    }

    // Continue with server-side tools only
    // ... existing code but using server_tools instead of response.tool_calls ...
}
```

### File 2: `crates/kelpie-server/src/models.rs`

#### Change 2A: Add ApprovalRequest to MessageResponse

```rust
/// Response from sending a message
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessageResponse {
    pub messages: Vec<Message>,
    pub usage: Option<UsageStats>,
    pub stop_reason: String,
    /// Tools that need client-side execution (when stop_reason is "requires_approval")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub approval_requests: Option<Vec<ApprovalRequest>>,
}

/// Tool that needs client-side execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApprovalRequest {
    pub tool_call_id: String,
    pub tool_name: String,
    pub tool_arguments: serde_json::Value,
}
```

### File 3: `crates/kelpie-server/src/actor/agent_actor.rs`

#### Change 3A: Add approval checking to handle_message_full

The actor-based path also needs the same changes. In `handle_message_full` around lines 319-390:

```rust
// Add client_tools parameter to HandleMessageFullRequest
pub struct HandleMessageFullRequest {
    pub content: String,
    pub client_tools: Vec<ClientTool>,  // NEW
}

// In handle_message_full, before executing tools:
for tool_call in &response.tool_calls {
    // NEW: Check if tool requires approval
    if self.tool_requires_approval(&tool_call.name, &request.client_tools) {
        // Return with requires_approval instead of executing
        return Ok(HandleMessageFullResponse {
            messages: ctx.state.all_messages().to_vec(),
            usage: UsageStats { ... },
            stop_reason: "requires_approval".to_string(),
            approval_requests: Some(vec![...]),
        });
    }

    // Existing execution code for server-side tools
    // ...
}
```

---

## Testing

After implementing, test with:

1. **Register a tool with default_requires_approval=true**:
```bash
curl -X POST http://localhost:8283/v1/tools \
  -H "Content-Type: application/json" \
  -d '{
    "name": "test_approval_tool",
    "description": "Test tool",
    "default_requires_approval": true,
    "source_code": "def test_approval_tool(**kwargs): pass"
  }'
```

2. **Send a message that triggers the tool**:
```bash
curl -X POST http://localhost:8283/v1/agents/{id}/messages \
  -H "Content-Type: application/json" \
  -d '{"content": "Use test_approval_tool"}'
```

3. **Verify response has**:
- `stop_reason: "requires_approval"`
- `approval_requests` array with the tool call details

4. **For streaming**, verify:
- `approval_request_message` SSE event is emitted
- `stop_reason` event shows "requires_approval"

---

## Phase 2: Handling Approval Responses

After Phase 1 is complete, need to handle when the client sends back tool execution results:

```rust
// Client sends:
{
  "tool_call_id": "call_123",
  "tool_return": "{\"result\": \"success\"}",
  "status": "success"
}

// Server should:
// 1. Find the pending conversation
// 2. Add the tool result to context
// 3. Continue the agent loop with the provided result
```

This is already partially supported via `ToolApproval` struct in models.rs:378-386.

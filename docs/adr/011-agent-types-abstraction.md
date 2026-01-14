# ADR-011: Agent Types Abstraction

**Status:** Proposed
**Date:** 2026-01-13
**Author:** Claude

## Context

Kelpie currently has an `AgentType` enum (`MemgptAgent`, `LettaV1Agent`, `ReactAgent`) that is stored in agent state but **never used to control behavior**. All agents receive identical tools and follow the same message handling logic regardless of type.

Letta implements different agent types with distinct behaviors:

| Agent Type | Memory Tools | Heartbeats | System Prompt | Use Case |
|------------|--------------|------------|---------------|----------|
| `memgpt_agent` | Full set (7) | Yes | MemGPT persona | Original MemGPT behavior |
| `letta_v1_agent` | Simplified (4) | No | Simplified | Simpler loop |
| `react_agent` | None | No | ReAct format | Basic tool use |

We need to implement type-specific behavior while maintaining DST testability.

## Decision

### 1. Agent Capabilities Struct (Not Trait)

**Decision:** Use a `AgentCapabilities` struct instead of a trait for type-specific configuration.

**Rationale:**
- Agent types differ in **configuration**, not behavior
- The agent loop logic is identical; only the available tools differ
- Structs are simpler to test deterministically
- No vtable overhead or dynamic dispatch complexity

```rust
/// Capabilities vary by agent type - determines what tools are available
pub struct AgentCapabilities {
    /// Tools this agent type can use
    pub allowed_tools: Vec<String>,
    /// Whether this agent supports pause_heartbeats
    pub supports_heartbeats: bool,
    /// Default system prompt template
    pub system_prompt_template: Option<String>,
    /// Maximum agent loop iterations (some types may have different limits)
    pub max_iterations: u32,
}
```

### 2. Static Capability Mapping

**Decision:** Define capabilities statically per agent type, not per agent instance.

**Rationale:**
- Simpler mental model - type determines capabilities
- No per-agent capability persistence needed
- DST can verify all types have valid capability sets
- Matches Letta's behavior

```rust
impl AgentType {
    /// Get capabilities for this agent type
    pub fn capabilities(&self) -> AgentCapabilities {
        match self {
            AgentType::MemgptAgent => AgentCapabilities {
                allowed_tools: vec![
                    "shell".into(),
                    "core_memory_append".into(),
                    "core_memory_replace".into(),
                    "archival_memory_insert".into(),
                    "archival_memory_search".into(),
                    "conversation_search".into(),
                    "pause_heartbeats".into(),
                ],
                supports_heartbeats: true,
                system_prompt_template: None, // Use default
                max_iterations: 5,
            },
            AgentType::ReactAgent => AgentCapabilities {
                allowed_tools: vec!["shell".into()],
                supports_heartbeats: false,
                system_prompt_template: Some(REACT_PROMPT.into()),
                max_iterations: 10, // ReAct may need more iterations
            },
            AgentType::LettaV1Agent => AgentCapabilities {
                allowed_tools: vec![
                    "shell".into(),
                    "core_memory_append".into(),
                    "core_memory_replace".into(),
                ],
                supports_heartbeats: false,
                system_prompt_template: None,
                max_iterations: 5,
            },
        }
    }
}
```

### 3. Tool Filtering at Execution Time

**Decision:** Filter tools when building the LLM request, not at registration time.

**Rationale:**
- All tools remain registered globally
- Filtering happens per-request based on agent type
- Simpler than maintaining per-agent registries
- Easy to audit which tools an agent can access

```rust
// In messages.rs send_message handler
let capabilities = agent.agent_type.capabilities();
let all_tools = state.tool_registry().get_tool_definitions().await;
let filtered_tools: Vec<_> = all_tools
    .into_iter()
    .filter(|t| capabilities.allowed_tools.contains(&t.name))
    .collect();
```

### 4. Heartbeat Control via Capabilities

**Decision:** Check `supports_heartbeats` before allowing pause_heartbeats tool.

**Rationale:**
- Even if tool is in `allowed_tools`, capability flag provides explicit control
- Allows future flexibility (e.g., admin override)
- Clear audit trail in logs

```rust
// When processing pause_heartbeats result
if !capabilities.supports_heartbeats {
    // Log warning but don't crash - tool shouldn't be available anyway
    tracing::warn!("Agent {} called pause_heartbeats but type {:?} doesn't support it",
        agent.id, agent.agent_type);
}
```

### 5. No Trait-Based Polymorphism

**Decision:** Do NOT use a `dyn Agent` trait for behavior dispatch.

**Rationale:**
- All agent types use the same message handling loop
- Polymorphism would add complexity without benefit
- Capability struct achieves the same goal more simply
- DST is easier with concrete types

**Rejected Alternative:**
```rust
// REJECTED: Unnecessary complexity
#[async_trait]
pub trait Agent: Send + Sync {
    fn agent_type(&self) -> &str;
    fn available_tools(&self) -> Vec<Arc<dyn Tool>>;
    async fn handle_message(&self, msg: &Message) -> Result<Response>;
}
```

### 6. DST Testing Strategy

**Decision:** Test each agent type's tool filtering and behavior under faults.

**Test Categories:**
1. **Capability Correctness** - Each type has expected tools
2. **Tool Filtering** - Filtered tools match capabilities
3. **Forbidden Tool Rejection** - Agent can't execute tools not in its set
4. **Heartbeat Enforcement** - Only MemgptAgent can pause
5. **Fault Tolerance** - All types handle storage/network faults
6. **Determinism** - Same seed = same type behavior

**No New Fault Types Needed:**
- Existing `StorageWriteFail`, `StorageReadFail` cover memory tool failures
- Existing `McpToolFail` covers external tool failures
- Tool filtering is pure logic (no I/O), doesn't need fault injection

## Consequences

### Positive
- Simple implementation (struct, not trait)
- Clear mental model (type → capabilities → tools)
- DST-friendly (no dynamic dispatch)
- Matches Letta semantics
- Easy to add new agent types

### Negative
- No per-agent tool customization (by design - use tool_ids field if needed later)
- Capability changes require code changes (no runtime config)

### Neutral
- Tool filtering happens every request (minimal overhead)
- System prompts can still be customized per-agent via `agent.system` field

## Implementation Plan

1. Add `AgentCapabilities` struct to `models.rs`
2. Implement `AgentType::capabilities()` method
3. Modify `send_message` to filter tools by capabilities
4. Add heartbeat support check
5. Write DST tests for all agent types
6. Update API to return capabilities in agent response

## DST Test Matrix

| Test | Fault Types | Agent Types | Assertion |
|------|-------------|-------------|-----------|
| Capability correctness | None | All | Expected tool count |
| Tool filtering | None | All | Filtered = capability set |
| Forbidden tool rejection | None | ReactAgent | Memory tools rejected |
| Heartbeat enforcement | None | ReactAgent | pause_heartbeats rejected |
| Memory tools under faults | StorageWriteFail | MemgptAgent | Graceful error handling |
| Type isolation | None | Mixed | Types don't affect each other |
| Determinism | Mixed (10%) | All | Same seed = same behavior |

## References

- [Letta Agent Types](https://docs.letta.com/agents/agent-types)
- [ADR-010: Heartbeat/Pause Mechanism](./010-heartbeat-pause-mechanism.md)
- [TigerStyle: Prefer simple structs over traits](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md)

# ADR-010: Heartbeat/Pause Mechanism

## Status

Accepted

## Date

2026-01-13

## Context

Kelpie's agent loop currently has a hardcoded 5-iteration limit for tool execution chains. This matches basic ReAct behavior but lacks the sophisticated control flow that Letta provides through its `pause_heartbeats` mechanism.

In Letta, agents can autonomously decide to pause their execution loop for a specified duration. This is useful when:
1. The agent has completed a task and wants to signal "I'm done thinking"
2. The agent is waiting for an external event (user input, timer, etc.)
3. The agent wants to conserve resources while idle

Without this mechanism, Kelpie agents either:
- Hit the 5-iteration limit and stop abruptly
- Continue iterating until the limit, wasting resources
- Have no way to gracefully signal completion

### Requirements

1. **Letta Compatibility**: Match Letta's `pause_heartbeats(minutes: int)` tool signature
2. **DST Support**: Work correctly with SimClock for deterministic testing
3. **Clock Fault Tolerance**: Behave correctly under ClockSkew/ClockJump faults
4. **Resource Efficiency**: Stop iteration immediately when pause is requested

## Decision

Implement a `pause_heartbeats` tool that integrates with the agent loop to control iteration flow.

### Design

```
┌─────────────────────────────────────────────────────────────────┐
│                     Agent Loop Control Flow                      │
├─────────────────────────────────────────────────────────────────┤
│  1. Receive user message                                         │
│  2. Build context (memory blocks + history)                      │
│  3. Call LLM with tools                                          │
│  4. LOOP while response.stop_reason == "tool_use":               │
│     a. Execute tools                                             │
│     b. IF pause_heartbeats called:                               │
│        - Record pause_until timestamp                            │
│        - BREAK loop immediately                                  │
│        - Return stop_reason = "pause_heartbeats"                 │
│     c. Continue with tool results                                │
│  5. Return final response                                        │
└─────────────────────────────────────────────────────────────────┘
```

### Tool Definition

```rust
pub struct PauseHeartbeats {
    /// Clock source (real or simulated)
    clock: ClockSource,
}

impl Tool for PauseHeartbeats {
    fn definition() -> ToolDefinition {
        ToolDefinition {
            name: "pause_heartbeats".to_string(),
            description: "Temporarily disable heartbeat messages and end the current step. \
                         Use when you have completed your current task and don't need to \
                         continue thinking. The system will automatically resume after \
                         the specified duration.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {
                    "minutes": {
                        "type": "integer",
                        "description": "Number of minutes to pause heartbeats (1-60)",
                        "minimum": 1,
                        "maximum": 60,
                        "default": 2
                    }
                },
                "required": []
            }),
        }
    }

    async fn execute(&self, input: Value) -> ToolResult {
        let minutes = input.get("minutes")
            .and_then(|v| v.as_i64())
            .unwrap_or(2)
            .clamp(1, 60) as u64;

        let pause_until_ms = self.clock.now_ms() + (minutes * 60 * 1000);

        ToolResult {
            output: format!("Heartbeats paused for {} minutes", minutes),
            success: true,
            signal: Some(ToolSignal::PauseHeartbeats {
                pause_until_ms,
                minutes
            }),
            ..Default::default()
        }
    }
}
```

### Agent Loop Integration

The agent loop checks for `ToolSignal::PauseHeartbeats` after each tool execution:

```rust
for tool_call in &response.tool_calls {
    let result = registry.execute(&tool_call.name, &tool_call.input).await;

    // Check for control flow signal
    if let Some(ToolSignal::PauseHeartbeats { pause_until_ms, minutes }) = result.signal {
        tracing::info!(
            agent_id = %agent_id,
            pause_minutes = minutes,
            pause_until_ms = pause_until_ms,
            "Agent requested heartbeat pause"
        );

        // Record pause state for future resumption
        state.set_heartbeat_pause(&agent_id, pause_until_ms)?;

        // Break loop immediately
        return Ok(Response {
            stop_reason: "pause_heartbeats".to_string(),
            pause_until_ms: Some(pause_until_ms),
            ..response
        });
    }

    tool_results.push((tool_call.id.clone(), result.output));
}
```

### Clock Abstraction

To support both real execution and DST, use a clock abstraction:

```rust
pub enum ClockSource {
    /// Real system clock (production)
    Real,
    /// Simulated clock (DST testing)
    Sim(SimClock),
}

impl ClockSource {
    pub fn now_ms(&self) -> u64 {
        match self {
            ClockSource::Real => {
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_millis() as u64
            }
            ClockSource::Sim(clock) => clock.now_ms(),
        }
    }
}
```

### Constants (TigerStyle)

```rust
/// Minimum pause duration in minutes
pub const HEARTBEAT_PAUSE_MINUTES_MIN: u64 = 1;

/// Maximum pause duration in minutes
pub const HEARTBEAT_PAUSE_MINUTES_MAX: u64 = 60;

/// Default pause duration in minutes
pub const HEARTBEAT_PAUSE_MINUTES_DEFAULT: u64 = 2;

/// Maximum agent loop iterations before forced stop
pub const AGENT_LOOP_ITERATIONS_MAX: u32 = 5;
```

## Consequences

### Positive

- **Letta Compatibility**: Matches Letta's `pause_heartbeats` behavior
- **DST Testable**: Clock abstraction enables deterministic testing
- **Clean Control Flow**: Uses tool signals rather than exceptions
- **Resource Efficient**: Stops iteration immediately on pause

### Negative

- **State Persistence**: Pause state must be persisted for server restarts
- **Complexity**: Adds control flow signal mechanism to tool execution
- **Clock Dependency**: Requires clock source injection throughout stack

### Neutral

- **API Response Change**: Adds `stop_reason: "pause_heartbeats"` to responses
- **Tool Count**: Adds one more built-in tool to the registry

## Alternatives Considered

### Alternative 1: Return Value Convention

Instead of tool signals, use a special return value convention:

```rust
if result.output.starts_with("PAUSE_HEARTBEATS:") {
    // Parse duration from output
}
```

**Rejected**: Fragile, relies on string parsing, not type-safe.

### Alternative 2: Agent Loop Configuration

Make the 5-iteration limit configurable per-agent instead of adding pause mechanism:

```rust
AgentConfig {
    max_iterations: 10,  // Configurable limit
}
```

**Rejected**: Doesn't address the core need - agents can't signal "I'm done."

### Alternative 3: Special Exception/Error Type

Use a custom error type to signal pause:

```rust
return Err(ControlFlow::PauseHeartbeats { minutes: 5 });
```

**Rejected**: Abuses error handling for control flow, not idiomatic Rust.

### Alternative 4: Callback-Based Approach

Register a callback that tools can invoke:

```rust
tool.set_pause_callback(|minutes| {
    // Handle pause
});
```

**Rejected**: More complex, harder to test, callback hell potential.

## DST Requirements

### Required Fault Coverage

| Test Scenario | Fault Types | Assertion |
|---------------|-------------|-----------|
| Basic pause | None | Loop stops, returns pause_heartbeats stop_reason |
| Pause duration | ClockSkew (5000ms) | Duration calculated correctly despite skew |
| Clock jump forward | ClockJump (+60000ms) | Pause ends if jump exceeds pause time |
| Clock jump backward | ClockJump (-30000ms) | Pause remains in effect |
| Persistence | CrashAfterWrite | Pause state survives restart |
| Multiple agents | None | Each agent has independent pause state |

### Simulation Test Example

```rust
#[test]
fn test_pause_heartbeats_with_clock_skew() {
    let config = SimConfig::from_env_or_random();

    Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::ClockSkew { delta_ms: 5000 }, 1.0))
        .run(|env| async move {
            // Setup agent with pause tool
            let clock_source = ClockSource::Sim(env.clock.clone());
            let pause_tool = PauseHeartbeats::new(clock_source);

            // Execute pause
            let input = json!({ "minutes": 2 });
            let result = pause_tool.execute(input).await;

            assert!(result.success);
            assert!(matches!(
                result.signal,
                Some(ToolSignal::PauseHeartbeats { minutes: 2, .. })
            ));

            // Verify pause duration is calculated from SimClock
            if let Some(ToolSignal::PauseHeartbeats { pause_until_ms, .. }) = result.signal {
                let expected = env.clock.now_ms() + (2 * 60 * 1000);
                assert_eq!(pause_until_ms, expected);
            }

            Ok(())
        })
        .expect("Pause heartbeats must work with clock skew");
}
```

## References

- [Letta pause_heartbeats implementation](https://github.com/letta-ai/letta)
- [ADR-006: Letta Code Compatibility](./006-letta-code-compatibility.md)
- [TigerStyle Guidelines](https://github.com/tigerbeetle/tigerbeetle/blob/main/docs/TIGER_STYLE.md)

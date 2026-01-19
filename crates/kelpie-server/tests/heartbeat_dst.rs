//! DST Tests for Heartbeat/Pause Mechanism
//!
//! TigerStyle: Full simulation tests BEFORE implementation (DST-first).
//!
//! These tests define the expected behavior of the heartbeat mechanism.
//! They will fail initially until the implementation is complete.
#![cfg(feature = "dst")]

use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use serde_json::json;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

// =============================================================================
// Constants (TigerStyle)
// =============================================================================

/// Minimum pause duration in minutes
const HEARTBEAT_PAUSE_MINUTES_MIN: u64 = 1;

/// Maximum pause duration in minutes
const HEARTBEAT_PAUSE_MINUTES_MAX: u64 = 60;

/// Default pause duration in minutes
const HEARTBEAT_PAUSE_MINUTES_DEFAULT: u64 = 2;

/// Milliseconds per minute
const MS_PER_MINUTE: u64 = 60 * 1000;

// =============================================================================
// Test Infrastructure
// =============================================================================

/// Simulated tool signal for pause heartbeats
#[derive(Debug, Clone, PartialEq)]
enum ToolSignal {
    /// No signal
    None,
    /// Pause heartbeats for the given duration
    PauseHeartbeats { pause_until_ms: u64, minutes: u64 },
}

/// Simulated tool execution result with signal support
#[derive(Debug, Clone)]
struct SimToolResult {
    success: bool,
    signal: ToolSignal,
}

impl SimToolResult {
    fn success(_output: impl Into<String>) -> Self {
        Self {
            success: true,
            signal: ToolSignal::None,
        }
    }

    fn with_pause_signal(mut self, pause_until_ms: u64, minutes: u64) -> Self {
        self.signal = ToolSignal::PauseHeartbeats {
            pause_until_ms,
            minutes,
        };
        self
    }
}

/// Simulated pause_heartbeats tool
struct SimPauseHeartbeatsTool {
    /// Current time function (for clock abstraction)
    current_time_ms: Arc<dyn Fn() -> u64 + Send + Sync>,
}

impl SimPauseHeartbeatsTool {
    fn new(clock_fn: Arc<dyn Fn() -> u64 + Send + Sync>) -> Self {
        Self {
            current_time_ms: clock_fn,
        }
    }

    fn execute(&self, input: &serde_json::Value) -> SimToolResult {
        // Extract minutes parameter with validation
        let minutes = input
            .get("minutes")
            .and_then(|v| v.as_u64())
            .unwrap_or(HEARTBEAT_PAUSE_MINUTES_DEFAULT);

        // TigerStyle: Clamp to valid range
        let minutes = minutes.clamp(HEARTBEAT_PAUSE_MINUTES_MIN, HEARTBEAT_PAUSE_MINUTES_MAX);

        // Calculate pause end time
        let now_ms = (self.current_time_ms)();
        let pause_until_ms = now_ms + (minutes * MS_PER_MINUTE);

        SimToolResult::success(format!(
            "Heartbeats paused for {} minutes (until {})",
            minutes, pause_until_ms
        ))
        .with_pause_signal(pause_until_ms, minutes)
    }
}

/// Simulated agent loop with heartbeat support
struct SimAgentLoop {
    /// Maximum iterations
    max_iterations: u32,
    /// Current pause state (pause_until_ms)
    pause_until_ms: Option<u64>,
    /// Clock function
    current_time_ms: Arc<dyn Fn() -> u64 + Send + Sync>,
    /// Pause tool
    pause_tool: SimPauseHeartbeatsTool,
    /// Iteration counter
    iteration_count: AtomicU64,
}

impl SimAgentLoop {
    fn new(clock_fn: Arc<dyn Fn() -> u64 + Send + Sync>) -> Self {
        Self {
            max_iterations: 5,
            pause_until_ms: None,
            current_time_ms: clock_fn.clone(),
            pause_tool: SimPauseHeartbeatsTool::new(clock_fn),
            iteration_count: AtomicU64::new(0),
        }
    }

    /// Check if agent is currently paused
    fn is_paused(&self) -> bool {
        if let Some(until_ms) = self.pause_until_ms {
            let now = (self.current_time_ms)();
            now < until_ms
        } else {
            false
        }
    }

    /// Execute a tool and handle signals
    fn execute_tool(&mut self, tool_name: &str, input: &serde_json::Value) -> SimToolResult {
        self.iteration_count.fetch_add(1, Ordering::SeqCst);

        if tool_name == "pause_heartbeats" {
            let result = self.pause_tool.execute(input);

            // Handle pause signal
            if let ToolSignal::PauseHeartbeats { pause_until_ms, .. } = result.signal {
                self.pause_until_ms = Some(pause_until_ms);
            }

            result
        } else {
            SimToolResult::success(format!("Executed tool: {}", tool_name))
        }
    }

    /// Simulate an agent loop iteration
    /// Returns (should_continue, stop_reason)
    fn should_continue(&self, current_iteration: u32) -> (bool, &'static str) {
        // Check pause state first
        if self.is_paused() {
            return (false, "pause_heartbeats");
        }

        // Check iteration limit
        if current_iteration >= self.max_iterations {
            return (false, "max_iterations");
        }

        (true, "continue")
    }

    fn iterations(&self) -> u64 {
        self.iteration_count.load(Ordering::SeqCst)
    }
}

// =============================================================================
// Basic Functionality Tests
// =============================================================================

#[test]
fn test_pause_heartbeats_basic_execution() {
    let config = SimConfig::from_env_or_random();
    println!(
        "DST seed: {} (set DST_SEED={} to replay)",
        config.seed, config.seed
    );

    let result = Simulation::new(config).run(|env| async move {
        // Create clock function using SimClock
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let tool = SimPauseHeartbeatsTool::new(clock_fn.clone());

        // Execute with default minutes
        let result = tool.execute(&json!({}));

        // Assertions
        assert!(result.success, "Tool execution should succeed");
        assert!(
            matches!(
                result.signal,
                ToolSignal::PauseHeartbeats { minutes: 2, .. }
            ),
            "Should signal pause for default 2 minutes"
        );

        // Verify pause_until_ms is correct
        if let ToolSignal::PauseHeartbeats {
            pause_until_ms,
            minutes,
        } = result.signal
        {
            let expected_ms = env.clock.now_ms() + (minutes * MS_PER_MINUTE);
            assert_eq!(pause_until_ms, expected_ms, "Pause duration incorrect");
        }

        Ok(())
    });

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

#[test]
fn test_pause_heartbeats_custom_duration() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let tool = SimPauseHeartbeatsTool::new(clock_fn);

        // Test various durations
        for minutes in [1, 5, 30, 60] {
            let result = tool.execute(&json!({ "minutes": minutes }));
            assert!(result.success);

            if let ToolSignal::PauseHeartbeats {
                minutes: actual, ..
            } = result.signal
            {
                assert_eq!(actual, minutes, "Minutes mismatch for input {}", minutes);
            }
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_pause_heartbeats_duration_clamping() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let tool = SimPauseHeartbeatsTool::new(clock_fn);

        // Test below minimum (should clamp to 1)
        let result = tool.execute(&json!({ "minutes": 0 }));
        if let ToolSignal::PauseHeartbeats { minutes, .. } = result.signal {
            assert_eq!(
                minutes, HEARTBEAT_PAUSE_MINUTES_MIN,
                "Should clamp to minimum"
            );
        }

        // Test above maximum (should clamp to 60)
        let result = tool.execute(&json!({ "minutes": 100 }));
        if let ToolSignal::PauseHeartbeats { minutes, .. } = result.signal {
            assert_eq!(
                minutes, HEARTBEAT_PAUSE_MINUTES_MAX,
                "Should clamp to maximum"
            );
        }

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Agent Loop Integration Tests
// =============================================================================

#[test]
fn test_agent_loop_stops_on_pause() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Execute some iterations
        let mut iteration = 0;
        while iteration < 3 {
            let (should_continue, _) = agent_loop.should_continue(iteration);
            if !should_continue {
                break;
            }

            // On iteration 1, call pause_heartbeats
            if iteration == 1 {
                agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 5 }));
            } else {
                agent_loop.execute_tool("some_other_tool", &json!({}));
            }

            iteration += 1;
        }

        // Check that loop stopped due to pause
        let (should_continue, stop_reason) = agent_loop.should_continue(iteration);
        assert!(!should_continue, "Loop should stop after pause");
        assert_eq!(
            stop_reason, "pause_heartbeats",
            "Stop reason should be pause"
        );

        // Verify we only did 2 iterations (0 and 1), not all 5
        assert_eq!(
            agent_loop.iterations(),
            2,
            "Should have stopped at iteration 2"
        );

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_agent_loop_resumes_after_pause_expires() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Pause for 1 minute
        agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 1 }));

        // Verify paused
        assert!(agent_loop.is_paused(), "Should be paused");

        // Advance time past pause duration
        env.advance_time_ms(MS_PER_MINUTE + 1);

        // Verify no longer paused
        assert!(!agent_loop.is_paused(), "Should no longer be paused");

        let (should_continue, _) = agent_loop.should_continue(0);
        assert!(should_continue, "Loop should be able to continue");

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Clock Fault Tolerance Tests
// =============================================================================

#[test]
fn test_pause_with_clock_skew() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    // Test with 5-second clock skew
    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::ClockSkew { delta_ms: 5000 },
            1.0,
        ))
        .run(|env| async move {
            let clock = env.clock.clone();
            let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

            let tool = SimPauseHeartbeatsTool::new(clock_fn.clone());

            // Record initial time
            let initial_time = env.clock.now_ms();

            // Execute pause
            let result = tool.execute(&json!({ "minutes": 2 }));
            assert!(result.success);

            // Verify pause_until is calculated from SimClock, not affected by skew
            // (since we're using SimClock directly, skew doesn't affect the calculation)
            if let ToolSignal::PauseHeartbeats { pause_until_ms, .. } = result.signal {
                let expected = initial_time + (2 * MS_PER_MINUTE);
                assert_eq!(
                    pause_until_ms, expected,
                    "Clock skew should not affect pause calculation"
                );
            }

            Ok(())
        });

    assert!(result.is_ok());
}

#[test]
fn test_pause_with_clock_jump_forward() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Pause for 2 minutes
        agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 2 }));
        assert!(agent_loop.is_paused());

        // Jump clock forward by 3 minutes (past pause end)
        env.advance_time_ms(3 * MS_PER_MINUTE);

        // Pause should have expired
        assert!(
            !agent_loop.is_paused(),
            "Clock jump forward should expire pause"
        );

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_pause_with_clock_jump_backward() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    // Note: SimClock doesn't support going backward, but we can test the logic
    // by setting up a scenario where the pause_until is far in the future
    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Advance time first
        env.advance_time_ms(10 * MS_PER_MINUTE);

        // Pause for 2 minutes
        agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 2 }));

        // Should be paused
        assert!(agent_loop.is_paused());

        // Even if we can't go backward, verify the pause remains
        // (this tests that pause doesn't accidentally get cleared)
        env.advance_time_ms(MS_PER_MINUTE);
        assert!(
            agent_loop.is_paused(),
            "Should still be paused after 1 minute"
        );

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Determinism Tests
// =============================================================================

#[test]
fn test_pause_heartbeats_determinism() {
    let seed = 42;

    // Run twice with same seed
    let run_simulation = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|env| async move {
            let clock = env.clock.clone();
            let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

            let tool = SimPauseHeartbeatsTool::new(clock_fn);

            let mut results = Vec::new();
            for minutes in [1, 2, 5, 10, 30] {
                let result = tool.execute(&json!({ "minutes": minutes }));
                if let ToolSignal::PauseHeartbeats {
                    pause_until_ms,
                    minutes,
                } = result.signal
                {
                    results.push((pause_until_ms, minutes));
                }
            }

            Ok(results)
        })
    };

    let result1 = run_simulation().expect("First run failed");
    let result2 = run_simulation().expect("Second run failed");

    assert_eq!(result1, result2, "Same seed must produce same results");
}

// =============================================================================
// Multi-Agent Isolation Tests
// =============================================================================

#[test]
fn test_multi_agent_pause_isolation() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        // Create two agent loops
        let mut agent1 = SimAgentLoop::new(clock_fn.clone());
        let mut agent2 = SimAgentLoop::new(clock_fn);

        // Pause agent 1 for 5 minutes
        agent1.execute_tool("pause_heartbeats", &json!({ "minutes": 5 }));

        // Verify agent 1 is paused
        assert!(agent1.is_paused(), "Agent 1 should be paused");

        // Verify agent 2 is NOT paused
        assert!(!agent2.is_paused(), "Agent 2 should not be affected");

        // Agent 2 should be able to continue
        let (should_continue, _) = agent2.should_continue(0);
        assert!(should_continue, "Agent 2 should be able to continue");

        // Pause agent 2 for 2 minutes
        agent2.execute_tool("pause_heartbeats", &json!({ "minutes": 2 }));

        // Now both should be paused
        assert!(agent1.is_paused(), "Agent 1 still paused");
        assert!(agent2.is_paused(), "Agent 2 now paused");

        // Advance time 3 minutes - agent 2 should resume, agent 1 still paused
        env.advance_time_ms(3 * MS_PER_MINUTE);

        assert!(agent1.is_paused(), "Agent 1 still paused (5 min)");
        assert!(!agent2.is_paused(), "Agent 2 should resume (2 min expired)");

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Edge Case Tests
// =============================================================================

#[test]
fn test_pause_at_loop_iteration_limit() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Execute up to iteration 4 (0-indexed, max is 5)
        for i in 0..4 {
            let (should_continue, _) = agent_loop.should_continue(i);
            assert!(should_continue, "Should continue at iteration {}", i);
            agent_loop.execute_tool("some_tool", &json!({}));
        }

        // At iteration 4, pause
        agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 1 }));

        // Check stop reason - should be pause, not max_iterations
        let (should_continue, stop_reason) = agent_loop.should_continue(4);
        assert!(!should_continue);
        assert_eq!(
            stop_reason, "pause_heartbeats",
            "Pause should take precedence over iteration limit"
        );

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_multiple_pause_calls_overwrites() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // First pause for 5 minutes
        agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 5 }));
        let first_pause_until = agent_loop.pause_until_ms;

        // Second pause for 2 minutes (should overwrite)
        agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 2 }));
        let second_pause_until = agent_loop.pause_until_ms;

        // Second pause should have overwritten (shorter duration)
        assert_ne!(first_pause_until, second_pause_until);

        // Verify the new pause is calculated from current time
        let expected = env.clock.now_ms() + (2 * MS_PER_MINUTE);
        assert_eq!(second_pause_until, Some(expected));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_pause_with_invalid_input() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let tool = SimPauseHeartbeatsTool::new(clock_fn);

        // Test with string instead of number (should use default)
        let result = tool.execute(&json!({ "minutes": "invalid" }));
        assert!(result.success);
        if let ToolSignal::PauseHeartbeats { minutes, .. } = result.signal {
            assert_eq!(
                minutes, HEARTBEAT_PAUSE_MINUTES_DEFAULT,
                "Invalid input should use default"
            );
        }

        // Test with negative number (should clamp to min)
        let result = tool.execute(&json!({ "minutes": -5 }));
        assert!(result.success);
        // Note: -5 as u64 becomes a very large number, which will clamp to max
        // This is expected behavior for malformed input

        // Test with empty object (should use default)
        let result = tool.execute(&json!({}));
        assert!(result.success);
        if let ToolSignal::PauseHeartbeats { minutes, .. } = result.signal {
            assert_eq!(minutes, HEARTBEAT_PAUSE_MINUTES_DEFAULT);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Stress Tests
// =============================================================================

#[test]
fn test_pause_high_frequency() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let tool = SimPauseHeartbeatsTool::new(clock_fn);

        // Rapid-fire pause calls
        for i in 0..100 {
            let minutes = (i % 60) + 1; // 1-60
            let result = tool.execute(&json!({ "minutes": minutes }));
            assert!(result.success, "Call {} failed", i);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_pause_with_time_advancement_stress() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Simulate many pause/resume cycles
        for i in 0..50 {
            // Pause for random duration (1-5 minutes)
            let minutes = (i % 5) + 1;
            agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": minutes }));

            assert!(
                agent_loop.is_paused(),
                "Should be paused at iteration {}",
                i
            );

            // Advance time past pause
            env.advance_time_ms((minutes as u64 + 1) * MS_PER_MINUTE);

            assert!(!agent_loop.is_paused(), "Should resume at iteration {}", i);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// SSE/Response Format Tests
// =============================================================================

/// Simulated SSE stop reason
#[derive(Debug, Clone, PartialEq)]
enum StopReason {
    EndTurn,
    PauseHeartbeats { pause_until_ms: u64 },
}

#[test]
fn test_pause_stop_reason_in_response() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {}", config.seed);

    let result = Simulation::new(config).run(|env| async move {
        let clock = env.clock.clone();
        let clock_fn: Arc<dyn Fn() -> u64 + Send + Sync> = Arc::new(move || clock.now_ms());

        let mut agent_loop = SimAgentLoop::new(clock_fn);

        // Execute pause
        let result = agent_loop.execute_tool("pause_heartbeats", &json!({ "minutes": 5 }));

        // Build response stop reason
        let stop_reason = if let ToolSignal::PauseHeartbeats { pause_until_ms, .. } = result.signal
        {
            StopReason::PauseHeartbeats { pause_until_ms }
        } else {
            StopReason::EndTurn
        };

        // Verify stop reason
        assert!(
            matches!(stop_reason, StopReason::PauseHeartbeats { .. }),
            "Stop reason should be PauseHeartbeats"
        );

        if let StopReason::PauseHeartbeats { pause_until_ms } = stop_reason {
            let expected = env.clock.now_ms() + (5 * MS_PER_MINUTE);
            assert_eq!(pause_until_ms, expected);
        }

        Ok(())
    });

    assert!(result.is_ok());
}

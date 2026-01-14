//! DST tests for AgentActor lifecycle and operations
//!
//! TigerStyle: Tests define the contract BEFORE implementation (DST-first).
//!
//! These tests will FAIL initially because AgentActor doesn't exist yet.
//! That's expected - Phase 3 will implement AgentActor to make them pass.

use kelpie_core::{ActorId, Error, Result};
use kelpie_dst::{FaultConfig, FaultType, SimConfig, SimEnvironment, Simulation};
use serde_json::json;

// ============================================================================
// Phase 3 TODO: Remove this mock module and import real types
// ============================================================================

/// Mock types for Phase 2 - these should be replaced by real implementations
mod phase3_types {
    use kelpie_core::Result;
    use kelpie_dst::SimEnvironment;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct CreateAgentRequest {
        pub name: String,
        pub agent_type: String,
        pub memory_blocks: Vec<Block>,
        pub tool_ids: Vec<String>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct Block {
        pub label: String,
        pub value: String,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct AgentState {
        pub id: String,
        pub name: String,
        pub agent_type: String,
        pub blocks: Vec<Block>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct MessageRequest {
        pub role: String,
        pub content: String,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct MessageResponse {
        pub role: String,
        pub content: String,
    }

    /// Mock dispatcher - Phase 3 should implement real one
    pub struct MockDispatcher;

    impl MockDispatcher {
        pub async fn invoke<T: serde::de::DeserializeOwned>(
            &self,
            _agent_id: &str,
            _method: &str,
            _payload: Vec<u8>,
        ) -> Result<T> {
            // This will fail in Phase 2 - that's expected!
            panic!("AgentActor not implemented - Phase 3 TODO");
        }

        pub async fn deactivate(&self, _agent_id: &str) -> Result<()> {
            panic!("AgentActor not implemented - Phase 3 TODO");
        }
    }

    /// Create mock dispatcher - Phase 3 should create real one with SimEnvironment
    pub fn create_dispatcher(_sim_env: &SimEnvironment) -> Result<MockDispatcher> {
        Ok(MockDispatcher)
    }
}

use phase3_types::*;

/// Helper to serialize to vec, converting errors properly
fn to_vec<T: serde::Serialize>(value: &T) -> Result<Vec<u8>> {
    serde_json::to_vec(value).map_err(|e| Error::Internal {
        message: format!("Serialization error: {}", e),
    })
}

/// Test basic agent actor activation
///
/// Contract:
/// - Create agent → actor activates
/// - State loads from storage (or creates if new)
/// - Actor is ready to handle messages
#[tokio::test]
async fn test_dst_agent_actor_activation_basic() {
    let config = SimConfig::new(42);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            // Create dispatcher
            let dispatcher = create_dispatcher(&sim_env)?;

            // Create agent
            let agent_id = "agent-test-001";
            let request = CreateAgentRequest {
                name: "test-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![],
                tool_ids: vec![],
            };

            // Activate actor by invoking create
            dispatcher
                .invoke::<()>(
                    agent_id,
                    "create",
                    to_vec(&request)?,
                )
                .await?;

            // Verify actor is active - get state
            let state: AgentState = dispatcher.invoke(agent_id, "get_state", vec![]).await?;
            assert_eq!(state.name, "test-agent");
            assert_eq!(state.agent_type, "letta_v1");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Activation failed: {:?}", result.err());
}

/// Test agent actor activation with storage read failure
///
/// Contract:
/// - 20% storage read fault rate
/// - Actor should handle gracefully (retry or return error)
/// - Should not panic or corrupt state
#[tokio::test]
async fn test_dst_agent_actor_activation_with_storage_fail() {
    let config = SimConfig::new(12345);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.2))
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;

            let mut success_count = 0;
            let mut failure_count = 0;

            for i in 0..10 {
                let agent_id = format!("agent-test-{:03}", i);
                let request = CreateAgentRequest {
                    name: format!("agent-{}", i),
                    agent_type: "letta_v1".to_string(),
                    memory_blocks: vec![],
                    tool_ids: vec![],
                };

                match dispatcher
                    .invoke::<()>(&agent_id, "create", to_vec(&request)?)
                    .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        // Storage fault - acceptable
                        assert!(
                            e.to_string().contains("storage")
                                || e.to_string().contains("Storage"),
                            "Expected storage error, got: {}",
                            e
                        );
                        failure_count += 1;
                    }
                }
            }

            // With 20% fault rate, should see some failures
            assert!(failure_count > 0, "Expected some storage failures");
            assert!(success_count > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor deactivation persists state
///
/// Contract:
/// - Deactivate actor → state written to storage
/// - Reactivate actor → state loaded correctly
/// - All data preserved across activation cycles
#[tokio::test]
async fn test_dst_agent_actor_deactivation_persists_state() {
    let config = SimConfig::new(54321);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-persistent";

            // Create and activate
            let request = CreateAgentRequest {
                name: "persistent-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![Block {
                    label: "persona".to_string(),
                    value: "I am helpful".to_string(),
                }],
                tool_ids: vec![],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            // Deactivate
            dispatcher.deactivate(agent_id).await?;

            // Reactivate and verify state preserved
            let state: AgentState = dispatcher.invoke(agent_id, "get_state", vec![]).await?;
            assert_eq!(state.name, "persistent-agent");
            assert_eq!(state.blocks.len(), 1);
            assert_eq!(state.blocks[0].label, "persona");
            assert_eq!(state.blocks[0].value, "I am helpful");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor deactivation with storage write failure
///
/// Contract:
/// - 20% storage write fault rate
/// - Actor should retry or fail gracefully
/// - State should remain consistent (no partial writes)
#[tokio::test]
async fn test_dst_agent_actor_deactivation_with_storage_fail() {
    let config = SimConfig::new(99999);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.2))
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;

            let mut success_count = 0;
            let mut failure_count = 0;

            for i in 0..10 {
                let agent_id = format!("agent-test-{:03}", i);
                let request = CreateAgentRequest {
                    name: format!("agent-{}", i),
                    agent_type: "letta_v1".to_string(),
                    memory_blocks: vec![],
                    tool_ids: vec![],
                };

                dispatcher
                    .invoke::<()>(&agent_id, "create", to_vec(&request)?)
                    .await?;

                // Try to deactivate
                match dispatcher.deactivate(&agent_id).await {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        // Storage fault during deactivation
                        assert!(
                            e.to_string().contains("storage")
                                || e.to_string().contains("Storage"),
                            "Expected storage error, got: {}",
                            e
                        );
                        failure_count += 1;
                    }
                }
            }

            // With 20% fault rate, should see some failures
            assert!(failure_count > 0, "Expected some storage failures");
            assert!(success_count > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor crash recovery
///
/// Contract:
/// - CrashAfterWrite fault → actor crashes after writing
/// - State should be consistent (transaction committed or rolled back)
/// - Actor can be reactivated and continue
#[tokio::test]
async fn test_dst_agent_actor_crash_recovery() {
    let config = SimConfig::new(77777);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashAfterWrite, 0.1))
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-crash-test";

            // Create agent
            let request = CreateAgentRequest {
                name: "crash-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![Block {
                    label: "persona".to_string(),
                    value: "Initial state".to_string(),
                }],
                tool_ids: vec![],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            // Update state (may crash)
            let update = json!({
                "label": "persona",
                "value": "Updated state"
            });
            let _ = dispatcher
                .invoke::<()>(agent_id, "update_block", to_vec(&update)?)
                .await;

            // Reactivate and verify state is consistent
            let state: AgentState = dispatcher.invoke(agent_id, "get_state", vec![]).await?;
            // State should be either "Initial state" OR "Updated state", never corrupted
            let persona_value = &state.blocks[0].value;
            assert!(
                persona_value == "Initial state" || persona_value == "Updated state",
                "State corrupted: {}",
                persona_value
            );

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor handles message with LLM
///
/// Contract:
/// - Send user message → actor builds prompt → calls LLM → returns response
/// - Message stored in conversation history
/// - State updated correctly
#[tokio::test]
async fn test_dst_agent_handle_message_basic() {
    let config = SimConfig::new(11111);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-chat-test";

            // Create agent
            let request = CreateAgentRequest {
                name: "chat-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![Block {
                    label: "persona".to_string(),
                    value: "I am helpful".to_string(),
                }],
                tool_ids: vec![],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            // Send message
            let message = MessageRequest {
                role: "user".to_string(),
                content: "Hello".to_string(),
            };
            let response: MessageResponse = dispatcher
                .invoke(agent_id, "handle_message", to_vec(&message)?)
                .await?;

            // Verify response
            assert!(!response.content.is_empty(), "Response should not be empty");
            assert_eq!(response.role, "assistant");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor handles LLM timeout
///
/// Contract:
/// - LlmTimeout fault → actor returns error gracefully
/// - State remains consistent
/// - Agent can retry on next message
#[tokio::test]
async fn test_dst_agent_handle_message_with_llm_timeout() {
    let config = SimConfig::new(22222);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::LlmTimeout, 0.3))
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-timeout-test";

            // Create agent
            let request = CreateAgentRequest {
                name: "timeout-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![],
                tool_ids: vec![],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            let mut success_count = 0;
            let mut timeout_count = 0;

            for i in 0..10 {
                let message = MessageRequest {
                    role: "user".to_string(),
                    content: format!("Message {}", i),
                };
                match dispatcher
                    .invoke::<MessageResponse>(
                        agent_id,
                        "handle_message",
                        to_vec(&message)?,
                    )
                    .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        let err_str = e.to_string();
                        assert!(
                            err_str.contains("timeout") || err_str.contains("timed out"),
                            "Expected LLM timeout error, got: {}",
                            e
                        );
                        timeout_count += 1;
                    }
                }
            }

            // With 30% timeout rate, should see some timeouts
            assert!(timeout_count > 0, "Expected some LLM timeouts");
            assert!(success_count > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor handles LLM failure
///
/// Contract:
/// - LlmFailure fault → actor returns error gracefully
/// - Error message is informative
/// - Agent state not corrupted
#[tokio::test]
async fn test_dst_agent_handle_message_with_llm_failure() {
    let config = SimConfig::new(33333);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::LlmFailure, 0.25))
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-failure-test";

            // Create agent
            let request = CreateAgentRequest {
                name: "failure-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![],
                tool_ids: vec![],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            let mut success_count = 0;
            let mut failure_count = 0;

            for i in 0..10 {
                let message = MessageRequest {
                    role: "user".to_string(),
                    content: format!("Message {}", i),
                };
                match dispatcher
                    .invoke::<MessageResponse>(
                        agent_id,
                        "handle_message",
                        to_vec(&message)?,
                    )
                    .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        let err_str = e.to_string();
                        assert!(
                            err_str.contains("failure")
                                || err_str.contains("failed")
                                || err_str.contains("error"),
                            "Expected LLM failure error, got: {}",
                            e
                        );
                        failure_count += 1;
                    }
                }
            }

            // With 25% failure rate, should see some failures
            assert!(failure_count > 0, "Expected some LLM failures");
            assert!(success_count > 0, "Expected some successes");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor tool execution
///
/// Contract:
/// - LLM requests tool → actor executes tool → returns result to LLM
/// - Tool result included in next LLM call
/// - Conversation history includes tool calls
#[tokio::test]
async fn test_dst_agent_tool_execution() {
    let config = SimConfig::new(44444);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-tool-test";

            // Create agent with tools
            let request = CreateAgentRequest {
                name: "tool-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![],
                tool_ids: vec!["shell".to_string()],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            // Send message that should trigger tool use
            let message = MessageRequest {
                role: "user".to_string(),
                content: "Execute a shell command".to_string(),
            };
            let response: MessageResponse = dispatcher
                .invoke(agent_id, "handle_message", to_vec(&message)?)
                .await?;

            // Verify we got a response (tool execution details depend on implementation)
            assert!(!response.content.is_empty());

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test agent actor memory tools (core_memory_append, etc.)
///
/// Contract:
/// - core_memory_append → updates block in state
/// - State persisted to storage
/// - Next message sees updated block in prompt
#[tokio::test]
async fn test_dst_agent_memory_tools() {
    let config = SimConfig::new(55555);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let agent_id = "agent-memory-test";

            // Create agent
            let request = CreateAgentRequest {
                name: "memory-agent".to_string(),
                agent_type: "letta_v1".to_string(),
                memory_blocks: vec![Block {
                    label: "persona".to_string(),
                    value: "I am helpful".to_string(),
                }],
                tool_ids: vec![],
            };
            dispatcher
                .invoke::<()>(agent_id, "create", to_vec(&request)?)
                .await?;

            // Call core_memory_append
            let tool_call = json!({
                "label": "persona",
                "content": ". I remember everything."
            });
            dispatcher
                .invoke::<()>(agent_id, "core_memory_append", to_vec(&tool_call)?)
                .await?;

            // Verify block was updated
            let state: AgentState = dispatcher.invoke(agent_id, "get_state", vec![]).await?;
            assert_eq!(
                state.blocks[0].value,
                "I am helpful. I remember everything."
            );

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

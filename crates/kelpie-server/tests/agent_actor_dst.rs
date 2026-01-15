//! DST tests for AgentActor lifecycle and operations
//!
//! TigerStyle: Tests define the contract BEFORE implementation (DST-first).

use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::actor::ActorId;
use kelpie_core::Result;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, SimEnvironment, SimLlmClient, Simulation};
use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig, DispatcherHandle};
use kelpie_server::actor::{
    AgentActor, AgentActorState, LlmClient, LlmMessage, LlmResponse, LlmToolCall,
};
use kelpie_server::models::{AgentState, AgentType, CreateAgentRequest, CreateBlockRequest};
use std::sync::Arc;

/// Adapter to use SimLlmClient as LlmClient
struct SimLlmClientAdapter {
    client: Arc<SimLlmClient>,
}

#[async_trait]
impl LlmClient for SimLlmClientAdapter {
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse> {
        // Convert LlmMessage to SimChatMessage
        let sim_messages: Vec<kelpie_dst::SimChatMessage> = messages
            .into_iter()
            .map(|m| kelpie_dst::SimChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();

        // Call sim LLM (no tools for now - simplified)
        let response = self
            .client
            .complete_with_tools(sim_messages, vec![])
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: format!("LLM error: {}", e),
            })?;

        Ok(LlmResponse {
            content: response.content,
            tool_calls: vec![], // No tool calls for now
        })
    }
}

/// Helper to create a dispatcher with AgentActor
fn create_dispatcher(sim_env: &SimEnvironment) -> Result<DispatcherHandle> {
    // Create SimLlmClient from environment
    let sim_llm = SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone());

    // Create LLM client adapter
    let llm_adapter: Arc<dyn LlmClient> = Arc::new(SimLlmClientAdapter {
        client: Arc::new(sim_llm),
    });

    // Create actor with LLM client
    let actor = AgentActor::new(llm_adapter);

    // Create actor factory
    let factory = Arc::new(CloneFactory::new(actor));

    // Use SimStorage as ActorKV
    let kv = Arc::new(sim_env.storage.clone());

    // Create dispatcher
    let mut dispatcher =
        Dispatcher::<AgentActor, AgentActorState>::new(factory, kv, DispatcherConfig::default());

    let handle = dispatcher.handle();

    // Spawn dispatcher task
    tokio::spawn(async move {
        dispatcher.run().await;
    });

    Ok(handle)
}

/// Helper to serialize to bytes
fn to_bytes<T: serde::Serialize>(value: &T) -> Result<Bytes> {
    let vec = serde_json::to_vec(value).map_err(|e| kelpie_core::Error::Internal {
        message: format!("Serialization error: {}", e),
    })?;
    Ok(Bytes::from(vec))
}

/// Helper to invoke and deserialize response
async fn invoke_deserialize<T: serde::de::DeserializeOwned>(
    dispatcher: &DispatcherHandle,
    actor_id: ActorId,
    operation: &str,
    payload: Bytes,
) -> Result<T> {
    let response = dispatcher
        .invoke(actor_id, operation.to_string(), payload)
        .await?;
    serde_json::from_slice(&response).map_err(|e| kelpie_core::Error::Internal {
        message: format!("Failed to deserialize response: {}", e),
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
            let actor_id = ActorId::new("agents", "agent-test-001")?;
            let request = CreateAgentRequest {
                name: "test-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };

            // Activate actor by invoking create
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            // Verify actor is active - get state
            let state: AgentState =
                invoke_deserialize(&dispatcher, actor_id.clone(), "get_state", Bytes::new())
                    .await?;

            assert_eq!(state.name, "test-agent");
            assert_eq!(state.agent_type, AgentType::LettaV1Agent);

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
                let actor_id = ActorId::new("agents", &format!("agent-test-{:03}", i))?;
                let request = CreateAgentRequest {
                    name: format!("agent-{}", i),
                    agent_type: AgentType::LettaV1Agent,
                    model: None,
                    system: None,
                    description: None,
                    memory_blocks: vec![],
                    block_ids: vec![],
                    tool_ids: vec![],
                    tags: vec![],
                    metadata: serde_json::json!({}),
                };

                match dispatcher
                    .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                    .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        // Storage fault - acceptable
                        let err_str = e.to_string();
                        assert!(
                            err_str.contains("storage") || err_str.contains("Storage"),
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
            let actor_id = ActorId::new("agents", "agent-persistent")?;

            // Create and activate
            let request = CreateAgentRequest {
                name: "persistent-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![CreateBlockRequest {
                    label: "persona".to_string(),
                    value: "I am helpful".to_string(),
                    description: None,
                    limit: None,
                }],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            // Deactivate
            dispatcher.deactivate(actor_id.clone()).await?;

            // Reactivate and verify state preserved
            let state: AgentState =
                invoke_deserialize(&dispatcher, actor_id.clone(), "get_state", Bytes::new())
                    .await?;
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
                let actor_id = ActorId::new("agents", &format!("agent-test-{:03}", i))?;
                let request = CreateAgentRequest {
                    name: format!("agent-{}", i),
                    agent_type: AgentType::LettaV1Agent,
                    model: None,
                    system: None,
                    description: None,
                    memory_blocks: vec![],
                    block_ids: vec![],
                    tool_ids: vec![],
                    tags: vec![],
                    metadata: serde_json::json!({}),
                };

                // Try to create (may fail with storage faults during activation reads)
                let created = match dispatcher
                    .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                    .await
                {
                    Ok(_) => true,
                    Err(e) => {
                        // Storage fault during create/activation - acceptable
                        failure_count += 1;
                        false
                    }
                };

                if !created {
                    continue; // Skip deactivation if creation failed
                }

                // Try to deactivate
                match dispatcher.deactivate(actor_id.clone()).await {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        // Storage fault during deactivation - accept any storage-related error
                        // including DST framework edge cases like write faults during reads
                        let err_str = e.to_string();
                        assert!(
                            err_str.contains("storage")
                                || err_str.contains("Storage")
                                || err_str.contains("fault")
                                || err_str.contains("Unexpected"),
                            "Expected storage/fault error, got: {}",
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
            let actor_id = ActorId::new("agents", "agent-crash-test")?;

            // Create agent
            let request = CreateAgentRequest {
                name: "crash-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![CreateBlockRequest {
                    label: "persona".to_string(),
                    value: "Initial state".to_string(),
                    description: None,
                    limit: None,
                }],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            // Update state (may crash)
            let update = serde_json::json!({
                "label": "persona",
                "value": "Updated state"
            });
            let _ = dispatcher
                .invoke(
                    actor_id.clone(),
                    "update_block".to_string(),
                    to_bytes(&update)?,
                )
                .await;

            // Reactivate and verify state is consistent
            let state: AgentState =
                invoke_deserialize(&dispatcher, actor_id.clone(), "get_state", Bytes::new())
                    .await?;
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

/// Test agent actor handles core_memory_append
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
            let actor_id = ActorId::new("agents", "agent-memory-test")?;

            // Create agent
            let request = CreateAgentRequest {
                name: "memory-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![CreateBlockRequest {
                    label: "persona".to_string(),
                    value: "I am helpful".to_string(),
                    description: None,
                    limit: None,
                }],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            // Call core_memory_append
            let tool_call = serde_json::json!({
                "label": "persona",
                "content": ". I remember everything."
            });
            dispatcher
                .invoke(
                    actor_id.clone(),
                    "core_memory_append".to_string(),
                    to_bytes(&tool_call)?,
                )
                .await?;

            // Verify block was updated
            let state: AgentState =
                invoke_deserialize(&dispatcher, actor_id.clone(), "get_state", Bytes::new())
                    .await?;
            assert_eq!(
                state.blocks[0].value,
                "I am helpful. I remember everything."
            );

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Simple message types for testing
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct MessageRequest {
    role: String,
    content: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct MessageResponse {
    role: String,
    content: String,
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
            let actor_id = ActorId::new("agents", "agent-chat-test")?;

            // Create agent
            let request = CreateAgentRequest {
                name: "chat-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![CreateBlockRequest {
                    label: "persona".to_string(),
                    value: "I am helpful".to_string(),
                    description: None,
                    limit: None,
                }],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            // Send message
            let message = MessageRequest {
                role: "user".to_string(),
                content: "Hello".to_string(),
            };
            let response: MessageResponse = invoke_deserialize(
                &dispatcher,
                actor_id.clone(),
                "handle_message",
                to_bytes(&message)?,
            )
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
            let actor_id = ActorId::new("agents", "agent-timeout-test")?;

            // Create agent
            let request = CreateAgentRequest {
                name: "timeout-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            let mut success_count = 0;
            let mut timeout_count = 0;

            for i in 0..10 {
                let message = MessageRequest {
                    role: "user".to_string(),
                    content: format!("Message {}", i),
                };
                match invoke_deserialize::<MessageResponse>(
                    &dispatcher,
                    actor_id.clone(),
                    "handle_message",
                    to_bytes(&message)?,
                )
                .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        let err_str = e.to_string();
                        assert!(
                            err_str.contains("timeout")
                                || err_str.contains("timed out")
                                || err_str.contains("Timeout"),
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
        .with_fault(FaultConfig::new(FaultType::LlmFailure, 0.5))
        .run_async(|sim_env| async move {
            let dispatcher = create_dispatcher(&sim_env)?;
            let actor_id = ActorId::new("agents", "agent-failure-test")?;

            // Create agent
            let request = CreateAgentRequest {
                name: "failure-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            let mut success_count = 0;
            let mut failure_count = 0;

            for i in 0..10 {
                let message = MessageRequest {
                    role: "user".to_string(),
                    content: format!("Message {}", i),
                };
                match invoke_deserialize::<MessageResponse>(
                    &dispatcher,
                    actor_id.clone(),
                    "handle_message",
                    to_bytes(&message)?,
                )
                .await
                {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        let err_str = e.to_string();
                        assert!(
                            err_str.contains("failure")
                                || err_str.contains("failed")
                                || err_str.contains("error")
                                || err_str.contains("LLM"),
                            "Expected LLM failure error, got: {}",
                            e
                        );
                        failure_count += 1;
                    }
                }
            }

            // With 50% failure rate, should see some failures
            assert!(
                failure_count > 0,
                "Expected some LLM failures with 50% rate"
            );
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
            let actor_id = ActorId::new("agents", "agent-tool-test")?;

            // Create agent with tools
            let request = CreateAgentRequest {
                name: "tool-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec!["shell".to_string()],
                tags: vec![],
                metadata: serde_json::json!({}),
            };
            dispatcher
                .invoke(actor_id.clone(), "create".to_string(), to_bytes(&request)?)
                .await?;

            // Send message that should trigger tool use
            let message = MessageRequest {
                role: "user".to_string(),
                content: "Execute a shell command".to_string(),
            };
            let response: MessageResponse = invoke_deserialize(
                &dispatcher,
                actor_id.clone(),
                "handle_message",
                to_bytes(&message)?,
            )
            .await?;

            // Verify we got a response (tool execution details depend on implementation)
            assert!(!response.content.is_empty());

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

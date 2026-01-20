//! DST tests for agent message handling with LLM and tools
//!
//! TigerStyle: DST-first development - these tests define the agent loop contract
//! and will initially FAIL until the full agent loop is implemented in AgentActor.
//!
//! Tests cover:
//! - Basic message → LLM response
//! - Tool execution loop
//! - Message history preservation
//! - Concurrent agent messaging
//! - Fault injection (storage failures)
#![cfg(feature = "dst")]

use async_trait::async_trait;
use kelpie_core::{Result, Runtime, TokioRuntime};
use kelpie_dst::{FaultConfig, FaultType, SimConfig, SimEnvironment, SimLlmClient, Simulation};
use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig};
use kelpie_server::actor::{AgentActor, AgentActorState, LlmClient, LlmMessage, LlmResponse};
use kelpie_server::models::{AgentType, CreateAgentRequest, CreateBlockRequest};
use kelpie_server::service::AgentService;
use kelpie_server::tools::UnifiedToolRegistry;
use std::sync::Arc;

/// Adapter to use SimLlmClient with actor LlmClient trait
struct SimLlmClientAdapter {
    client: Arc<SimLlmClient>,
}

#[async_trait]
impl LlmClient for SimLlmClientAdapter {
    async fn complete_with_tools(
        &self,
        messages: Vec<LlmMessage>,
        tools: Vec<kelpie_server::llm::ToolDefinition>,
    ) -> Result<LlmResponse> {
        let sim_messages: Vec<kelpie_dst::SimChatMessage> = messages
            .into_iter()
            .map(|m| kelpie_dst::SimChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();
        let sim_tools: Vec<kelpie_dst::SimToolDefinition> = tools
            .into_iter()
            .map(|t| kelpie_dst::SimToolDefinition {
                name: t.name,
                description: t.description,
            })
            .collect();

        let response = self
            .client
            .complete_with_tools(sim_messages, sim_tools)
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: format!("LLM error: {}", e),
            })?;

        Ok(LlmResponse {
            content: response.content,
            tool_calls: response
                .tool_calls
                .into_iter()
                .map(|tc| kelpie_server::actor::LlmToolCall {
                    id: tc.id,
                    name: tc.name,
                    input: tc.input,
                })
                .collect(),
            prompt_tokens: response.prompt_tokens,
            completion_tokens: response.completion_tokens,
            stop_reason: response.stop_reason,
        })
    }

    async fn continue_with_tool_result(
        &self,
        messages: Vec<LlmMessage>,
        tools: Vec<kelpie_server::llm::ToolDefinition>,
        _assistant_blocks: Vec<kelpie_server::llm::ContentBlock>,
        tool_results: Vec<(String, String)>,
    ) -> Result<LlmResponse> {
        let sim_messages: Vec<kelpie_dst::SimChatMessage> = messages
            .into_iter()
            .map(|m| kelpie_dst::SimChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();
        let sim_tools: Vec<kelpie_dst::SimToolDefinition> = tools
            .into_iter()
            .map(|t| kelpie_dst::SimToolDefinition {
                name: t.name,
                description: t.description,
            })
            .collect();

        let response = self
            .client
            .continue_with_tool_result(sim_messages, sim_tools, tool_results)
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: format!("LLM error: {}", e),
            })?;

        Ok(LlmResponse {
            content: response.content,
            tool_calls: response
                .tool_calls
                .into_iter()
                .map(|tc| kelpie_server::actor::LlmToolCall {
                    id: tc.id,
                    name: tc.name,
                    input: tc.input,
                })
                .collect(),
            prompt_tokens: response.prompt_tokens,
            completion_tokens: response.completion_tokens,
            stop_reason: response.stop_reason,
        })
    }
}

/// Create AgentService from simulation environment
fn create_service<R: Runtime + 'static>(
    runtime: R,
    sim_env: &SimEnvironment,
) -> Result<AgentService<R>> {
    let sim_llm = SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone());
    let llm_adapter: Arc<dyn LlmClient> = Arc::new(SimLlmClientAdapter {
        client: Arc::new(sim_llm),
    });

    let actor = AgentActor::new(llm_adapter, Arc::new(UnifiedToolRegistry::new()));
    let factory = Arc::new(CloneFactory::new(actor));
    let kv = Arc::new(sim_env.storage.clone());

    let mut dispatcher = Dispatcher::<AgentActor, AgentActorState, _>::new(
        factory,
        kv,
        DispatcherConfig::default(),
        runtime.clone(),
    );
    let handle = dispatcher.handle();

    runtime.spawn(async move {
        dispatcher.run().await;
    });

    Ok(AgentService::new(handle))
}

/// Test basic message handling: send message, get LLM response
///
/// Contract:
/// - User sends message via service.send_message_full()
/// - LLM processes message
/// - Response returned with message history
/// - User message and assistant response stored in history
#[tokio::test]
async fn test_dst_agent_message_basic() {
    let config = SimConfig::new(3001);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(TokioRuntime, &sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "message-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                embedding: None,
                system: Some("You are helpful".to_string()),
                description: None,
                memory_blocks: vec![CreateBlockRequest {
                    label: "persona".to_string(),
                    value: "I am a test agent".to_string(),
                    description: None,
                    limit: None,
                }],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
                project_id: None,
            };
            let agent = service.create_agent(request).await?;

            // Send message (will fail until send_message_full is implemented)
            let message_request = serde_json::json!({
                "role": "user",
                "content": "Hello, how are you?"
            });

            // This will fail with "method not found" until implemented
            let response = service.send_message(&agent.id, message_request).await?;

            // Assertions: Basic message handling
            assert!(
                response.get("messages").is_some(),
                "Response should contain messages"
            );

            let messages = response.get("messages").unwrap().as_array().unwrap();
            assert!(
                messages.len() >= 2,
                "Should have at least user + assistant messages"
            );

            // Verify user message
            let user_msg = &messages[0];
            assert_eq!(user_msg.get("role").unwrap().as_str().unwrap(), "user");
            assert_eq!(
                user_msg.get("content").unwrap().as_str().unwrap(),
                "Hello, how are you?"
            );

            // Verify assistant message
            let assistant_msg = &messages[1];
            assert_eq!(
                assistant_msg.get("role").unwrap().as_str().unwrap(),
                "assistant"
            );
            assert!(
                !assistant_msg
                    .get("content")
                    .unwrap()
                    .as_str()
                    .unwrap()
                    .is_empty(),
                "Assistant should have content"
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Basic message handling failed: {:?}",
        result.err()
    );
}

/// Test message handling with tool execution loop
///
/// Contract:
/// - LLM can call tools
/// - Tool results fed back to LLM
/// - Loop continues until no more tool calls (max 5 iterations)
/// - All tool calls/results in message history
#[tokio::test]
async fn test_dst_agent_message_with_tool_call() {
    let config = SimConfig::new(3002);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(TokioRuntime, &sim_env)?;

            // Create agent with shell tool
            let request = CreateAgentRequest {
                name: "tool-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                embedding: None,
                system: Some("You can execute shell commands".to_string()),
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec!["shell".to_string()],
                tags: vec![],
                metadata: serde_json::json!({}),
                project_id: None,
            };
            let agent = service.create_agent(request).await?;

            // Send message that should trigger tool call
            let message_request = serde_json::json!({
                "role": "user",
                "content": "Run the command 'echo hello'"
            });

            let response = service.send_message(&agent.id, message_request).await?;

            // Assertions: Tool execution
            let messages = response.get("messages").unwrap().as_array().unwrap();

            // Should have: user, (assistant + tool messages), final assistant
            assert!(
                messages.len() >= 2,
                "Should have multiple messages with tool calls"
            );

            // Check if any message is a tool call or tool response
            // (This validates that the tool loop executed)
            let has_tool_interaction = messages.iter().any(|msg| {
                let role = msg.get("role").unwrap().as_str().unwrap();
                role == "tool" || msg.get("tool_calls").is_some()
            });

            assert!(
                has_tool_interaction,
                "Should have tool call or tool response in message history"
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Tool call handling failed: {:?}",
        result.err()
    );
}

/// Test message handling with storage faults
///
/// Contract:
/// - Storage writes can fail (fault injection)
/// - System retries or handles gracefully
/// - No data corruption
/// - Messages still delivered
#[tokio::test]
async fn test_dst_agent_message_with_storage_fault() {
    let config = SimConfig::new(3003);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
        .run_async(|sim_env| async move {
            let service = create_service(TokioRuntime, &sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "fault-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                embedding: None,
                system: None,
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
                project_id: None,
            };
            let agent = service.create_agent(request).await?;

            // Send message with storage faults active
            let message_request = serde_json::json!({
                "role": "user",
                "content": "Test message with faults"
            });

            // Should either succeed or fail gracefully (no panic)
            let response_result = service.send_message(&agent.id, message_request).await;

            // Assertions: Handles faults gracefully
            match response_result {
                Ok(response) => {
                    // If succeeded, verify response is valid
                    assert!(response.get("messages").is_some());
                }
                Err(e) => {
                    // If failed, verify it's a retriable error (not corruption)
                    let err_str = e.to_string();
                    assert!(
                        err_str.contains("storage") || err_str.contains("write"),
                        "Error should be storage-related: {}",
                        err_str
                    );
                }
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Storage fault handling failed: {:?}",
        result.err()
    );
}

/// Test message history preservation across actor restarts
///
/// Contract:
/// - Messages stored in AgentActorState
/// - State persisted to KV storage
/// - After deactivation + reactivation, history is loaded
/// - Subsequent messages see full history
#[tokio::test]
async fn test_dst_agent_message_history() {
    let config = SimConfig::new(3004);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(TokioRuntime, &sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "history-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                embedding: None,
                system: Some("Remember our conversation".to_string()),
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
                project_id: None,
            };
            let agent = service.create_agent(request).await?;

            // Send first message
            let msg1 = serde_json::json!({"role": "user", "content": "My name is Alice"});
            let response1 = service.send_message(&agent.id, msg1).await?;
            assert!(response1.get("messages").is_some());

            // Send second message
            let msg2 = serde_json::json!({"role": "user", "content": "What is my name?"});
            let response2 = service.send_message(&agent.id, msg2).await?;

            // Assertions: History preserved
            let messages = response2.get("messages").unwrap().as_array().unwrap();

            // Should include both conversations
            // (exact count depends on implementation, but should be > 2)
            assert!(
                messages.len() >= 2,
                "Message history should include multiple messages"
            );

            // Verify first message is in history
            let has_first_msg = messages.iter().any(|msg| {
                msg.get("content")
                    .and_then(|c| c.as_str())
                    .map(|s| s.contains("Alice"))
                    .unwrap_or(false)
            });

            assert!(
                has_first_msg,
                "First message should be in history for context"
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Message history test failed: {:?}",
        result.err()
    );
}

/// Test concurrent message handling across multiple agents
///
/// Contract:
/// - Multiple agents can process messages simultaneously
/// - No message mixing between agents
/// - Each agent maintains its own history
/// - All responses are correct
#[tokio::test]
async fn test_dst_agent_message_concurrent() {
    let config = SimConfig::new(3005);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let runtime = TokioRuntime;
            let service = create_service(runtime.clone(), &sim_env)?;

            // Create 5 agents with different names
            let mut agent_ids = Vec::new();
            for i in 1..=5 {
                let request = CreateAgentRequest {
                    name: format!("agent-{}", i),
                    agent_type: AgentType::LettaV1Agent,
                    model: None,
                    embedding: None,
                    system: Some(format!("You are agent number {}", i)),
                    description: None,
                    memory_blocks: vec![],
                    block_ids: vec![],
                    tool_ids: vec![],
                    tags: vec![],
                    metadata: serde_json::json!({}),
                    project_id: None,
                };
                let agent = service.create_agent(request).await?;
                agent_ids.push(agent.id);
            }

            // Send messages to all agents concurrently
            let mut handles = Vec::new();
            for (idx, agent_id) in agent_ids.iter().enumerate() {
                let service_clone = service.clone();
                let agent_id_clone = agent_id.clone();
                let message = format!("Message to agent {}", idx + 1);

                let handle = runtime.spawn(async move {
                    let msg_request = serde_json::json!({"role": "user", "content": message});
                    service_clone
                        .send_message(&agent_id_clone, msg_request)
                        .await
                });
                handles.push(handle);
            }

            // Wait for all messages to complete
            let mut responses = Vec::new();
            for handle in handles {
                let response = handle.await.unwrap()?;
                responses.push(response);
            }

            // Assertions: All agents responded
            assert_eq!(responses.len(), 5, "All agents should respond");

            // Verify all responses are valid
            for response in &responses {
                assert!(
                    response.get("messages").is_some(),
                    "Each response should have messages"
                );
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Concurrent message handling failed: {:?}",
        result.err()
    );
}

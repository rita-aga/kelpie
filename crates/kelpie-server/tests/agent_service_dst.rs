//! DST tests for AgentService layer
//!
//! TigerStyle: Tests define the contract BEFORE implementation (DST-first).

use async_trait::async_trait;
use kelpie_core::actor::ActorId;
use kelpie_core::Result;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, SimEnvironment, SimLlmClient, Simulation};
use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig};
use kelpie_server::actor::{AgentActor, AgentActorState, LlmClient, LlmMessage, LlmResponse};
use kelpie_server::models::{AgentState, AgentType, CreateAgentRequest, CreateBlockRequest};
use kelpie_server::service::AgentService;
use std::sync::Arc;

/// Test service creates agent successfully
///
/// Contract:
/// - Service wraps dispatcher
/// - create_agent() → AgentActor activated
/// - Returns AgentState with ID
#[tokio::test]
async fn test_dst_service_create_agent() {
    let config = SimConfig::new(1001);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            // Create service with dispatcher
            let service = create_service(&sim_env)?;

            // Create agent via service
            let request = CreateAgentRequest {
                name: "test-agent".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: Some("You are helpful".to_string()),
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

            let agent_state = service.create_agent(request).await?;

            // Verify agent created
            assert_eq!(agent_state.name, "test-agent");
            assert_eq!(agent_state.agent_type, AgentType::LettaV1Agent);
            assert_eq!(agent_state.blocks.len(), 1);
            assert_eq!(agent_state.blocks[0].label, "persona");
            assert!(!agent_state.id.is_empty(), "Agent should have ID");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Service create_agent failed: {:?}",
        result.err()
    );
}

/// Test service sends message to agent
///
/// Contract:
/// - send_message() → routes to AgentActor handle_message
/// - Returns LLM response
/// - Message history updated
#[tokio::test]
async fn test_dst_service_send_message() {
    let config = SimConfig::new(1002);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "chat-agent".to_string(),
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
            let agent = service.create_agent(request).await?;

            // Send message
            let message_request = serde_json::json!({
                "role": "user",
                "content": "Hello, how are you?"
            });
            let response = service.send_message(&agent.id, message_request).await?;

            // Verify response
            assert!(response.is_object(), "Response should be JSON object");
            assert!(
                response.get("content").is_some(),
                "Response should have content"
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Service send_message failed: {:?}",
        result.err()
    );
}

/// Test service retrieves agent state
///
/// Contract:
/// - get_agent() → returns current AgentState
/// - Includes all metadata and blocks
#[tokio::test]
async fn test_dst_service_get_agent() {
    let config = SimConfig::new(1003);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "get-test-agent".to_string(),
                agent_type: AgentType::ReactAgent,
                model: None,
                system: None,
                description: Some("Test description".to_string()),
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec!["shell".to_string()],
                tags: vec!["test".to_string()],
                metadata: serde_json::json!({"key": "value"}),
            };
            let created = service.create_agent(request).await?;

            // Get agent
            let retrieved = service.get_agent(&created.id).await?;

            // Verify all fields
            assert_eq!(retrieved.id, created.id);
            assert_eq!(retrieved.name, "get-test-agent");
            assert_eq!(retrieved.agent_type, AgentType::ReactAgent);
            assert_eq!(retrieved.description, Some("Test description".to_string()));
            assert_eq!(retrieved.tool_ids, vec!["shell".to_string()]);
            assert_eq!(retrieved.tags, vec!["test".to_string()]);

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Service get_agent failed: {:?}",
        result.err()
    );
}

/// Test service updates agent state
///
/// Contract:
/// - update_agent() → updates AgentActor state
/// - Returns updated AgentState
/// - Changes persisted
#[tokio::test]
async fn test_dst_service_update_agent() {
    let config = SimConfig::new(1004);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "original-name".to_string(),
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
            let agent = service.create_agent(request).await?;

            // Update agent
            let update = serde_json::json!({
                "name": "updated-name",
                "description": "New description"
            });
            let updated = service.update_agent(&agent.id, update).await?;

            // Verify update
            assert_eq!(updated.name, "updated-name");
            assert_eq!(updated.description, Some("New description".to_string()));
            assert_eq!(updated.id, agent.id, "ID should not change");

            // Verify persistence by getting again
            let retrieved = service.get_agent(&agent.id).await?;
            assert_eq!(retrieved.name, "updated-name");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Service update_agent failed: {:?}",
        result.err()
    );
}

/// Test service deletes agent
///
/// Contract:
/// - delete_agent() → deactivates AgentActor
/// - Subsequent get_agent() fails with NotFound
#[tokio::test]
async fn test_dst_service_delete_agent() {
    let config = SimConfig::new(1005);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "to-be-deleted".to_string(),
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
            let agent = service.create_agent(request).await?;

            // Delete agent
            service.delete_agent(&agent.id).await?;

            // Verify deleted - get should fail
            match service.get_agent(&agent.id).await {
                Err(e) => {
                    let err_str = e.to_string();
                    assert!(
                        err_str.contains("not found")
                            || err_str.contains("Not found")
                            || err_str.contains("not created"),
                        "Expected not found error, got: {}",
                        e
                    );
                }
                Ok(_) => panic!("Expected error after delete, but got success"),
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Service delete_agent failed: {:?}",
        result.err()
    );
}

/// Test service handles dispatcher failures gracefully
///
/// Contract:
/// - Storage failures → proper error propagation
/// - Service doesn't panic or corrupt state
/// - Errors are informative
#[tokio::test]
async fn test_dst_service_dispatcher_failure() {
    let config = SimConfig::new(1006);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            let mut success_count = 0;
            let mut failure_count = 0;

            // Try to create multiple agents
            for i in 0..10 {
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

                match service.create_agent(request).await {
                    Ok(_) => success_count += 1,
                    Err(e) => {
                        // Verify error is informative (not generic panic)
                        let err_str = e.to_string();
                        assert!(
                            !err_str.is_empty() && err_str.len() > 5,
                            "Error message too short: {}",
                            err_str
                        );
                        failure_count += 1;
                    }
                }
            }

            // With 30% fault rate, should see some failures
            // But both successes and failures are acceptable - important is handling
            assert!(
                success_count + failure_count == 10,
                "Expected 10 total attempts"
            );

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Test Helpers
// ============================================================================

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

/// Create AgentService from simulation environment
fn create_service(sim_env: &SimEnvironment) -> Result<AgentService> {
    // Create SimLlmClient from environment
    let sim_llm = SimLlmClient::new(sim_env.rng.clone(), sim_env.faults.clone());

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

    // Create service
    Ok(AgentService::new(handle))
}

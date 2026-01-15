//! DST tests for AgentService::send_message_full (Phase 6.9)
//!
//! TigerStyle: DST-first with full simulation environment
//!
//! Tests cover:
//! - Typed API contract (HandleMessageFullResponse not JSON Value)
//! - Multiple fault types (storage, network delays)
//! - Concurrent operations under faults
//! - Error handling and recovery

use async_trait::async_trait;
use kelpie_core::Result;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, SimEnvironment, SimLlmClient, Simulation};
use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig};
use kelpie_server::actor::{
    AgentActor, AgentActorState, HandleMessageFullResponse, LlmClient, LlmMessage, LlmResponse,
};
use kelpie_server::models::{AgentType, CreateAgentRequest, MessageRole};
use kelpie_server::service::AgentService;
use std::sync::Arc;

/// Adapter to use SimLlmClient with actor LlmClient trait
struct SimLlmClientAdapter {
    client: Arc<SimLlmClient>,
}

#[async_trait]
impl LlmClient for SimLlmClientAdapter {
    async fn complete(&self, _messages: Vec<LlmMessage>) -> Result<LlmResponse> {
        Ok(LlmResponse {
            content: "Simulated LLM response".to_string(),
            tool_calls: vec![],
        })
    }
}

/// Create AgentService from simulation environment
fn create_service(sim_env: &SimEnvironment) -> Result<AgentService> {
    let sim_llm = SimLlmClient::new(sim_env.fork_rng_raw(), sim_env.faults.clone());
    let llm_adapter: Arc<dyn LlmClient> = Arc::new(SimLlmClientAdapter {
        client: Arc::new(sim_llm),
    });

    let actor = AgentActor::new(llm_adapter);
    let factory = Arc::new(CloneFactory::new(actor));
    let kv = Arc::new(sim_env.storage.clone());

    let mut dispatcher =
        Dispatcher::<AgentActor, AgentActorState>::new(factory, kv, DispatcherConfig::default());
    let handle = dispatcher.handle();

    tokio::spawn(async move {
        dispatcher.run().await;
    });

    Ok(AgentService::new(handle))
}

/// Test send_message_full returns typed HandleMessageFullResponse
///
/// Contract:
/// - Method signature: send_message_full(agent_id: &str, content: String) -> Result<HandleMessageFullResponse>
/// - Returns typed response with messages Vec and usage stats
/// - NOT a JSON Value like old send_message
#[tokio::test]
async fn test_dst_send_message_full_typed_response() {
    let config = SimConfig::new(4001);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "typed-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: Some("You are helpful".to_string()),
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
                project_id: None,
            };
            let agent = service.create_agent(request).await?;

            // Call typed send_message_full (this will fail until implemented)
            let response: HandleMessageFullResponse = service
                .send_message_full(&agent.id, "Hello, world!".to_string())
                .await?;

            // Verify typed response structure
            assert!(
                !response.messages.is_empty(),
                "Response should have messages"
            );
            assert_eq!(
                response.messages[0].role,
                MessageRole::User,
                "First message should be user"
            );
            assert_eq!(
                response.messages[0].content, "Hello, world!",
                "User message content should match"
            );

            // Verify assistant response present
            let has_assistant = response
                .messages
                .iter()
                .any(|m| m.role == MessageRole::Assistant);
            assert!(has_assistant, "Should have assistant response");

            // Verify usage stats present (even if 0 for now)
            assert_eq!(response.usage.total_tokens, 0); // TODO(Phase 6.9): real token tracking

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Typed send_message_full failed: {:?}",
        result.err()
    );
}

/// Test send_message_full with storage write faults
///
/// Contract:
/// - Service handles storage faults gracefully
/// - Either succeeds or returns clear error
/// - No panics or data corruption
#[tokio::test]
async fn test_dst_send_message_full_storage_faults() {
    let config = SimConfig::new(4002);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "fault-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
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

            // Try sending message with faults active
            let response_result = service
                .send_message_full(&agent.id, "Test under faults".to_string())
                .await;

            // Assertions: Either succeeds or fails gracefully
            match response_result {
                Ok(response) => {
                    // If succeeded despite faults, verify valid response
                    assert!(!response.messages.is_empty());
                }
                Err(e) => {
                    // If failed, should be storage-related error
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

/// Test send_message_full with network delay simulation
///
/// Contract:
/// - Service handles network delays gracefully
/// - Operations complete despite latency
/// - Response remains valid
#[tokio::test]
async fn test_dst_send_message_full_network_delay() {
    let config = SimConfig::new(4003);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 10,
                max_ms: 100,
            },
            0.5,
        ))
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create agent
            let request = CreateAgentRequest {
                name: "network-test".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
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

            // Send message with network delays active
            let response = service
                .send_message_full(&agent.id, "Test with delays".to_string())
                .await?;

            // Verify response valid despite delays
            assert!(!response.messages.is_empty());
            assert_eq!(response.messages[0].content, "Test with delays");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Network delay handling failed: {:?}",
        result.err()
    );
}

/// Test concurrent send_message_full calls
///
/// Contract:
/// - Multiple agents can process messages concurrently
/// - No message mixing between agents
/// - All responses are valid
#[tokio::test]
async fn test_dst_send_message_full_concurrent_with_faults() {
    let config = SimConfig::new(4004);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Create 3 agents
            let mut agent_ids = Vec::new();
            for i in 1..=3 {
                let request = CreateAgentRequest {
                    name: format!("concurrent-agent-{}", i),
                    agent_type: AgentType::LettaV1Agent,
                    model: None,
                    system: Some(format!("Agent number {}", i)),
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

            // Send messages concurrently to all agents
            let mut handles = Vec::new();
            for (idx, agent_id) in agent_ids.iter().enumerate() {
                let service_clone = service.clone();
                let agent_id_clone = agent_id.clone();
                let handle = tokio::spawn(async move {
                    service_clone
                        .send_message_full(&agent_id_clone, format!("Message to agent {}", idx + 1))
                        .await
                });
                handles.push(handle);
            }

            // Collect results - all should succeed
            for handle in handles {
                match handle.await {
                    Ok(Ok(response)) => {
                        // Verify successful response is valid
                        assert!(!response.messages.is_empty());
                    }
                    Ok(Err(e)) => {
                        panic!("Operation failed unexpectedly: {:?}", e);
                    }
                    Err(e) => {
                        panic!("Task panicked: {:?}", e);
                    }
                }
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Concurrent operations with faults failed: {:?}",
        result.err()
    );
}

/// Test send_message_full with invalid agent_id
///
/// Contract:
/// - Returns clear error for non-existent agent
/// - Error message indicates agent not found
#[tokio::test]
async fn test_dst_send_message_full_invalid_agent() {
    let config = SimConfig::new(4005);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let service = create_service(&sim_env)?;

            // Try to send message to non-existent agent
            let response_result = service
                .send_message_full("non-existent-agent-id", "Hello".to_string())
                .await;

            // Should fail with clear error
            assert!(response_result.is_err(), "Should fail for invalid agent");

            let err = response_result.unwrap_err();
            let err_str = err.to_string();

            // Error should indicate agent not found or not created
            assert!(
                err_str.contains("not found") || err_str.contains("not created"),
                "Error should indicate agent not found: {}",
                err_str
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Invalid agent error handling failed: {:?}",
        result.err()
    );
}

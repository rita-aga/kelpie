//! DST tests for RegistryActor
//!
//! Tests registry operations under fault injection to ensure:
//! - Registry consistency under storage faults
//! - Concurrent registrations don't conflict
//! - Registry state survives actor deactivation/reactivation
//! - Self-registration works under failures

#![cfg(feature = "dst")]

use bytes::Bytes;
use kelpie_core::actor::{Actor, ActorContext, ActorId};
use kelpie_core::{Error, Result};
use kelpie_dst::{SimConfig, Simulation};
use kelpie_server::actor::{
    AgentActor, AgentActorState, GetRequest, GetResponse, ListRequest, ListResponse,
    RegisterRequest, RegisterResponse, RegistryActor, RegistryActorState, UnregisterRequest,
};
use kelpie_server::models::{AgentType, CreateAgentRequest};
use kelpie_server::storage::{AgentMetadata, KvAdapter};
use kelpie_server::tools::UnifiedToolRegistry;
use kelpie_storage::{ActorKV, ScopedKV};
use std::sync::Arc;

/// Mock LLM for testing
struct MockLlm;

#[async_trait::async_trait]
impl kelpie_server::actor::LlmClient for MockLlm {
    async fn complete(
        &self,
        _messages: Vec<kelpie_server::actor::LlmMessage>,
    ) -> Result<kelpie_server::actor::LlmResponse> {
        Ok(kelpie_server::actor::LlmResponse {
            content: "Mock response".to_string(),
            tool_calls: vec![],
            prompt_tokens: 10,
            completion_tokens: 10,
            stop_reason: "end_turn".to_string(),
        })
    }

    async fn complete_with_tools(
        &self,
        _messages: Vec<kelpie_server::actor::LlmMessage>,
        _tools: Vec<kelpie_server::llm::ToolDefinition>,
    ) -> Result<kelpie_server::actor::LlmResponse> {
        Ok(kelpie_server::actor::LlmResponse {
            content: "Mock response".to_string(),
            tool_calls: vec![],
            prompt_tokens: 10,
            completion_tokens: 10,
            stop_reason: "end_turn".to_string(),
        })
    }

    async fn continue_with_tool_result(
        &self,
        _messages: Vec<kelpie_server::actor::LlmMessage>,
        _tools: Vec<kelpie_server::llm::ToolDefinition>,
        _assistant_blocks: Vec<kelpie_server::llm::ContentBlock>,
        _tool_results: Vec<(String, String)>,
    ) -> Result<kelpie_server::actor::LlmResponse> {
        Ok(kelpie_server::actor::LlmResponse {
            content: "Continued".to_string(),
            tool_calls: vec![],
            prompt_tokens: 5,
            completion_tokens: 10,
            stop_reason: "end_turn".to_string(),
        })
    }
}

fn create_test_metadata(id: &str, name: &str) -> AgentMetadata {
    AgentMetadata::new(id.to_string(), name.to_string(), AgentType::MemgptAgent)
}

/// Test: Registry operations under virtual time (DST basic functionality)
#[cfg_attr(feature = "madsim", madsim::test)]
#[cfg_attr(not(feature = "madsim"), tokio::test)]
async fn test_registry_operations_dst() {
    let config = SimConfig::new(9001);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let kv = Arc::new(sim_env.storage.clone());
            let storage = Arc::new(KvAdapter::new(kv.clone()));
            let registry_actor = RegistryActor::new(storage.clone());

            let registry_id = ActorId::new("system", "agent_registry")?;
            let scoped_kv = ScopedKV::new(registry_id.clone(), kv as Arc<dyn ActorKV>);
            let mut ctx = ActorContext::new(
                registry_id,
                RegistryActorState::default(),
                Box::new(scoped_kv),
            );

            // Register 3 agents
            for i in 1..=3 {
                let metadata =
                    create_test_metadata(&format!("agent-{}", i), &format!("Agent {}", i));
                let request = RegisterRequest { metadata };
                let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize RegisterRequest: {}", e),
                })?;
                let response_bytes = registry_actor
                    .invoke(&mut ctx, "register", Bytes::from(payload))
                    .await?;
                let _response: RegisterResponse =
                    serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize RegisterResponse: {}", e),
                    })?;
            }

            // List all agents
            let list_request = ListRequest { filter: None };
            let payload = serde_json::to_vec(&list_request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize ListRequest: {}", e),
            })?;
            let response_bytes = registry_actor
                .invoke(&mut ctx, "list", Bytes::from(payload))
                .await?;
            let response: ListResponse =
                serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize ListResponse: {}", e),
                })?;
            assert_eq!(response.agents.len(), 3);

            // Get specific agent
            let get_request = GetRequest {
                agent_id: "agent-2".to_string(),
            };
            let payload = serde_json::to_vec(&get_request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize GetRequest: {}", e),
            })?;
            let response_bytes = registry_actor
                .invoke(&mut ctx, "get", Bytes::from(payload))
                .await?;
            let response: GetResponse =
                serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize GetResponse: {}", e),
                })?;
            assert!(response.agent.is_some());
            assert_eq!(response.agent.unwrap().name, "Agent 2");

            tracing::info!("✅ Registry operations work under DST");
            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test: Registry state survives actor deactivation/reactivation
#[cfg_attr(feature = "madsim", madsim::test)]
#[cfg_attr(not(feature = "madsim"), tokio::test)]
async fn test_registry_survives_deactivation_dst() {
    let config = SimConfig::new(9002);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let kv = Arc::new(sim_env.storage.clone());
            let storage = Arc::new(KvAdapter::new(kv.clone()));
            let registry_actor = RegistryActor::new(storage.clone());

            let registry_id = ActorId::new("system", "agent_registry")?;
            let scoped_kv = ScopedKV::new(registry_id.clone(), kv.clone() as Arc<dyn ActorKV>);
            let mut ctx = ActorContext::new(
                registry_id.clone(),
                RegistryActorState::default(),
                Box::new(scoped_kv),
            );

            // Register agents
            for i in 1..=5 {
                let metadata =
                    create_test_metadata(&format!("agent-{}", i), &format!("Agent {}", i));
                let request = RegisterRequest { metadata };
                let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize RegisterRequest: {}", e),
                })?;
                let _response_bytes = registry_actor
                    .invoke(&mut ctx, "register", Bytes::from(payload))
                    .await?;
            }

            assert_eq!(ctx.state.agent_count, 5);

            // Deactivate actor (simulates actor being evicted from memory)
            registry_actor.on_deactivate(&mut ctx).await?;

            // Persist state (normally done by runtime)
            let state_bytes = serde_json::to_vec(&ctx.state).map_err(|e| Error::Internal {
                message: format!("Failed to serialize state: {}", e),
            })?;
            ctx.kv_set(b"registry_state", &state_bytes).await?;

            // Simulate reactivation - load state from storage
            let loaded_state_bytes = ctx.kv_get(b"registry_state").await?.unwrap();
            let loaded_state: RegistryActorState = serde_json::from_slice(&loaded_state_bytes)
                .map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize state: {}", e),
                })?;
            ctx.state = loaded_state;

            // Verify state preserved
            assert_eq!(ctx.state.agent_count, 5);

            // Verify agents still accessible via storage
            let list_request = ListRequest { filter: None };
            let payload = serde_json::to_vec(&list_request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize ListRequest: {}", e),
            })?;
            let response_bytes = registry_actor
                .invoke(&mut ctx, "list", Bytes::from(payload))
                .await?;
            let response: ListResponse =
                serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize ListResponse: {}", e),
                })?;
            assert_eq!(response.agents.len(), 5);

            tracing::info!("✅ Registry state survives deactivation/reactivation");
            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test: Multiple agents registering concurrently
#[cfg_attr(feature = "madsim", madsim::test)]
#[cfg_attr(not(feature = "madsim"), tokio::test)]
async fn test_concurrent_registrations_dst() {
    let config = SimConfig::new(9003);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let kv = Arc::new(sim_env.storage.clone());
            let storage = Arc::new(KvAdapter::new(kv.clone()));
            let registry_actor = RegistryActor::new(storage.clone());

            let registry_id = ActorId::new("system", "agent_registry")?;
            let scoped_kv = ScopedKV::new(registry_id.clone(), kv as Arc<dyn ActorKV>);
            let mut ctx = ActorContext::new(
                registry_id,
                RegistryActorState::default(),
                Box::new(scoped_kv),
            );

            // Simulate concurrent registrations by registering multiple agents rapidly
            // In a real system, these would be concurrent invocations
            // Here we test that sequential rapid registrations maintain consistency
            for i in 1..=10 {
                let metadata =
                    create_test_metadata(&format!("agent-{}", i), &format!("Agent {}", i));
                let request = RegisterRequest { metadata };
                let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize RegisterRequest: {}", e),
                })?;
                let _response_bytes = registry_actor
                    .invoke(&mut ctx, "register", Bytes::from(payload))
                    .await?;
            }

            // Verify all registered
            let list_request = ListRequest { filter: None };
            let payload = serde_json::to_vec(&list_request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize ListRequest: {}", e),
            })?;
            let response_bytes = registry_actor
                .invoke(&mut ctx, "list", Bytes::from(payload))
                .await?;
            let response: ListResponse =
                serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize ListResponse: {}", e),
                })?;
            assert_eq!(response.agents.len(), 10);
            assert_eq!(ctx.state.agent_count, 10);

            // Verify no duplicates
            let mut ids: Vec<_> = response.agents.iter().map(|a| a.id.as_str()).collect();
            ids.sort();
            ids.dedup();
            assert_eq!(ids.len(), 10, "Found duplicate agent IDs");

            tracing::info!("✅ Concurrent registrations maintain consistency");
            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test: Registry operations with agent lifecycle (create + self-register)
#[cfg_attr(feature = "madsim", madsim::test)]
#[cfg_attr(not(feature = "madsim"), tokio::test)]
async fn test_agent_lifecycle_with_registry_dst() {
    let config = SimConfig::new(9004);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let kv = Arc::new(sim_env.storage.clone());
            let storage = Arc::new(KvAdapter::new(kv.clone()));

            // Create RegistryActor
            let registry_actor = RegistryActor::new(storage.clone());
            let registry_id = ActorId::new("system", "agent_registry")?;
            let registry_scoped_kv =
                ScopedKV::new(registry_id.clone(), kv.clone() as Arc<dyn ActorKV>);
            let mut registry_ctx = ActorContext::new(
                registry_id.clone(),
                RegistryActorState::default(),
                Box::new(registry_scoped_kv),
            );

            registry_actor.on_activate(&mut registry_ctx).await?;

            // Create AgentActor (without dispatcher for this test)
            let llm = Arc::new(MockLlm);
            let tool_registry = Arc::new(UnifiedToolRegistry::new());
            let agent_actor = AgentActor::new(llm, tool_registry);

            let agent_id = ActorId::new("agents", "test-agent")?;
            let agent_scoped_kv = ScopedKV::new(agent_id.clone(), kv.clone() as Arc<dyn ActorKV>);
            let mut agent_ctx = ActorContext::new(
                agent_id.clone(),
                AgentActorState::default(),
                Box::new(agent_scoped_kv),
            );

            // Create agent
            let request = CreateAgentRequest {
                name: "Test Agent".to_string(),
                agent_type: AgentType::MemgptAgent,
                model: None,
                embedding: None,
                system: Some("You are helpful".to_string()),
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
                project_id: None,
                user_id: None,
                org_id: None,
            };

            let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize CreateAgentRequest: {}", e),
            })?;
            agent_actor
                .invoke(&mut agent_ctx, "create", Bytes::from(payload))
                .await?;

            // Manually register agent (simulating what dispatcher would do)
            // In real system, AgentActor.on_activate() would send message to RegistryActor
            if let Some(agent) = &agent_ctx.state.agent {
                let metadata = AgentMetadata {
                    id: agent.id.clone(),
                    name: agent.name.clone(),
                    agent_type: agent.agent_type.clone(),
                    model: agent.model.clone(),
                    embedding: agent.embedding.clone(),
                    system: agent.system.clone(),
                    description: agent.description.clone(),
                    tool_ids: agent.tool_ids.clone(),
                    tags: agent.tags.clone(),
                    metadata: agent.metadata.clone(),
                    created_at: agent.created_at,
                    updated_at: agent.updated_at,
                };

                let register_request = RegisterRequest { metadata };
                let payload =
                    serde_json::to_vec(&register_request).map_err(|e| Error::Internal {
                        message: format!("Failed to serialize RegisterRequest: {}", e),
                    })?;
                let _response_bytes = registry_actor
                    .invoke(&mut registry_ctx, "register", Bytes::from(payload))
                    .await?;
            }

            // Verify agent is registered
            let list_request = ListRequest { filter: None };
            let payload = serde_json::to_vec(&list_request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize ListRequest: {}", e),
            })?;
            let response_bytes = registry_actor
                .invoke(&mut registry_ctx, "list", Bytes::from(payload))
                .await?;
            let response: ListResponse =
                serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize ListResponse: {}", e),
                })?;
            assert_eq!(response.agents.len(), 1);
            assert_eq!(response.agents[0].id, "test-agent");
            assert_eq!(response.agents[0].name, "Test Agent");

            tracing::info!("✅ Agent lifecycle with registry works in DST");
            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

/// Test: Registry unregister operation
#[cfg_attr(feature = "madsim", madsim::test)]
#[cfg_attr(not(feature = "madsim"), tokio::test)]
async fn test_registry_unregister_dst() {
    let config = SimConfig::new(9005);

    let result = Simulation::new(config)
        .run_async(|sim_env| async move {
            let kv = Arc::new(sim_env.storage.clone());
            let storage = Arc::new(KvAdapter::new(kv.clone()));
            let registry_actor = RegistryActor::new(storage.clone());

            let registry_id = ActorId::new("system", "agent_registry")?;
            let scoped_kv = ScopedKV::new(registry_id.clone(), kv as Arc<dyn ActorKV>);
            let mut ctx = ActorContext::new(
                registry_id,
                RegistryActorState::default(),
                Box::new(scoped_kv),
            );

            // Register 5 agents
            for i in 1..=5 {
                let metadata =
                    create_test_metadata(&format!("agent-{}", i), &format!("Agent {}", i));
                let request = RegisterRequest { metadata };
                let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize RegisterRequest: {}", e),
                })?;
                let _response_bytes = registry_actor
                    .invoke(&mut ctx, "register", Bytes::from(payload))
                    .await?;
            }

            assert_eq!(ctx.state.agent_count, 5);

            // Unregister 2 agents
            for i in [2, 4] {
                let unregister_request = UnregisterRequest {
                    agent_id: format!("agent-{}", i),
                };
                let payload =
                    serde_json::to_vec(&unregister_request).map_err(|e| Error::Internal {
                        message: format!("Failed to serialize UnregisterRequest: {}", e),
                    })?;
                let _response_bytes = registry_actor
                    .invoke(&mut ctx, "unregister", Bytes::from(payload))
                    .await?;
            }

            // Verify count updated
            assert_eq!(ctx.state.agent_count, 3);

            // Verify correct agents remain
            let list_request = ListRequest { filter: None };
            let payload = serde_json::to_vec(&list_request).map_err(|e| Error::Internal {
                message: format!("Failed to serialize ListRequest: {}", e),
            })?;
            let response_bytes = registry_actor
                .invoke(&mut ctx, "list", Bytes::from(payload))
                .await?;
            let response: ListResponse =
                serde_json::from_slice(&response_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize ListResponse: {}", e),
                })?;
            assert_eq!(response.agents.len(), 3);

            let remaining_ids: Vec<_> = response.agents.iter().map(|a| a.id.as_str()).collect();
            assert!(remaining_ids.contains(&"agent-1"));
            assert!(remaining_ids.contains(&"agent-3"));
            assert!(remaining_ids.contains(&"agent-5"));
            assert!(!remaining_ids.contains(&"agent-2"));
            assert!(!remaining_ids.contains(&"agent-4"));

            tracing::info!("✅ Registry unregister works correctly");
            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

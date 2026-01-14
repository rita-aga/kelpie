//! AgentActor implementation
//!
//! TigerStyle: Single actor type for all agent types, state-based configuration.

use super::llm_trait::{LlmClient, LlmMessage};
use super::state::AgentActorState;
use crate::models::{AgentState, CreateAgentRequest, UpdateAgentRequest};
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::actor::{Actor, ActorContext};
use kelpie_core::{Error, Result};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// AgentActor - implements virtual actor for agents
///
/// Single actor type handles all agent types (MemgptAgent, LettaV1Agent, ReactAgent).
/// Agent-specific behavior is determined by configuration in state, not by actor type.
///
/// TigerStyle: Explicit operations, serializable state, assertions for invariants.
#[derive(Clone)]
pub struct AgentActor {
    /// LLM client for message handling
    llm: Arc<dyn LlmClient>,
}

impl AgentActor {
    /// Create a new AgentActor with LLM client
    pub fn new(llm: Arc<dyn LlmClient>) -> Self {
        Self { llm }
    }

    /// Handle "create" operation - initialize agent from request
    ///
    /// Returns the created AgentState directly to avoid timing window
    /// between state creation and persistence (BUG-001 fix)
    async fn handle_create(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        request: CreateAgentRequest,
    ) -> Result<AgentState> {
        // TigerStyle: Assertions for preconditions
        assert!(ctx.state.agent.is_none(), "Agent already created");

        // Create agent state from request
        let mut agent_state = AgentState::from_request(request);

        // Set agent ID to match actor ID (just the id part, not the full namespace:id)
        agent_state.id = ctx.id.id().to_string();

        // Store in actor state
        ctx.state.agent = Some(agent_state.clone());

        // Return the created state directly (BUG-001 fix)
        Ok(agent_state)
    }

    /// Handle "get_state" operation - return current agent state
    async fn handle_get_state(&self, ctx: &ActorContext<AgentActorState>) -> Result<AgentState> {
        ctx.state.agent().cloned().ok_or_else(|| Error::Internal {
            message: "Agent not created".to_string(),
        })
    }

    /// Handle "update_block" operation - update a memory block
    async fn handle_update_block(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        update: BlockUpdate,
    ) -> Result<()> {
        let updated = ctx.state.update_block(&update.label, |block| {
            block.value = update.value;
            block.updated_at = chrono::Utc::now();
        });

        if !updated {
            return Err(Error::Internal {
                message: format!("Block '{}' not found", update.label),
            });
        }

        Ok(())
    }

    /// Handle "core_memory_append" operation - append to a memory block
    async fn handle_core_memory_append(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        append: CoreMemoryAppend,
    ) -> Result<()> {
        let updated = ctx.state.update_block(&append.label, |block| {
            block.value.push_str(&append.content);
            block.updated_at = chrono::Utc::now();
        });

        if !updated {
            return Err(Error::Internal {
                message: format!("Block '{}' not found", append.label),
            });
        }

        Ok(())
    }

    /// Handle "update_agent" operation - update agent metadata
    async fn handle_update_agent(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        update: UpdateAgentRequest,
    ) -> Result<AgentState> {
        // Get mutable agent state
        let agent = ctx.state.agent_mut().ok_or_else(|| Error::Internal {
            message: "Agent not created".to_string(),
        })?;

        // Apply update
        agent.apply_update(update);

        // Return updated state
        ctx.state.agent().cloned().ok_or_else(|| Error::Internal {
            message: "Agent not created".to_string(),
        })
    }

    /// Handle "delete_agent" operation - mark agent as deleted
    async fn handle_delete_agent(&self, ctx: &mut ActorContext<AgentActorState>) -> Result<()> {
        // Clear agent state to mark as deleted
        ctx.state.agent = None;

        // Delete state from storage
        ctx.kv_delete(b"agent_state").await?;

        Ok(())
    }

    /// Handle "handle_message" operation - process user message with LLM
    async fn handle_handle_message(
        &self,
        ctx: &ActorContext<AgentActorState>,
        request: HandleMessageRequest,
    ) -> Result<HandleMessageResponse> {
        // TigerStyle: Validate agent exists
        let agent = ctx.state.agent().ok_or_else(|| Error::Internal {
            message: "Agent not created".to_string(),
        })?;

        // Build prompt from agent blocks
        let mut messages = Vec::new();

        // Add system prompt if present
        if let Some(system) = &agent.system {
            messages.push(LlmMessage {
                role: "system".to_string(),
                content: system.clone(),
            });
        }

        // Add memory blocks as system context
        for block in &agent.blocks {
            messages.push(LlmMessage {
                role: "system".to_string(),
                content: format!("[{}]\n{}", block.label, block.value),
            });
        }

        // Add user message
        messages.push(LlmMessage {
            role: request.role,
            content: request.content,
        });

        // Call LLM
        let response = self.llm.complete(messages).await?;

        Ok(HandleMessageResponse {
            role: "assistant".to_string(),
            content: response.content,
        })
    }
}

/// Block update request
#[derive(Debug, Clone, Serialize, Deserialize)]
struct BlockUpdate {
    label: String,
    value: String,
}

/// Core memory append request
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CoreMemoryAppend {
    label: String,
    content: String,
}

/// Handle message request
#[derive(Debug, Clone, Serialize, Deserialize)]
struct HandleMessageRequest {
    role: String,
    content: String,
}

/// Handle message response
#[derive(Debug, Clone, Serialize, Deserialize)]
struct HandleMessageResponse {
    role: String,
    content: String,
}

#[async_trait]
impl Actor for AgentActor {
    type State = AgentActorState;

    async fn invoke(
        &self,
        ctx: &mut ActorContext<Self::State>,
        operation: &str,
        payload: Bytes,
    ) -> Result<Bytes> {
        // TigerStyle: Explicit operation routing with clear error messages
        match operation {
            "create" => {
                let request: CreateAgentRequest =
                    serde_json::from_slice(&payload).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize CreateAgentRequest: {}", e),
                    })?;
                let agent_state = self.handle_create(ctx, request).await?;
                let response = serde_json::to_vec(&agent_state).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize AgentState: {}", e),
                })?;
                Ok(Bytes::from(response))
            }
            "get_state" => {
                let state = self.handle_get_state(ctx).await?;
                let response = serde_json::to_vec(&state).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize AgentState: {}", e),
                })?;
                Ok(Bytes::from(response))
            }
            "update_block" => {
                let update: BlockUpdate =
                    serde_json::from_slice(&payload).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize BlockUpdate: {}", e),
                    })?;
                self.handle_update_block(ctx, update).await?;
                Ok(Bytes::from("{}"))
            }
            "core_memory_append" => {
                let append: CoreMemoryAppend =
                    serde_json::from_slice(&payload).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize CoreMemoryAppend: {}", e),
                    })?;
                self.handle_core_memory_append(ctx, append).await?;
                Ok(Bytes::from("{}"))
            }
            "update_agent" => {
                let update: UpdateAgentRequest =
                    serde_json::from_slice(&payload).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize UpdateAgentRequest: {}", e),
                    })?;
                let response = self.handle_update_agent(ctx, update).await?;
                let response_bytes =
                    serde_json::to_vec(&response).map_err(|e| Error::Internal {
                        message: format!("Failed to serialize AgentState: {}", e),
                    })?;
                Ok(Bytes::from(response_bytes))
            }
            "handle_message" => {
                let request: HandleMessageRequest =
                    serde_json::from_slice(&payload).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize HandleMessageRequest: {}", e),
                    })?;
                let response = self.handle_handle_message(ctx, request).await?;
                let response_bytes =
                    serde_json::to_vec(&response).map_err(|e| Error::Internal {
                        message: format!("Failed to serialize HandleMessageResponse: {}", e),
                    })?;
                Ok(Bytes::from(response_bytes))
            }
            "delete_agent" => {
                self.handle_delete_agent(ctx).await?;
                Ok(Bytes::from("{}"))
            }
            _ => Err(Error::Internal {
                message: format!("Unknown operation: {}", operation),
            }),
        }
    }

    async fn on_activate(&self, ctx: &mut ActorContext<Self::State>) -> Result<()> {
        // TigerStyle: Log activation for debugging
        debug_assert!(!ctx.id.id().is_empty(), "ActorId must not be empty");

        // Try to load existing state from KV store
        let state_key = b"agent_state";
        if let Some(state_bytes) = ctx.kv_get(state_key).await? {
            let loaded_state: AgentActorState =
                serde_json::from_slice(&state_bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize AgentActorState: {}", e),
                })?;
            ctx.state = loaded_state;
        }
        // If no state exists, that's OK - will be created on first "create" operation

        Ok(())
    }

    async fn on_deactivate(&self, ctx: &mut ActorContext<Self::State>) -> Result<()> {
        // TigerStyle: Persist state on deactivation
        let state_key = b"agent_state";
        let state_bytes = serde_json::to_vec(&ctx.state).map_err(|e| Error::Internal {
            message: format!("Failed to serialize AgentActorState: {}", e),
        })?;
        ctx.kv_set(state_key, &state_bytes).await?;

        Ok(())
    }
}

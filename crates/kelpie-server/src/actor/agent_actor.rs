//! AgentActor implementation
//!
//! TigerStyle: Single actor type for all agent types, state-based configuration.

use super::llm_trait::{LlmClient, LlmMessage, LlmToolCall};
use super::state::AgentActorState;
use crate::models::{AgentState, CreateAgentRequest, Message, MessageRole, ToolCall, UpdateAgentRequest, UsageStats};
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

    /// Handle message with full agent loop (Phase 6.8)
    ///
    /// Implements complete agent behavior:
    /// 1. Add user message to history
    /// 2. Build LLM prompt from agent blocks + history
    /// 3. Call LLM with tools
    /// 4. Execute tool calls (loop up to 5 iterations)
    /// 5. Add assistant response to history
    /// 6. Return all messages + usage stats
    async fn handle_message_full(
        &self,
        ctx: &mut ActorContext<AgentActorState>,
        request: HandleMessageFullRequest,
    ) -> Result<HandleMessageFullResponse> {
        // TigerStyle: Validate preconditions
        assert!(!request.content.is_empty(), "message content must not be empty");

        // Clone agent data before any mutable operations
        let agent = ctx.state.agent().ok_or_else(|| Error::Internal {
            message: "Agent not created".to_string(),
        })?.clone();

        // 1. Create and store user message
        let user_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: request.content.clone(),
            tool_call_id: None,
            tool_calls: None,
            created_at: chrono::Utc::now(),
        };

        // Store user message
        ctx.state.add_message(user_msg.clone());

        // 2. Build LLM messages
        let mut llm_messages = Vec::new();

        // System prompt
        if let Some(system) = &agent.system {
            llm_messages.push(LlmMessage {
                role: "system".to_string(),
                content: system.clone(),
            });
        }

        // Memory blocks as system context
        for block in &agent.blocks {
            llm_messages.push(LlmMessage {
                role: "system".to_string(),
                content: format!("[{}]\n{}", block.label, block.value),
            });
        }

        // Recent message history (last 20)
        for msg in ctx.state.recent_messages(20) {
            let role = match msg.role {
                MessageRole::User => "user",
                MessageRole::Assistant => "assistant",
                MessageRole::System => "system",
                MessageRole::Tool => "tool",
            };
            llm_messages.push(LlmMessage {
                role: role.to_string(),
                content: msg.content.clone(),
            });
        }

        // 3. Call LLM
        let mut response = self.llm.complete(llm_messages.clone()).await?;

        // TODO(Phase 6.9): Track real token usage from LLM API
        // Currently returns 0 because LlmClient trait doesn't provide token counts.
        // Will be fixed when integrating with real LLM API that returns usage metadata.
        let total_prompt_tokens = 0u64;
        let total_completion_tokens = 0u64;

        let mut iterations = 0u32;
        const MAX_ITERATIONS: u32 = 5;

        // TigerStyle: Explicit limit enforcement
        assert!(MAX_ITERATIONS > 0, "MAX_ITERATIONS must be positive");

        // 4. Tool execution loop
        while !response.tool_calls.is_empty() && iterations < MAX_ITERATIONS {
            iterations += 1;

            // Map LlmToolCall to ToolCall for message storage
            let tool_calls_mapped = Some(
                response
                    .tool_calls
                    .iter()
                    .map(|tc| ToolCall {
                        id: tc.id.clone(),
                        name: tc.name.clone(),
                        arguments: tc.input.clone(),
                    })
                    .collect(),
            );

            // Store assistant message with tool calls
            let assistant_msg = Message {
                id: uuid::Uuid::new_v4().to_string(),
                agent_id: ctx.id.id().to_string(),
                message_type: "assistant_message".to_string(),
                role: MessageRole::Assistant,
                content: response.content.clone(),
                tool_call_id: None,
                tool_calls: tool_calls_mapped,
                created_at: chrono::Utc::now(),
            };
            ctx.state.add_message(assistant_msg);

            // Execute each tool
            for tool_call in &response.tool_calls {
                let result = self.execute_tool(ctx, tool_call).await?;

                // Store tool result message
                let tool_msg = Message {
                    id: uuid::Uuid::new_v4().to_string(),
                    agent_id: ctx.id.id().to_string(),
                    message_type: "tool_return_message".to_string(),
                    role: MessageRole::Tool,
                    content: result,
                    tool_call_id: Some(tool_call.id.clone()),
                    tool_calls: None,
                    created_at: chrono::Utc::now(),
                };
                ctx.state.add_message(tool_msg);
            }

            // Rebuild messages with tool results for next LLM call
            llm_messages.clear();

            // Re-add system context
            if let Some(system) = &agent.system {
                llm_messages.push(LlmMessage {
                    role: "system".to_string(),
                    content: system.clone(),
                });
            }
            for block in &agent.blocks {
                llm_messages.push(LlmMessage {
                    role: "system".to_string(),
                    content: format!("[{}]\n{}", block.label, block.value),
                });
            }

            // Add recent history including tool results
            for msg in ctx.state.recent_messages(20) {
                let role = match msg.role {
                    MessageRole::User => "user",
                    MessageRole::Assistant => "assistant",
                    MessageRole::System => "system",
                    MessageRole::Tool => "tool",
                };
                llm_messages.push(LlmMessage {
                    role: role.to_string(),
                    content: msg.content.clone(),
                });
            }

            // Continue conversation
            response = self.llm.complete(llm_messages.clone()).await?;
        }

        // 5. Store final assistant response
        let assistant_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            message_type: "assistant_message".to_string(),
            role: MessageRole::Assistant,
            content: response.content.clone(),
            tool_call_id: None,
            tool_calls: None,
            created_at: chrono::Utc::now(),
        };
        ctx.state.add_message(assistant_msg);

        // 6. Return response with all conversation history
        // Note: Tests expect full history, not just current turn messages
        Ok(HandleMessageFullResponse {
            messages: ctx.state.all_messages().to_vec(),
            usage: UsageStats {
                prompt_tokens: total_prompt_tokens,
                completion_tokens: total_completion_tokens,
                total_tokens: total_prompt_tokens + total_completion_tokens,
            },
        })
    }

    /// Execute a tool call (Phase 6.8)
    ///
    /// TigerStyle: Explicit error handling, no unwrap
    async fn execute_tool(
        &self,
        _ctx: &ActorContext<AgentActorState>,
        tool_call: &LlmToolCall,
    ) -> Result<String> {
        // TigerStyle: Validate preconditions
        assert!(!tool_call.name.is_empty(), "tool name must not be empty");
        assert!(!tool_call.id.is_empty(), "tool id must not be empty");

        match tool_call.name.as_str() {
            "shell" => {
                let command = tool_call
                    .input
                    .get("command")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| Error::Internal {
                        message: "shell tool requires 'command' parameter".to_string(),
                    })?;

                // Placeholder - return simulated result
                // TODO: Integrate with kelpie-sandbox in Phase 8
                Ok(format!("Executed: {}", command))
            }
            _ => Err(Error::Internal {
                message: format!("Unknown tool: {}", tool_call.name),
            }),
        }
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

/// Request for full message handling (Phase 6.8)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleMessageFullRequest {
    pub content: String,
}

/// Response from full message handling (Phase 6.8)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleMessageFullResponse {
    pub messages: Vec<Message>,
    pub usage: UsageStats,
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
            "handle_message_full" => {
                let request: HandleMessageFullRequest =
                    serde_json::from_slice(&payload).map_err(|e| Error::Internal {
                        message: format!("Failed to deserialize HandleMessageFullRequest: {}", e),
                    })?;
                let response = self.handle_message_full(ctx, request).await?;
                let response_bytes =
                    serde_json::to_vec(&response).map_err(|e| Error::Internal {
                        message: format!("Failed to serialize HandleMessageFullResponse: {}", e),
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

//! AgentActor implementation
//!
//! TigerStyle: Single actor type for all agent types, state-based configuration.

use super::llm_trait::{LlmClient, LlmMessage, LlmToolCall};
use super::state::AgentActorState;
use crate::models::{
    AgentState, CreateAgentRequest, Message, MessageRole, ToolCall, UpdateAgentRequest, UsageStats,
};
use crate::tools::{parse_pause_signal, ToolExecutionContext, ToolSignal, UnifiedToolRegistry};
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
    /// Unified tool registry for tool execution
    tool_registry: Arc<UnifiedToolRegistry>,
    /// Optional dispatcher for inter-actor communication (e.g., RegistryActor registration)
    /// If None, self-registration is skipped (backward compatible)
    dispatcher: Option<kelpie_runtime::DispatcherHandle<kelpie_core::TokioRuntime>>,
}

impl AgentActor {
    /// Create a new AgentActor with LLM client
    pub fn new(llm: Arc<dyn LlmClient>, tool_registry: Arc<UnifiedToolRegistry>) -> Self {
        Self {
            llm,
            tool_registry,
            dispatcher: None,
        }
    }

    /// Create AgentActor with dispatcher for self-registration
    pub fn with_dispatcher(
        mut self,
        dispatcher: kelpie_runtime::DispatcherHandle<kelpie_core::TokioRuntime>,
    ) -> Self {
        self.dispatcher = Some(dispatcher);
        self
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
        assert!(
            !request.content.is_empty(),
            "message content must not be empty"
        );

        // Clone agent data before any mutable operations
        let agent = ctx
            .state
            .agent()
            .ok_or_else(|| Error::Internal {
                message: "Agent not created".to_string(),
            })?
            .clone();

        // 1. Create and store user message
        let user_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: request.content.clone(),
            tool_call_id: None,
            tool_calls: vec![],
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
            // Skip tool and system messages - Claude API doesn't support role "tool"
            if msg.role == MessageRole::Tool || msg.role == MessageRole::System {
                continue;
            }
            let role = match msg.role {
                MessageRole::User => "user",
                MessageRole::Assistant => "assistant",
                MessageRole::System => "system", // Won't reach
                MessageRole::Tool => "user",     // Won't reach
            };
            llm_messages.push(LlmMessage {
                role: role.to_string(),
                content: msg.content.clone(),
            });
        }

        // 3. Get tool definitions (filtered by agent capabilities + tool_ids)
        let capabilities = agent.agent_type.capabilities();
        let all_tools = self.tool_registry.get_tool_definitions().await;

        tracing::debug!(
            agent_id = %ctx.id.id(),
            agent_tool_ids = ?agent.tool_ids,
            all_tool_names = ?all_tools.iter().map(|t| &t.name).collect::<Vec<_>>(),
            "Tool filtering inputs"
        );

        // TigerStyle: Tools allowed if in static capabilities OR in agent's tool_ids
        let tools: Vec<_> = all_tools
            .into_iter()
            .filter(|t| {
                capabilities.allowed_tools.contains(&t.name) || agent.tool_ids.contains(&t.name)
            })
            .collect();

        tracing::debug!(
            agent_id = %ctx.id.id(),
            total_tools = tools.len(),
            tool_names = ?tools.iter().map(|t| &t.name).collect::<Vec<_>>(),
            "Loaded tools for LLM prompt"
        );

        // 4. Call LLM with tools
        let mut response = self
            .llm
            .complete_with_tools(llm_messages.clone(), tools.clone())
            .await?;

        let mut total_prompt_tokens = response.prompt_tokens;
        let mut total_completion_tokens = response.completion_tokens;
        let mut iterations = 0u32;
        const MAX_ITERATIONS: u32 = 5;

        // TigerStyle: Explicit limit enforcement
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(MAX_ITERATIONS > 0, "MAX_ITERATIONS must be positive");
        }

        // 5. Tool execution loop
        while !response.tool_calls.is_empty() && iterations < MAX_ITERATIONS {
            iterations += 1;

            // Store assistant message (without tool calls - those are separate messages in Letta format)
            let assistant_msg = Message {
                id: uuid::Uuid::new_v4().to_string(),
                agent_id: ctx.id.id().to_string(),
                message_type: "assistant_message".to_string(),
                role: MessageRole::Assistant,
                content: response.content.clone(),
                tool_call_id: None,
                tool_calls: vec![],
                created_at: chrono::Utc::now(),
            };
            ctx.state.add_message(assistant_msg);

            // Execute each tool and create tool_call/tool_return messages per Letta format
            let mut tool_results = Vec::new();
            let mut should_break = false;
            for tool_call in &response.tool_calls {
                // Create tool_call message for this specific tool
                let tool_call_msg = Message {
                    id: uuid::Uuid::new_v4().to_string(),
                    agent_id: ctx.id.id().to_string(),
                    message_type: "tool_call_message".to_string(),
                    role: MessageRole::Assistant,
                    content: response.content.clone(),
                    tool_call_id: None,
                    tool_calls: vec![ToolCall {
                        id: tool_call.id.clone(),
                        name: tool_call.name.clone(),
                        arguments: tool_call.input.clone(),
                    }],
                    created_at: chrono::Utc::now(),
                };
                ctx.state.add_message(tool_call_msg);
                let context = ToolExecutionContext {
                    agent_id: Some(ctx.id.id().to_string()),
                    project_id: agent.project_id.clone(),
                };
                let exec_result = self
                    .tool_registry
                    .execute_with_context(&tool_call.name, &tool_call.input, Some(&context))
                    .await;
                let result = exec_result.output.clone();
                tool_results.push((tool_call.id.clone(), result.clone()));

                // Store tool result message
                let tool_msg = Message {
                    id: uuid::Uuid::new_v4().to_string(),
                    agent_id: ctx.id.id().to_string(),
                    message_type: "tool_return_message".to_string(),
                    role: MessageRole::Tool,
                    content: result,
                    tool_call_id: Some(tool_call.id.clone()),
                    tool_calls: vec![],
                    created_at: chrono::Utc::now(),
                };
                ctx.state.add_message(tool_msg);

                if let Some((minutes, pause_until_ms)) = parse_pause_signal(&exec_result.output) {
                    if !capabilities.supports_heartbeats {
                        tracing::warn!(
                            agent_id = %ctx.id.id(),
                            agent_type = ?agent.agent_type,
                            "Agent called pause_heartbeats but type doesn't support heartbeats"
                        );
                    } else {
                        ctx.state.is_paused = true;
                        ctx.state.pause_until_ms = Some(pause_until_ms);
                        should_break = true;
                        tracing::info!(
                            agent_id = %ctx.id.id(),
                            pause_minutes = minutes,
                            pause_until_ms = pause_until_ms,
                            "Agent requested heartbeat pause"
                        );
                    }
                }

                if let ToolSignal::PauseHeartbeats {
                    minutes,
                    pause_until_ms,
                } = exec_result.signal
                {
                    if !capabilities.supports_heartbeats {
                        tracing::warn!(
                            agent_id = %ctx.id.id(),
                            agent_type = ?agent.agent_type,
                            "Agent called pause_heartbeats but type doesn't support heartbeats (via signal)"
                        );
                    } else {
                        ctx.state.is_paused = true;
                        ctx.state.pause_until_ms = Some(pause_until_ms);
                        should_break = true;
                        tracing::info!(
                            agent_id = %ctx.id.id(),
                            pause_minutes = minutes,
                            pause_until_ms = pause_until_ms,
                            "Agent requested heartbeat pause (via signal)"
                        );
                    }
                }
            }

            if should_break {
                break;
            }

            // Build assistant content blocks for continuation
            let mut assistant_blocks = Vec::new();
            if !response.content.is_empty() {
                assistant_blocks.push(crate::llm::ContentBlock::Text {
                    text: response.content.clone(),
                });
            }
            for tc in &response.tool_calls {
                assistant_blocks.push(crate::llm::ContentBlock::ToolUse {
                    id: tc.id.clone(),
                    name: tc.name.clone(),
                    input: tc.input.clone(),
                });
            }

            // Continue conversation after tool execution
            response = self
                .llm
                .continue_with_tool_result(
                    llm_messages.clone(),
                    tools.clone(),
                    assistant_blocks,
                    tool_results,
                )
                .await?;
            total_prompt_tokens += response.prompt_tokens;
            total_completion_tokens += response.completion_tokens;
        }

        // 5. Store final assistant response (with dual-mode send_message support)
        // Check if agent used send_message tool in final iteration
        let final_content = self.extract_send_message_content(&response, ctx).await?;

        let assistant_msg = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: ctx.id.id().to_string(),
            message_type: "assistant_message".to_string(),
            role: MessageRole::Assistant,
            content: final_content,
            tool_call_id: None,
            tool_calls: vec![],
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

    /// Extract send_message content for dual-mode support
    ///
    /// If the LLM response includes send_message tool calls, extract and return
    /// the message content from those calls. Supports multiple send_message calls
    /// in one turn (concatenates them). If no send_message calls, returns the
    /// direct LLM response content as fallback.
    ///
    /// This implements Letta's dual-mode messaging:
    /// - Agent calls send_message("text") -> use that text
    /// - Agent doesn't call send_message -> use LLM's direct response
    async fn extract_send_message_content(
        &self,
        response: &super::llm_trait::LlmResponse,
        _ctx: &ActorContext<AgentActorState>,
    ) -> Result<String> {
        // Find all send_message tool calls
        let send_message_calls: Vec<&LlmToolCall> = response
            .tool_calls
            .iter()
            .filter(|tc| tc.name == "send_message")
            .collect();

        // If no send_message calls, use direct LLM response (fallback mode)
        if send_message_calls.is_empty() {
            return Ok(response.content.clone());
        }

        // Extract message content from send_message calls
        let mut messages = Vec::new();
        for tool_call in send_message_calls {
            if let Some(message) = tool_call.input.get("message").and_then(|v| v.as_str()) {
                messages.push(message.to_string());
            }
        }

        // Concatenate multiple send_message calls with newlines
        if messages.is_empty() {
            // send_message was called but no valid message parameter - return direct response
            Ok(response.content.clone())
        } else {
            // Use send_message content (join multiple calls with newlines)
            Ok(messages.join("\n\n"))
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

        // Phase 2: Registry Gap Fix
        // Self-register in the global registry if we have state (i.e., we are a valid agent)
        if let Some(agent) = &ctx.state.agent {
            // We need to write to "system/agent_registry"
            // Since we don't have direct access to other actors' storage, we rely on the
            // storage layer's ability to access the registry keyspace if configured.
            // However, ActorContext only gives access to *our* storage.

            // In the current architecture, the Actor cannot write to the Registry directly
            // unless the Registry is part of its own storage or shared storage.
            // FdbAgentRegistry uses a shared FDB connection.
            // KvAdapter uses a shared ActorKV.

            // If we are running with KvAdapter, we are in a simulation or test.
            // We can try to write to a "well-known" key in our own storage that the Registry scanner looks for?
            // No, the Registry scanner looks at "system/agent_registry".

            // Ideally, we would send a message to the Registry actor:
            // ctx.send(registry_id, RegisterAgent(agent)).await?
            // But we don't have a Registry actor implemented as an Actor yet (it's just a storage abstraction).

            // Workaround: Write a "metadata" key in our own namespace.
            // And update KvAdapter to scan all actors? No, too expensive.

            // Correct Fix: The "Registry" should be an Actor.
            // But refactoring Registry to be an Actor is a larger task.

            // For now, we will rely on the Service to register the agent on creation (which it does via AppState).
            // But for Teleport/Recovery, the Service isn't involved.

            // Registry Gap: FIXED with RegistryActor (Option 1)
            //
            // Self-registration is now implemented via message passing to RegistryActor.
            // If dispatcher is available, agent registers itself on activation.
            //
            // Registration paths by scenario:
            // 1. Normal creation: API → AppState → storage.save_agent() → AgentActor.create() → on_activate self-registers
            // 2. Teleport in: TeleportService.teleport_in() → restore → on_activate self-registers
            // 3. Recovery: Actor restarts → on_activate self-registers (idempotent)
            //
            // Backward compatible: If dispatcher is None, registration is handled by service layer (Option 2)

            if let Some(ref dispatcher) = self.dispatcher {
                // Convert AgentState to AgentMetadata for registry
                use crate::storage::AgentMetadata;
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

                // Send register message to RegistryActor
                let registry_id = kelpie_core::actor::ActorId::new("system", "agent_registry")?;
                let request = super::registry_actor::RegisterRequest { metadata };
                let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
                    message: format!("Failed to serialize RegisterRequest: {}", e),
                })?;

                match dispatcher
                    .invoke(registry_id, "register".to_string(), Bytes::from(payload))
                    .await
                {
                    Ok(_) => {
                        tracing::info!(agent_id = %agent.id, "Agent self-registered via RegistryActor");
                    }
                    Err(e) => {
                        // Non-fatal: registration failure doesn't prevent actor activation
                        tracing::warn!(
                            agent_id = %agent.id,
                            error = %e,
                            "Failed to self-register with RegistryActor (non-fatal)"
                        );
                    }
                }
            } else {
                tracing::debug!(
                    agent_id = %agent.id,
                    "Agent activated (no dispatcher, registry managed by service layer)"
                );
            }
        }

        Ok(())
    }

    async fn on_deactivate(&self, ctx: &mut ActorContext<Self::State>) -> Result<()> {
        // Phase 2: Storage Unification
        // Write granular keys for API compatibility AND the BLOB for fast recovery

        // TigerStyle: Keep agent_state BLOB for fast Actor recovery
        let state_key = b"agent_state";
        let state_bytes = serde_json::to_vec(&ctx.state).map_err(|e| Error::Internal {
            message: format!("Failed to serialize AgentActorState: {}", e),
        })?;
        ctx.kv_set(state_key, &state_bytes).await?;

        // Write granular keys for API (AgentStorage) compatibility
        // 1. Write memory blocks
        if let Some(agent) = &ctx.state.agent {
            let blocks_value = serde_json::to_vec(&agent.blocks).map_err(|e| Error::Internal {
                message: format!("Failed to serialize blocks: {}", e),
            })?;
            ctx.kv_set(b"blocks", &blocks_value).await?;
        }

        // 2. Write messages as individual keys (message:0, message:1, ...)
        let message_count = ctx.state.messages.len() as u64;
        for (idx, message) in ctx.state.messages.iter().enumerate() {
            let message_key = format!("message:{}", idx);
            let message_value = serde_json::to_vec(message).map_err(|e| Error::Internal {
                message: format!("Failed to serialize message {}: {}", idx, e),
            })?;
            ctx.kv_set(message_key.as_bytes(), &message_value).await?;
        }

        // 3. Write message count
        let count_value = Bytes::from(message_count.to_string());
        ctx.kv_set(b"message_count", &count_value).await?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::actor::llm_trait::{LlmResponse, LlmToolCall};
    use crate::tools::UnifiedToolRegistry;
    use kelpie_core::actor::{ActorId, NoOpKV};
    use serde_json::json;

    /// Test dual-mode: send_message tool call content is extracted
    #[tokio::test]
    async fn test_extract_send_message_content_single() {
        let actor = AgentActor::new(Arc::new(MockLlm), Arc::new(UnifiedToolRegistry::new()));

        let response = LlmResponse {
            content: "This should be ignored".to_string(),
            tool_calls: vec![LlmToolCall {
                id: "call_1".to_string(),
                name: "send_message".to_string(),
                input: json!({
                    "message": "Hello from send_message!"
                }),
            }],
            prompt_tokens: 0,
            completion_tokens: 0,
            stop_reason: "end_turn".to_string(),
        };

        let kv = Box::new(NoOpKV);
        let actor_id = ActorId::new("test", "agent1").unwrap();
        let state = AgentActorState::default();
        let ctx = ActorContext::new(actor_id, state, kv);

        let result = actor
            .extract_send_message_content(&response, &ctx)
            .await
            .unwrap();
        assert_eq!(result, "Hello from send_message!");
    }

    /// Test dual-mode: multiple send_message calls are concatenated
    #[tokio::test]
    async fn test_extract_send_message_content_multiple() {
        let actor = AgentActor::new(Arc::new(MockLlm), Arc::new(UnifiedToolRegistry::new()));

        let response = LlmResponse {
            content: "This should be ignored".to_string(),
            tool_calls: vec![
                LlmToolCall {
                    id: "call_1".to_string(),
                    name: "send_message".to_string(),
                    input: json!({
                        "message": "First message"
                    }),
                },
                LlmToolCall {
                    id: "call_2".to_string(),
                    name: "send_message".to_string(),
                    input: json!({
                        "message": "Second message"
                    }),
                },
            ],
            prompt_tokens: 0,
            completion_tokens: 0,
            stop_reason: "end_turn".to_string(),
        };

        let kv = Box::new(NoOpKV);
        let actor_id = ActorId::new("test", "agent1").unwrap();
        let state = AgentActorState::default();
        let ctx = ActorContext::new(actor_id, state, kv);

        let result = actor
            .extract_send_message_content(&response, &ctx)
            .await
            .unwrap();
        assert_eq!(result, "First message\n\nSecond message");
    }

    /// Test dual-mode: no send_message call uses direct LLM response (fallback)
    #[tokio::test]
    async fn test_extract_send_message_content_fallback() {
        let actor = AgentActor::new(Arc::new(MockLlm), Arc::new(UnifiedToolRegistry::new()));

        let response = LlmResponse {
            content: "Direct LLM response".to_string(),
            tool_calls: vec![LlmToolCall {
                id: "call_1".to_string(),
                name: "shell".to_string(),
                input: json!({
                    "command": "ls"
                }),
            }],
            prompt_tokens: 0,
            completion_tokens: 0,
            stop_reason: "end_turn".to_string(),
        };

        let kv = Box::new(NoOpKV);
        let actor_id = ActorId::new("test", "agent1").unwrap();
        let state = AgentActorState::default();
        let ctx = ActorContext::new(actor_id, state, kv);

        let result = actor
            .extract_send_message_content(&response, &ctx)
            .await
            .unwrap();
        assert_eq!(result, "Direct LLM response");
    }

    /// Test dual-mode: empty tool calls uses direct response
    #[tokio::test]
    async fn test_extract_send_message_content_no_tools() {
        let actor = AgentActor::new(Arc::new(MockLlm), Arc::new(UnifiedToolRegistry::new()));

        let response = LlmResponse {
            content: "Direct response, no tools".to_string(),
            tool_calls: vec![],
            prompt_tokens: 0,
            completion_tokens: 0,
            stop_reason: "end_turn".to_string(),
        };

        let kv = Box::new(NoOpKV);
        let actor_id = ActorId::new("test", "agent1").unwrap();
        let state = AgentActorState::default();
        let ctx = ActorContext::new(actor_id, state, kv);

        let result = actor
            .extract_send_message_content(&response, &ctx)
            .await
            .unwrap();
        assert_eq!(result, "Direct response, no tools");
    }

    /// Mock LLM for testing
    struct MockLlm;

    #[async_trait]
    impl LlmClient for MockLlm {
        async fn complete_with_tools(
            &self,
            _messages: Vec<LlmMessage>,
            _tools: Vec<crate::llm::ToolDefinition>,
        ) -> Result<LlmResponse> {
            Ok(LlmResponse {
                content: "Mock response".to_string(),
                tool_calls: vec![],
                prompt_tokens: 0,
                completion_tokens: 0,
                stop_reason: "end_turn".to_string(),
            })
        }

        async fn continue_with_tool_result(
            &self,
            _messages: Vec<LlmMessage>,
            _tools: Vec<crate::llm::ToolDefinition>,
            _assistant_blocks: Vec<crate::llm::ContentBlock>,
            _tool_results: Vec<(String, String)>,
        ) -> Result<LlmResponse> {
            Ok(LlmResponse {
                content: "Mock response".to_string(),
                tool_calls: vec![],
                prompt_tokens: 0,
                completion_tokens: 0,
                stop_reason: "end_turn".to_string(),
            })
        }
    }
}

//! Service layer for agent operations
//!
//! TigerStyle: Service wraps dispatcher, provides clean API, handles errors.

mod teleport_service;

pub use teleport_service::{
    TeleportInRequest, TeleportInResponse, TeleportOutRequest, TeleportOutResponse,
    TeleportPackageInfo, TeleportService,
};

use crate::actor::{HandleMessageFullRequest, HandleMessageFullResponse};
use crate::models::{AgentState, CreateAgentRequest, StreamEvent, UpdateAgentRequest};
use bytes::Bytes;
use kelpie_core::actor::ActorId;
use kelpie_core::{Error, Result};
use kelpie_runtime::DispatcherHandle;
use serde_json::Value;
use tokio::sync::mpsc;

/// AgentService - service layer for agent operations
///
/// Wraps DispatcherHandle and provides high-level agent operations.
/// Handles serialization/deserialization and error mapping.
///
/// TigerStyle: Clean abstraction, explicit error handling, testable.
#[derive(Clone)]
pub struct AgentService {
    /// Dispatcher handle for actor invocations
    dispatcher: DispatcherHandle,
}

impl AgentService {
    /// Create a new AgentService
    pub fn new(dispatcher: DispatcherHandle) -> Self {
        Self { dispatcher }
    }

    /// Create a new agent
    ///
    /// # Arguments
    /// * `request` - Agent creation request
    ///
    /// # Returns
    /// Created agent state with ID
    ///
    /// # Errors
    /// Returns error if actor creation fails
    pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState> {
        // Generate actor ID from agent name
        let actor_id = ActorId::new("agents", uuid::Uuid::new_v4().to_string())?;

        // Serialize request
        let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
            message: format!("Failed to serialize CreateAgentRequest: {}", e),
        })?;

        // Invoke create operation - returns AgentState directly (BUG-001 fix)
        let response = self
            .dispatcher
            .invoke(actor_id.clone(), "create".to_string(), Bytes::from(payload))
            .await?;

        // Deserialize and return the created agent state
        serde_json::from_slice(&response).map_err(|e| Error::Internal {
            message: format!(
                "Failed to deserialize AgentState from create response: {}",
                e
            ),
        })
    }

    /// Send message to agent
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    /// * `message` - Message as JSON value
    ///
    /// # Returns
    /// Response as JSON value
    pub async fn send_message(&self, agent_id: &str, message: Value) -> Result<Value> {
        let actor_id = ActorId::new("agents", agent_id)?;

        // Extract content from message (Phase 6.8: support multiple formats)
        let content = message
            .get("content")
            .and_then(|v| v.as_str())
            .ok_or_else(|| Error::Internal {
                message: "Message must have 'content' field".to_string(),
            })?;

        // Build HandleMessageFullRequest
        let request = serde_json::json!({
            "content": content
        });

        // Serialize request
        let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
            message: format!("Failed to serialize HandleMessageFullRequest: {}", e),
        })?;

        // Invoke handle_message_full operation
        let response = self
            .dispatcher
            .invoke(
                actor_id,
                "handle_message_full".to_string(),
                Bytes::from(payload),
            )
            .await?;

        // Deserialize response
        serde_json::from_slice(&response).map_err(|e| Error::Internal {
            message: format!("Failed to deserialize message response: {}", e),
        })
    }

    /// Send message with full agent loop (Phase 6.9)
    ///
    /// Typed API for agent message handling. Returns structured response
    /// with full conversation history and usage stats.
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    /// * `content` - Message content from user
    ///
    /// # Returns
    /// HandleMessageFullResponse with messages and usage stats
    ///
    /// # Errors
    /// - Invalid agent_id
    /// - Agent not found/created
    /// - Actor invocation failure
    /// - Serialization/deserialization error
    ///
    /// # TigerStyle
    /// - Explicit typed API (not JSON Value)
    /// - Clear error messages
    /// - No unwrap()
    pub async fn send_message_full(
        &self,
        agent_id: &str,
        content: String,
    ) -> Result<HandleMessageFullResponse> {
        // TigerStyle: Validate preconditions
        assert!(!agent_id.is_empty(), "agent_id must not be empty");
        assert!(!content.is_empty(), "content must not be empty");

        let actor_id = ActorId::new("agents", agent_id)?;

        // Build typed request
        let request = HandleMessageFullRequest { content };

        // Serialize request
        let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
            message: format!("Failed to serialize HandleMessageFullRequest: {}", e),
        })?;

        // Invoke handle_message_full operation
        let response = self
            .dispatcher
            .invoke(
                actor_id,
                "handle_message_full".to_string(),
                Bytes::from(payload),
            )
            .await?;

        // Deserialize typed response
        serde_json::from_slice(&response).map_err(|e| Error::Internal {
            message: format!("Failed to deserialize HandleMessageFullResponse: {}", e),
        })
    }

    /// Send message to agent with streaming
    ///
    /// Phase 7: Streams events (tokens, tool calls) via channel as agent processes message
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    /// * `message` - Message as JSON value
    /// * `tx` - Channel sender for streaming events
    ///
    /// # Returns
    /// Ok(()) on success, Err if processing fails
    ///
    /// # Errors
    /// - Invalid agent_id
    /// - Actor invocation failure
    /// - Channel send failure (client disconnected)
    pub async fn send_message_stream(
        &self,
        agent_id: &str,
        message: Value,
        tx: mpsc::Sender<StreamEvent>,
    ) -> Result<()> {
        // Phase 7.4: Simplified implementation that emits synthetic events
        // Full streaming will require dispatcher.invoke_stream() in future phases

        // Emit a message chunk (simulated streaming)
        if tx
            .send(StreamEvent::MessageChunk {
                content: "Processing your message...".to_string(),
            })
            .await
            .is_err()
        {
            // Client disconnected - stop processing
            return Ok(());
        }

        // Call the regular send_message (non-streaming)
        let response = self.send_message(agent_id, message).await?;

        // Parse response and emit events
        if let Some(content) = response.get("content").and_then(|v| v.as_str()) {
            // Emit content as chunk
            if tx
                .send(StreamEvent::MessageChunk {
                    content: content.to_string(),
                })
                .await
                .is_err()
            {
                return Ok(());
            }
        }

        // Check for tool calls in response
        if let Some(tool_calls) = response.get("tool_calls").and_then(|v| v.as_array()) {
            for tool_call in tool_calls {
                let tool_call_id = tool_call
                    .get("id")
                    .and_then(|v| v.as_str())
                    .unwrap_or("unknown");
                let tool_name = tool_call
                    .get("name")
                    .and_then(|v| v.as_str())
                    .unwrap_or("unknown");

                // Emit tool call start
                if tx
                    .send(StreamEvent::ToolCallStart {
                        tool_call_id: tool_call_id.to_string(),
                        tool_name: tool_name.to_string(),
                        input: tool_call.get("arguments").cloned(),
                    })
                    .await
                    .is_err()
                {
                    return Ok(());
                }

                // Emit tool call complete (simulated)
                if tx
                    .send(StreamEvent::ToolCallComplete {
                        tool_call_id: tool_call_id.to_string(),
                        result: "Tool executed".to_string(),
                    })
                    .await
                    .is_err()
                {
                    return Ok(());
                }
            }
        }

        // Emit completion event
        let message_id = response
            .get("message_id")
            .and_then(|v| v.as_str())
            .unwrap_or("msg_generated");

        if tx
            .send(StreamEvent::MessageComplete {
                message_id: message_id.to_string(),
            })
            .await
            .is_err()
        {
            return Ok(());
        }

        Ok(())
    }

    /// Get agent state
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    ///
    /// # Returns
    /// Current agent state
    pub async fn get_agent(&self, agent_id: &str) -> Result<AgentState> {
        let actor_id = ActorId::new("agents", agent_id)?;

        // Invoke get_state operation
        let response = self
            .dispatcher
            .invoke(actor_id, "get_state".to_string(), Bytes::new())
            .await?;

        // Deserialize response
        serde_json::from_slice(&response).map_err(|e| Error::Internal {
            message: format!("Failed to deserialize AgentState: {}", e),
        })
    }

    /// Update agent
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    /// * `update` - Update as JSON value
    ///
    /// # Returns
    /// Updated agent state
    pub async fn update_agent(&self, agent_id: &str, update: Value) -> Result<AgentState> {
        let actor_id = ActorId::new("agents", agent_id)?;

        // Convert JSON value to UpdateAgentRequest
        let update_request: UpdateAgentRequest =
            serde_json::from_value(update).map_err(|e| Error::Internal {
                message: format!("Failed to parse update request: {}", e),
            })?;

        // For now, update individual fields via update_block if needed
        // This is simplified - a full implementation would have an update_agent operation
        // For this phase, we'll just get the current state and return it
        // (Real update would invoke an update operation on the actor)

        // Serialize update
        let payload = serde_json::to_vec(&update_request).map_err(|e| Error::Internal {
            message: format!("Failed to serialize UpdateAgentRequest: {}", e),
        })?;

        // Invoke update_agent operation (we'll need to add this to AgentActor)
        let response = self
            .dispatcher
            .invoke(
                actor_id.clone(),
                "update_agent".to_string(),
                Bytes::from(payload),
            )
            .await?;

        // Deserialize response
        serde_json::from_slice(&response).map_err(|e| Error::Internal {
            message: format!("Failed to deserialize updated AgentState: {}", e),
        })
    }

    /// Delete agent
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    pub async fn delete_agent(&self, agent_id: &str) -> Result<()> {
        let actor_id = ActorId::new("agents", agent_id)?;

        // Invoke delete operation to clear state
        self.dispatcher
            .invoke(actor_id.clone(), "delete_agent".to_string(), Bytes::new())
            .await?;

        // Then deactivate the actor
        self.dispatcher.deactivate(actor_id).await?;

        Ok(())
    }

    /// Update a memory block by label
    ///
    /// # Arguments
    /// * `agent_id` - Agent ID string
    /// * `label` - Block label
    /// * `value` - New block value
    ///
    /// # Returns
    /// Ok(()) on success
    pub async fn update_block_by_label(
        &self,
        agent_id: &str,
        label: &str,
        value: String,
    ) -> Result<()> {
        let actor_id = ActorId::new("agents", agent_id)?;

        // Build update request (using internal BlockUpdate struct format)
        let request = serde_json::json!({
            "label": label,
            "value": value,
        });

        // Serialize request
        let payload = serde_json::to_vec(&request).map_err(|e| Error::Internal {
            message: format!("Failed to serialize BlockUpdate: {}", e),
        })?;

        // Invoke update_block operation
        self.dispatcher
            .invoke(actor_id, "update_block".to_string(), Bytes::from(payload))
            .await?;

        Ok(())
    }
}

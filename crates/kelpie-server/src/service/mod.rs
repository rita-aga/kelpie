//! Service layer for agent operations
//!
//! TigerStyle: Service wraps dispatcher, provides clean API, handles errors.

use crate::models::{AgentState, CreateAgentRequest, UpdateAgentRequest};
use bytes::Bytes;
use kelpie_core::actor::ActorId;
use kelpie_core::{Error, Result};
use kelpie_runtime::DispatcherHandle;
use serde_json::Value;

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

        // Invoke create operation
        self.dispatcher
            .invoke(actor_id.clone(), "create".to_string(), Bytes::from(payload))
            .await?;

        // Get agent state
        self.get_agent(actor_id.id()).await
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

        // Serialize message
        let payload = serde_json::to_vec(&message).map_err(|e| Error::Internal {
            message: format!("Failed to serialize message: {}", e),
        })?;

        // Invoke handle_message operation
        let response = self
            .dispatcher
            .invoke(actor_id, "handle_message".to_string(), Bytes::from(payload))
            .await?;

        // Deserialize response
        serde_json::from_slice(&response).map_err(|e| Error::Internal {
            message: format!("Failed to deserialize message response: {}", e),
        })
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
}

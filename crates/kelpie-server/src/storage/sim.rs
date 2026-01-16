//! Simulated Storage Backend for DST
//!
//! TigerStyle: In-memory storage with fault injection for deterministic testing.
//!
//! This backend is used in DST tests to simulate storage failures and verify
//! that the system handles them correctly.

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use async_trait::async_trait;
use chrono::Utc;
use kelpie_dst::fault::FaultInjector;

use crate::models::{Block, Message};

use super::traits::{AgentStorage, StorageError};
use super::types::{AgentMetadata, CustomToolRecord, SessionState};

/// Shared storage state for crash recovery simulation
///
/// Multiple SimStorage instances can share the same underlying data
/// to simulate process restarts in DST tests.
#[derive(Clone)]
struct SharedState {
    agents: Arc<RwLock<HashMap<String, AgentMetadata>>>,
    blocks: Arc<RwLock<HashMap<String, Vec<Block>>>>,
    sessions: Arc<RwLock<HashMap<(String, String), SessionState>>>,
    messages: Arc<RwLock<HashMap<String, Vec<Message>>>>,
    custom_tools: Arc<RwLock<HashMap<String, CustomToolRecord>>>,
}

impl SharedState {
    fn new() -> Self {
        Self {
            agents: Arc::new(RwLock::new(HashMap::new())),
            blocks: Arc::new(RwLock::new(HashMap::new())),
            sessions: Arc::new(RwLock::new(HashMap::new())),
            messages: Arc::new(RwLock::new(HashMap::new())),
            custom_tools: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

/// Simulated storage backend with fault injection
///
/// TigerStyle: All state in RwLock-protected HashMaps wrapped in Arc for sharing.
/// FaultInjector determines when operations fail.
pub struct SimStorage {
    /// Shared state (supports crash recovery tests)
    state: SharedState,

    /// Fault injector for DST
    fault_injector: Option<Arc<FaultInjector>>,
}

impl SimStorage {
    /// Create a new SimStorage without fault injection
    pub fn new() -> Self {
        Self {
            state: SharedState::new(),
            fault_injector: None,
        }
    }

    /// Create a new SimStorage with fault injection
    pub fn with_fault_injector(injector: Arc<FaultInjector>) -> Self {
        Self {
            state: SharedState::new(),
            fault_injector: Some(injector),
        }
    }

    /// Create a new SimStorage sharing state with another instance
    ///
    /// This allows crash recovery tests to simulate process restart
    /// while maintaining persistent data.
    pub fn with_shared_state(other: &SimStorage) -> Self {
        Self {
            state: other.state.clone(),
            fault_injector: other.fault_injector.clone(),
        }
    }

    /// Check if a fault should be injected for an operation
    fn should_fail(&self, operation: &str) -> bool {
        self.fault_injector
            .as_ref()
            .and_then(|fi| fi.should_inject(operation))
            .is_some()
    }

    /// Return a fault-injected error if appropriate
    fn maybe_fail(&self, operation: &str) -> Result<(), StorageError> {
        if self.should_fail(operation) {
            Err(StorageError::FaultInjected {
                operation: operation.to_string(),
            })
        } else {
            Ok(())
        }
    }
}

impl Default for SimStorage {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl AgentStorage for SimStorage {
    // =========================================================================
    // Agent Metadata Operations
    // =========================================================================

    async fn save_agent(&self, agent: &AgentMetadata) -> Result<(), StorageError> {
        self.maybe_fail("agent_write")?;

        let mut agents = self
            .state
            .agents
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        agents.insert(agent.id.clone(), agent.clone());

        // Initialize empty blocks and messages for new agent
        let mut blocks = self
            .state
            .blocks
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;
        blocks.entry(agent.id.clone()).or_insert_with(Vec::new);

        let mut messages = self
            .state
            .messages
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;
        messages.entry(agent.id.clone()).or_insert_with(Vec::new);

        Ok(())
    }

    async fn load_agent(&self, id: &str) -> Result<Option<AgentMetadata>, StorageError> {
        self.maybe_fail("agent_read")?;

        let agents = self
            .state
            .agents
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(agents.get(id).cloned())
    }

    async fn delete_agent(&self, id: &str) -> Result<(), StorageError> {
        self.maybe_fail("agent_write")?;

        let mut agents = self
            .state
            .agents
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        if agents.remove(id).is_none() {
            return Err(StorageError::NotFound {
                resource: "agent",
                id: id.to_string(),
            });
        }

        // Also delete associated data
        let mut blocks = self
            .state
            .blocks
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;
        blocks.remove(id);

        let mut messages = self
            .state
            .messages
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;
        messages.remove(id);

        let mut sessions = self
            .state
            .sessions
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;
        sessions.retain(|(agent_id, _), _| agent_id != id);

        Ok(())
    }

    async fn list_agents(&self) -> Result<Vec<AgentMetadata>, StorageError> {
        self.maybe_fail("agent_read")?;

        let agents = self
            .state
            .agents
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(agents.values().cloned().collect())
    }

    // =========================================================================
    // Core Memory Block Operations
    // =========================================================================

    async fn save_blocks(&self, agent_id: &str, blocks: &[Block]) -> Result<(), StorageError> {
        self.maybe_fail("block_write")?;

        // Verify agent exists
        let agents = self
            .state
            .agents
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;
        if !agents.contains_key(agent_id) {
            return Err(StorageError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            });
        }
        drop(agents);

        let mut all_blocks = self
            .state
            .blocks
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        all_blocks.insert(agent_id.to_string(), blocks.to_vec());

        Ok(())
    }

    async fn load_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StorageError> {
        self.maybe_fail("block_read")?;

        let blocks = self
            .state
            .blocks
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(blocks.get(agent_id).cloned().unwrap_or_default())
    }

    async fn update_block(
        &self,
        agent_id: &str,
        label: &str,
        value: &str,
    ) -> Result<Block, StorageError> {
        self.maybe_fail("block_write")?;

        let mut all_blocks = self
            .state
            .blocks
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let blocks = all_blocks
            .get_mut(agent_id)
            .ok_or_else(|| StorageError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        // Find and update block
        for block in blocks.iter_mut() {
            if block.label == label {
                block.value = value.to_string();
                block.updated_at = Utc::now();
                return Ok(block.clone());
            }
        }

        Err(StorageError::NotFound {
            resource: "block",
            id: label.to_string(),
        })
    }

    async fn append_block(
        &self,
        agent_id: &str,
        label: &str,
        content: &str,
    ) -> Result<Block, StorageError> {
        self.maybe_fail("block_write")?;

        let mut all_blocks = self
            .state
            .blocks
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let blocks = all_blocks
            .get_mut(agent_id)
            .ok_or_else(|| StorageError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        // Find existing block or create new
        for block in blocks.iter_mut() {
            if block.label == label {
                block.value.push_str(content);
                block.updated_at = Utc::now();
                return Ok(block.clone());
            }
        }

        // Create new block
        let block = Block::new(label, content);
        blocks.push(block.clone());
        Ok(block)
    }

    // =========================================================================
    // Session State Operations
    // =========================================================================

    async fn save_session(&self, state: &SessionState) -> Result<(), StorageError> {
        self.maybe_fail("session_write")?;

        let mut sessions = self
            .state
            .sessions
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let key = (state.agent_id.clone(), state.session_id.clone());
        sessions.insert(key, state.clone());

        Ok(())
    }

    async fn load_session(
        &self,
        agent_id: &str,
        session_id: &str,
    ) -> Result<Option<SessionState>, StorageError> {
        self.maybe_fail("session_read")?;

        let sessions = self
            .state
            .sessions
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let key = (agent_id.to_string(), session_id.to_string());
        Ok(sessions.get(&key).cloned())
    }

    async fn delete_session(&self, agent_id: &str, session_id: &str) -> Result<(), StorageError> {
        self.maybe_fail("session_write")?;

        let mut sessions = self
            .state
            .sessions
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let key = (agent_id.to_string(), session_id.to_string());
        if sessions.remove(&key).is_none() {
            return Err(StorageError::NotFound {
                resource: "session",
                id: session_id.to_string(),
            });
        }

        Ok(())
    }

    async fn list_sessions(&self, agent_id: &str) -> Result<Vec<SessionState>, StorageError> {
        self.maybe_fail("session_read")?;

        let sessions = self
            .state
            .sessions
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(sessions
            .iter()
            .filter(|((aid, _), _)| aid == agent_id)
            .map(|(_, s)| s.clone())
            .collect())
    }

    // =========================================================================
    // Message Operations
    // =========================================================================

    async fn append_message(&self, agent_id: &str, message: &Message) -> Result<(), StorageError> {
        self.maybe_fail("message_write")?;

        let mut all_messages = self
            .state
            .messages
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let messages = all_messages
            .get_mut(agent_id)
            .ok_or_else(|| StorageError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        messages.push(message.clone());

        Ok(())
    }

    async fn load_messages(
        &self,
        agent_id: &str,
        limit: usize,
    ) -> Result<Vec<Message>, StorageError> {
        self.maybe_fail("message_read")?;

        let all_messages = self
            .state
            .messages
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let messages = all_messages.get(agent_id).cloned().unwrap_or_default();

        // Return most recent messages (last `limit` items)
        let start = messages.len().saturating_sub(limit);
        Ok(messages[start..].to_vec())
    }

    async fn load_messages_since(
        &self,
        agent_id: &str,
        since_ms: u64,
    ) -> Result<Vec<Message>, StorageError> {
        self.maybe_fail("message_read")?;

        let all_messages = self
            .state
            .messages
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        let messages = all_messages.get(agent_id).cloned().unwrap_or_default();

        // Filter by timestamp
        Ok(messages
            .into_iter()
            .filter(|m| m.created_at.timestamp_millis() as u64 > since_ms)
            .collect())
    }

    async fn count_messages(&self, agent_id: &str) -> Result<usize, StorageError> {
        self.maybe_fail("message_read")?;

        let all_messages = self
            .state
            .messages
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(all_messages.get(agent_id).map(|m| m.len()).unwrap_or(0))
    }

    async fn delete_messages(&self, agent_id: &str) -> Result<(), StorageError> {
        self.maybe_fail("message_write")?;

        let mut all_messages = self
            .state
            .messages
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        if let Some(messages) = all_messages.get_mut(agent_id) {
            messages.clear();
        }

        Ok(())
    }

    // =========================================================================
    // Custom Tool Operations
    // =========================================================================

    async fn save_custom_tool(&self, tool: &CustomToolRecord) -> Result<(), StorageError> {
        self.maybe_fail("tool_write")?;

        let mut tools = self
            .state
            .custom_tools
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        tools.insert(tool.name.clone(), tool.clone());
        Ok(())
    }

    async fn load_custom_tool(&self, name: &str) -> Result<Option<CustomToolRecord>, StorageError> {
        self.maybe_fail("tool_read")?;

        let tools = self
            .state
            .custom_tools
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(tools.get(name).cloned())
    }

    async fn delete_custom_tool(&self, name: &str) -> Result<(), StorageError> {
        self.maybe_fail("tool_write")?;

        let mut tools = self
            .state
            .custom_tools
            .write()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        if tools.remove(name).is_none() {
            return Err(StorageError::NotFound {
                resource: "tool",
                id: name.to_string(),
            });
        }

        Ok(())
    }

    async fn list_custom_tools(&self) -> Result<Vec<CustomToolRecord>, StorageError> {
        self.maybe_fail("tool_read")?;

        let tools = self
            .state
            .custom_tools
            .read()
            .map_err(|_| StorageError::Internal {
                message: "lock poisoned".to_string(),
            })?;

        Ok(tools.values().cloned().collect())
    }

    // =========================================================================
    // Transactional Operations
    // =========================================================================

    async fn checkpoint(
        &self,
        session: &SessionState,
        message: Option<&Message>,
    ) -> Result<(), StorageError> {
        // For SimStorage, we do both writes but they're not truly atomic
        // This is fine for DST since we inject faults explicitly
        self.maybe_fail("checkpoint_write")?;

        self.save_session(session).await?;

        if let Some(msg) = message {
            self.append_message(&session.agent_id, msg).await?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{AgentType, MessageRole};

    #[tokio::test]
    async fn test_sim_storage_agent_crud() {
        let storage = SimStorage::new();

        // Create agent
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        storage.save_agent(&agent).await.unwrap();

        // Load agent
        let loaded = storage.load_agent("agent-1").await.unwrap();
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().name, "Test Agent");

        // List agents
        let agents = storage.list_agents().await.unwrap();
        assert_eq!(agents.len(), 1);

        // Delete agent
        storage.delete_agent("agent-1").await.unwrap();

        // Verify deleted
        let loaded = storage.load_agent("agent-1").await.unwrap();
        assert!(loaded.is_none());
    }

    #[tokio::test]
    async fn test_sim_storage_session_crud() {
        let storage = SimStorage::new();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        storage.save_agent(&agent).await.unwrap();

        // Create session
        let session = SessionState::new("session-1".to_string(), "agent-1".to_string());
        storage.save_session(&session).await.unwrap();

        // Load session
        let loaded = storage.load_session("agent-1", "session-1").await.unwrap();
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().iteration, 0);

        // Update session
        let mut updated = session.clone();
        updated.advance_iteration();
        storage.save_session(&updated).await.unwrap();

        // Verify update
        let loaded = storage.load_session("agent-1", "session-1").await.unwrap();
        assert_eq!(loaded.unwrap().iteration, 1);
    }

    #[tokio::test]
    async fn test_sim_storage_messages() {
        let storage = SimStorage::new();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        storage.save_agent(&agent).await.unwrap();

        // Add messages
        let msg1 = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: "Hello".to_string(),
            tool_calls: None,
            tool_call_id: None,
            created_at: Utc::now(),
        };
        storage.append_message("agent-1", &msg1).await.unwrap();

        let msg2 = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "assistant_message".to_string(),
            role: MessageRole::Assistant,
            content: "Hi there!".to_string(),
            tool_calls: None,
            tool_call_id: None,
            created_at: Utc::now(),
        };
        storage.append_message("agent-1", &msg2).await.unwrap();

        // Load messages
        let messages = storage.load_messages("agent-1", 10).await.unwrap();
        assert_eq!(messages.len(), 2);
        assert_eq!(messages[0].content, "Hello");
        assert_eq!(messages[1].content, "Hi there!");

        // Count messages
        let count = storage.count_messages("agent-1").await.unwrap();
        assert_eq!(count, 2);
    }

    #[tokio::test]
    async fn test_sim_storage_blocks() {
        let storage = SimStorage::new();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        storage.save_agent(&agent).await.unwrap();

        // Append to block (creates new)
        let block = storage
            .append_block("agent-1", "persona", "I am helpful")
            .await
            .unwrap();
        assert_eq!(block.label, "persona");
        assert_eq!(block.value, "I am helpful");

        // Append more
        let block = storage
            .append_block("agent-1", "persona", " and kind")
            .await
            .unwrap();
        assert_eq!(block.value, "I am helpful and kind");

        // Load blocks
        let blocks = storage.load_blocks("agent-1").await.unwrap();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].value, "I am helpful and kind");
    }
}

//! KV Adapter for AgentStorage
//!
//! TigerStyle: Structural adapter mapping AgentStorage trait onto byte-level ActorKV.
//!
//! This adapter enables kelpie-server to use the proper kelpie-dst infrastructure
//! for deterministic simulation testing, replacing the ad-hoc SimStorage implementation.
//!
//! ## Key Mapping Strategy
//!
//! All keys are scoped under a single ActorId("kelpie", "server") namespace:
//! - `agents/{id}` -> JSON-serialized AgentMetadata
//! - `sessions/{agent_id}/{session_id}` -> JSON-serialized SessionState
//! - `messages/{agent_id}/{message_id}` -> JSON-serialized Message
//! - `blocks/{agent_id}` -> JSON-serialized Vec<Block>
//! - `tools/{name}` -> JSON-serialized CustomToolRecord

use async_trait::async_trait;
use kelpie_core::ActorId;
use kelpie_storage::ActorKV;
use std::sync::Arc;

use crate::models::{Block, Message};

use super::traits::{AgentStorage, StorageError};
use super::types::{AgentMetadata, CustomToolRecord, SessionState};

/// Maximum key length in bytes
const KEY_LENGTH_BYTES_MAX: usize = 256;

/// Maximum value size in bytes (10 MB)
const VALUE_SIZE_BYTES_MAX: usize = 10 * 1024 * 1024;

/// Adapter that wraps ActorKV and implements AgentStorage
///
/// TigerStyle: Explicit scoping, bounded keys, JSON serialization for debuggability.
pub struct KvAdapter {
    /// Underlying key-value store (SimStorage, MemoryKV, or FdbKV)
    kv: Arc<dyn ActorKV>,
    /// Actor ID used as namespace for all server storage
    actor_id: ActorId,
}

impl KvAdapter {
    /// Create a new KvAdapter wrapping the given ActorKV
    ///
    /// All storage operations will be scoped under ActorId("kelpie", "server").
    pub fn new(kv: Arc<dyn ActorKV>) -> Self {
        let actor_id = ActorId::new("kelpie", "server")
            .expect("failed to create server actor id - this is a bug");

        Self { kv, actor_id }
    }

    /// Create a KvAdapter backed by MemoryKV (for testing)
    ///
    /// This is a convenience method for creating in-memory storage for unit tests.
    pub fn with_memory() -> Self {
        use kelpie_storage::memory::MemoryKV;
        let kv: Arc<dyn ActorKV> = Arc::new(MemoryKV::new());
        Self::new(kv)
    }

    /// Create a KvAdapter backed by SimStorage (for DST testing)
    ///
    /// This connects the server to the proper kelpie-dst infrastructure with
    /// fault injection and deterministic behavior.
    ///
    /// # Arguments
    /// * `rng` - Deterministic RNG from kelpie-dst
    /// * `fault_injector` - FaultInjector for simulating failures
    #[cfg(feature = "dst")]
    pub fn with_dst_storage(
        rng: kelpie_dst::DeterministicRng,
        fault_injector: std::sync::Arc<kelpie_dst::FaultInjector>,
    ) -> Self {
        use kelpie_dst::SimStorage;
        let storage = SimStorage::new(rng, fault_injector);
        let kv: Arc<dyn ActorKV> = Arc::new(storage);
        Self::new(kv)
    }

    /// Get the underlying ActorKV (for testing)
    #[cfg(test)]
    pub fn underlying_kv(&self) -> Arc<dyn ActorKV> {
        self.kv.clone()
    }

    // =========================================================================
    // Key Mapping Functions
    // =========================================================================

    /// Generate key for agent metadata: `agents/{id}`
    fn agent_key(id: &str) -> Vec<u8> {
        assert!(!id.is_empty(), "agent id cannot be empty");
        let key = format!("agents/{}", id);
        assert!(
            key.len() <= KEY_LENGTH_BYTES_MAX,
            "agent key too long: {} bytes",
            key.len()
        );
        key.into_bytes()
    }

    /// Generate key for session state: `sessions/{agent_id}/{session_id}`
    fn session_key(agent_id: &str, session_id: &str) -> Vec<u8> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session_id.is_empty(), "session id cannot be empty");
        let key = format!("sessions/{}/{}", agent_id, session_id);
        assert!(
            key.len() <= KEY_LENGTH_BYTES_MAX,
            "session key too long: {} bytes",
            key.len()
        );
        key.into_bytes()
    }

    /// Generate prefix for listing sessions: `sessions/{agent_id}/`
    fn session_prefix(agent_id: &str) -> Vec<u8> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        format!("sessions/{}/", agent_id).into_bytes()
    }

    /// Generate key for message: `messages/{agent_id}/{message_id}`
    fn message_key(agent_id: &str, message_id: &str) -> Vec<u8> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!message_id.is_empty(), "message id cannot be empty");
        let key = format!("messages/{}/{}", agent_id, message_id);
        assert!(
            key.len() <= KEY_LENGTH_BYTES_MAX,
            "message key too long: {} bytes",
            key.len()
        );
        key.into_bytes()
    }

    /// Generate prefix for listing messages: `messages/{agent_id}/`
    fn message_prefix(agent_id: &str) -> Vec<u8> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        format!("messages/{}/", agent_id).into_bytes()
    }

    /// Generate key for blocks: `blocks/{agent_id}`
    fn blocks_key(agent_id: &str) -> Vec<u8> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        let key = format!("blocks/{}", agent_id);
        assert!(
            key.len() <= KEY_LENGTH_BYTES_MAX,
            "blocks key too long: {} bytes",
            key.len()
        );
        key.into_bytes()
    }

    /// Generate key for custom tool: `tools/{name}`
    fn tool_key(name: &str) -> Vec<u8> {
        assert!(!name.is_empty(), "tool name cannot be empty");
        let key = format!("tools/{}", name);
        assert!(
            key.len() <= KEY_LENGTH_BYTES_MAX,
            "tool key too long: {} bytes",
            key.len()
        );
        key.into_bytes()
    }

    // =========================================================================
    // Serialization Helpers
    // =========================================================================

    /// Serialize a value to JSON bytes
    fn serialize<T: serde::Serialize + ?Sized>(value: &T) -> Result<Vec<u8>, StorageError> {
        let json = serde_json::to_vec(value).map_err(|e| StorageError::SerializationFailed {
            reason: e.to_string(),
        })?;

        assert!(
            json.len() <= VALUE_SIZE_BYTES_MAX,
            "value too large: {} bytes (max {})",
            json.len(),
            VALUE_SIZE_BYTES_MAX
        );

        Ok(json)
    }

    /// Deserialize JSON bytes to a value
    fn deserialize<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Map kelpie_core::Error to StorageError
    fn map_kv_error(operation: &str, err: kelpie_core::Error) -> StorageError {
        match err {
            kelpie_core::Error::StorageReadFailed { key, reason } => StorageError::ReadFailed {
                operation: format!("{}: {}", operation, key),
                reason,
            },
            kelpie_core::Error::StorageWriteFailed { key, reason } => StorageError::WriteFailed {
                operation: format!("{}: {}", operation, key),
                reason,
            },
            kelpie_core::Error::Internal { message } => StorageError::Internal { message },
            _ => StorageError::Internal {
                message: format!("{}: {}", operation, err),
            },
        }
    }
}

#[async_trait]
impl AgentStorage for KvAdapter {
    // =========================================================================
    // Agent Metadata Operations
    // =========================================================================

    async fn save_agent(&self, agent: &AgentMetadata) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent.id.is_empty(), "agent id cannot be empty");

        let key = Self::agent_key(&agent.id);
        let value = Self::serialize(agent)?;

        self.kv
            .set(&self.actor_id, &key, &value)
            .await
            .map_err(|e| Self::map_kv_error("save_agent", e))?;

        Ok(())
    }

    async fn load_agent(&self, id: &str) -> Result<Option<AgentMetadata>, StorageError> {
        // Preconditions
        assert!(!id.is_empty(), "agent id cannot be empty");

        let key = Self::agent_key(id);

        let bytes = self
            .kv
            .get(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("load_agent", e))?;

        match bytes {
            Some(b) => {
                let agent = Self::deserialize(&b)?;
                Ok(Some(agent))
            }
            None => Ok(None),
        }
    }

    async fn delete_agent(&self, id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!id.is_empty(), "agent id cannot be empty");

        // Check if agent exists first
        if !self.agent_exists(id).await? {
            return Err(StorageError::NotFound {
                resource: "agent",
                id: id.to_string(),
            });
        }

        // Delete agent metadata
        let agent_key = Self::agent_key(id);
        self.kv
            .delete(&self.actor_id, &agent_key)
            .await
            .map_err(|e| Self::map_kv_error("delete_agent_metadata", e))?;

        // Delete associated blocks
        let blocks_key = Self::blocks_key(id);
        let _ = self.kv.delete(&self.actor_id, &blocks_key).await; // Ignore if not exists

        // Delete associated sessions
        let session_prefix = Self::session_prefix(id);
        let session_keys = self
            .kv
            .list_keys(&self.actor_id, &session_prefix)
            .await
            .map_err(|e| Self::map_kv_error("delete_agent_sessions", e))?;

        for key in session_keys {
            let _ = self.kv.delete(&self.actor_id, &key).await; // Continue on error
        }

        // Delete associated messages
        let message_prefix = Self::message_prefix(id);
        let message_keys = self
            .kv
            .list_keys(&self.actor_id, &message_prefix)
            .await
            .map_err(|e| Self::map_kv_error("delete_agent_messages", e))?;

        for key in message_keys {
            let _ = self.kv.delete(&self.actor_id, &key).await; // Continue on error
        }

        Ok(())
    }

    async fn list_agents(&self) -> Result<Vec<AgentMetadata>, StorageError> {
        let prefix = b"agents/";
        let pairs = self
            .kv
            .scan_prefix(&self.actor_id, prefix)
            .await
            .map_err(|e| Self::map_kv_error("list_agents", e))?;

        let mut agents = Vec::with_capacity(pairs.len());
        for (_key, value) in pairs {
            let agent = Self::deserialize(&value)?;
            agents.push(agent);
        }

        Ok(agents)
    }

    // =========================================================================
    // Core Memory Block Operations
    // =========================================================================

    async fn save_blocks(&self, agent_id: &str, blocks: &[Block]) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        // Verify agent exists
        if !self.agent_exists(agent_id).await? {
            return Err(StorageError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            });
        }

        let key = Self::blocks_key(agent_id);
        let value = Self::serialize(blocks)?;

        self.kv
            .set(&self.actor_id, &key, &value)
            .await
            .map_err(|e| Self::map_kv_error("save_blocks", e))?;

        Ok(())
    }

    async fn load_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let key = Self::blocks_key(agent_id);

        let bytes = self
            .kv
            .get(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("load_blocks", e))?;

        match bytes {
            Some(b) => {
                let blocks = Self::deserialize(&b)?;
                Ok(blocks)
            }
            None => Ok(Vec::new()), // No blocks = empty vec
        }
    }

    async fn update_block(
        &self,
        agent_id: &str,
        label: &str,
        value: &str,
    ) -> Result<Block, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!label.is_empty(), "label cannot be empty");

        let mut blocks = self.load_blocks(agent_id).await?;

        // Find and update block
        for block in blocks.iter_mut() {
            if block.label == label {
                block.value = value.to_string();
                block.updated_at = chrono::Utc::now();
                let result = block.clone();

                // Save updated blocks (after cloning)
                self.save_blocks(agent_id, &blocks).await?;

                return Ok(result);
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
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!label.is_empty(), "label cannot be empty");

        let mut blocks = self.load_blocks(agent_id).await?;

        // Find existing block or create new
        for block in blocks.iter_mut() {
            if block.label == label {
                block.value.push_str(content);
                block.updated_at = chrono::Utc::now();
                let result = block.clone();

                // Save updated blocks (after cloning)
                self.save_blocks(agent_id, &blocks).await?;

                return Ok(result);
            }
        }

        // Create new block
        let block = Block::new(label, content);
        blocks.push(block.clone());
        self.save_blocks(agent_id, &blocks).await?;

        Ok(block)
    }

    // =========================================================================
    // Session State Operations
    // =========================================================================

    async fn save_session(&self, state: &SessionState) -> Result<(), StorageError> {
        // Preconditions
        assert!(!state.agent_id.is_empty(), "agent id cannot be empty");
        assert!(!state.session_id.is_empty(), "session id cannot be empty");

        let key = Self::session_key(&state.agent_id, &state.session_id);
        let value = Self::serialize(state)?;

        self.kv
            .set(&self.actor_id, &key, &value)
            .await
            .map_err(|e| Self::map_kv_error("save_session", e))?;

        Ok(())
    }

    async fn load_session(
        &self,
        agent_id: &str,
        session_id: &str,
    ) -> Result<Option<SessionState>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session_id.is_empty(), "session id cannot be empty");

        let key = Self::session_key(agent_id, session_id);

        let bytes = self
            .kv
            .get(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("load_session", e))?;

        match bytes {
            Some(b) => {
                let session = Self::deserialize(&b)?;
                Ok(Some(session))
            }
            None => Ok(None),
        }
    }

    async fn delete_session(&self, agent_id: &str, session_id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session_id.is_empty(), "session id cannot be empty");

        let key = Self::session_key(agent_id, session_id);

        // Check if exists
        if !self
            .kv
            .exists(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("delete_session_exists_check", e))?
        {
            return Err(StorageError::NotFound {
                resource: "session",
                id: session_id.to_string(),
            });
        }

        self.kv
            .delete(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("delete_session", e))?;

        Ok(())
    }

    async fn list_sessions(&self, agent_id: &str) -> Result<Vec<SessionState>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let prefix = Self::session_prefix(agent_id);
        let pairs = self
            .kv
            .scan_prefix(&self.actor_id, &prefix)
            .await
            .map_err(|e| Self::map_kv_error("list_sessions", e))?;

        let mut sessions = Vec::with_capacity(pairs.len());
        for (_key, value) in pairs {
            let session = Self::deserialize(&value)?;
            sessions.push(session);
        }

        Ok(sessions)
    }

    // =========================================================================
    // Message Operations
    // =========================================================================

    async fn append_message(&self, agent_id: &str, message: &Message) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!message.id.is_empty(), "message id cannot be empty");
        assert_eq!(
            message.agent_id, agent_id,
            "message agent_id must match parameter"
        );

        let key = Self::message_key(agent_id, &message.id);
        let value = Self::serialize(message)?;

        self.kv
            .set(&self.actor_id, &key, &value)
            .await
            .map_err(|e| Self::map_kv_error("append_message", e))?;

        Ok(())
    }

    async fn load_messages(
        &self,
        agent_id: &str,
        limit: usize,
    ) -> Result<Vec<Message>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(limit > 0, "limit must be positive");
        assert!(limit <= 10000, "limit too large: {}", limit);

        let prefix = Self::message_prefix(agent_id);
        let pairs = self
            .kv
            .scan_prefix(&self.actor_id, &prefix)
            .await
            .map_err(|e| Self::map_kv_error("load_messages", e))?;

        let mut messages = Vec::with_capacity(pairs.len());
        for (_key, value) in pairs {
            let message: Message = Self::deserialize(&value)?;
            messages.push(message);
        }

        // Sort by created_at (oldest first)
        messages.sort_by_key(|m| m.created_at);

        // Return most recent messages (last `limit` items)
        let start = messages.len().saturating_sub(limit);
        Ok(messages[start..].to_vec())
    }

    async fn load_messages_since(
        &self,
        agent_id: &str,
        since_ms: u64,
    ) -> Result<Vec<Message>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let prefix = Self::message_prefix(agent_id);
        let pairs = self
            .kv
            .scan_prefix(&self.actor_id, &prefix)
            .await
            .map_err(|e| Self::map_kv_error("load_messages_since", e))?;

        let mut messages = Vec::with_capacity(pairs.len());
        for (_key, value) in pairs {
            let message: Message = Self::deserialize(&value)?;
            if message.created_at.timestamp_millis() as u64 > since_ms {
                messages.push(message);
            }
        }

        // Sort by created_at (oldest first)
        messages.sort_by_key(|m| m.created_at);

        Ok(messages)
    }

    async fn count_messages(&self, agent_id: &str) -> Result<usize, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let prefix = Self::message_prefix(agent_id);
        let keys = self
            .kv
            .list_keys(&self.actor_id, &prefix)
            .await
            .map_err(|e| Self::map_kv_error("count_messages", e))?;

        Ok(keys.len())
    }

    async fn delete_messages(&self, agent_id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let prefix = Self::message_prefix(agent_id);
        let keys = self
            .kv
            .list_keys(&self.actor_id, &prefix)
            .await
            .map_err(|e| Self::map_kv_error("delete_messages", e))?;

        for key in keys {
            let _ = self.kv.delete(&self.actor_id, &key).await; // Continue on error
        }

        Ok(())
    }

    // =========================================================================
    // Custom Tool Operations
    // =========================================================================

    async fn save_custom_tool(&self, tool: &CustomToolRecord) -> Result<(), StorageError> {
        // Preconditions
        assert!(!tool.name.is_empty(), "tool name cannot be empty");

        let key = Self::tool_key(&tool.name);
        let value = Self::serialize(tool)?;

        self.kv
            .set(&self.actor_id, &key, &value)
            .await
            .map_err(|e| Self::map_kv_error("save_custom_tool", e))?;

        Ok(())
    }

    async fn load_custom_tool(&self, name: &str) -> Result<Option<CustomToolRecord>, StorageError> {
        // Preconditions
        assert!(!name.is_empty(), "tool name cannot be empty");

        let key = Self::tool_key(name);

        let bytes = self
            .kv
            .get(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("load_custom_tool", e))?;

        match bytes {
            Some(b) => {
                let tool = Self::deserialize(&b)?;
                Ok(Some(tool))
            }
            None => Ok(None),
        }
    }

    async fn delete_custom_tool(&self, name: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!name.is_empty(), "tool name cannot be empty");

        let key = Self::tool_key(name);

        // Check if exists
        if !self
            .kv
            .exists(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("delete_custom_tool_exists_check", e))?
        {
            return Err(StorageError::NotFound {
                resource: "tool",
                id: name.to_string(),
            });
        }

        self.kv
            .delete(&self.actor_id, &key)
            .await
            .map_err(|e| Self::map_kv_error("delete_custom_tool", e))?;

        Ok(())
    }

    async fn list_custom_tools(&self) -> Result<Vec<CustomToolRecord>, StorageError> {
        let prefix = b"tools/";
        let pairs = self
            .kv
            .scan_prefix(&self.actor_id, prefix)
            .await
            .map_err(|e| Self::map_kv_error("list_custom_tools", e))?;

        let mut tools = Vec::with_capacity(pairs.len());
        for (_key, value) in pairs {
            let tool = Self::deserialize(&value)?;
            tools.push(tool);
        }

        Ok(tools)
    }

    // =========================================================================
    // Transactional Operations
    // =========================================================================

    async fn checkpoint(
        &self,
        session: &SessionState,
        message: Option<&Message>,
    ) -> Result<(), StorageError> {
        // Preconditions
        assert!(
            !session.agent_id.is_empty(),
            "session agent_id cannot be empty"
        );
        assert!(
            !session.session_id.is_empty(),
            "session session_id cannot be empty"
        );

        if let Some(msg) = message {
            assert!(!msg.id.is_empty(), "message id cannot be empty");
            assert_eq!(
                msg.agent_id, session.agent_id,
                "message agent_id must match session agent_id"
            );
        }

        // Use ActorKV transaction for atomicity
        let mut txn = self
            .kv
            .begin_transaction(&self.actor_id)
            .await
            .map_err(|e| Self::map_kv_error("checkpoint_begin_txn", e))?;

        // 1. Save session state
        let session_key = Self::session_key(&session.agent_id, &session.session_id);
        let session_value = Self::serialize(session)?;
        txn.set(&session_key, &session_value)
            .await
            .map_err(|e| Self::map_kv_error("checkpoint_save_session", e))?;

        // 2. Append message if present
        if let Some(msg) = message {
            let message_key = Self::message_key(&session.agent_id, &msg.id);
            let message_value = Self::serialize(msg)?;
            txn.set(&message_key, &message_value)
                .await
                .map_err(|e| Self::map_kv_error("checkpoint_save_message", e))?;
        }

        // 3. Commit transaction atomically
        txn.commit()
            .await
            .map_err(|e| Self::map_kv_error("checkpoint_commit", e))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{AgentType, MessageRole};
    use kelpie_storage::memory::MemoryKV;

    fn test_adapter() -> KvAdapter {
        let kv: Arc<dyn ActorKV> = Arc::new(MemoryKV::new());
        KvAdapter::new(kv)
    }

    #[tokio::test]
    async fn test_adapter_agent_crud() {
        let adapter = test_adapter();

        // Create agent
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        adapter.save_agent(&agent).await.unwrap();

        // Load agent
        let loaded = adapter.load_agent("agent-1").await.unwrap();
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().name, "Test Agent");

        // List agents
        let agents = adapter.list_agents().await.unwrap();
        assert_eq!(agents.len(), 1);

        // Delete agent
        adapter.delete_agent("agent-1").await.unwrap();

        // Verify deleted
        let loaded = adapter.load_agent("agent-1").await.unwrap();
        assert!(loaded.is_none());
    }

    #[tokio::test]
    async fn test_adapter_session_crud() {
        let adapter = test_adapter();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        adapter.save_agent(&agent).await.unwrap();

        // Create session
        let session = SessionState::new("session-1".to_string(), "agent-1".to_string());
        adapter.save_session(&session).await.unwrap();

        // Load session
        let loaded = adapter.load_session("agent-1", "session-1").await.unwrap();
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().iteration, 0);

        // Update session
        let mut updated = session.clone();
        updated.advance_iteration();
        adapter.save_session(&updated).await.unwrap();

        // Verify update
        let loaded = adapter.load_session("agent-1", "session-1").await.unwrap();
        assert_eq!(loaded.unwrap().iteration, 1);

        // Delete session
        adapter
            .delete_session("agent-1", "session-1")
            .await
            .unwrap();

        // Verify deleted
        let loaded = adapter.load_session("agent-1", "session-1").await.unwrap();
        assert!(loaded.is_none());
    }

    #[tokio::test]
    async fn test_adapter_messages() {
        let adapter = test_adapter();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        adapter.save_agent(&agent).await.unwrap();

        // Add messages
        let msg1 = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: "Hello".to_string(),
            tool_calls: None,
            tool_call_id: None,
            created_at: chrono::Utc::now(),
        };
        adapter.append_message("agent-1", &msg1).await.unwrap();

        let msg2 = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "assistant_message".to_string(),
            role: MessageRole::Assistant,
            content: "Hi there!".to_string(),
            tool_calls: None,
            tool_call_id: None,
            created_at: chrono::Utc::now(),
        };
        adapter.append_message("agent-1", &msg2).await.unwrap();

        // Load messages
        let messages = adapter.load_messages("agent-1", 10).await.unwrap();
        assert_eq!(messages.len(), 2);
        assert_eq!(messages[0].content, "Hello");
        assert_eq!(messages[1].content, "Hi there!");

        // Count messages
        let count = adapter.count_messages("agent-1").await.unwrap();
        assert_eq!(count, 2);

        // Delete messages
        adapter.delete_messages("agent-1").await.unwrap();

        // Verify deleted
        let count = adapter.count_messages("agent-1").await.unwrap();
        assert_eq!(count, 0);
    }

    #[tokio::test]
    async fn test_adapter_blocks() {
        let adapter = test_adapter();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        adapter.save_agent(&agent).await.unwrap();

        // Append to block (creates new)
        let block = adapter
            .append_block("agent-1", "persona", "I am helpful")
            .await
            .unwrap();
        assert_eq!(block.label, "persona");
        assert_eq!(block.value, "I am helpful");

        // Append more
        let block = adapter
            .append_block("agent-1", "persona", " and kind")
            .await
            .unwrap();
        assert_eq!(block.value, "I am helpful and kind");

        // Load blocks
        let blocks = adapter.load_blocks("agent-1").await.unwrap();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].value, "I am helpful and kind");

        // Update block
        let updated = adapter
            .update_block("agent-1", "persona", "I am very helpful")
            .await
            .unwrap();
        assert_eq!(updated.value, "I am very helpful");

        // Verify update
        let blocks = adapter.load_blocks("agent-1").await.unwrap();
        assert_eq!(blocks[0].value, "I am very helpful");
    }

    #[tokio::test]
    async fn test_adapter_custom_tools() {
        let adapter = test_adapter();

        // Create tool
        let now = chrono::Utc::now();
        let tool = CustomToolRecord {
            name: "test_tool".to_string(),
            description: "A test tool".to_string(),
            source_code: "def test(): pass".to_string(),
            input_schema: serde_json::json!({"type": "object"}),
            runtime: "python".to_string(),
            requirements: vec![],
            created_at: now,
            updated_at: now,
        };
        adapter.save_custom_tool(&tool).await.unwrap();

        // Load tool
        let loaded = adapter.load_custom_tool("test_tool").await.unwrap();
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().description, "A test tool");

        // List tools
        let tools = adapter.list_custom_tools().await.unwrap();
        assert_eq!(tools.len(), 1);

        // Delete tool
        adapter.delete_custom_tool("test_tool").await.unwrap();

        // Verify deleted
        let loaded = adapter.load_custom_tool("test_tool").await.unwrap();
        assert!(loaded.is_none());
    }

    #[tokio::test]
    async fn test_adapter_checkpoint_atomic() {
        let adapter = test_adapter();

        // Create agent first
        let agent = AgentMetadata::new(
            "agent-1".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );
        adapter.save_agent(&agent).await.unwrap();

        // Create session and message
        let session = SessionState::new("session-1".to_string(), "agent-1".to_string());
        let message = Message {
            id: uuid::Uuid::new_v4().to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: "Test message".to_string(),
            tool_calls: None,
            tool_call_id: None,
            created_at: chrono::Utc::now(),
        };

        // Checkpoint atomically
        adapter.checkpoint(&session, Some(&message)).await.unwrap();

        // Verify both saved
        let loaded_session = adapter.load_session("agent-1", "session-1").await.unwrap();
        assert!(loaded_session.is_some());

        let messages = adapter.load_messages("agent-1", 10).await.unwrap();
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].content, "Test message");
    }

    #[tokio::test]
    async fn test_adapter_key_assertions() {
        // Test key length assertions
        let long_id = "a".repeat(300);
        let result = std::panic::catch_unwind(|| KvAdapter::agent_key(&long_id));
        assert!(result.is_err(), "should panic on key too long");

        // Test empty id assertions
        let result = std::panic::catch_unwind(|| KvAdapter::agent_key(""));
        assert!(result.is_err(), "should panic on empty agent id");
    }
}

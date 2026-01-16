//! FoundationDB Agent Registry
//!
//! TigerStyle: AgentStorage implementation using FdbKV for unified storage.
//!
//! Architecture:
//! - Global agent registry stored as special actor ("system/agent_registry")
//! - Per-agent data stored in actor's own KV space
//! - Single FDB connection shared across all storage operations
//!
//! Key Space (via FdbKV/ActorKV):
//! ```text
//! Registry: ("kelpie", "actors", "system", "agent_registry", "data", "agent-123")
//! Per-agent: ("kelpie", "actors", "agents", "agent-123", "data", "blocks")
//! Per-agent: ("kelpie", "actors", "agents", "agent-123", "data", "session:xyz")
//! Per-agent: ("kelpie", "actors", "agents", "agent-123", "data", "message:0")
//! ```

use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, Result as CoreResult};
use kelpie_storage::{ActorKV, FdbKV};
use std::sync::Arc;

use crate::models::{Block, Message};

use super::traits::{AgentStorage, StorageError};
use super::types::{AgentMetadata, CustomToolRecord, SessionState};

// =============================================================================
// Constants (TigerStyle)
// =============================================================================

/// Registry actor ID for global agent metadata
const REGISTRY_NAMESPACE: &str = "system";
const REGISTRY_ID: &str = "agent_registry";
const TOOL_REGISTRY_ID: &str = "tool_registry";

/// Key prefixes for per-agent data
const KEY_PREFIX_BLOCKS: &[u8] = b"blocks";
const KEY_PREFIX_SESSION: &[u8] = b"session:";
const KEY_PREFIX_MESSAGE: &[u8] = b"message:";
const KEY_PREFIX_MESSAGE_COUNT: &[u8] = b"message_count";
const KEY_PREFIX_TOOL: &[u8] = b"tool:";

// =============================================================================
// FdbAgentRegistry Implementation
// =============================================================================

/// FDB-backed agent registry using FdbKV
///
/// Uses FdbKV under the hood:
/// - Registry: Special actor ("system/agent_registry") stores agent metadata
/// - Per-agent: Regular actors ("agents/{id}") store blocks/sessions/messages
pub struct FdbAgentRegistry {
    /// Shared FDB KV instance
    fdb: Arc<FdbKV>,
}

impl FdbAgentRegistry {
    /// Create new FDB agent registry
    ///
    /// # Arguments
    /// * `fdb` - Shared FdbKV instance
    pub fn new(fdb: Arc<FdbKV>) -> Self {
        Self { fdb }
    }

    /// Get registry actor ID (for storing agent metadata)
    fn registry_actor_id() -> CoreResult<ActorId> {
        ActorId::new(REGISTRY_NAMESPACE, REGISTRY_ID)
    }

    /// Get registry actor ID for tools
    fn tool_registry_actor_id() -> CoreResult<ActorId> {
        ActorId::new(REGISTRY_NAMESPACE, TOOL_REGISTRY_ID)
    }

    /// Get actor ID for an agent
    fn agent_actor_id(agent_id: &str) -> CoreResult<ActorId> {
        ActorId::new("agents", agent_id)
    }

    /// Serialize metadata to bytes
    fn serialize_metadata(agent: &AgentMetadata) -> Result<Bytes, StorageError> {
        serde_json::to_vec(agent)
            .map(Bytes::from)
            .map_err(|e| StorageError::SerializationFailed {
                reason: e.to_string(),
            })
    }

    /// Deserialize metadata from bytes
    fn deserialize_metadata(bytes: &Bytes) -> Result<AgentMetadata, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Serialize blocks to bytes
    fn serialize_blocks(blocks: &[Block]) -> Result<Bytes, StorageError> {
        serde_json::to_vec(blocks)
            .map(Bytes::from)
            .map_err(|e| StorageError::SerializationFailed {
                reason: e.to_string(),
            })
    }

    /// Deserialize blocks from bytes
    fn deserialize_blocks(bytes: &Bytes) -> Result<Vec<Block>, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Serialize session to bytes
    fn serialize_session(session: &SessionState) -> Result<Bytes, StorageError> {
        serde_json::to_vec(session).map(Bytes::from).map_err(|e| {
            StorageError::SerializationFailed {
                reason: e.to_string(),
            }
        })
    }

    /// Deserialize session from bytes
    fn deserialize_session(bytes: &Bytes) -> Result<SessionState, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Serialize message to bytes
    fn serialize_message(message: &Message) -> Result<Bytes, StorageError> {
        serde_json::to_vec(message).map(Bytes::from).map_err(|e| {
            StorageError::SerializationFailed {
                reason: e.to_string(),
            }
        })
    }

    /// Deserialize message from bytes
    fn deserialize_message(bytes: &Bytes) -> Result<Message, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Serialize custom tool to bytes
    fn serialize_custom_tool(tool: &CustomToolRecord) -> Result<Bytes, StorageError> {
        serde_json::to_vec(tool)
            .map(Bytes::from)
            .map_err(|e| StorageError::SerializationFailed {
                reason: e.to_string(),
            })
    }

    /// Deserialize custom tool from bytes
    fn deserialize_custom_tool(bytes: &Bytes) -> Result<CustomToolRecord, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Convert kelpie_core::Error to StorageError
    fn map_core_error(err: kelpie_core::Error) -> StorageError {
        StorageError::Internal {
            message: err.to_string(),
        }
    }
}

#[async_trait]
impl AgentStorage for FdbAgentRegistry {
    // =========================================================================
    // Agent Metadata Operations (Global Registry)
    // =========================================================================

    async fn save_agent(&self, agent: &AgentMetadata) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent.id.is_empty(), "agent id cannot be empty");
        assert!(!agent.name.is_empty(), "agent name cannot be empty");

        let registry_id = Self::registry_actor_id().map_err(Self::map_core_error)?;
        let key = agent.id.as_bytes();
        let value = Self::serialize_metadata(agent)?;

        self.fdb
            .set(&registry_id, key, &value)
            .await
            .map_err(Self::map_core_error)?;

        Ok(())
    }

    async fn load_agent(&self, id: &str) -> Result<Option<AgentMetadata>, StorageError> {
        // Preconditions
        assert!(!id.is_empty(), "agent id cannot be empty");

        let registry_id = Self::registry_actor_id().map_err(Self::map_core_error)?;
        let key = id.as_bytes();

        match self.fdb.get(&registry_id, key).await {
            Ok(Some(bytes)) => {
                let metadata = Self::deserialize_metadata(&bytes)?;
                Ok(Some(metadata))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(Self::map_core_error(e)),
        }
    }

    async fn delete_agent(&self, id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!id.is_empty(), "agent id cannot be empty");

        // Delete from registry
        let registry_id = Self::registry_actor_id().map_err(Self::map_core_error)?;
        let key = id.as_bytes();

        self.fdb
            .delete(&registry_id, key)
            .await
            .map_err(Self::map_core_error)?;

        // Delete per-agent data
        let agent_id = Self::agent_actor_id(id).map_err(Self::map_core_error)?;

        // Delete blocks
        self.fdb
            .delete(&agent_id, KEY_PREFIX_BLOCKS)
            .await
            .map_err(Self::map_core_error)?;

        // Delete message count
        self.fdb
            .delete(&agent_id, KEY_PREFIX_MESSAGE_COUNT)
            .await
            .map_err(Self::map_core_error)?;

        // TODO: Delete all sessions (need scan + delete loop)
        // TODO: Delete all messages (need scan + delete loop)

        Ok(())
    }

    async fn list_agents(&self) -> Result<Vec<AgentMetadata>, StorageError> {
        let registry_id = Self::registry_actor_id().map_err(Self::map_core_error)?;

        // Scan all keys in registry (empty prefix = all keys)
        let kvs = self
            .fdb
            .scan_prefix(&registry_id, b"")
            .await
            .map_err(Self::map_core_error)?;

        let mut agents = Vec::new();
        for (_key, value) in kvs {
            let metadata = Self::deserialize_metadata(&value)?;
            agents.push(metadata);
        }

        // Sort by ID for deterministic ordering
        agents.sort_by(|a, b| a.id.cmp(&b.id));

        Ok(agents)
    }

    // =========================================================================
    // Core Memory Block Operations (Per-Agent)
    // =========================================================================

    async fn save_blocks(&self, agent_id: &str, blocks: &[Block]) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;
        let value = Self::serialize_blocks(blocks)?;

        self.fdb
            .set(&actor_id, KEY_PREFIX_BLOCKS, &value)
            .await
            .map_err(Self::map_core_error)?;

        Ok(())
    }

    async fn load_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        match self.fdb.get(&actor_id, KEY_PREFIX_BLOCKS).await {
            Ok(Some(bytes)) => Self::deserialize_blocks(&bytes),
            Ok(None) => Ok(Vec::new()),
            Err(e) => Err(Self::map_core_error(e)),
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

        // Load existing blocks
        let mut blocks = self.load_blocks(agent_id).await?;

        // Find and update block
        let mut found = false;
        let mut result_block = None;
        for block in &mut blocks {
            if block.label == label {
                block.value = value.to_string();
                block.updated_at = chrono::Utc::now();
                result_block = Some(block.clone());
                found = true;
                break;
            }
        }

        if found {
            // Save updated blocks (after mutable borrow ends)
            self.save_blocks(agent_id, &blocks).await?;
            return Ok(result_block.unwrap());
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

        // Load existing blocks
        let mut blocks = self.load_blocks(agent_id).await?;

        // Find existing block or create new
        let mut found = false;
        let mut result_block = None;
        for block in &mut blocks {
            if block.label == label {
                block.value.push_str(content);
                block.updated_at = chrono::Utc::now();
                result_block = Some(block.clone());
                found = true;
                break;
            }
        }

        if found {
            // Save updated blocks (after mutable borrow ends)
            self.save_blocks(agent_id, &blocks).await?;
            return Ok(result_block.unwrap());
        }

        // Create new block
        let block = Block::new(label, content);
        blocks.push(block.clone());
        self.save_blocks(agent_id, &blocks).await?;

        Ok(block)
    }

    // =========================================================================
    // Session State Operations (Per-Agent)
    // =========================================================================

    async fn save_session(&self, state: &SessionState) -> Result<(), StorageError> {
        // Preconditions
        assert!(!state.agent_id.is_empty(), "agent id cannot be empty");
        assert!(!state.session_id.is_empty(), "session id cannot be empty");

        let actor_id = Self::agent_actor_id(&state.agent_id).map_err(Self::map_core_error)?;
        let key = format!(
            "{}{}",
            String::from_utf8_lossy(KEY_PREFIX_SESSION),
            state.session_id
        );
        let value = Self::serialize_session(state)?;

        self.fdb
            .set(&actor_id, key.as_bytes(), &value)
            .await
            .map_err(Self::map_core_error)?;

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

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;
        let key = format!(
            "{}{}",
            String::from_utf8_lossy(KEY_PREFIX_SESSION),
            session_id
        );

        match self.fdb.get(&actor_id, key.as_bytes()).await {
            Ok(Some(bytes)) => {
                let session = Self::deserialize_session(&bytes)?;
                Ok(Some(session))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(Self::map_core_error(e)),
        }
    }

    async fn delete_session(&self, agent_id: &str, session_id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session_id.is_empty(), "session id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;
        let key = format!(
            "{}{}",
            String::from_utf8_lossy(KEY_PREFIX_SESSION),
            session_id
        );

        self.fdb
            .delete(&actor_id, key.as_bytes())
            .await
            .map_err(Self::map_core_error)?;

        Ok(())
    }

    async fn list_sessions(&self, agent_id: &str) -> Result<Vec<SessionState>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        // Scan all keys with session prefix
        let kvs = self
            .fdb
            .scan_prefix(&actor_id, KEY_PREFIX_SESSION)
            .await
            .map_err(Self::map_core_error)?;

        let mut sessions = Vec::new();
        for (_key, value) in kvs {
            let session = Self::deserialize_session(&value)?;
            sessions.push(session);
        }

        Ok(sessions)
    }

    // =========================================================================
    // Message Operations (Per-Agent)
    // =========================================================================

    async fn append_message(&self, agent_id: &str, message: &Message) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        // Get current message count
        let count = match self.fdb.get(&actor_id, KEY_PREFIX_MESSAGE_COUNT).await {
            Ok(Some(bytes)) => {
                let count_str = String::from_utf8(bytes.to_vec()).map_err(|e| {
                    StorageError::DeserializationFailed {
                        reason: e.to_string(),
                    }
                })?;
                count_str
                    .parse::<u64>()
                    .map_err(|e| StorageError::DeserializationFailed {
                        reason: e.to_string(),
                    })?
            }
            Ok(None) => 0,
            Err(e) => return Err(Self::map_core_error(e)),
        };

        // Store message at index
        let message_key = format!("{}{}", String::from_utf8_lossy(KEY_PREFIX_MESSAGE), count);
        let message_value = Self::serialize_message(message)?;

        self.fdb
            .set(&actor_id, message_key.as_bytes(), &message_value)
            .await
            .map_err(Self::map_core_error)?;

        // Increment count
        let new_count = count + 1;
        self.fdb
            .set(
                &actor_id,
                KEY_PREFIX_MESSAGE_COUNT,
                &Bytes::from(new_count.to_string()),
            )
            .await
            .map_err(Self::map_core_error)?;

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

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        // Get message count
        let count = match self.fdb.get(&actor_id, KEY_PREFIX_MESSAGE_COUNT).await {
            Ok(Some(bytes)) => {
                let count_str = String::from_utf8(bytes.to_vec()).map_err(|e| {
                    StorageError::DeserializationFailed {
                        reason: e.to_string(),
                    }
                })?;
                count_str
                    .parse::<u64>()
                    .map_err(|e| StorageError::DeserializationFailed {
                        reason: e.to_string(),
                    })?
            }
            Ok(None) => return Ok(Vec::new()),
            Err(e) => return Err(Self::map_core_error(e)),
        };

        // Calculate range (most recent messages)
        let start_idx = count.saturating_sub(limit as u64);

        let mut messages = Vec::new();
        for i in start_idx..count {
            let message_key = format!("{}{}", String::from_utf8_lossy(KEY_PREFIX_MESSAGE), i);
            match self.fdb.get(&actor_id, message_key.as_bytes()).await {
                Ok(Some(bytes)) => {
                    let message = Self::deserialize_message(&bytes)?;
                    messages.push(message);
                }
                Ok(None) => {
                    // Message not found - skip
                }
                Err(e) => return Err(Self::map_core_error(e)),
            }
        }

        Ok(messages)
    }

    async fn load_messages_since(
        &self,
        agent_id: &str,
        since_ms: u64,
    ) -> Result<Vec<Message>, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        // Load all messages and filter by timestamp
        // TODO: Optimize with secondary index
        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        let kvs = self
            .fdb
            .scan_prefix(&actor_id, KEY_PREFIX_MESSAGE)
            .await
            .map_err(Self::map_core_error)?;

        let mut messages = Vec::new();
        for (_key, value) in kvs {
            let message = Self::deserialize_message(&value)?;
            if message.created_at.timestamp_millis() as u64 > since_ms {
                messages.push(message);
            }
        }

        Ok(messages)
    }

    async fn count_messages(&self, agent_id: &str) -> Result<usize, StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        match self.fdb.get(&actor_id, KEY_PREFIX_MESSAGE_COUNT).await {
            Ok(Some(bytes)) => {
                let count_str = String::from_utf8(bytes.to_vec()).map_err(|e| {
                    StorageError::DeserializationFailed {
                        reason: e.to_string(),
                    }
                })?;
                let count = count_str.parse::<usize>().map_err(|e| {
                    StorageError::DeserializationFailed {
                        reason: e.to_string(),
                    }
                })?;
                Ok(count)
            }
            Ok(None) => Ok(0),
            Err(e) => Err(Self::map_core_error(e)),
        }
    }

    async fn delete_messages(&self, agent_id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let actor_id = Self::agent_actor_id(agent_id).map_err(Self::map_core_error)?;

        // Get message count
        let count = self.count_messages(agent_id).await?;

        // Delete all message keys
        for i in 0..count {
            let message_key = format!("{}{}", String::from_utf8_lossy(KEY_PREFIX_MESSAGE), i);
            self.fdb
                .delete(&actor_id, message_key.as_bytes())
                .await
                .map_err(Self::map_core_error)?;
        }

        // Reset count
        self.fdb
            .set(&actor_id, KEY_PREFIX_MESSAGE_COUNT, &Bytes::from("0"))
            .await
            .map_err(Self::map_core_error)?;

        Ok(())
    }

    // =========================================================================
    // Custom Tool Operations
    // =========================================================================

    async fn save_custom_tool(&self, tool: &CustomToolRecord) -> Result<(), StorageError> {
        assert!(!tool.name.is_empty(), "tool name cannot be empty");

        let registry_id = Self::tool_registry_actor_id().map_err(Self::map_core_error)?;
        let key = [KEY_PREFIX_TOOL, tool.name.as_bytes()].concat();
        let value = Self::serialize_custom_tool(tool)?;

        self.fdb
            .set(&registry_id, &key, &value)
            .await
            .map_err(Self::map_core_error)?;

        Ok(())
    }

    async fn load_custom_tool(&self, name: &str) -> Result<Option<CustomToolRecord>, StorageError> {
        assert!(!name.is_empty(), "tool name cannot be empty");

        let registry_id = Self::tool_registry_actor_id().map_err(Self::map_core_error)?;
        let key = [KEY_PREFIX_TOOL, name.as_bytes()].concat();

        match self.fdb.get(&registry_id, &key).await {
            Ok(Some(bytes)) => {
                let tool = Self::deserialize_custom_tool(&bytes)?;
                Ok(Some(tool))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(Self::map_core_error(e)),
        }
    }

    async fn delete_custom_tool(&self, name: &str) -> Result<(), StorageError> {
        assert!(!name.is_empty(), "tool name cannot be empty");

        let registry_id = Self::tool_registry_actor_id().map_err(Self::map_core_error)?;
        let key = [KEY_PREFIX_TOOL, name.as_bytes()].concat();

        self.fdb
            .delete(&registry_id, &key)
            .await
            .map_err(Self::map_core_error)?;

        Ok(())
    }

    async fn list_custom_tools(&self) -> Result<Vec<CustomToolRecord>, StorageError> {
        let registry_id = Self::tool_registry_actor_id().map_err(Self::map_core_error)?;
        let keys = self
            .fdb
            .list_keys(&registry_id, KEY_PREFIX_TOOL)
            .await
            .map_err(Self::map_core_error)?;

        let mut tools = Vec::new();
        for key in keys {
            if let Ok(Some(bytes)) = self.fdb.get(&registry_id, &key).await {
                if let Ok(tool) = Self::deserialize_custom_tool(&bytes) {
                    tools.push(tool);
                }
            }
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
        assert!(!session.agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session.session_id.is_empty(), "session id cannot be empty");

        // Save session
        self.save_session(session).await?;

        // Append message if provided
        if let Some(msg) = message {
            self.append_message(&session.agent_id, msg).await?;
        }

        // TODO: Use FDB transaction for atomicity
        // Currently these are separate operations
        // Need to expose begin_transaction() on FdbKV

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::AgentType;

    #[test]
    fn test_registry_actor_id() {
        let id = FdbAgentRegistry::registry_actor_id().unwrap();
        assert_eq!(id.namespace(), "system");
        assert_eq!(id.id(), "agent_registry");
    }

    #[test]
    fn test_agent_actor_id() {
        let id = FdbAgentRegistry::agent_actor_id("test-agent").unwrap();
        assert_eq!(id.namespace(), "agents");
        assert_eq!(id.id(), "test-agent");
    }

    #[test]
    fn test_metadata_serialization() {
        let agent = AgentMetadata::new(
            "test-123".to_string(),
            "Test Agent".to_string(),
            AgentType::MemgptAgent,
        );

        let bytes = FdbAgentRegistry::serialize_metadata(&agent).unwrap();
        let deserialized = FdbAgentRegistry::deserialize_metadata(&bytes).unwrap();

        assert_eq!(agent.id, deserialized.id);
        assert_eq!(agent.name, deserialized.name);
    }
}

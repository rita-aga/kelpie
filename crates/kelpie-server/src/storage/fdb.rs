//! FoundationDB Storage Backend
//!
//! TigerStyle: Production-ready, linearizable storage for agent persistence.
//!
//! # Key Space Design
//!
//! Keys are encoded using FDB tuple layer:
//! ```text
//! ("kelpie", "agents", agent_id, "metadata")           -> AgentMetadata
//! ("kelpie", "agents", agent_id, "blocks", label)      -> Block
//! ("kelpie", "sessions", agent_id, session_id)         -> SessionState
//! ("kelpie", "messages", agent_id, timestamp_ms)       -> Message
//! ```

use async_trait::async_trait;
use foundationdb::api::FdbApiBuilder;
use foundationdb::tuple::Subspace;
use foundationdb::{Database, RangeOption, Transaction as FdbTransaction};
use std::sync::Arc;
use tracing::{debug, instrument, warn};

use crate::models::{Block, Message};

use super::traits::{AgentStorage, StorageError};
use super::types::{AgentMetadata, SessionState};

// =============================================================================
// Constants (TigerStyle)
// =============================================================================

/// Key prefix for Kelpie data
const KEY_PREFIX_KELPIE: &str = "kelpie";

/// Key prefix for agents
const KEY_PREFIX_AGENTS: &str = "agents";

/// Key prefix for sessions
const KEY_PREFIX_SESSIONS: &str = "sessions";

/// Key prefix for messages
const KEY_PREFIX_MESSAGES: &str = "messages";

/// Subkey for agent metadata
const SUBKEY_METADATA: &str = "metadata";

/// Subkey for blocks
const SUBKEY_BLOCKS: &str = "blocks";

/// Maximum retry attempts for retriable errors
const TRANSACTION_RETRY_COUNT_MAX: usize = 5;

/// Transaction timeout in milliseconds
const TRANSACTION_TIMEOUT_MS: u64 = 5000;

// =============================================================================
// FdbStorage Implementation
// =============================================================================

/// FoundationDB storage backend for agent persistence
///
/// TigerStyle: Linearizable storage with explicit key encoding.
#[derive(Clone)]
pub struct FdbStorage {
    /// FDB database handle (connection pooled internally)
    db: Arc<Database>,
    /// Subspace for agent data
    agents_subspace: Subspace,
    /// Subspace for session data
    sessions_subspace: Subspace,
    /// Subspace for message data
    messages_subspace: Subspace,
}

impl FdbStorage {
    /// Connect to FoundationDB cluster
    ///
    /// # Arguments
    ///
    /// * `cluster_file` - Path to FDB cluster file. If None, uses default location.
    ///
    /// # Errors
    ///
    /// Returns error if connection fails or FDB network cannot be started.
    #[instrument(skip_all, fields(cluster_file))]
    pub async fn connect(cluster_file: Option<&str>) -> Result<Self, StorageError> {
        // Boot FDB network (must be called once per process)
        let network_builder = FdbApiBuilder::default()
            .build()
            .map_err(|e| StorageError::ConnectionFailed {
                reason: format!("FDB API build failed: {}", e),
            })?;

        // Start network thread (non-blocking after first call)
        unsafe {
            network_builder
                .boot()
                .map_err(|e| StorageError::ConnectionFailed {
                    reason: format!("FDB network boot failed: {}", e),
                })?;
        }

        // Open database
        let db = Database::new(cluster_file).map_err(|e| StorageError::ConnectionFailed {
            reason: format!("FDB database open failed: {}", e),
        })?;

        // Create subspaces for different data types
        let agents_subspace = Subspace::from((KEY_PREFIX_KELPIE, KEY_PREFIX_AGENTS));
        let sessions_subspace = Subspace::from((KEY_PREFIX_KELPIE, KEY_PREFIX_SESSIONS));
        let messages_subspace = Subspace::from((KEY_PREFIX_KELPIE, KEY_PREFIX_MESSAGES));

        debug!("Connected to FoundationDB");

        Ok(Self {
            db: Arc::new(db),
            agents_subspace,
            sessions_subspace,
            messages_subspace,
        })
    }

    /// Execute a transaction with retry logic
    async fn run_transaction<F, T>(&self, mut f: F) -> Result<T, StorageError>
    where
        F: FnMut(&FdbTransaction) -> Result<T, StorageError>,
    {
        let mut attempts = 0;

        loop {
            let txn = self
                .db
                .create_trx()
                .map_err(|e| StorageError::Internal {
                    message: format!("Failed to create transaction: {}", e),
                })?;

            // Set transaction timeout
            txn.set_option(foundationdb::options::TransactionOption::Timeout(
                TRANSACTION_TIMEOUT_MS as i32,
            ))
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to set timeout: {}", e),
            })?;

            match f(&txn) {
                Ok(result) => {
                    // Commit the transaction
                    txn.commit().await.map_err(|e| {
                        if e.is_retryable() {
                            StorageError::TransactionConflict {
                                reason: e.to_string(),
                            }
                        } else {
                            StorageError::WriteFailed {
                                operation: "commit".to_string(),
                                reason: e.to_string(),
                            }
                        }
                    })?;
                    return Ok(result);
                }
                Err(e) if e.is_retriable() && attempts < TRANSACTION_RETRY_COUNT_MAX => {
                    attempts += 1;
                    warn!(attempt = attempts, error = %e, "Retrying transaction");
                    continue;
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// Serialize a value to JSON bytes
    fn serialize<T: serde::Serialize>(value: &T) -> Result<Vec<u8>, StorageError> {
        serde_json::to_vec(value).map_err(|e| StorageError::SerializationFailed {
            reason: e.to_string(),
        })
    }

    /// Deserialize JSON bytes to a value
    fn deserialize<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, StorageError> {
        serde_json::from_slice(bytes).map_err(|e| StorageError::DeserializationFailed {
            reason: e.to_string(),
        })
    }
}

#[async_trait]
impl AgentStorage for FdbStorage {
    // =========================================================================
    // Agent Metadata Operations
    // =========================================================================

    async fn save_agent(&self, agent: &AgentMetadata) -> Result<(), StorageError> {
        // Preconditions
        assert!(!agent.id.is_empty(), "agent id cannot be empty");

        let key = self
            .agents_subspace
            .pack(&(&agent.id, SUBKEY_METADATA));
        let value = Self::serialize(agent)?;

        self.run_transaction(|txn| {
            txn.set(&key, &value);
            Ok(())
        })
        .await
    }

    async fn load_agent(&self, id: &str) -> Result<Option<AgentMetadata>, StorageError> {
        // Preconditions
        assert!(!id.is_empty(), "agent id cannot be empty");

        let key = self.agents_subspace.pack(&(id, SUBKEY_METADATA));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        match txn.get(&key, false).await {
            Ok(Some(value)) => {
                let agent = Self::deserialize(&value)?;
                Ok(Some(agent))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(StorageError::ReadFailed {
                operation: "load_agent".to_string(),
                reason: e.to_string(),
            }),
        }
    }

    async fn delete_agent(&self, id: &str) -> Result<(), StorageError> {
        // Preconditions
        assert!(!id.is_empty(), "agent id cannot be empty");

        // Delete agent metadata
        let metadata_key = self.agents_subspace.pack(&(id, SUBKEY_METADATA));

        // Delete all blocks for agent
        let blocks_start = self.agents_subspace.pack(&(id, SUBKEY_BLOCKS, ""));
        let blocks_end = self.agents_subspace.pack(&(id, SUBKEY_BLOCKS, "\xff"));

        // Delete all sessions for agent
        let sessions_start = self.sessions_subspace.pack(&(id, ""));
        let sessions_end = self.sessions_subspace.pack(&(id, "\xff"));

        // Delete all messages for agent
        let messages_start = self.messages_subspace.pack(&(id, 0u64));
        let messages_end = self.messages_subspace.pack(&(id, u64::MAX));

        self.run_transaction(|txn| {
            txn.clear(&metadata_key);
            txn.clear_range(&blocks_start, &blocks_end);
            txn.clear_range(&sessions_start, &sessions_end);
            txn.clear_range(&messages_start, &messages_end);
            Ok(())
        })
        .await
    }

    async fn list_agents(&self) -> Result<Vec<AgentMetadata>, StorageError> {
        let start = self.agents_subspace.pack(&("", SUBKEY_METADATA));
        let end = self.agents_subspace.pack(&("\xff", SUBKEY_METADATA));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let range = RangeOption::from((start.as_slice(), end.as_slice()));
        let results = txn.get_range(&range, 1000, false).await.map_err(|e| {
            StorageError::ReadFailed {
                operation: "list_agents".to_string(),
                reason: e.to_string(),
            }
        })?;

        let mut agents = Vec::new();
        for kv in results {
            let agent: AgentMetadata = Self::deserialize(kv.value())?;
            agents.push(agent);
        }

        Ok(agents)
    }

    // =========================================================================
    // Block Operations
    // =========================================================================

    async fn save_blocks(&self, agent_id: &str, blocks: &[Block]) -> Result<(), StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        self.run_transaction(|txn| {
            for block in blocks {
                let key = self
                    .agents_subspace
                    .pack(&(agent_id, SUBKEY_BLOCKS, &block.label));
                let value = Self::serialize(block)?;
                txn.set(&key, &value);
            }
            Ok(())
        })
        .await
    }

    async fn load_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let start = self
            .agents_subspace
            .pack(&(agent_id, SUBKEY_BLOCKS, ""));
        let end = self
            .agents_subspace
            .pack(&(agent_id, SUBKEY_BLOCKS, "\xff"));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let range = RangeOption::from((start.as_slice(), end.as_slice()));
        let results = txn.get_range(&range, 100, false).await.map_err(|e| {
            StorageError::ReadFailed {
                operation: "load_blocks".to_string(),
                reason: e.to_string(),
            }
        })?;

        let mut blocks = Vec::new();
        for kv in results {
            let block: Block = Self::deserialize(kv.value())?;
            blocks.push(block);
        }

        Ok(blocks)
    }

    async fn update_block(
        &self,
        agent_id: &str,
        label: &str,
        value: &str,
    ) -> Result<Block, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!label.is_empty(), "label cannot be empty");

        let key = self
            .agents_subspace
            .pack(&(agent_id, SUBKEY_BLOCKS, label));

        // Load existing block or create new one
        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let mut block = match txn.get(&key, false).await {
            Ok(Some(existing)) => Self::deserialize(&existing)?,
            Ok(None) => Block::new(label, ""),
            Err(e) => {
                return Err(StorageError::ReadFailed {
                    operation: "update_block".to_string(),
                    reason: e.to_string(),
                })
            }
        };

        // Update value
        block.value = value.to_string();

        // Save updated block
        let serialized = Self::serialize(&block)?;
        self.run_transaction(|txn| {
            txn.set(&key, &serialized);
            Ok(())
        })
        .await?;

        Ok(block)
    }

    async fn append_block(
        &self,
        agent_id: &str,
        label: &str,
        content: &str,
    ) -> Result<Block, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!label.is_empty(), "label cannot be empty");

        let key = self
            .agents_subspace
            .pack(&(agent_id, SUBKEY_BLOCKS, label));

        // Load existing block or create new one
        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let mut block = match txn.get(&key, false).await {
            Ok(Some(existing)) => Self::deserialize(&existing)?,
            Ok(None) => Block::new(label, ""),
            Err(e) => {
                return Err(StorageError::ReadFailed {
                    operation: "append_block".to_string(),
                    reason: e.to_string(),
                })
            }
        };

        // Append content
        if !block.value.is_empty() {
            block.value.push('\n');
        }
        block.value.push_str(content);

        // Save updated block
        let serialized = Self::serialize(&block)?;
        self.run_transaction(|txn| {
            txn.set(&key, &serialized);
            Ok(())
        })
        .await?;

        Ok(block)
    }

    // =========================================================================
    // Session Operations
    // =========================================================================

    async fn save_session(&self, state: &SessionState) -> Result<(), StorageError> {
        assert!(!state.agent_id.is_empty(), "agent id cannot be empty");
        assert!(!state.session_id.is_empty(), "session id cannot be empty");

        let key = self
            .sessions_subspace
            .pack(&(&state.agent_id, &state.session_id));
        let value = Self::serialize(state)?;

        self.run_transaction(|txn| {
            txn.set(&key, &value);
            Ok(())
        })
        .await
    }

    async fn load_session(
        &self,
        agent_id: &str,
        session_id: &str,
    ) -> Result<Option<SessionState>, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session_id.is_empty(), "session id cannot be empty");

        let key = self.sessions_subspace.pack(&(agent_id, session_id));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        match txn.get(&key, false).await {
            Ok(Some(value)) => {
                let state = Self::deserialize(&value)?;
                Ok(Some(state))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(StorageError::ReadFailed {
                operation: "load_session".to_string(),
                reason: e.to_string(),
            }),
        }
    }

    async fn delete_session(&self, agent_id: &str, session_id: &str) -> Result<(), StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session_id.is_empty(), "session id cannot be empty");

        let key = self.sessions_subspace.pack(&(agent_id, session_id));

        self.run_transaction(|txn| {
            txn.clear(&key);
            Ok(())
        })
        .await
    }

    async fn list_sessions(&self, agent_id: &str) -> Result<Vec<SessionState>, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let start = self.sessions_subspace.pack(&(agent_id, ""));
        let end = self.sessions_subspace.pack(&(agent_id, "\xff"));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let range = RangeOption::from((start.as_slice(), end.as_slice()));
        let results = txn.get_range(&range, 100, false).await.map_err(|e| {
            StorageError::ReadFailed {
                operation: "list_sessions".to_string(),
                reason: e.to_string(),
            }
        })?;

        let mut sessions = Vec::new();
        for kv in results {
            let session: SessionState = Self::deserialize(kv.value())?;
            sessions.push(session);
        }

        Ok(sessions)
    }

    // =========================================================================
    // Message Operations
    // =========================================================================

    async fn append_message(&self, agent_id: &str, message: &Message) -> Result<(), StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        // Use timestamp as part of key for ordering
        let timestamp_ms = message.created_at.timestamp_millis() as u64;
        let key = self
            .messages_subspace
            .pack(&(agent_id, timestamp_ms, &message.id));
        let value = Self::serialize(message)?;

        self.run_transaction(|txn| {
            txn.set(&key, &value);
            Ok(())
        })
        .await
    }

    async fn load_messages(
        &self,
        agent_id: &str,
        limit: usize,
    ) -> Result<Vec<Message>, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");
        assert!(limit > 0, "limit must be positive");

        // Read messages in reverse order (most recent first)
        let start = self.messages_subspace.pack(&(agent_id, 0u64, ""));
        let end = self.messages_subspace.pack(&(agent_id, u64::MAX, "\xff"));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let range = RangeOption::from((start.as_slice(), end.as_slice()));
        let results = txn
            .get_range(&range, limit as i32, true) // reverse order
            .await
            .map_err(|e| StorageError::ReadFailed {
                operation: "load_messages".to_string(),
                reason: e.to_string(),
            })?;

        let mut messages = Vec::new();
        for kv in results {
            let message: Message = Self::deserialize(kv.value())?;
            messages.push(message);
        }

        // Reverse to get chronological order
        messages.reverse();

        Ok(messages)
    }

    async fn load_messages_since(
        &self,
        agent_id: &str,
        since_ms: u64,
    ) -> Result<Vec<Message>, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let start = self.messages_subspace.pack(&(agent_id, since_ms, ""));
        let end = self.messages_subspace.pack(&(agent_id, u64::MAX, "\xff"));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let range = RangeOption::from((start.as_slice(), end.as_slice()));
        let results = txn.get_range(&range, 1000, false).await.map_err(|e| {
            StorageError::ReadFailed {
                operation: "load_messages_since".to_string(),
                reason: e.to_string(),
            }
        })?;

        let mut messages = Vec::new();
        for kv in results {
            let message: Message = Self::deserialize(kv.value())?;
            messages.push(message);
        }

        Ok(messages)
    }

    async fn count_messages(&self, agent_id: &str) -> Result<usize, StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let start = self.messages_subspace.pack(&(agent_id, 0u64, ""));
        let end = self.messages_subspace.pack(&(agent_id, u64::MAX, "\xff"));

        let txn = self
            .db
            .create_trx()
            .map_err(|e| StorageError::Internal {
                message: format!("Failed to create transaction: {}", e),
            })?;

        let range = RangeOption::from((start.as_slice(), end.as_slice()));
        let results = txn.get_range(&range, 10000, false).await.map_err(|e| {
            StorageError::ReadFailed {
                operation: "count_messages".to_string(),
                reason: e.to_string(),
            }
        })?;

        Ok(results.len())
    }

    async fn delete_messages(&self, agent_id: &str) -> Result<(), StorageError> {
        assert!(!agent_id.is_empty(), "agent id cannot be empty");

        let start = self.messages_subspace.pack(&(agent_id, 0u64, ""));
        let end = self.messages_subspace.pack(&(agent_id, u64::MAX, "\xff"));

        self.run_transaction(|txn| {
            txn.clear_range(&start, &end);
            Ok(())
        })
        .await
    }

    // =========================================================================
    // Transactional Operations
    // =========================================================================

    async fn checkpoint(
        &self,
        session: &SessionState,
        message: Option<&Message>,
    ) -> Result<(), StorageError> {
        assert!(!session.agent_id.is_empty(), "agent id cannot be empty");
        assert!(!session.session_id.is_empty(), "session id cannot be empty");

        let session_key = self
            .sessions_subspace
            .pack(&(&session.agent_id, &session.session_id));
        let session_value = Self::serialize(session)?;

        let message_data = if let Some(msg) = message {
            let timestamp_ms = msg.created_at.timestamp_millis() as u64;
            let key = self
                .messages_subspace
                .pack(&(&session.agent_id, timestamp_ms, &msg.id));
            let value = Self::serialize(msg)?;
            Some((key, value))
        } else {
            None
        };

        // Atomic transaction: save session and message together
        self.run_transaction(|txn| {
            txn.set(&session_key, &session_value);
            if let Some((key, value)) = &message_data {
                txn.set(key, value);
            }
            Ok(())
        })
        .await
    }
}

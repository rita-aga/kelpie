//! Memory checkpointing for persistence
//!
//! TigerStyle: Explicit checkpoint boundaries with versioned snapshots.
//!
//! Checkpoints capture the state of memory tiers for durability.
//! They can be stored to KV storage and restored on activation.

use crate::core::CoreMemory;
use crate::error::{MemoryError, MemoryResult};
use crate::types::{now, Timestamp};
use crate::working::WorkingMemory;
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::actor::ActorId;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// Version of the checkpoint format
pub const CHECKPOINT_FORMAT_VERSION: u32 = 1;

/// Key prefix for checkpoints in storage
pub const CHECKPOINT_KEY_PREFIX: &str = "checkpoint";

/// A memory checkpoint
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Checkpoint {
    /// Format version for compatibility
    pub version: u32,
    /// Actor this checkpoint belongs to
    pub actor_id: ActorId,
    /// When the checkpoint was created
    pub created_at: Timestamp,
    /// Sequence number (for ordering)
    pub sequence: u64,
    /// Serialized core memory
    pub core_memory: Option<Vec<u8>>,
    /// Serialized working memory
    pub working_memory: Option<Vec<u8>>,
}

impl Checkpoint {
    /// Create a new checkpoint from memory state
    pub fn new(
        actor_id: ActorId,
        sequence: u64,
        core: Option<&CoreMemory>,
        working: Option<&WorkingMemory>,
    ) -> MemoryResult<Self> {
        let core_memory = if let Some(core) = core {
            Some(
                serde_json::to_vec(core).map_err(|e| MemoryError::SerializationFailed {
                    reason: e.to_string(),
                })?,
            )
        } else {
            None
        };

        let working_memory = if let Some(working) = working {
            Some(
                serde_json::to_vec(working).map_err(|e| MemoryError::SerializationFailed {
                    reason: e.to_string(),
                })?,
            )
        } else {
            None
        };

        Ok(Self {
            version: CHECKPOINT_FORMAT_VERSION,
            actor_id,
            created_at: now(),
            sequence,
            core_memory,
            working_memory,
        })
    }

    /// Restore core memory from checkpoint
    pub fn restore_core(&self) -> MemoryResult<Option<CoreMemory>> {
        match &self.core_memory {
            Some(data) => {
                let core = serde_json::from_slice(data).map_err(|e| {
                    MemoryError::DeserializationFailed {
                        reason: e.to_string(),
                    }
                })?;
                Ok(Some(core))
            }
            None => Ok(None),
        }
    }

    /// Restore working memory from checkpoint
    pub fn restore_working(&self) -> MemoryResult<Option<WorkingMemory>> {
        match &self.working_memory {
            Some(data) => {
                let working = serde_json::from_slice(data).map_err(|e| {
                    MemoryError::DeserializationFailed {
                        reason: e.to_string(),
                    }
                })?;
                Ok(Some(working))
            }
            None => Ok(None),
        }
    }

    /// Serialize checkpoint to bytes
    pub fn to_bytes(&self) -> MemoryResult<Bytes> {
        let data = serde_json::to_vec(self).map_err(|e| MemoryError::SerializationFailed {
            reason: e.to_string(),
        })?;
        Ok(Bytes::from(data))
    }

    /// Deserialize checkpoint from bytes
    pub fn from_bytes(data: &[u8]) -> MemoryResult<Self> {
        serde_json::from_slice(data).map_err(|e| MemoryError::DeserializationFailed {
            reason: e.to_string(),
        })
    }

    /// Get the storage key for this checkpoint
    pub fn storage_key(&self) -> Vec<u8> {
        format!(
            "{}/{}/{}",
            CHECKPOINT_KEY_PREFIX, self.actor_id, self.sequence
        )
        .into_bytes()
    }

    /// Get the latest checkpoint key for an actor
    pub fn latest_key(actor_id: &ActorId) -> Vec<u8> {
        format!("{}/{}/latest", CHECKPOINT_KEY_PREFIX, actor_id).into_bytes()
    }

    /// Size of the checkpoint in bytes
    pub fn size_bytes(&self) -> u64 {
        let core_size = self.core_memory.as_ref().map(|d| d.len()).unwrap_or(0);
        let working_size = self.working_memory.as_ref().map(|d| d.len()).unwrap_or(0);
        (core_size + working_size) as u64
    }
}

/// Storage backend for checkpoints
#[async_trait]
pub trait CheckpointStorage: Send + Sync {
    /// Store a checkpoint
    async fn store(&self, checkpoint: &Checkpoint) -> MemoryResult<()>;

    /// Load the latest checkpoint for an actor
    async fn load_latest(&self, actor_id: &ActorId) -> MemoryResult<Option<Checkpoint>>;

    /// Load a specific checkpoint by sequence number
    async fn load_by_sequence(
        &self,
        actor_id: &ActorId,
        sequence: u64,
    ) -> MemoryResult<Option<Checkpoint>>;

    /// List checkpoint sequences for an actor
    async fn list_sequences(&self, actor_id: &ActorId) -> MemoryResult<Vec<u64>>;

    /// Delete old checkpoints, keeping only the latest N
    async fn prune(&self, actor_id: &ActorId, keep_count: usize) -> MemoryResult<usize>;
}

/// Checkpoint manager for coordinating checkpoints
pub struct CheckpointManager<S: CheckpointStorage> {
    /// Storage backend
    storage: Arc<S>,
    /// Current sequence number
    sequence: u64,
    /// Actor ID
    actor_id: ActorId,
}

impl<S: CheckpointStorage> CheckpointManager<S> {
    /// Create a new checkpoint manager
    pub fn new(actor_id: ActorId, storage: Arc<S>) -> Self {
        Self {
            storage,
            sequence: 0,
            actor_id,
        }
    }

    /// Initialize from storage (loads latest sequence)
    pub async fn init(&mut self) -> MemoryResult<()> {
        if let Some(checkpoint) = self.storage.load_latest(&self.actor_id).await? {
            self.sequence = checkpoint.sequence;
        }
        Ok(())
    }

    /// Create and store a checkpoint
    pub async fn checkpoint(
        &mut self,
        core: Option<&CoreMemory>,
        working: Option<&WorkingMemory>,
    ) -> MemoryResult<Checkpoint> {
        self.sequence += 1;

        let checkpoint = Checkpoint::new(self.actor_id.clone(), self.sequence, core, working)?;

        self.storage.store(&checkpoint).await?;

        Ok(checkpoint)
    }

    /// Load the latest checkpoint
    pub async fn load_latest(&self) -> MemoryResult<Option<Checkpoint>> {
        self.storage.load_latest(&self.actor_id).await
    }

    /// Restore memory from the latest checkpoint
    pub async fn restore(
        &self,
    ) -> MemoryResult<Option<(Option<CoreMemory>, Option<WorkingMemory>)>> {
        match self.storage.load_latest(&self.actor_id).await? {
            Some(checkpoint) => {
                let core = checkpoint.restore_core()?;
                let working = checkpoint.restore_working()?;
                Ok(Some((core, working)))
            }
            None => Ok(None),
        }
    }

    /// Get current sequence number
    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Prune old checkpoints
    pub async fn prune(&self, keep_count: usize) -> MemoryResult<usize> {
        self.storage.prune(&self.actor_id, keep_count).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checkpoint_creation() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let core = CoreMemory::with_defaults();

        let checkpoint = Checkpoint::new(actor_id.clone(), 1, Some(&core), None).unwrap();

        assert_eq!(checkpoint.version, CHECKPOINT_FORMAT_VERSION);
        assert_eq!(checkpoint.actor_id, actor_id);
        assert_eq!(checkpoint.sequence, 1);
        assert!(checkpoint.core_memory.is_some());
        assert!(checkpoint.working_memory.is_none());
    }

    #[test]
    fn test_checkpoint_restore_core() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let mut core = CoreMemory::with_defaults();

        use crate::block::MemoryBlock;
        core.add_block(MemoryBlock::system("Test system prompt"))
            .unwrap();

        let checkpoint = Checkpoint::new(actor_id, 1, Some(&core), None).unwrap();

        let restored = checkpoint.restore_core().unwrap().unwrap();
        assert_eq!(restored.block_count(), 1);
    }

    #[test]
    fn test_checkpoint_restore_working() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let mut working = WorkingMemory::with_defaults();

        working.set("key", Bytes::from("value")).unwrap();

        let checkpoint = Checkpoint::new(actor_id, 1, None, Some(&working)).unwrap();

        let restored = checkpoint.restore_working().unwrap().unwrap();
        assert!(restored.exists("key"));
    }

    #[test]
    fn test_checkpoint_serialization_roundtrip() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let core = CoreMemory::with_defaults();
        let working = WorkingMemory::with_defaults();

        let checkpoint = Checkpoint::new(actor_id, 1, Some(&core), Some(&working)).unwrap();

        let bytes = checkpoint.to_bytes().unwrap();
        let restored = Checkpoint::from_bytes(&bytes).unwrap();

        assert_eq!(restored.sequence, checkpoint.sequence);
        assert_eq!(restored.version, checkpoint.version);
    }

    #[test]
    fn test_checkpoint_storage_key() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let checkpoint = Checkpoint::new(actor_id, 42, None, None).unwrap();

        let key = String::from_utf8(checkpoint.storage_key()).unwrap();
        assert!(key.contains("checkpoint"));
        assert!(key.contains("42"));
    }

    #[test]
    fn test_checkpoint_latest_key() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let key = String::from_utf8(Checkpoint::latest_key(&actor_id)).unwrap();
        assert!(key.contains("latest"));
    }
}

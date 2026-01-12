//! In-memory KV storage
//!
//! For testing and DST simulations.
//!
//! TigerStyle: Simple in-memory implementation with transaction support.

use crate::kv::{ActorKV, ActorTransaction};
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, Result};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::instrument;

/// Per-actor KV data: key -> value
type ActorData = HashMap<Vec<u8>, Vec<u8>>;

/// Storage data: actor_id -> actor data
type StorageData = HashMap<String, ActorData>;

/// In-memory KV store
#[derive(Clone)]
pub struct MemoryKV {
    /// Data storage: actor_id -> (key -> value)
    data: Arc<RwLock<StorageData>>,
}

impl MemoryKV {
    /// Create a new in-memory KV store
    pub fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    fn actor_key(actor_id: &ActorId) -> String {
        actor_id.qualified_name()
    }
}

impl Default for MemoryKV {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl ActorKV for MemoryKV {
    #[instrument(skip(self, key), fields(actor_id = %actor_id.qualified_name(), key_len = key.len()))]
    async fn get(&self, actor_id: &ActorId, key: &[u8]) -> Result<Option<Bytes>> {
        let data = self.data.read().await;
        let actor_key = Self::actor_key(actor_id);

        Ok(data
            .get(&actor_key)
            .and_then(|actor_data| actor_data.get(key))
            .map(|v| Bytes::copy_from_slice(v)))
    }

    #[instrument(skip(self, key, value), fields(actor_id = %actor_id.qualified_name(), key_len = key.len(), value_len = value.len()))]
    async fn set(&self, actor_id: &ActorId, key: &[u8], value: &[u8]) -> Result<()> {
        let mut data = self.data.write().await;
        let actor_key = Self::actor_key(actor_id);

        data.entry(actor_key)
            .or_default()
            .insert(key.to_vec(), value.to_vec());

        Ok(())
    }

    #[instrument(skip(self, key), fields(actor_id = %actor_id.qualified_name(), key_len = key.len()))]
    async fn delete(&self, actor_id: &ActorId, key: &[u8]) -> Result<()> {
        let mut data = self.data.write().await;
        let actor_key = Self::actor_key(actor_id);

        if let Some(actor_data) = data.get_mut(&actor_key) {
            actor_data.remove(key);
        }

        Ok(())
    }

    #[instrument(skip(self, prefix), fields(actor_id = %actor_id.qualified_name(), prefix_len = prefix.len()))]
    async fn list_keys(&self, actor_id: &ActorId, prefix: &[u8]) -> Result<Vec<Vec<u8>>> {
        let data = self.data.read().await;
        let actor_key = Self::actor_key(actor_id);

        Ok(data
            .get(&actor_key)
            .map(|actor_data| {
                actor_data
                    .keys()
                    .filter(|k| k.starts_with(prefix))
                    .cloned()
                    .collect()
            })
            .unwrap_or_default())
    }

    #[instrument(skip(self), fields(actor_id = %actor_id.qualified_name()))]
    async fn begin_transaction(&self, actor_id: &ActorId) -> Result<Box<dyn ActorTransaction>> {
        Ok(Box::new(MemoryTransaction::new(
            actor_id.clone(),
            self.clone(),
        )))
    }
}

/// Transaction for in-memory KV store
///
/// Buffers writes until commit. All writes are applied atomically on commit.
/// TigerStyle: Explicit state tracking, 2+ assertions per method.
pub struct MemoryTransaction {
    /// Actor this transaction operates on
    actor_id: ActorId,
    /// Reference to the underlying storage
    storage: MemoryKV,
    /// Buffered writes: key -> Some(value) for set, None for delete
    write_buffer: HashMap<Vec<u8>, Option<Vec<u8>>>,
    /// Whether this transaction has been finalized (committed or aborted)
    finalized: bool,
}

impl MemoryTransaction {
    fn new(actor_id: ActorId, storage: MemoryKV) -> Self {
        Self {
            actor_id,
            storage,
            write_buffer: HashMap::new(),
            finalized: false,
        }
    }
}

#[async_trait]
impl ActorTransaction for MemoryTransaction {
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(!key.is_empty(), "key cannot be empty");

        // Check write buffer first (read-your-writes)
        if let Some(buffered) = self.write_buffer.get(key) {
            return Ok(buffered.as_ref().map(|v| Bytes::copy_from_slice(v)));
        }

        // Fall back to storage
        self.storage.get(&self.actor_id, key).await
    }

    async fn set(&mut self, key: &[u8], value: &[u8]) -> Result<()> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(!key.is_empty(), "key cannot be empty");

        self.write_buffer.insert(key.to_vec(), Some(value.to_vec()));
        Ok(())
    }

    async fn delete(&mut self, key: &[u8]) -> Result<()> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(!key.is_empty(), "key cannot be empty");

        self.write_buffer.insert(key.to_vec(), None);
        Ok(())
    }

    async fn commit(mut self: Box<Self>) -> Result<()> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(
            self.write_buffer.len() <= 10000,
            "transaction too large: {} operations",
            self.write_buffer.len()
        );

        // Apply all buffered writes
        for (key, value) in self.write_buffer.drain() {
            match value {
                Some(v) => self.storage.set(&self.actor_id, &key, &v).await?,
                None => self.storage.delete(&self.actor_id, &key).await?,
            }
        }

        self.finalized = true;
        Ok(())
    }

    async fn abort(mut self: Box<Self>) -> Result<()> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");

        // Discard all buffered writes
        self.write_buffer.clear();
        self.finalized = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_memory_kv_basic() {
        let kv = MemoryKV::new();
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Set and get
        kv.set(&actor_id, b"key1", b"value1").await.unwrap();
        let value = kv.get(&actor_id, b"key1").await.unwrap();
        assert_eq!(value, Some(Bytes::from("value1")));

        // Delete
        kv.delete(&actor_id, b"key1").await.unwrap();
        let value = kv.get(&actor_id, b"key1").await.unwrap();
        assert!(value.is_none());
    }

    #[tokio::test]
    async fn test_memory_kv_isolation() {
        let kv = MemoryKV::new();
        let actor1 = ActorId::new("test", "actor-1").unwrap();
        let actor2 = ActorId::new("test", "actor-2").unwrap();

        kv.set(&actor1, b"key", b"value1").await.unwrap();
        kv.set(&actor2, b"key", b"value2").await.unwrap();

        assert_eq!(
            kv.get(&actor1, b"key").await.unwrap(),
            Some(Bytes::from("value1"))
        );
        assert_eq!(
            kv.get(&actor2, b"key").await.unwrap(),
            Some(Bytes::from("value2"))
        );
    }

    #[tokio::test]
    async fn test_transaction_commit() {
        let kv = MemoryKV::new();
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Begin transaction and write
        let mut txn = kv.begin_transaction(&actor_id).await.unwrap();
        txn.set(b"key1", b"value1").await.unwrap();
        txn.set(b"key2", b"value2").await.unwrap();

        // Before commit, values not visible via direct KV access
        assert!(kv.get(&actor_id, b"key1").await.unwrap().is_none());

        // Commit
        txn.commit().await.unwrap();

        // After commit, values visible
        assert_eq!(
            kv.get(&actor_id, b"key1").await.unwrap(),
            Some(Bytes::from("value1"))
        );
        assert_eq!(
            kv.get(&actor_id, b"key2").await.unwrap(),
            Some(Bytes::from("value2"))
        );
    }

    #[tokio::test]
    async fn test_transaction_abort() {
        let kv = MemoryKV::new();
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Begin transaction and write
        let mut txn = kv.begin_transaction(&actor_id).await.unwrap();
        txn.set(b"key1", b"value1").await.unwrap();

        // Abort
        txn.abort().await.unwrap();

        // After abort, values not visible
        assert!(kv.get(&actor_id, b"key1").await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_transaction_read_your_writes() {
        let kv = MemoryKV::new();
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Set initial value
        kv.set(&actor_id, b"key1", b"initial").await.unwrap();

        // Begin transaction
        let mut txn = kv.begin_transaction(&actor_id).await.unwrap();

        // Read initial value
        assert_eq!(
            txn.get(b"key1").await.unwrap(),
            Some(Bytes::from("initial"))
        );

        // Write new value
        txn.set(b"key1", b"updated").await.unwrap();

        // Read updated value (read-your-writes)
        assert_eq!(
            txn.get(b"key1").await.unwrap(),
            Some(Bytes::from("updated"))
        );

        txn.commit().await.unwrap();
    }

    #[tokio::test]
    async fn test_transaction_delete() {
        let kv = MemoryKV::new();
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Set initial value
        kv.set(&actor_id, b"key1", b"value1").await.unwrap();

        // Begin transaction and delete
        let mut txn = kv.begin_transaction(&actor_id).await.unwrap();
        txn.delete(b"key1").await.unwrap();

        // Read-your-writes: see the delete
        assert!(txn.get(b"key1").await.unwrap().is_none());

        // Commit
        txn.commit().await.unwrap();

        // Value deleted
        assert!(kv.get(&actor_id, b"key1").await.unwrap().is_none());
    }
}

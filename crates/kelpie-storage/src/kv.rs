//! KV trait and operations
//!
//! TigerStyle: Explicit operations, bounded sizes, atomic transactions.

use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, ContextKV, Result};
use std::sync::Arc;

/// Operation on the KV store
#[derive(Debug, Clone)]
pub enum KVOperation {
    /// Get a value by key
    Get { key: Vec<u8> },
    /// Set a key-value pair
    Set { key: Vec<u8>, value: Vec<u8> },
    /// Delete a key
    Delete { key: Vec<u8> },
}

/// Transaction on an actor's KV store
///
/// Provides atomic multi-key operations. Writes are buffered until commit.
/// On commit, all writes are applied atomically. On abort (or drop without commit),
/// all writes are discarded.
///
/// TigerStyle: Explicit commit/abort, no implicit behavior on drop.
#[async_trait]
pub trait ActorTransaction: Send {
    /// Get a value within the transaction
    ///
    /// Returns the buffered value if set in this transaction,
    /// otherwise reads from the underlying store.
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>>;

    /// Set a value (buffered until commit)
    ///
    /// The write is not visible to other transactions until commit.
    async fn set(&mut self, key: &[u8], value: &[u8]) -> Result<()>;

    /// Delete a key (buffered until commit)
    ///
    /// The delete is not visible to other transactions until commit.
    async fn delete(&mut self, key: &[u8]) -> Result<()>;

    /// Commit the transaction atomically
    ///
    /// All buffered writes are applied atomically. If any write fails,
    /// none are applied. Consumes the transaction.
    ///
    /// # Errors
    /// Returns error if commit fails (e.g., conflict, storage failure, crash).
    async fn commit(self: Box<Self>) -> Result<()>;

    /// Abort the transaction, discarding all writes
    ///
    /// All buffered writes are discarded. Consumes the transaction.
    async fn abort(self: Box<Self>) -> Result<()>;
}

/// Per-actor KV store trait
#[async_trait]
pub trait ActorKV: Send + Sync {
    /// Get a value by key
    async fn get(&self, actor_id: &ActorId, key: &[u8]) -> Result<Option<Bytes>>;

    /// Set a key-value pair
    async fn set(&self, actor_id: &ActorId, key: &[u8], value: &[u8]) -> Result<()>;

    /// Delete a key
    async fn delete(&self, actor_id: &ActorId, key: &[u8]) -> Result<()>;

    /// Check if a key exists
    async fn exists(&self, actor_id: &ActorId, key: &[u8]) -> Result<bool> {
        Ok(self.get(actor_id, key).await?.is_some())
    }

    /// List keys with a prefix
    async fn list_keys(&self, actor_id: &ActorId, prefix: &[u8]) -> Result<Vec<Vec<u8>>>;

    /// Begin a new transaction for an actor
    ///
    /// Returns a transaction handle that buffers writes until commit.
    /// The transaction provides atomic multi-key operations.
    ///
    /// # Example
    /// ```ignore
    /// let mut txn = kv.begin_transaction(&actor_id).await?;
    /// txn.set(b"key1", b"value1").await?;
    /// txn.set(b"key2", b"value2").await?;
    /// txn.commit().await?;  // Atomic commit
    /// ```
    async fn begin_transaction(&self, actor_id: &ActorId) -> Result<Box<dyn ActorTransaction>>;
}

/// KV store scoped to a specific actor
///
/// Wraps an ActorKV and automatically supplies the actor_id for all operations.
/// This provides a cleaner interface for per-actor operations.
pub struct ScopedKV {
    actor_id: ActorId,
    kv: Arc<dyn ActorKV>,
}

impl ScopedKV {
    /// Create a new ScopedKV bound to a specific actor
    pub fn new(actor_id: ActorId, kv: Arc<dyn ActorKV>) -> Self {
        Self { actor_id, kv }
    }

    /// Get the actor ID this KV is scoped to
    pub fn actor_id(&self) -> &ActorId {
        &self.actor_id
    }

    /// Get a clone of the underlying ActorKV
    ///
    /// Used by the runtime to create buffering wrappers.
    pub fn underlying_kv(&self) -> Arc<dyn ActorKV> {
        self.kv.clone()
    }

    /// Get a value by key
    pub async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> {
        self.kv.get(&self.actor_id, key).await
    }

    /// Set a key-value pair
    pub async fn set(&self, key: &[u8], value: &[u8]) -> Result<()> {
        self.kv.set(&self.actor_id, key, value).await
    }

    /// Delete a key
    pub async fn delete(&self, key: &[u8]) -> Result<()> {
        self.kv.delete(&self.actor_id, key).await
    }

    /// Check if a key exists
    pub async fn exists(&self, key: &[u8]) -> Result<bool> {
        self.kv.exists(&self.actor_id, key).await
    }

    /// List keys with a prefix
    pub async fn list_keys(&self, prefix: &[u8]) -> Result<Vec<Vec<u8>>> {
        self.kv.list_keys(&self.actor_id, prefix).await
    }

    /// Begin a new transaction
    ///
    /// Returns a transaction handle that buffers writes until commit.
    /// The transaction is automatically scoped to this actor.
    pub async fn begin_transaction(&self) -> Result<Box<dyn ActorTransaction>> {
        self.kv.begin_transaction(&self.actor_id).await
    }
}

/// Implement ContextKV for ScopedKV
///
/// This allows ScopedKV to be used as the KV backend for ActorContext.
#[async_trait]
impl ContextKV for ScopedKV {
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> {
        ScopedKV::get(self, key).await
    }

    async fn set(&self, key: &[u8], value: &[u8]) -> Result<()> {
        ScopedKV::set(self, key, value).await
    }

    async fn delete(&self, key: &[u8]) -> Result<()> {
        ScopedKV::delete(self, key).await
    }

    async fn exists(&self, key: &[u8]) -> Result<bool> {
        ScopedKV::exists(self, key).await
    }

    async fn list_keys(&self, prefix: &[u8]) -> Result<Vec<Vec<u8>>> {
        ScopedKV::list_keys(self, prefix).await
    }
}

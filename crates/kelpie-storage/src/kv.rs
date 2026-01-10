//! KV trait and operations
//!
//! TigerStyle: Explicit operations, bounded sizes.

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

//! KV trait and operations
//!
//! TigerStyle: Explicit operations, bounded sizes.

use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, Result};

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

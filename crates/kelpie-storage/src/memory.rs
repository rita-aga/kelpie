//! In-memory KV storage
//!
//! For testing and DST simulations.

use crate::kv::ActorKV;
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, Result};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Per-actor KV data: key -> value
type ActorData = HashMap<Vec<u8>, Vec<u8>>;

/// Storage data: actor_id -> actor data
type StorageData = HashMap<String, ActorData>;

/// In-memory KV store
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
    async fn get(&self, actor_id: &ActorId, key: &[u8]) -> Result<Option<Bytes>> {
        let data = self.data.read().await;
        let actor_key = Self::actor_key(actor_id);

        Ok(data
            .get(&actor_key)
            .and_then(|actor_data| actor_data.get(key))
            .map(|v| Bytes::copy_from_slice(v)))
    }

    async fn set(&self, actor_id: &ActorId, key: &[u8], value: &[u8]) -> Result<()> {
        let mut data = self.data.write().await;
        let actor_key = Self::actor_key(actor_id);

        data.entry(actor_key)
            .or_default()
            .insert(key.to_vec(), value.to_vec());

        Ok(())
    }

    async fn delete(&self, actor_id: &ActorId, key: &[u8]) -> Result<()> {
        let mut data = self.data.write().await;
        let actor_key = Self::actor_key(actor_id);

        if let Some(actor_data) = data.get_mut(&actor_key) {
            actor_data.remove(key);
        }

        Ok(())
    }

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
}

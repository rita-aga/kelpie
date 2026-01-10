//! Simulated storage for deterministic testing
//!
//! TigerStyle: In-memory storage with fault injection.

use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, Error, Result};
use kelpie_storage::ActorKV;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Simulated storage for DST
///
/// Provides an in-memory key-value store with configurable fault injection.
#[derive(Debug)]
pub struct SimStorage {
    /// Storage data
    data: Arc<RwLock<HashMap<Vec<u8>, Vec<u8>>>>,
    /// Fault injector
    fault_injector: Arc<FaultInjector>,
    /// RNG for deterministic behavior
    rng: DeterministicRng,
    /// Storage size limit in bytes (None = unlimited)
    size_limit_bytes: Option<usize>,
    /// Current storage size in bytes
    current_size_bytes: Arc<std::sync::atomic::AtomicUsize>,
}

impl SimStorage {
    /// Create new simulated storage
    pub fn new(rng: DeterministicRng, fault_injector: Arc<FaultInjector>) -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
            fault_injector,
            rng,
            size_limit_bytes: None,
            current_size_bytes: Arc::new(std::sync::atomic::AtomicUsize::new(0)),
        }
    }

    /// Set a storage size limit
    pub fn with_size_limit(mut self, limit_bytes: usize) -> Self {
        self.size_limit_bytes = Some(limit_bytes);
        self
    }

    /// Read a value from storage
    pub async fn read(&self, key: &[u8]) -> Result<Option<Bytes>> {
        // Check for fault injection
        if let Some(fault) = self.fault_injector.should_inject("storage_read") {
            return self.handle_read_fault(fault, key);
        }

        let data = self.data.read().await;
        Ok(data.get(key).map(|v| Bytes::copy_from_slice(v)))
    }

    /// Write a value to storage
    pub async fn write(&self, key: &[u8], value: &[u8]) -> Result<()> {
        // Check for fault injection
        if let Some(fault) = self.fault_injector.should_inject("storage_write") {
            return self.handle_write_fault(fault, key);
        }

        // Check size limit
        if let Some(limit) = self.size_limit_bytes {
            let new_size = key.len() + value.len();
            let current = self
                .current_size_bytes
                .load(std::sync::atomic::Ordering::SeqCst);
            if current + new_size > limit {
                return Err(Error::StorageWriteFailed {
                    key: String::from_utf8_lossy(key).to_string(),
                    reason: "storage size limit exceeded".into(),
                });
            }
        }

        let mut data = self.data.write().await;

        // Update size tracking
        let old_size = data.get(key).map(|v| v.len()).unwrap_or(0);
        let new_size = value.len();
        let size_delta = new_size as isize - old_size as isize;

        data.insert(key.to_vec(), value.to_vec());

        if size_delta > 0 {
            self.current_size_bytes
                .fetch_add(size_delta as usize, std::sync::atomic::Ordering::SeqCst);
        } else {
            self.current_size_bytes
                .fetch_sub((-size_delta) as usize, std::sync::atomic::Ordering::SeqCst);
        }

        Ok(())
    }

    /// Delete a value from storage
    pub async fn delete(&self, key: &[u8]) -> Result<()> {
        // Check for fault injection
        if let Some(fault) = self.fault_injector.should_inject("storage_delete") {
            return self.handle_write_fault(fault, key);
        }

        let mut data = self.data.write().await;

        if let Some(old_value) = data.remove(key) {
            self.current_size_bytes
                .fetch_sub(old_value.len(), std::sync::atomic::Ordering::SeqCst);
        }

        Ok(())
    }

    /// Check if a key exists
    pub async fn exists(&self, key: &[u8]) -> Result<bool> {
        let data = self.data.read().await;
        Ok(data.contains_key(key))
    }

    /// List all keys with a given prefix
    pub async fn list_keys(&self, prefix: &[u8]) -> Result<Vec<Vec<u8>>> {
        let data = self.data.read().await;
        Ok(data
            .keys()
            .filter(|k| k.starts_with(prefix))
            .cloned()
            .collect())
    }

    /// Get current storage size in bytes
    pub fn size_bytes(&self) -> usize {
        self.current_size_bytes
            .load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Clear all data
    pub async fn clear(&self) {
        let mut data = self.data.write().await;
        data.clear();
        self.current_size_bytes
            .store(0, std::sync::atomic::Ordering::SeqCst);
    }

    /// Handle read faults
    fn handle_read_fault(&self, fault: FaultType, key: &[u8]) -> Result<Option<Bytes>> {
        match fault {
            FaultType::StorageReadFail => Err(Error::StorageReadFailed {
                key: String::from_utf8_lossy(key).to_string(),
                reason: "injected fault".into(),
            }),
            FaultType::StorageCorruption => {
                // Return corrupted data
                let corrupted = self.rng.next_u64().to_le_bytes().to_vec();
                Ok(Some(Bytes::from(corrupted)))
            }
            _ => Ok(None),
        }
    }

    /// Handle write faults
    fn handle_write_fault(&self, fault: FaultType, key: &[u8]) -> Result<()> {
        match fault {
            FaultType::StorageWriteFail => Err(Error::StorageWriteFailed {
                key: String::from_utf8_lossy(key).to_string(),
                reason: "injected fault".into(),
            }),
            FaultType::DiskFull => Err(Error::StorageWriteFailed {
                key: String::from_utf8_lossy(key).to_string(),
                reason: "disk full (injected)".into(),
            }),
            FaultType::CrashBeforeWrite => Err(Error::Internal {
                message: "crash before write (injected)".into(),
            }),
            FaultType::CrashAfterWrite => {
                // Write succeeds but then we "crash"
                // In a real simulation, this would trigger recovery
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Create a scoped key by prefixing with actor_id
    fn scoped_key(actor_id: &ActorId, key: &[u8]) -> Vec<u8> {
        let prefix = actor_id.to_key_bytes();
        let mut scoped = Vec::with_capacity(prefix.len() + 1 + key.len());
        scoped.extend_from_slice(&prefix);
        scoped.push(b'/');
        scoped.extend_from_slice(key);
        scoped
    }
}

/// Implement ActorKV for SimStorage
///
/// This allows SimStorage to be used as the storage backend for actor runtime
/// in deterministic simulation tests. Keys are automatically prefixed with actor_id.
#[async_trait]
impl ActorKV for SimStorage {
    async fn get(&self, actor_id: &ActorId, key: &[u8]) -> Result<Option<Bytes>> {
        let scoped_key = Self::scoped_key(actor_id, key);
        self.read(&scoped_key).await
    }

    async fn set(&self, actor_id: &ActorId, key: &[u8], value: &[u8]) -> Result<()> {
        let scoped_key = Self::scoped_key(actor_id, key);
        self.write(&scoped_key, value).await
    }

    async fn delete(&self, actor_id: &ActorId, key: &[u8]) -> Result<()> {
        let scoped_key = Self::scoped_key(actor_id, key);
        SimStorage::delete(self, &scoped_key).await
    }

    async fn exists(&self, actor_id: &ActorId, key: &[u8]) -> Result<bool> {
        let scoped_key = Self::scoped_key(actor_id, key);
        SimStorage::exists(self, &scoped_key).await
    }

    async fn list_keys(&self, actor_id: &ActorId, prefix: &[u8]) -> Result<Vec<Vec<u8>>> {
        let scoped_prefix = Self::scoped_key(actor_id, prefix);
        let actor_prefix = Self::scoped_key(actor_id, b"");

        // Get keys with the scoped prefix
        let keys = SimStorage::list_keys(self, &scoped_prefix).await?;

        // Remove the actor prefix from each key to return only the user's key portion
        Ok(keys
            .into_iter()
            .map(|k| k[actor_prefix.len()..].to_vec())
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::{FaultConfig, FaultInjectorBuilder};

    #[tokio::test]
    async fn test_sim_storage_basic() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector);

        // Write and read
        storage.write(b"key1", b"value1").await.unwrap();
        let value = storage.read(b"key1").await.unwrap();
        assert_eq!(value, Some(Bytes::from("value1")));

        // Delete
        storage.delete(b"key1").await.unwrap();
        let value = storage.read(b"key1").await.unwrap();
        assert!(value.is_none());
    }

    #[tokio::test]
    async fn test_sim_storage_with_faults() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 1.0))
                .build(),
        );
        let storage = SimStorage::new(rng, fault_injector);

        // Write should fail
        let result = storage.write(b"key1", b"value1").await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_sim_storage_size_limit() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector).with_size_limit(100);

        // Write within limit
        storage.write(b"key1", b"value1").await.unwrap();
        assert!(storage.size_bytes() > 0);

        // Write exceeding limit should fail
        let large_value = vec![0u8; 200];
        let result = storage.write(b"key2", &large_value).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_sim_storage_list_keys() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector);

        storage.write(b"prefix:key1", b"value1").await.unwrap();
        storage.write(b"prefix:key2", b"value2").await.unwrap();
        storage.write(b"other:key3", b"value3").await.unwrap();

        let keys = storage.list_keys(b"prefix:").await.unwrap();
        assert_eq!(keys.len(), 2);
    }
}

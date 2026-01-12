//! Simulated storage for deterministic testing
//!
//! TigerStyle: In-memory storage with fault injection, including transaction support.

use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::{ActorId, Error, Result};
use kelpie_storage::{ActorKV, ActorTransaction};
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
            match &fault {
                FaultType::StorageLatency { min_ms, max_ms } => {
                    // Add delay, then continue with actual read
                    let range = max_ms.saturating_sub(*min_ms) + 1;
                    let delay_ms = if range > 0 {
                        min_ms + (self.rng.next_u64() % range)
                    } else {
                        *min_ms
                    };
                    tokio::time::sleep(std::time::Duration::from_millis(delay_ms)).await;
                    // Fall through to actual read
                }
                _ => {
                    return self.handle_read_fault(fault, key);
                }
            }
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
            FaultType::StorageLatency {
                min_ms: _,
                max_ms: _,
            } => {
                // Latency fault - sleep would happen in async context
                // For now, just continue with normal read (latency handled elsewhere)
                // This should NOT return Ok(None) - that's a bug!
                // Return a marker that this fault doesn't affect the read result
                Err(Error::Internal {
                    message: "StorageLatency fault should not be handled in handle_read_fault"
                        .into(),
                })
            }
            _ => {
                // Unknown fault types should not silently return Ok(None)
                // That's misleading - it makes it look like the key doesn't exist
                Err(Error::Internal {
                    message: format!("Unexpected fault type in handle_read_fault: {:?}", fault),
                })
            }
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

    async fn begin_transaction(&self, actor_id: &ActorId) -> Result<Box<dyn ActorTransaction>> {
        // Note: We don't inject faults at transaction begin.
        // Transaction failures are more realistic at commit time (when writes happen).
        // General storage faults (StorageWriteFail) should not block beginning a transaction.
        // The CrashDuringTransaction fault is injected at commit time.

        Ok(Box::new(SimTransaction::new(
            actor_id.clone(),
            self.data.clone(),
            self.fault_injector.clone(),
        )))
    }
}

/// Transaction for simulated storage with fault injection
///
/// Buffers writes until commit. Supports CrashDuringTransaction fault injection
/// to test application behavior when transactions fail mid-commit.
///
/// TigerStyle: Explicit state, fault injection at commit boundary.
pub struct SimTransaction {
    /// Actor this transaction operates on
    actor_id: ActorId,
    /// Reference to the underlying storage data
    data: Arc<RwLock<HashMap<Vec<u8>, Vec<u8>>>>,
    /// Fault injector for crash simulation
    fault_injector: Arc<FaultInjector>,
    /// Buffered writes: scoped_key -> Some(value) for set, None for delete
    write_buffer: HashMap<Vec<u8>, Option<Vec<u8>>>,
    /// Whether this transaction has been finalized (committed or aborted)
    finalized: bool,
}

impl SimTransaction {
    fn new(
        actor_id: ActorId,
        data: Arc<RwLock<HashMap<Vec<u8>, Vec<u8>>>>,
        fault_injector: Arc<FaultInjector>,
    ) -> Self {
        Self {
            actor_id,
            data,
            fault_injector,
            write_buffer: HashMap::new(),
            finalized: false,
        }
    }

    /// Create a scoped key by prefixing with actor_id
    fn scoped_key(&self, key: &[u8]) -> Vec<u8> {
        let prefix = self.actor_id.to_key_bytes();
        let mut scoped = Vec::with_capacity(prefix.len() + 1 + key.len());
        scoped.extend_from_slice(&prefix);
        scoped.push(b'/');
        scoped.extend_from_slice(key);
        scoped
    }
}

#[async_trait]
impl ActorTransaction for SimTransaction {
    async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(!key.is_empty(), "key cannot be empty");

        let scoped_key = self.scoped_key(key);

        // Check write buffer first (read-your-writes)
        if let Some(buffered) = self.write_buffer.get(&scoped_key) {
            return Ok(buffered.as_ref().map(|v| Bytes::copy_from_slice(v)));
        }

        // Check for read fault injection
        if let Some(fault) = self.fault_injector.should_inject("transaction_read") {
            if matches!(fault, FaultType::StorageReadFail) {
                return Err(Error::StorageReadFailed {
                    key: String::from_utf8_lossy(key).to_string(),
                    reason: "injected fault in transaction".into(),
                });
            }
        }

        // Fall back to storage
        let data = self.data.read().await;
        Ok(data.get(&scoped_key).map(|v| Bytes::copy_from_slice(v)))
    }

    async fn set(&mut self, key: &[u8], value: &[u8]) -> Result<()> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(!key.is_empty(), "key cannot be empty");

        let scoped_key = self.scoped_key(key);
        self.write_buffer.insert(scoped_key, Some(value.to_vec()));
        Ok(())
    }

    async fn delete(&mut self, key: &[u8]) -> Result<()> {
        // Preconditions
        assert!(!self.finalized, "transaction already finalized");
        assert!(!key.is_empty(), "key cannot be empty");

        let scoped_key = self.scoped_key(key);
        self.write_buffer.insert(scoped_key, None);
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

        // Check for CrashDuringTransaction fault - this is the KEY fault for DST
        if let Some(fault) = self.fault_injector.should_inject("transaction_commit") {
            match fault {
                FaultType::CrashDuringTransaction => {
                    // Simulate crash: transaction is NOT applied
                    // Application should handle this by retrying or recovering
                    return Err(Error::Internal {
                        message: "crash during transaction commit (injected)".into(),
                    });
                }
                FaultType::StorageWriteFail => {
                    return Err(Error::StorageWriteFailed {
                        key: "transaction".into(),
                        reason: "injected fault during commit".into(),
                    });
                }
                FaultType::CrashBeforeWrite => {
                    // Crash before any writes applied
                    return Err(Error::Internal {
                        message: "crash before transaction write (injected)".into(),
                    });
                }
                FaultType::CrashAfterWrite => {
                    // Writes succeed, but we "crash" after - for DST this means
                    // the transaction succeeded but the caller might not know
                    // Fall through to apply writes, then return Ok
                }
                _ => {}
            }
        }

        // Apply all buffered writes atomically
        let mut data = self.data.write().await;
        for (key, value) in self.write_buffer.drain() {
            match value {
                Some(v) => {
                    data.insert(key, v);
                }
                None => {
                    data.remove(&key);
                }
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

    // ============ Transaction Tests ============

    #[tokio::test]
    async fn test_transaction_atomic_commit() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector);
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Begin transaction and write multiple keys
        let mut txn = storage.begin_transaction(&actor_id).await.unwrap();
        txn.set(b"key1", b"value1").await.unwrap();
        txn.set(b"key2", b"value2").await.unwrap();
        txn.set(b"key3", b"value3").await.unwrap();

        // Before commit, values not visible via direct storage access
        assert!(storage.get(&actor_id, b"key1").await.unwrap().is_none());

        // Commit
        txn.commit().await.unwrap();

        // After commit, ALL values visible (atomic)
        assert_eq!(
            storage.get(&actor_id, b"key1").await.unwrap(),
            Some(Bytes::from("value1"))
        );
        assert_eq!(
            storage.get(&actor_id, b"key2").await.unwrap(),
            Some(Bytes::from("value2"))
        );
        assert_eq!(
            storage.get(&actor_id, b"key3").await.unwrap(),
            Some(Bytes::from("value3"))
        );
    }

    #[tokio::test]
    async fn test_transaction_abort_rollback() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector);
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Begin transaction and write
        let mut txn = storage.begin_transaction(&actor_id).await.unwrap();
        txn.set(b"key1", b"value1").await.unwrap();
        txn.set(b"key2", b"value2").await.unwrap();

        // Abort
        txn.abort().await.unwrap();

        // After abort, NO values visible
        assert!(storage.get(&actor_id, b"key1").await.unwrap().is_none());
        assert!(storage.get(&actor_id, b"key2").await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_crash_during_transaction() {
        let rng = DeterministicRng::new(42);
        // Inject CrashDuringTransaction fault with 100% probability
        let fault_injector = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(
                    FaultConfig::new(FaultType::CrashDuringTransaction, 1.0)
                        .with_filter("transaction_commit"),
                )
                .build(),
        );
        let storage = SimStorage::new(rng, fault_injector);
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Begin transaction and write
        let mut txn = storage.begin_transaction(&actor_id).await.unwrap();
        txn.set(b"key1", b"value1").await.unwrap();
        txn.set(b"key2", b"value2").await.unwrap();

        // Commit should fail due to injected crash
        let result = txn.commit().await;
        assert!(result.is_err());

        // After crash, NO values visible (rollback semantics)
        assert!(storage.get(&actor_id, b"key1").await.unwrap().is_none());
        assert!(storage.get(&actor_id, b"key2").await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_crash_after_commit_preserves_data() {
        let rng = DeterministicRng::new(42);
        // Inject CrashAfterWrite - commit succeeds but caller may not know
        let fault_injector = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(
                    FaultConfig::new(FaultType::CrashAfterWrite, 1.0)
                        .with_filter("transaction_commit"),
                )
                .build(),
        );
        let storage = SimStorage::new(rng, fault_injector);
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Begin transaction and write
        let mut txn = storage.begin_transaction(&actor_id).await.unwrap();
        txn.set(b"key1", b"value1").await.unwrap();

        // Commit should succeed (CrashAfterWrite doesn't block commit)
        let result = txn.commit().await;
        assert!(result.is_ok());

        // Data IS visible because the write happened before the "crash"
        assert_eq!(
            storage.get(&actor_id, b"key1").await.unwrap(),
            Some(Bytes::from("value1"))
        );
    }

    #[tokio::test]
    async fn test_transaction_isolation() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector);
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        // Set initial value
        storage.set(&actor_id, b"key1", b"initial").await.unwrap();

        // Begin transaction
        let mut txn = storage.begin_transaction(&actor_id).await.unwrap();

        // Write in transaction
        txn.set(b"key1", b"updated").await.unwrap();

        // Transaction sees its own write
        assert_eq!(
            txn.get(b"key1").await.unwrap(),
            Some(Bytes::from("updated"))
        );

        // External read still sees old value (uncommitted not visible)
        assert_eq!(
            storage.get(&actor_id, b"key1").await.unwrap(),
            Some(Bytes::from("initial"))
        );

        // Commit
        txn.commit().await.unwrap();

        // Now external read sees new value
        assert_eq!(
            storage.get(&actor_id, b"key1").await.unwrap(),
            Some(Bytes::from("updated"))
        );
    }

    #[tokio::test]
    async fn test_transaction_read_your_writes() {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng, fault_injector);
        let actor_id = ActorId::new("test", "actor-1").unwrap();

        let mut txn = storage.begin_transaction(&actor_id).await.unwrap();

        // Write then read
        txn.set(b"key1", b"value1").await.unwrap();
        assert_eq!(txn.get(b"key1").await.unwrap(), Some(Bytes::from("value1")));

        // Delete then read
        txn.delete(b"key1").await.unwrap();
        assert!(txn.get(b"key1").await.unwrap().is_none());

        txn.abort().await.unwrap();
    }

    #[tokio::test]
    async fn test_transaction_determinism() {
        // Same seed should produce same results
        for seed in [42u64, 123, 456] {
            let rng1 = DeterministicRng::new(seed);
            let rng2 = DeterministicRng::new(seed);

            let fi1 = Arc::new(
                FaultInjectorBuilder::new(rng1.fork())
                    .with_fault(
                        FaultConfig::new(FaultType::CrashDuringTransaction, 0.5)
                            .with_filter("transaction_commit"),
                    )
                    .build(),
            );
            let fi2 = Arc::new(
                FaultInjectorBuilder::new(rng2.fork())
                    .with_fault(
                        FaultConfig::new(FaultType::CrashDuringTransaction, 0.5)
                            .with_filter("transaction_commit"),
                    )
                    .build(),
            );

            let storage1 = SimStorage::new(rng1, fi1);
            let storage2 = SimStorage::new(rng2, fi2);
            let actor_id = ActorId::new("test", "actor-1").unwrap();

            // Run same sequence of operations
            let results1 = run_transaction_sequence(&storage1, &actor_id).await;
            let results2 = run_transaction_sequence(&storage2, &actor_id).await;

            // Results should be identical (deterministic)
            assert_eq!(
                results1, results2,
                "seed {} produced different results",
                seed
            );
        }
    }

    async fn run_transaction_sequence(storage: &SimStorage, actor_id: &ActorId) -> Vec<bool> {
        let mut results = Vec::new();

        for i in 0..5 {
            let mut txn = storage.begin_transaction(actor_id).await.unwrap();
            txn.set(format!("key{}", i).as_bytes(), b"value")
                .await
                .unwrap();
            results.push(txn.commit().await.is_ok());
        }

        results
    }
}

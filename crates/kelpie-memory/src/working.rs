//! Working Memory - Fast KV store for session state
//!
//! TigerStyle: Redis-like access patterns with explicit TTL and size limits.
//!
//! Working memory stores transient data that doesn't need to be in every LLM context:
//! - Conversation history
//! - Scratch space for intermediate computations
//! - Session-specific data

use crate::error::{MemoryError, MemoryResult};
use crate::types::{now, MemoryMetadata, Timestamp};
use bytes::Bytes;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Default maximum working memory size (1MB)
pub const WORKING_MEMORY_SIZE_BYTES_MAX_DEFAULT: u64 = 1024 * 1024;

/// Default maximum entry size (64KB)
pub const WORKING_MEMORY_ENTRY_SIZE_BYTES_MAX_DEFAULT: u64 = 64 * 1024;

/// Default TTL for entries (1 hour)
pub const WORKING_MEMORY_TTL_SECS_DEFAULT: u64 = 3600;

/// Configuration for working memory
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkingMemoryConfig {
    /// Maximum total size in bytes
    pub max_bytes: u64,
    /// Maximum size per entry in bytes
    pub max_entry_bytes: u64,
    /// Default TTL for entries (0 = no expiry)
    pub default_ttl_secs: u64,
}

impl WorkingMemoryConfig {
    /// Create with default settings
    pub fn new() -> Self {
        Self {
            max_bytes: WORKING_MEMORY_SIZE_BYTES_MAX_DEFAULT,
            max_entry_bytes: WORKING_MEMORY_ENTRY_SIZE_BYTES_MAX_DEFAULT,
            default_ttl_secs: WORKING_MEMORY_TTL_SECS_DEFAULT,
        }
    }

    /// Create with no TTL (entries never expire)
    pub fn no_expiry() -> Self {
        Self {
            default_ttl_secs: 0,
            ..Self::new()
        }
    }
}

impl Default for WorkingMemoryConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// A single entry in working memory
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkingMemoryEntry {
    /// The key
    pub key: String,
    /// The value
    pub value: Bytes,
    /// Size in bytes
    pub size_bytes: u64,
    /// Expiration time (None = no expiry)
    pub expires_at: Option<Timestamp>,
    /// Metadata
    pub metadata: MemoryMetadata,
}

impl WorkingMemoryEntry {
    /// Create a new entry
    pub fn new(key: impl Into<String>, value: impl Into<Bytes>, ttl_secs: u64) -> Self {
        let key = key.into();
        let value = value.into();
        let size_bytes = (key.len() + value.len()) as u64;

        let expires_at = if ttl_secs > 0 {
            Some(now() + chrono::Duration::seconds(ttl_secs as i64))
        } else {
            None
        };

        Self {
            key,
            value,
            size_bytes,
            expires_at,
            metadata: MemoryMetadata::new(),
        }
    }

    /// Check if this entry has expired
    pub fn is_expired(&self) -> bool {
        self.expires_at.map(|exp| now() > exp).unwrap_or(false)
    }

    /// Update the value
    pub fn update(&mut self, value: impl Into<Bytes>, ttl_secs: u64) {
        let value = value.into();
        self.size_bytes = (self.key.len() + value.len()) as u64;
        self.value = value;

        self.expires_at = if ttl_secs > 0 {
            Some(now() + chrono::Duration::seconds(ttl_secs as i64))
        } else {
            None
        };

        self.metadata.record_modification();
    }

    /// Touch to update expiration
    pub fn touch(&mut self, ttl_secs: u64) {
        if ttl_secs > 0 {
            self.expires_at = Some(now() + chrono::Duration::seconds(ttl_secs as i64));
        }
        self.metadata.record_access();
    }
}

/// Working memory storage
///
/// Provides Redis-like KV operations with TTL support.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkingMemory {
    /// Configuration
    config: WorkingMemoryConfig,
    /// Entries indexed by key
    entries: HashMap<String, WorkingMemoryEntry>,
    /// Current total size in bytes
    current_bytes: u64,
    /// Metadata
    metadata: MemoryMetadata,
}

impl WorkingMemory {
    /// Create a new empty working memory
    pub fn new(config: WorkingMemoryConfig) -> Self {
        Self {
            config,
            entries: HashMap::new(),
            current_bytes: 0,
            metadata: MemoryMetadata::new(),
        }
    }

    /// Create with default configuration
    pub fn with_defaults() -> Self {
        Self::new(WorkingMemoryConfig::default())
    }

    /// Set a key-value pair
    pub fn set(&mut self, key: impl Into<String>, value: impl Into<Bytes>) -> MemoryResult<()> {
        self.set_with_ttl(key, value, self.config.default_ttl_secs)
    }

    /// Set a key-value pair with custom TTL
    pub fn set_with_ttl(
        &mut self,
        key: impl Into<String>,
        value: impl Into<Bytes>,
        ttl_secs: u64,
    ) -> MemoryResult<()> {
        let key = key.into();
        let value: Bytes = value.into();

        // Check entry size
        let entry_size = (key.len() + value.len()) as u64;
        if entry_size > self.config.max_entry_bytes {
            return Err(MemoryError::BlockTooLarge {
                block_id: key,
                size_bytes: entry_size,
                max_bytes: self.config.max_entry_bytes,
            });
        }

        // Calculate size change
        let old_size = self.entries.get(&key).map(|e| e.size_bytes).unwrap_or(0);
        let new_total = self.current_bytes - old_size + entry_size;

        if new_total > self.config.max_bytes {
            // Try to make space by removing expired entries
            self.remove_expired();
            let new_total = self.current_bytes - old_size + entry_size;

            if new_total > self.config.max_bytes {
                return Err(MemoryError::CoreMemoryFull {
                    current_bytes: self.current_bytes,
                    max_bytes: self.config.max_bytes,
                    requested_bytes: entry_size,
                });
            }
        }

        // Update or insert
        if let Some(entry) = self.entries.get_mut(&key) {
            self.current_bytes -= entry.size_bytes;
            entry.update(value, ttl_secs);
            self.current_bytes += entry.size_bytes;
        } else {
            let entry = WorkingMemoryEntry::new(key.clone(), value, ttl_secs);
            self.current_bytes += entry.size_bytes;
            self.entries.insert(key, entry);
        }

        self.metadata.record_modification();
        Ok(())
    }

    /// Get a value by key
    pub fn get(&self, key: &str) -> Option<&Bytes> {
        self.entries
            .get(key)
            .and_then(|e| if e.is_expired() { None } else { Some(&e.value) })
    }

    /// Get an entry with metadata
    pub fn get_entry(&self, key: &str) -> Option<&WorkingMemoryEntry> {
        self.entries.get(key).filter(|e| !e.is_expired())
    }

    /// Get a mutable entry
    pub fn get_entry_mut(&mut self, key: &str) -> Option<&mut WorkingMemoryEntry> {
        self.entries.get_mut(key).filter(|e| !e.is_expired())
    }

    /// Check if a key exists
    pub fn exists(&self, key: &str) -> bool {
        self.entries
            .get(key)
            .map(|e| !e.is_expired())
            .unwrap_or(false)
    }

    /// Delete a key
    pub fn delete(&mut self, key: &str) -> Option<Bytes> {
        if let Some(entry) = self.entries.remove(key) {
            self.current_bytes -= entry.size_bytes;
            self.metadata.record_modification();
            Some(entry.value)
        } else {
            None
        }
    }

    /// Touch a key to update its TTL
    pub fn touch(&mut self, key: &str) -> bool {
        if let Some(entry) = self.entries.get_mut(key) {
            if !entry.is_expired() {
                entry.touch(self.config.default_ttl_secs);
                return true;
            }
        }
        false
    }

    /// Get all keys
    pub fn keys(&self) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|(_, e)| !e.is_expired())
            .map(|(k, _)| k.as_str())
            .collect()
    }

    /// Get keys matching a prefix
    pub fn keys_with_prefix(&self, prefix: &str) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|(k, e)| k.starts_with(prefix) && !e.is_expired())
            .map(|(k, _)| k.as_str())
            .collect()
    }

    /// Remove all expired entries
    pub fn remove_expired(&mut self) -> usize {
        let expired: Vec<String> = self
            .entries
            .iter()
            .filter(|(_, e)| e.is_expired())
            .map(|(k, _)| k.clone())
            .collect();

        let count = expired.len();
        for key in expired {
            if let Some(entry) = self.entries.remove(&key) {
                self.current_bytes -= entry.size_bytes;
            }
        }

        if count > 0 {
            self.metadata.record_modification();
        }

        count
    }

    /// Clear all entries
    pub fn clear(&mut self) {
        self.entries.clear();
        self.current_bytes = 0;
        self.metadata.record_modification();
    }

    /// Get the number of entries (including expired)
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Get the number of non-expired entries
    pub fn active_len(&self) -> usize {
        self.entries.values().filter(|e| !e.is_expired()).count()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get current size in bytes
    pub fn size_bytes(&self) -> u64 {
        self.current_bytes
    }

    /// Get maximum size in bytes
    pub fn max_bytes(&self) -> u64 {
        self.config.max_bytes
    }

    /// Get available space in bytes
    pub fn available_bytes(&self) -> u64 {
        self.config.max_bytes - self.current_bytes
    }

    /// Increment a numeric value (creates if doesn't exist)
    pub fn incr(&mut self, key: &str, delta: i64) -> MemoryResult<i64> {
        let current = self
            .get(key)
            .and_then(|v| std::str::from_utf8(v).ok())
            .and_then(|s| s.parse::<i64>().ok())
            .unwrap_or(0);

        let new_value = current + delta;
        self.set(key, Bytes::from(new_value.to_string()))?;

        Ok(new_value)
    }

    /// Append to a value
    pub fn append(&mut self, key: &str, value: impl AsRef<[u8]>) -> MemoryResult<()> {
        let new_value = if let Some(existing) = self.get(key) {
            let mut combined = existing.to_vec();
            combined.extend_from_slice(value.as_ref());
            Bytes::from(combined)
        } else {
            Bytes::from(value.as_ref().to_vec())
        };

        self.set(key, new_value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_working_memory_new() {
        let memory = WorkingMemory::with_defaults();
        assert!(memory.is_empty());
        assert_eq!(memory.size_bytes(), 0);
    }

    #[test]
    fn test_set_and_get() {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("key1", Bytes::from("value1")).unwrap();

        let value = memory.get("key1").unwrap();
        assert_eq!(value.as_ref(), b"value1");
    }

    #[test]
    fn test_set_overwrite() {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("key", Bytes::from("value1")).unwrap();
        memory.set("key", Bytes::from("value2")).unwrap();

        let value = memory.get("key").unwrap();
        assert_eq!(value.as_ref(), b"value2");
    }

    #[test]
    fn test_exists() {
        let mut memory = WorkingMemory::with_defaults();

        assert!(!memory.exists("key"));

        memory.set("key", Bytes::from("value")).unwrap();
        assert!(memory.exists("key"));
    }

    #[test]
    fn test_delete() {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("key", Bytes::from("value")).unwrap();
        let deleted = memory.delete("key");

        assert!(deleted.is_some());
        assert_eq!(deleted.unwrap().as_ref(), b"value");
        assert!(!memory.exists("key"));
    }

    #[test]
    fn test_keys() {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("user:1:name", Bytes::from("Alice")).unwrap();
        memory.set("user:2:name", Bytes::from("Bob")).unwrap();
        memory.set("session:abc", Bytes::from("data")).unwrap();

        let all_keys = memory.keys();
        assert_eq!(all_keys.len(), 3);

        let user_keys = memory.keys_with_prefix("user:");
        assert_eq!(user_keys.len(), 2);
    }

    #[test]
    fn test_capacity_limit() {
        let config = WorkingMemoryConfig {
            max_bytes: 100,
            max_entry_bytes: 50,
            default_ttl_secs: 0,
        };
        let mut memory = WorkingMemory::new(config);

        // Add some data
        memory.set("key1", Bytes::from("x".repeat(40))).unwrap();

        // Try to add more than capacity
        let result = memory.set("key2", Bytes::from("x".repeat(70)));
        assert!(result.is_err());
    }

    #[test]
    fn test_entry_size_limit() {
        let config = WorkingMemoryConfig {
            max_bytes: 1000,
            max_entry_bytes: 50,
            default_ttl_secs: 0,
        };
        let mut memory = WorkingMemory::new(config);

        let result = memory.set("key", Bytes::from("x".repeat(100)));
        assert!(matches!(result, Err(MemoryError::BlockTooLarge { .. })));
    }

    #[test]
    fn test_clear() {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("key1", Bytes::from("value1")).unwrap();
        memory.set("key2", Bytes::from("value2")).unwrap();

        memory.clear();

        assert!(memory.is_empty());
        assert_eq!(memory.size_bytes(), 0);
    }

    #[test]
    fn test_incr() {
        let mut memory = WorkingMemory::with_defaults();

        // Increment non-existent key
        let val = memory.incr("counter", 1).unwrap();
        assert_eq!(val, 1);

        // Increment existing key
        let val = memory.incr("counter", 5).unwrap();
        assert_eq!(val, 6);

        // Decrement
        let val = memory.incr("counter", -2).unwrap();
        assert_eq!(val, 4);
    }

    #[test]
    fn test_append() {
        let mut memory = WorkingMemory::with_defaults();

        memory.append("log", "line1\n").unwrap();
        memory.append("log", "line2\n").unwrap();

        let value = memory.get("log").unwrap();
        assert_eq!(value.as_ref(), b"line1\nline2\n");
    }

    #[test]
    fn test_size_tracking() {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("key1", Bytes::from("value1")).unwrap();
        let size1 = memory.size_bytes();

        memory.set("key2", Bytes::from("value2")).unwrap();
        let size2 = memory.size_bytes();

        assert!(size2 > size1);

        memory.delete("key1");
        let size3 = memory.size_bytes();

        assert!(size3 < size2);
    }

    // Note: TTL tests are harder to test without mocking time
    // In production, these would use SimClock from kelpie-dst
}

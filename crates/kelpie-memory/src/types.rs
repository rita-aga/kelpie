//! Common types for the memory system
//!
//! TigerStyle: Explicit types with clear semantics.

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

/// Timestamp type for memory operations
///
/// Uses UTC to avoid timezone ambiguity.
pub type Timestamp = DateTime<Utc>;

/// Returns the current timestamp
pub fn now() -> Timestamp {
    Utc::now()
}

/// Metadata associated with a memory entry
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct MemoryMetadata {
    /// When the memory was created
    pub created_at: Timestamp,
    /// When the memory was last accessed
    pub accessed_at: Timestamp,
    /// When the memory was last modified
    pub modified_at: Timestamp,
    /// Number of times this memory has been accessed
    pub access_count: u64,
    /// Optional importance score (0.0 - 1.0)
    pub importance: Option<f32>,
    /// Optional tags for categorization
    pub tags: Vec<String>,
    /// Optional source information (e.g., "user_message", "tool_result")
    pub source: Option<String>,
}

impl MemoryMetadata {
    /// Create new metadata with current timestamp
    pub fn new() -> Self {
        let now = now();
        Self {
            created_at: now,
            accessed_at: now,
            modified_at: now,
            access_count: 0,
            importance: None,
            tags: Vec::new(),
            source: None,
        }
    }

    /// Create metadata with a specific source
    pub fn with_source(source: impl Into<String>) -> Self {
        let mut meta = Self::new();
        meta.source = Some(source.into());
        meta
    }

    /// Record an access to this memory
    pub fn record_access(&mut self) {
        self.accessed_at = now();
        self.access_count = self.access_count.saturating_add(1);
    }

    /// Record a modification to this memory
    pub fn record_modification(&mut self) {
        let now = now();
        self.accessed_at = now;
        self.modified_at = now;
    }

    /// Add a tag
    pub fn add_tag(&mut self, tag: impl Into<String>) {
        let tag = tag.into();
        if !self.tags.contains(&tag) {
            self.tags.push(tag);
        }
    }

    /// Set importance score
    pub fn set_importance(&mut self, importance: f32) {
        assert!(
            (0.0..=1.0).contains(&importance),
            "importance must be between 0.0 and 1.0"
        );
        self.importance = Some(importance);
    }
}

impl Default for MemoryMetadata {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics about memory usage
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct MemoryStats {
    /// Total number of blocks in core memory
    pub core_block_count: u64,
    /// Total bytes used in core memory
    pub core_bytes_used: u64,
    /// Total number of entries in working memory
    pub working_entry_count: u64,
    /// Total bytes used in working memory
    pub working_bytes_used: u64,
    /// Total number of entries in archival memory
    pub archival_entry_count: u64,
    /// Last checkpoint timestamp
    pub last_checkpoint: Option<Timestamp>,
}

impl MemoryStats {
    /// Create empty stats
    pub fn new() -> Self {
        Self::default()
    }

    /// Total memory usage across all tiers
    pub fn total_bytes(&self) -> u64 {
        self.core_bytes_used + self.working_bytes_used
    }

    /// Total entry count across all tiers
    pub fn total_entries(&self) -> u64 {
        self.core_block_count + self.working_entry_count + self.archival_entry_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metadata_new() {
        let meta = MemoryMetadata::new();
        assert_eq!(meta.access_count, 0);
        assert!(meta.importance.is_none());
        assert!(meta.tags.is_empty());
    }

    #[test]
    fn test_metadata_with_source() {
        let meta = MemoryMetadata::with_source("user_message");
        assert_eq!(meta.source, Some("user_message".to_string()));
    }

    #[test]
    fn test_metadata_record_access() {
        let mut meta = MemoryMetadata::new();
        let original_accessed = meta.accessed_at;

        std::thread::sleep(std::time::Duration::from_millis(10));
        meta.record_access();

        assert_eq!(meta.access_count, 1);
        assert!(meta.accessed_at >= original_accessed);
    }

    #[test]
    fn test_metadata_add_tag() {
        let mut meta = MemoryMetadata::new();
        meta.add_tag("important");
        meta.add_tag("important"); // Duplicate should be ignored
        meta.add_tag("work");

        assert_eq!(meta.tags.len(), 2);
        assert!(meta.tags.contains(&"important".to_string()));
        assert!(meta.tags.contains(&"work".to_string()));
    }

    #[test]
    fn test_metadata_set_importance() {
        let mut meta = MemoryMetadata::new();
        meta.set_importance(0.8);
        assert_eq!(meta.importance, Some(0.8));
    }

    #[test]
    #[should_panic(expected = "importance must be between 0.0 and 1.0")]
    fn test_metadata_invalid_importance() {
        let mut meta = MemoryMetadata::new();
        meta.set_importance(1.5);
    }

    #[test]
    fn test_stats_totals() {
        let stats = MemoryStats {
            core_block_count: 5,
            core_bytes_used: 1000,
            working_entry_count: 10,
            working_bytes_used: 2000,
            archival_entry_count: 100,
            last_checkpoint: None,
        };

        assert_eq!(stats.total_bytes(), 3000);
        assert_eq!(stats.total_entries(), 115);
    }
}

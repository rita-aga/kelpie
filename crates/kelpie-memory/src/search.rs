//! Memory search functionality
//!
//! TigerStyle: Explicit search types with semantic and temporal queries.
//!
//! Provides search across memory tiers:
//! - Text search (substring matching)
//! - Temporal search (time-based filtering)
//! - Semantic search (vector similarity - requires external embedding)

use crate::block::{MemoryBlock, MemoryBlockType};
use crate::types::Timestamp;
use serde::{Deserialize, Serialize};

/// Maximum number of search results
pub const SEARCH_RESULTS_LIMIT_DEFAULT: usize = 100;

/// A search query
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchQuery {
    /// Text to search for (substring match)
    pub text: Option<String>,
    /// Filter by block types
    pub block_types: Option<Vec<MemoryBlockType>>,
    /// Filter by tags
    pub tags: Option<Vec<String>>,
    /// Filter by creation time (after this timestamp)
    pub created_after: Option<Timestamp>,
    /// Filter by creation time (before this timestamp)
    pub created_before: Option<Timestamp>,
    /// Filter by modification time (after this timestamp)
    pub modified_after: Option<Timestamp>,
    /// Filter by modification time (before this timestamp)
    pub modified_before: Option<Timestamp>,
    /// Minimum importance score
    pub min_importance: Option<f32>,
    /// Maximum number of results
    pub limit: usize,
    /// Offset for pagination
    pub offset: usize,
}

impl SearchQuery {
    /// Create an empty query (matches all)
    pub fn new() -> Self {
        Self {
            text: None,
            block_types: None,
            tags: None,
            created_after: None,
            created_before: None,
            modified_after: None,
            modified_before: None,
            min_importance: None,
            limit: SEARCH_RESULTS_LIMIT_DEFAULT,
            offset: 0,
        }
    }

    /// Search for text
    pub fn text(mut self, text: impl Into<String>) -> Self {
        self.text = Some(text.into());
        self
    }

    /// Filter by block types
    pub fn block_types(mut self, types: Vec<MemoryBlockType>) -> Self {
        self.block_types = Some(types);
        self
    }

    /// Filter by a single block type
    pub fn block_type(mut self, block_type: MemoryBlockType) -> Self {
        self.block_types = Some(vec![block_type]);
        self
    }

    /// Filter by tags
    pub fn tags(mut self, tags: Vec<String>) -> Self {
        self.tags = Some(tags);
        self
    }

    /// Filter created after a timestamp
    pub fn created_after(mut self, timestamp: Timestamp) -> Self {
        self.created_after = Some(timestamp);
        self
    }

    /// Filter created before a timestamp
    pub fn created_before(mut self, timestamp: Timestamp) -> Self {
        self.created_before = Some(timestamp);
        self
    }

    /// Filter modified after a timestamp
    pub fn modified_after(mut self, timestamp: Timestamp) -> Self {
        self.modified_after = Some(timestamp);
        self
    }

    /// Filter modified before a timestamp
    pub fn modified_before(mut self, timestamp: Timestamp) -> Self {
        self.modified_before = Some(timestamp);
        self
    }

    /// Filter by minimum importance
    pub fn min_importance(mut self, importance: f32) -> Self {
        self.min_importance = Some(importance);
        self
    }

    /// Set result limit
    pub fn limit(mut self, limit: usize) -> Self {
        self.limit = limit;
        self
    }

    /// Set offset for pagination
    pub fn offset(mut self, offset: usize) -> Self {
        self.offset = offset;
        self
    }

    /// Check if a block matches this query
    pub fn matches(&self, block: &MemoryBlock) -> bool {
        // Text filter
        if let Some(ref text) = self.text {
            let text_lower = text.to_lowercase();
            if !block.content.to_lowercase().contains(&text_lower)
                && !block.label.to_lowercase().contains(&text_lower)
            {
                return false;
            }
        }

        // Block type filter
        if let Some(ref types) = self.block_types {
            if !types.contains(&block.block_type) {
                return false;
            }
        }

        // Tag filter
        if let Some(ref tags) = self.tags {
            if !tags.iter().any(|t| block.metadata.tags.contains(t)) {
                return false;
            }
        }

        // Created after filter
        if let Some(after) = self.created_after {
            if block.metadata.created_at <= after {
                return false;
            }
        }

        // Created before filter
        if let Some(before) = self.created_before {
            if block.metadata.created_at >= before {
                return false;
            }
        }

        // Modified after filter
        if let Some(after) = self.modified_after {
            if block.metadata.modified_at <= after {
                return false;
            }
        }

        // Modified before filter
        if let Some(before) = self.modified_before {
            if block.metadata.modified_at >= before {
                return false;
            }
        }

        // Importance filter
        if let Some(min_importance) = self.min_importance {
            match block.metadata.importance {
                Some(importance) if importance >= min_importance => {}
                _ => return false,
            }
        }

        true
    }
}

impl Default for SearchQuery {
    fn default() -> Self {
        Self::new()
    }
}

/// A single search result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    /// The matching block
    pub block: MemoryBlock,
    /// Relevance score (0.0 - 1.0)
    pub score: f32,
    /// Which part matched (for highlighting)
    pub matched_text: Option<String>,
}

impl SearchResult {
    /// Create a new search result
    pub fn new(block: MemoryBlock, score: f32) -> Self {
        Self {
            block,
            score,
            matched_text: None,
        }
    }

    /// Create with matched text
    pub fn with_match(block: MemoryBlock, score: f32, matched_text: impl Into<String>) -> Self {
        Self {
            block,
            score,
            matched_text: Some(matched_text.into()),
        }
    }
}

/// Collection of search results
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SearchResults {
    /// The matching results
    pub results: Vec<SearchResult>,
    /// Total number of matches (before pagination)
    pub total_count: usize,
    /// Whether there are more results
    pub has_more: bool,
}

impl SearchResults {
    /// Create empty results
    pub fn empty() -> Self {
        Self {
            results: Vec::new(),
            total_count: 0,
            has_more: false,
        }
    }

    /// Create from results
    pub fn new(results: Vec<SearchResult>, total_count: usize, has_more: bool) -> Self {
        Self {
            results,
            total_count,
            has_more,
        }
    }

    /// Get the number of results
    pub fn len(&self) -> usize {
        self.results.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.results.is_empty()
    }

    /// Get results as blocks
    pub fn into_blocks(self) -> Vec<MemoryBlock> {
        self.results.into_iter().map(|r| r.block).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_block(content: &str, block_type: MemoryBlockType) -> MemoryBlock {
        MemoryBlock::new(block_type, content)
    }

    #[test]
    fn test_query_new() {
        let query = SearchQuery::new();
        assert!(query.text.is_none());
        assert_eq!(query.limit, SEARCH_RESULTS_LIMIT_DEFAULT);
    }

    #[test]
    fn test_query_builder() {
        let query = SearchQuery::new()
            .text("hello")
            .block_type(MemoryBlockType::Facts)
            .limit(10);

        assert_eq!(query.text, Some("hello".to_string()));
        assert_eq!(query.block_types, Some(vec![MemoryBlockType::Facts]));
        assert_eq!(query.limit, 10);
    }

    #[test]
    fn test_query_matches_text() {
        let query = SearchQuery::new().text("hello");

        let block1 = make_test_block("hello world", MemoryBlockType::Facts);
        let block2 = make_test_block("goodbye world", MemoryBlockType::Facts);

        assert!(query.matches(&block1));
        assert!(!query.matches(&block2));
    }

    #[test]
    fn test_query_matches_text_case_insensitive() {
        let query = SearchQuery::new().text("HELLO");

        let block = make_test_block("hello world", MemoryBlockType::Facts);
        assert!(query.matches(&block));
    }

    #[test]
    fn test_query_matches_block_type() {
        let query = SearchQuery::new().block_type(MemoryBlockType::Facts);

        let facts_block = make_test_block("content", MemoryBlockType::Facts);
        let persona_block = make_test_block("content", MemoryBlockType::Persona);

        assert!(query.matches(&facts_block));
        assert!(!query.matches(&persona_block));
    }

    #[test]
    fn test_query_matches_multiple_types() {
        let query =
            SearchQuery::new().block_types(vec![MemoryBlockType::Facts, MemoryBlockType::Persona]);

        let facts_block = make_test_block("content", MemoryBlockType::Facts);
        let persona_block = make_test_block("content", MemoryBlockType::Persona);
        let system_block = make_test_block("content", MemoryBlockType::System);

        assert!(query.matches(&facts_block));
        assert!(query.matches(&persona_block));
        assert!(!query.matches(&system_block));
    }

    #[test]
    fn test_query_matches_tags() {
        let query = SearchQuery::new().tags(vec!["important".to_string()]);

        let mut block1 = make_test_block("content", MemoryBlockType::Facts);
        block1.metadata.add_tag("important");

        let block2 = make_test_block("content", MemoryBlockType::Facts);

        assert!(query.matches(&block1));
        assert!(!query.matches(&block2));
    }

    #[test]
    fn test_query_empty_matches_all() {
        let query = SearchQuery::new();

        let block1 = make_test_block("hello", MemoryBlockType::Facts);
        let block2 = make_test_block("world", MemoryBlockType::Persona);

        assert!(query.matches(&block1));
        assert!(query.matches(&block2));
    }

    #[test]
    fn test_search_results() {
        let block = make_test_block("test", MemoryBlockType::Facts);
        let result = SearchResult::new(block.clone(), 0.9);

        let results = SearchResults::new(vec![result], 1, false);

        assert_eq!(results.len(), 1);
        assert!(!results.has_more);
    }

    #[test]
    fn test_search_results_into_blocks() {
        let block1 = make_test_block("test1", MemoryBlockType::Facts);
        let block2 = make_test_block("test2", MemoryBlockType::Facts);

        let results = SearchResults::new(
            vec![
                SearchResult::new(block1.clone(), 0.9),
                SearchResult::new(block2.clone(), 0.8),
            ],
            2,
            false,
        );

        let blocks = results.into_blocks();
        assert_eq!(blocks.len(), 2);
    }
}

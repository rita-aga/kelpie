//! Hierarchical memory system for Kelpie agents
//!
//! TigerStyle: Three-tier memory with explicit boundaries and persistence guarantees.
//!
//! # Memory Tiers
//!
//! 1. **Core Memory** (~32KB) - Always loaded, in-context for LLM
//!    - System prompt, persona, key facts
//!    - Automatically included in every request
//!
//! 2. **Working Memory** - Fast KV store for session state
//!    - Conversation history, scratch space
//!    - Redis-like access patterns
//!
//! 3. **Archival Memory** - Long-term storage with semantic search
//!    - Vector embeddings for similarity search
//!    - Graph relationships (causal, temporal, topical)
//!
//! # Design Principles
//!
//! - Explicit tier boundaries (no automatic promotion/demotion)
//! - Checkpointing for durability
//! - Semantic + temporal search across tiers

mod block;
mod checkpoint;
mod core;
mod embedder;
mod error;
mod search;
mod types;
mod working;

pub use block::{MemoryBlock, MemoryBlockId, MemoryBlockType, MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX};
pub use checkpoint::{Checkpoint, CheckpointManager};
pub use core::{
    CoreMemory, CoreMemoryConfig, CORE_MEMORY_SIZE_BYTES_MAX_DEFAULT, CORE_MEMORY_SIZE_BYTES_MIN,
};
pub use embedder::{
    Embedder, EmbedderConfig, LocalEmbedder, MockEmbedder, EMBEDDING_DIM_1024, EMBEDDING_DIM_1536,
    EMBEDDING_DIM_384, EMBEDDING_DIM_768,
};
pub use error::{MemoryError, MemoryResult};
pub use search::{
    cosine_similarity, semantic_search, similarity_score, SearchQuery, SearchResult, SearchResults,
    SemanticQuery, SemanticSearchResult, SEARCH_RESULTS_LIMIT_DEFAULT,
    SEMANTIC_SEARCH_SIMILARITY_MIN_DEFAULT,
};
pub use types::{MemoryMetadata, MemoryStats, Timestamp};
pub use working::{WorkingMemory, WorkingMemoryConfig};

// Re-export for convenience
pub use kelpie_core::actor::ActorId;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_module_compiles() {
        // Smoke test - ensures all modules compile
        let _ = MemoryBlockId::new();
    }
}

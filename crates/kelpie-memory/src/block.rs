//! Memory block types and structures
//!
//! TigerStyle: Immutable blocks with explicit types and metadata.

use crate::types::{MemoryMetadata, Timestamp};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Maximum size for a single memory block content
pub const MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX: usize = 16 * 1024; // 16KB

/// Unique identifier for a memory block
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MemoryBlockId(String);

impl MemoryBlockId {
    /// Create a new unique block ID
    pub fn new() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    /// Create from an existing string
    pub fn from_string(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    /// Get the ID as a string reference
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for MemoryBlockId {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for MemoryBlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Type of memory block
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MemoryBlockType {
    /// System prompt and instructions
    System,
    /// Agent persona and personality
    Persona,
    /// Human/user information
    Human,
    /// Key facts and knowledge
    Facts,
    /// Goals and objectives
    Goals,
    /// Scratchpad for temporary notes
    Scratch,
    /// Custom block type
    Custom,
}

impl MemoryBlockType {
    /// Get the default label for this block type
    pub fn default_label(&self) -> &'static str {
        match self {
            Self::System => "system",
            Self::Persona => "persona",
            Self::Human => "human",
            Self::Facts => "facts",
            Self::Goals => "goals",
            Self::Scratch => "scratch",
            Self::Custom => "custom",
        }
    }
}

impl std::fmt::Display for MemoryBlockType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.default_label())
    }
}

/// A memory block containing structured content
///
/// Memory blocks are the fundamental unit of core memory.
/// Each block has a type, content, and metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryBlock {
    /// Unique identifier
    pub id: MemoryBlockId,
    /// Block type
    pub block_type: MemoryBlockType,
    /// Human-readable label
    pub label: String,
    /// The actual content
    pub content: String,
    /// Size in bytes (cached for quick access)
    pub size_bytes: u64,
    /// Metadata
    pub metadata: MemoryMetadata,
}

impl MemoryBlock {
    /// Create a new memory block
    ///
    /// # Panics
    /// Panics if content exceeds MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX
    pub fn new(block_type: MemoryBlockType, content: impl Into<String>) -> Self {
        let content = content.into();
        let size_bytes = content.len() as u64;

        assert!(
            size_bytes <= MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX as u64,
            "block content exceeds maximum size: {} > {}",
            size_bytes,
            MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX
        );

        Self {
            id: MemoryBlockId::new(),
            block_type,
            label: block_type.default_label().to_string(),
            content,
            size_bytes,
            metadata: MemoryMetadata::new(),
        }
    }

    /// Create a new block with a custom label
    pub fn with_label(
        block_type: MemoryBlockType,
        label: impl Into<String>,
        content: impl Into<String>,
    ) -> Self {
        let mut block = Self::new(block_type, content);
        block.label = label.into();
        block
    }

    /// Create a system block
    pub fn system(content: impl Into<String>) -> Self {
        Self::new(MemoryBlockType::System, content)
    }

    /// Create a persona block
    pub fn persona(content: impl Into<String>) -> Self {
        Self::new(MemoryBlockType::Persona, content)
    }

    /// Create a human/user info block
    pub fn human(content: impl Into<String>) -> Self {
        Self::new(MemoryBlockType::Human, content)
    }

    /// Create a facts block
    pub fn facts(content: impl Into<String>) -> Self {
        Self::new(MemoryBlockType::Facts, content)
    }

    /// Create a goals block
    pub fn goals(content: impl Into<String>) -> Self {
        Self::new(MemoryBlockType::Goals, content)
    }

    /// Create a scratch block
    pub fn scratch(content: impl Into<String>) -> Self {
        Self::new(MemoryBlockType::Scratch, content)
    }

    /// Update the content of this block
    ///
    /// # Panics
    /// Panics if content exceeds MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX
    pub fn update_content(&mut self, content: impl Into<String>) {
        let content = content.into();
        let size_bytes = content.len() as u64;

        assert!(
            size_bytes <= MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX as u64,
            "block content exceeds maximum size: {} > {}",
            size_bytes,
            MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX
        );

        self.content = content;
        self.size_bytes = size_bytes;
        self.metadata.record_modification();
    }

    /// Append to the content of this block
    ///
    /// # Panics
    /// Panics if resulting content exceeds MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX
    pub fn append_content(&mut self, additional: &str) {
        let new_content = format!("{}{}", self.content, additional);
        self.update_content(new_content);
    }

    /// Check if this block is empty
    pub fn is_empty(&self) -> bool {
        self.content.is_empty()
    }

    /// Get the creation timestamp
    pub fn created_at(&self) -> Timestamp {
        self.metadata.created_at
    }

    /// Get the last modified timestamp
    pub fn modified_at(&self) -> Timestamp {
        self.metadata.modified_at
    }

    /// Record an access to this block
    pub fn record_access(&mut self) {
        self.metadata.record_access();
    }
}

impl PartialEq for MemoryBlock {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for MemoryBlock {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_id_unique() {
        let id1 = MemoryBlockId::new();
        let id2 = MemoryBlockId::new();
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_block_id_from_string() {
        let id = MemoryBlockId::from_string("test-id");
        assert_eq!(id.as_str(), "test-id");
    }

    #[test]
    fn test_block_creation() {
        let block = MemoryBlock::system("You are a helpful assistant.");
        assert_eq!(block.block_type, MemoryBlockType::System);
        assert_eq!(block.label, "system");
        assert_eq!(block.content, "You are a helpful assistant.");
        assert_eq!(block.size_bytes, 28); // "You are a helpful assistant." is 28 bytes
    }

    #[test]
    fn test_block_with_label() {
        let block =
            MemoryBlock::with_label(MemoryBlockType::Custom, "my_custom_block", "Custom content");
        assert_eq!(block.label, "my_custom_block");
        assert_eq!(block.block_type, MemoryBlockType::Custom);
    }

    #[test]
    fn test_block_update_content() {
        let mut block = MemoryBlock::facts("Initial facts");
        let original_created = block.created_at();

        std::thread::sleep(std::time::Duration::from_millis(10));
        block.update_content("Updated facts");

        assert_eq!(block.content, "Updated facts");
        assert_eq!(block.size_bytes, 13);
        assert_eq!(block.created_at(), original_created);
        assert!(block.modified_at() > original_created);
    }

    #[test]
    fn test_block_append_content() {
        let mut block = MemoryBlock::scratch("Note 1");
        block.append_content("\nNote 2");

        assert_eq!(block.content, "Note 1\nNote 2");
    }

    #[test]
    #[should_panic(expected = "block content exceeds maximum size")]
    fn test_block_content_too_large() {
        let large_content = "x".repeat(MEMORY_BLOCK_CONTENT_SIZE_BYTES_MAX + 1);
        MemoryBlock::system(large_content);
    }

    #[test]
    fn test_block_type_display() {
        assert_eq!(MemoryBlockType::System.to_string(), "system");
        assert_eq!(MemoryBlockType::Persona.to_string(), "persona");
        assert_eq!(MemoryBlockType::Custom.to_string(), "custom");
    }

    #[test]
    fn test_block_equality() {
        let block1 = MemoryBlock::system("Content");
        let mut block2 = block1.clone();
        block2.content = "Different content".to_string();

        // Equality is based on ID only
        assert_eq!(block1, block2);

        let block3 = MemoryBlock::system("Content");
        assert_ne!(block1, block3);
    }

    #[test]
    fn test_block_is_empty() {
        let empty_block = MemoryBlock::scratch("");
        assert!(empty_block.is_empty());

        let non_empty = MemoryBlock::scratch("content");
        assert!(!non_empty.is_empty());
    }
}

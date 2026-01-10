//! Core Memory - Always loaded, in-context for LLM
//!
//! TigerStyle: Fixed capacity with explicit block management.
//!
//! Core memory contains blocks that are always included in the LLM context:
//! - System prompts and instructions
//! - Agent persona and personality
//! - Key facts about the user/environment
//! - Goals and current objectives

use crate::block::{MemoryBlock, MemoryBlockId, MemoryBlockType};
use crate::error::{MemoryError, MemoryResult};
use crate::types::MemoryMetadata;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Default maximum core memory size (32KB)
pub const CORE_MEMORY_SIZE_BYTES_MAX_DEFAULT: u64 = 32 * 1024;

/// Minimum core memory size (4KB)
pub const CORE_MEMORY_SIZE_BYTES_MIN: u64 = 4 * 1024;

/// Configuration for core memory
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoreMemoryConfig {
    /// Maximum total size in bytes
    pub max_bytes: u64,
}

impl CoreMemoryConfig {
    /// Create with default settings
    pub fn new() -> Self {
        Self {
            max_bytes: CORE_MEMORY_SIZE_BYTES_MAX_DEFAULT,
        }
    }

    /// Create with custom max size
    pub fn with_max_bytes(max_bytes: u64) -> Self {
        assert!(
            max_bytes >= CORE_MEMORY_SIZE_BYTES_MIN,
            "core memory size must be at least {} bytes",
            CORE_MEMORY_SIZE_BYTES_MIN
        );
        Self { max_bytes }
    }
}

impl Default for CoreMemoryConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Core memory storage
///
/// Manages memory blocks that are always included in LLM context.
/// Has a fixed capacity to ensure predictable context usage.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoreMemory {
    /// Configuration
    config: CoreMemoryConfig,
    /// Memory blocks indexed by ID
    blocks: HashMap<MemoryBlockId, MemoryBlock>,
    /// Block ordering (for consistent serialization)
    block_order: Vec<MemoryBlockId>,
    /// Current total size in bytes
    current_bytes: u64,
    /// Metadata
    metadata: MemoryMetadata,
}

impl CoreMemory {
    /// Create a new empty core memory
    pub fn new(config: CoreMemoryConfig) -> Self {
        Self {
            config,
            blocks: HashMap::new(),
            block_order: Vec::new(),
            current_bytes: 0,
            metadata: MemoryMetadata::new(),
        }
    }

    /// Create with default configuration
    pub fn with_defaults() -> Self {
        Self::new(CoreMemoryConfig::default())
    }

    /// Add a memory block
    ///
    /// Returns the block ID if successful.
    pub fn add_block(&mut self, block: MemoryBlock) -> MemoryResult<MemoryBlockId> {
        // Check capacity
        let new_size = self.current_bytes + block.size_bytes;
        if new_size > self.config.max_bytes {
            return Err(MemoryError::CoreMemoryFull {
                current_bytes: self.current_bytes,
                max_bytes: self.config.max_bytes,
                requested_bytes: block.size_bytes,
            });
        }

        let id = block.id.clone();
        self.current_bytes = new_size;
        self.block_order.push(id.clone());
        self.blocks.insert(id.clone(), block);
        self.metadata.record_modification();

        Ok(id)
    }

    /// Get a block by ID
    pub fn get_block(&self, id: &MemoryBlockId) -> Option<&MemoryBlock> {
        self.blocks.get(id)
    }

    /// Get a mutable reference to a block by ID
    pub fn get_block_mut(&mut self, id: &MemoryBlockId) -> Option<&mut MemoryBlock> {
        self.blocks.get_mut(id)
    }

    /// Get blocks by type
    pub fn get_blocks_by_type(&self, block_type: MemoryBlockType) -> Vec<&MemoryBlock> {
        self.blocks
            .values()
            .filter(|b| b.block_type == block_type)
            .collect()
    }

    /// Get the first block of a given type
    pub fn get_first_by_type(&self, block_type: MemoryBlockType) -> Option<&MemoryBlock> {
        self.block_order
            .iter()
            .find_map(|id| self.blocks.get(id).filter(|b| b.block_type == block_type))
    }

    /// Get mutable reference to the first block of a given type
    pub fn get_first_by_type_mut(
        &mut self,
        block_type: MemoryBlockType,
    ) -> Option<&mut MemoryBlock> {
        let id = self.block_order.iter().find(|id| {
            self.blocks
                .get(*id)
                .map(|b| b.block_type == block_type)
                .unwrap_or(false)
        })?;
        self.blocks.get_mut(id)
    }

    /// Update a block's content
    pub fn update_block(
        &mut self,
        id: &MemoryBlockId,
        content: impl Into<String>,
    ) -> MemoryResult<()> {
        let content = content.into();
        let new_size = content.len() as u64;

        let block = self
            .blocks
            .get_mut(id)
            .ok_or_else(|| MemoryError::BlockNotFound {
                block_id: id.to_string(),
            })?;

        let old_size = block.size_bytes;
        let size_diff = new_size as i64 - old_size as i64;
        let projected_total = (self.current_bytes as i64 + size_diff) as u64;

        if projected_total > self.config.max_bytes {
            return Err(MemoryError::CoreMemoryFull {
                current_bytes: self.current_bytes,
                max_bytes: self.config.max_bytes,
                requested_bytes: new_size,
            });
        }

        block.update_content(content);
        self.current_bytes = projected_total;
        self.metadata.record_modification();

        Ok(())
    }

    /// Remove a block
    pub fn remove_block(&mut self, id: &MemoryBlockId) -> MemoryResult<MemoryBlock> {
        let block = self
            .blocks
            .remove(id)
            .ok_or_else(|| MemoryError::BlockNotFound {
                block_id: id.to_string(),
            })?;

        self.block_order.retain(|b| b != id);
        self.current_bytes -= block.size_bytes;
        self.metadata.record_modification();

        Ok(block)
    }

    /// Clear all blocks
    pub fn clear(&mut self) {
        self.blocks.clear();
        self.block_order.clear();
        self.current_bytes = 0;
        self.metadata.record_modification();
    }

    /// Get all blocks in order
    pub fn blocks(&self) -> impl Iterator<Item = &MemoryBlock> {
        self.block_order
            .iter()
            .filter_map(move |id| self.blocks.get(id))
    }

    /// Get the number of blocks
    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
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

    /// Get utilization as a percentage (0.0 - 1.0)
    pub fn utilization(&self) -> f64 {
        if self.config.max_bytes == 0 {
            return 0.0;
        }
        self.current_bytes as f64 / self.config.max_bytes as f64
    }

    /// Render core memory as a string for LLM context
    ///
    /// Format:
    /// ```text
    /// <core_memory>
    /// <block label="system">
    /// System content here
    /// </block>
    /// <block label="persona">
    /// Persona content here
    /// </block>
    /// </core_memory>
    /// ```
    pub fn render(&self) -> String {
        let mut output = String::from("<core_memory>\n");

        for block in self.blocks() {
            output.push_str(&format!("<block label=\"{}\">\n", block.label));
            output.push_str(&block.content);
            if !block.content.ends_with('\n') {
                output.push('\n');
            }
            output.push_str("</block>\n");
        }

        output.push_str("</core_memory>");
        output
    }

    /// Create core memory with standard Letta-style blocks
    pub fn letta_default() -> Self {
        let mut memory = Self::with_defaults();

        // Add standard blocks (empty initially)
        let _ = memory.add_block(MemoryBlock::persona(""));
        let _ = memory.add_block(MemoryBlock::human(""));

        memory
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_core_memory_new() {
        let memory = CoreMemory::with_defaults();
        assert!(memory.is_empty());
        assert_eq!(memory.size_bytes(), 0);
        assert_eq!(memory.max_bytes(), CORE_MEMORY_SIZE_BYTES_MAX_DEFAULT);
    }

    #[test]
    fn test_add_block() {
        let mut memory = CoreMemory::with_defaults();
        let block = MemoryBlock::system("You are a helpful assistant.");

        let id = memory.add_block(block).unwrap();
        assert_eq!(memory.block_count(), 1);
        assert!(memory.size_bytes() > 0);

        let retrieved = memory.get_block(&id).unwrap();
        assert_eq!(retrieved.content, "You are a helpful assistant.");
    }

    #[test]
    fn test_add_multiple_blocks() {
        let mut memory = CoreMemory::with_defaults();

        memory
            .add_block(MemoryBlock::system("System prompt"))
            .unwrap();
        memory
            .add_block(MemoryBlock::persona("Friendly assistant"))
            .unwrap();
        memory
            .add_block(MemoryBlock::human("User is a developer"))
            .unwrap();

        assert_eq!(memory.block_count(), 3);
    }

    #[test]
    fn test_get_blocks_by_type() {
        let mut memory = CoreMemory::with_defaults();

        memory.add_block(MemoryBlock::facts("Fact 1")).unwrap();
        memory.add_block(MemoryBlock::facts("Fact 2")).unwrap();
        memory.add_block(MemoryBlock::persona("Persona")).unwrap();

        let facts = memory.get_blocks_by_type(MemoryBlockType::Facts);
        assert_eq!(facts.len(), 2);

        let personas = memory.get_blocks_by_type(MemoryBlockType::Persona);
        assert_eq!(personas.len(), 1);
    }

    #[test]
    fn test_update_block() {
        let mut memory = CoreMemory::with_defaults();
        let id = memory.add_block(MemoryBlock::scratch("Initial")).unwrap();

        memory.update_block(&id, "Updated content").unwrap();

        let block = memory.get_block(&id).unwrap();
        assert_eq!(block.content, "Updated content");
    }

    #[test]
    fn test_remove_block() {
        let mut memory = CoreMemory::with_defaults();
        let id = memory.add_block(MemoryBlock::scratch("To remove")).unwrap();

        assert_eq!(memory.block_count(), 1);

        let removed = memory.remove_block(&id).unwrap();
        assert_eq!(removed.content, "To remove");
        assert_eq!(memory.block_count(), 0);
        assert_eq!(memory.size_bytes(), 0);
    }

    #[test]
    fn test_capacity_limit() {
        // Use minimum allowed size
        let config = CoreMemoryConfig::with_max_bytes(CORE_MEMORY_SIZE_BYTES_MIN);
        let mut memory = CoreMemory::new(config);

        // Add block that fits (2KB)
        memory
            .add_block(MemoryBlock::scratch("x".repeat(2000)))
            .unwrap();

        // Try to add block that doesn't fit (3KB when only ~2KB remaining)
        let large_content = "x".repeat(3000);
        let result = memory.add_block(MemoryBlock::scratch(large_content));

        assert!(matches!(result, Err(MemoryError::CoreMemoryFull { .. })));
    }

    #[test]
    fn test_update_capacity_limit() {
        // Use minimum allowed size
        let config = CoreMemoryConfig::with_max_bytes(CORE_MEMORY_SIZE_BYTES_MIN);
        let mut memory = CoreMemory::new(config);

        let id = memory
            .add_block(MemoryBlock::scratch("Short content"))
            .unwrap();

        // Update with content that exceeds capacity (5KB > 4KB)
        let large_content = "x".repeat(5000);
        let result = memory.update_block(&id, large_content);

        assert!(matches!(result, Err(MemoryError::CoreMemoryFull { .. })));
    }

    #[test]
    fn test_clear() {
        let mut memory = CoreMemory::with_defaults();

        memory.add_block(MemoryBlock::system("System")).unwrap();
        memory.add_block(MemoryBlock::persona("Persona")).unwrap();

        assert_eq!(memory.block_count(), 2);

        memory.clear();

        assert!(memory.is_empty());
        assert_eq!(memory.size_bytes(), 0);
    }

    #[test]
    fn test_render() {
        let mut memory = CoreMemory::with_defaults();

        memory
            .add_block(MemoryBlock::system("You are helpful."))
            .unwrap();
        memory.add_block(MemoryBlock::persona("Friendly")).unwrap();

        let rendered = memory.render();

        assert!(rendered.contains("<core_memory>"));
        assert!(rendered.contains("</core_memory>"));
        assert!(rendered.contains("<block label=\"system\">"));
        assert!(rendered.contains("You are helpful."));
        assert!(rendered.contains("<block label=\"persona\">"));
        assert!(rendered.contains("Friendly"));
    }

    #[test]
    fn test_utilization() {
        // Use minimum allowed size (4KB)
        let config = CoreMemoryConfig::with_max_bytes(CORE_MEMORY_SIZE_BYTES_MIN);
        let mut memory = CoreMemory::new(config);

        assert_eq!(memory.utilization(), 0.0);

        // Add 2KB (50% of 4KB)
        memory
            .add_block(MemoryBlock::scratch("x".repeat(2048)))
            .unwrap();

        assert!((memory.utilization() - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_letta_default() {
        let memory = CoreMemory::letta_default();

        // Should have persona and human blocks
        assert!(memory.get_first_by_type(MemoryBlockType::Persona).is_some());
        assert!(memory.get_first_by_type(MemoryBlockType::Human).is_some());
    }

    #[test]
    fn test_blocks_iteration_order() {
        let mut memory = CoreMemory::with_defaults();

        memory
            .add_block(MemoryBlock::with_label(
                MemoryBlockType::Custom,
                "first",
                "1",
            ))
            .unwrap();
        memory
            .add_block(MemoryBlock::with_label(
                MemoryBlockType::Custom,
                "second",
                "2",
            ))
            .unwrap();
        memory
            .add_block(MemoryBlock::with_label(
                MemoryBlockType::Custom,
                "third",
                "3",
            ))
            .unwrap();

        let labels: Vec<_> = memory.blocks().map(|b| b.label.as_str()).collect();
        assert_eq!(labels, vec!["first", "second", "third"]);
    }
}

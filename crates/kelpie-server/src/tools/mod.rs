//! Unified Tool Registry for Kelpie Server
//!
//! TigerStyle: Unified interface for built-in and MCP tools with fault injection support.
//!
//! This module provides a unified registry that combines:
//! - Built-in Rust tools (shell, memory operations)
//! - MCP tools from connected external servers
//! - DST-compatible simulated tools for testing

mod memory;
mod registry;

pub use memory::register_memory_tools;
pub use registry::{
    BuiltinToolHandler, RegisteredTool, RegistryStats, ToolExecutionResult, ToolSource,
    UnifiedToolRegistry,
};

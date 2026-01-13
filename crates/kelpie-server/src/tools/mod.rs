//! Unified Tool Registry for Kelpie Server
//!
//! TigerStyle: Unified interface for built-in and MCP tools with fault injection support.
//!
//! This module provides a unified registry that combines:
//! - Built-in Rust tools (shell, memory operations, heartbeat control)
//! - MCP tools from connected external servers
//! - DST-compatible simulated tools for testing

mod heartbeat;
mod memory;
mod registry;

pub use heartbeat::{
    parse_pause_signal, register_heartbeat_tools, register_pause_heartbeats_with_clock,
    ClockSource,
};
pub use memory::register_memory_tools;
pub use registry::{
    BuiltinToolHandler, RegisteredTool, RegistryStats, ToolExecutionResult, ToolSignal,
    ToolSource, UnifiedToolRegistry, AGENT_LOOP_ITERATIONS_MAX, HEARTBEAT_PAUSE_MINUTES_DEFAULT,
    HEARTBEAT_PAUSE_MINUTES_MAX, HEARTBEAT_PAUSE_MINUTES_MIN, MS_PER_MINUTE,
};

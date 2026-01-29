//! Unified Tool Registry for Kelpie Server
//!
//! TigerStyle: Unified interface for built-in and MCP tools with fault injection support.
//!
//! This module provides a unified registry that combines:
//! - Built-in Rust tools (shell, memory operations, heartbeat control, messaging)
//! - Agent-to-agent communication tools (Issue #75)
//! - MCP tools from connected external servers
//! - DST-compatible simulated tools for testing

mod agent_call;
mod code_execution;
mod executor;
mod heartbeat;
mod memory;
mod messaging;
mod registry;
mod web_search;

pub use agent_call::{
    create_nested_context, register_call_agent_tool, validate_call_context, AGENT_CALL_DEPTH_MAX,
    AGENT_CALL_MESSAGE_SIZE_BYTES_MAX, AGENT_CALL_RESPONSE_SIZE_BYTES_MAX,
    AGENT_CALL_TIMEOUT_MS_DEFAULT, AGENT_CALL_TIMEOUT_MS_MAX, AGENT_CONCURRENT_CALLS_MAX,
};
pub use code_execution::register_run_code_tool;
pub use heartbeat::{
    parse_pause_signal, register_heartbeat_tools, register_pause_heartbeats_with_clock, ClockSource,
};
pub use memory::register_memory_tools;
pub use messaging::register_messaging_tools;
pub use registry::{
    AgentDispatcher, BuiltinToolHandler, ContextAwareToolHandler, CustomToolDefinition,
    RegisteredTool, RegistryStats, ToolExecutionContext, ToolExecutionResult, ToolSignal,
    ToolSource, UnifiedToolRegistry, AGENT_LOOP_ITERATIONS_MAX, HEARTBEAT_PAUSE_MINUTES_DEFAULT,
    HEARTBEAT_PAUSE_MINUTES_MAX, HEARTBEAT_PAUSE_MINUTES_MIN, MS_PER_MINUTE,
};
pub use web_search::register_web_search_tool;

pub use executor::{
    create_sandbox_pool, ExecutionResult, ExecutorStats, ExtendedToolDefinition, ToolExecutor,
    ToolLanguage, EXECUTOR_CONCURRENT_EXECUTIONS_MAX, EXECUTOR_OUTPUT_BYTES_MAX,
    EXECUTOR_SOURCE_CODE_BYTES_MAX, EXECUTOR_TIMEOUT_MS_DEFAULT, EXECUTOR_TIMEOUT_MS_MAX,
};

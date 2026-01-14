//! Storage Layer for Agent Persistence
//!
//! TigerStyle: Trait-based abstraction for DST compatibility.
//!
//! This module provides the `AgentStorage` trait that abstracts over:
//! - SimStorage (in-memory, fault-injectable for DST)
//! - FdbStorage (FoundationDB for production)
//!
//! # Key Design Decisions
//!
//! 1. **Iteration-level checkpointing** - Session state saved after each loop iteration
//! 2. **Separate concerns** - Agent metadata vs session state vs messages
//! 3. **DST-first** - All operations can have faults injected

mod traits;
mod types;

#[cfg(feature = "dst")]
mod sim;

pub use traits::{AgentStorage, StorageError};
pub use types::{AgentMetadata, PendingToolCall, SessionState};

#[cfg(feature = "dst")]
pub use sim::SimStorage;

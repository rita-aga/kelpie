//! Storage Layer for Agent Persistence
//!
//! TigerStyle: Trait-based abstraction for DST compatibility.
//!
//! This module provides the `AgentStorage` trait that abstracts over:
//! - SimStorage (in-memory, fault-injectable for DST)
//! - FdbAgentRegistry (FoundationDB via FdbKV for production)
//!
//! # Unified Architecture
//!
//! Both implementations use the same underlying abstraction:
//! - Registry: Global agent metadata (special actor "system/agent_registry")
//! - Per-agent: Blocks/sessions/messages (regular actors "agents/{id}")
//!
//! # Key Design Decisions
//!
//! 1. **Iteration-level checkpointing** - Session state saved after each loop iteration
//! 2. **Separate concerns** - Agent metadata vs session state vs messages
//! 3. **DST-first** - All operations can have faults injected

mod teleport;
mod traits;
mod types;

#[cfg(feature = "fdb")]
mod fdb;

#[cfg(feature = "dst")]
mod sim;

#[cfg(feature = "fdb")]
pub use fdb::FdbAgentRegistry;
pub use kelpie_core::teleport::{
    Architecture, SnapshotKind, TeleportPackage, TeleportStorage, TeleportStorageError,
    TeleportStorageResult, TELEPORT_ID_LENGTH_BYTES_MAX,
};
pub use teleport::{LocalTeleportStorage, TELEPORT_PACKAGE_SIZE_BYTES_DEFAULT_MAX};
pub use traits::{AgentStorage, StorageError};
pub use types::{AgentMetadata, CustomToolRecord, PendingToolCall, SessionState};

#[cfg(feature = "dst")]
pub use sim::SimStorage;

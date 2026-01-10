//! Kelpie Storage
//!
//! Per-actor KV storage for Kelpie virtual actors.
//!
//! # Overview
//!
//! Provides durable, transactional key-value storage for each actor.
//! Supports multiple backends:
//! - In-memory (for testing and DST)
//! - FoundationDB (for production)

pub mod kv;
pub mod memory;
pub mod transaction;

pub use kv::{ActorKV, KVOperation, ScopedKV};
pub use memory::MemoryKV;
pub use transaction::Transaction;

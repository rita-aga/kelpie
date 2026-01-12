//! Kelpie Storage
//!
//! Per-actor KV storage for Kelpie virtual actors.
//!
//! # Overview
//!
//! Provides durable, transactional key-value storage for each actor.
//! Supports multiple backends:
//! - In-memory (for testing and DST)
//! - FoundationDB (for production, requires `fdb` feature)
//!
//! # Features
//!
//! - `fdb` - Enable FoundationDB backend (requires FDB C client installed)

pub mod kv;
pub mod memory;
pub mod transaction;

#[cfg(feature = "fdb")]
pub mod fdb;

pub use kv::{ActorKV, ActorTransaction, KVOperation, ScopedKV};
pub use memory::MemoryKV;
pub use transaction::Transaction;

#[cfg(feature = "fdb")]
pub use fdb::{FdbActorTransaction, FdbKV};

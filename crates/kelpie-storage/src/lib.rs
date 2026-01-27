//! Kelpie Storage
//!
//! Per-actor KV storage for Kelpie virtual actors.
//!
//! # Overview
//!
//! Provides durable, transactional key-value storage for each actor.
//! Supports multiple backends:
//! - In-memory (for testing and DST)
//! - FoundationDB (production backend, requires `fdb` feature)
//!
//! # Features
//!
//! - `fdb` - FoundationDB backend (optional, requires FDB C client installed)

#[cfg(feature = "fdb")]
pub mod fdb;
pub mod kv;
pub mod memory;
pub mod transaction;

#[cfg(feature = "fdb")]
pub use fdb::{FdbActorTransaction, FdbKV};
pub use kv::{ActorKV, ActorTransaction, KVOperation, ScopedKV};
pub use memory::MemoryKV;
pub use transaction::Transaction;

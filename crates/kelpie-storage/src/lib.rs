//! Kelpie Storage
//!
//! Per-actor KV storage for Kelpie virtual actors.
//!
//! # Overview
//!
//! Provides durable, transactional key-value storage for each actor.
//! Supports multiple backends:
//! - In-memory (for testing and DST)
//! - FoundationDB (production backend, enabled by default)
//!
//! # Features
//!
//! - `fdb` - FoundationDB backend (default, requires FDB C client installed)
//!
//! # DST Support
//!
//! All components support TimeProvider injection for deterministic simulation testing.
//! Use `with_time_provider()` constructors for DST, or default constructors for production.

pub mod fdb;
pub mod kv;
pub mod memory;
pub mod transaction;
pub mod wal;

pub use fdb::{FdbActorTransaction, FdbKV};
pub use kv::{ActorKV, ActorTransaction, KVOperation, ScopedKV};
pub use memory::MemoryKV;
pub use transaction::Transaction;
pub use wal::{KvWal, MemoryWal, WalEntry, WalEntryId, WalOperation, WalStatus, WriteAheadLog};

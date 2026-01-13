//! Memory Backend - Umi Integration
//!
//! TigerStyle: DST-first, agent-scoped memory operations.
//!
//! This module provides the `UmiMemoryBackend` which wraps Umi's Memory
//! to provide agent-scoped memory operations for Kelpie agents.

mod umi_backend;

pub use umi_backend::UmiMemoryBackend;

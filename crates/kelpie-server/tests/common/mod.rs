//! Common test utilities for kelpie-server DST tests.
//!
//! This module provides:
//! - TLA+ invariant verification helpers (`invariants`)
//! - TLA+ bug pattern test scenarios (`tla_scenarios`)
//! - Assertion utilities with detailed failure messages
//!
//! # Usage
//!
//! ```rust,ignore
//! mod common;
//! use common::invariants::*;
//! use common::tla_scenarios::*;
//!
//! #[tokio::test]
//! async fn test_single_activation() {
//!     // ... setup ...
//!     verify_single_activation(&registry).await.expect("SingleActivation violated!");
//! }
//!
//! #[tokio::test]
//! async fn test_toctou_race() {
//!     let (violations, desc) = scenario_toctou_race_dual_activation().await;
//!     assert!(!violations.is_empty(), "Expected TOCTOU violation");
//! }
//! ```

pub mod invariants;
pub mod tla_scenarios;

// Re-export commonly used items
pub use invariants::InvariantViolation;

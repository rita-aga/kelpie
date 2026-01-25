//! Optimistic Concurrency Control primitives for TLA+ specification compliance
//!
//! TigerStyle: Explicit OCC types matching TLA+ KelpieSingleActivation spec.
//!
//! This module provides the foundational primitives for ensuring single activation
//! guarantee as specified in `docs/tla/KelpieSingleActivation.tla`:
//!
//! # Key Invariants (from TLA+ spec)
//! - `SingleActivation`: At most one node is active for any actor at any time
//! - `ConsistentHolder`: FDB holder matches node state beliefs
//!
//! # FDB Transaction Semantics Modeled
//! 1. Read phase: snapshot read captures current version
//! 2. Write phase: prepare mutation (not yet visible)
//! 3. Commit phase: atomic commit iff version unchanged, else abort
//!
//! # Related Specifications
//! - `docs/tla/KelpieSingleActivation.tla` - Single activation protocol
//! - `docs/tla/KelpieLease.tla` - Lease-based ownership with fencing tokens
//! - `docs/adr/004-linearizability-guarantees.md` - CP semantics

use serde::{Deserialize, Serialize};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

// =============================================================================
// Version for OCC (matches TLA+ fdb_version)
// =============================================================================

/// Version number for optimistic concurrency control
///
/// Corresponds to `fdb_version` in TLA+ KelpieSingleActivation spec.
/// Monotonically increasing on each write to a key.
///
/// # TigerStyle
/// - Explicit type (not raw u64) for type safety
/// - `VERSION_INITIAL = 0` matches TLA+ `fdb_version = 0` in Init
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize,
)]
pub struct Version(u64);

impl Version {
    /// Initial version for new keys (matches TLA+ Init: fdb_version = 0)
    pub const INITIAL: Self = Version(0);

    /// Create a new version
    pub const fn new(v: u64) -> Self {
        Version(v)
    }

    /// Get the raw version number
    pub const fn value(&self) -> u64 {
        self.0
    }

    /// Increment version for a write operation
    ///
    /// Corresponds to TLA+: `fdb_version' = fdb_version + 1`
    pub fn increment(&self) -> Self {
        Version(self.0.saturating_add(1))
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl From<u64> for Version {
    fn from(v: u64) -> Self {
        Version(v)
    }
}

// =============================================================================
// Fencing Token (matches TLA+ fencingTokens)
// =============================================================================

/// Fencing token for preventing stale writes
///
/// From TLA+ KelpieLease spec:
/// - `FencingTokenMonotonic`: Fencing tokens never decrease
/// - Incremented on each lease acquisition (not renewal)
/// - Used to reject stale operations from old lease holders
///
/// # TigerStyle
/// - Monotonically increasing (cannot decrement)
/// - Explicit type for compile-time safety
/// - Thread-safe atomic operations
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize,
)]
pub struct FencingToken(u64);

impl FencingToken {
    /// Initial fencing token (matches TLA+ Init: fencingTokens = [a \in Actors |-> 0])
    pub const INITIAL: Self = FencingToken(0);

    /// Create a new fencing token
    pub const fn new(token: u64) -> Self {
        FencingToken(token)
    }

    /// Get the raw token value
    pub const fn value(&self) -> u64 {
        self.0
    }

    /// Generate next token (for lease acquisition)
    ///
    /// Corresponds to TLA+: `newToken == fencingTokens[actor] + 1`
    pub fn next(&self) -> Self {
        FencingToken(self.0.saturating_add(1))
    }

    /// Check if this token is stale (older than the current token)
    pub fn is_stale(&self, current: &FencingToken) -> bool {
        self.0 < current.0
    }

    /// Validate this token matches the expected value
    pub fn validate(&self, expected: &FencingToken) -> Result<(), FencingError> {
        if self == expected {
            Ok(())
        } else if self.is_stale(expected) {
            Err(FencingError::StaleToken {
                provided: *self,
                current: *expected,
            })
        } else {
            Err(FencingError::FutureToken {
                provided: *self,
                current: *expected,
            })
        }
    }
}

impl fmt::Display for FencingToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ft:{}", self.0)
    }
}

impl From<u64> for FencingToken {
    fn from(token: u64) -> Self {
        FencingToken(token)
    }
}

/// Atomic fencing token for concurrent access
#[derive(Debug, Default)]
pub struct AtomicFencingToken(AtomicU64);

impl AtomicFencingToken {
    /// Create a new atomic fencing token with initial value
    pub const fn new(token: FencingToken) -> Self {
        AtomicFencingToken(AtomicU64::new(token.0))
    }

    /// Load the current token value
    pub fn load(&self) -> FencingToken {
        FencingToken(self.0.load(Ordering::SeqCst))
    }

    /// Store a new token value
    pub fn store(&self, token: FencingToken) {
        self.0.store(token.0, Ordering::SeqCst);
    }

    /// Atomically increment and return the new token
    pub fn fetch_increment(&self) -> FencingToken {
        let old = self.0.fetch_add(1, Ordering::SeqCst);
        FencingToken(old.saturating_add(1))
    }

    /// Compare and swap: only update if current value matches expected
    pub fn compare_exchange(
        &self,
        expected: FencingToken,
        new: FencingToken,
    ) -> Result<FencingToken, FencingToken> {
        self.0
            .compare_exchange(expected.0, new.0, Ordering::SeqCst, Ordering::SeqCst)
            .map(FencingToken)
            .map_err(FencingToken)
    }
}

// =============================================================================
// OCC Errors (matches TLA+ conflict states)
// =============================================================================

/// Error from fencing token validation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FencingError {
    /// Token is from an old lease holder
    StaleToken {
        provided: FencingToken,
        current: FencingToken,
    },
    /// Token is newer than expected (should not happen normally)
    FutureToken {
        provided: FencingToken,
        current: FencingToken,
    },
}

impl fmt::Display for FencingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FencingError::StaleToken { provided, current } => {
                write!(
                    f,
                    "stale fencing token: provided {}, current {}",
                    provided, current
                )
            }
            FencingError::FutureToken { provided, current } => {
                write!(
                    f,
                    "future fencing token: provided {}, current {}",
                    provided, current
                )
            }
        }
    }
}

impl std::error::Error for FencingError {}

/// Result of an OCC write attempt
///
/// Models the commit outcome in TLA+ CommitClaim action:
/// - Success: version unchanged AND preconditions met
/// - Conflict: version changed (someone wrote since our read)
/// - Precondition failed: other preconditions not met
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OccResult<T> {
    /// Write succeeded
    Success(T),
    /// Version conflict - another writer committed between read and write
    VersionConflict {
        read_version: Version,
        current_version: Version,
    },
    /// Precondition not met (e.g., actor already has holder)
    PreconditionFailed { reason: String },
}

impl<T> OccResult<T> {
    /// Check if the result is a success
    pub fn is_success(&self) -> bool {
        matches!(self, OccResult::Success(_))
    }

    /// Check if the result is a conflict
    pub fn is_conflict(&self) -> bool {
        matches!(self, OccResult::VersionConflict { .. })
    }

    /// Convert to Option, returning Some on success
    pub fn ok(self) -> Option<T> {
        match self {
            OccResult::Success(v) => Some(v),
            _ => None,
        }
    }
}

// =============================================================================
// Versioned Value (for OCC storage)
// =============================================================================

/// A value with its version for OCC
///
/// Used to track the version at read time for conflict detection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Versioned<T> {
    /// The value
    pub value: T,
    /// The version when this value was read
    pub version: Version,
}

impl<T> Versioned<T> {
    /// Create a new versioned value
    pub fn new(value: T, version: Version) -> Self {
        Versioned { value, version }
    }

    /// Create a versioned value with initial version
    pub fn initial(value: T) -> Self {
        Versioned {
            value,
            version: Version::INITIAL,
        }
    }

    /// Map the inner value
    pub fn map<U, F>(self, f: F) -> Versioned<U>
    where
        F: FnOnce(T) -> U,
    {
        Versioned {
            value: f(self.value),
            version: self.version,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_initial() {
        assert_eq!(Version::INITIAL.value(), 0);
    }

    #[test]
    fn test_version_increment() {
        let v0 = Version::INITIAL;
        let v1 = v0.increment();
        let v2 = v1.increment();

        assert_eq!(v0.value(), 0);
        assert_eq!(v1.value(), 1);
        assert_eq!(v2.value(), 2);
    }

    #[test]
    fn test_version_ordering() {
        let v0 = Version::new(0);
        let v1 = Version::new(1);
        let v2 = Version::new(2);

        assert!(v0 < v1);
        assert!(v1 < v2);
        assert!(v0 < v2);
    }

    #[test]
    fn test_fencing_token_initial() {
        assert_eq!(FencingToken::INITIAL.value(), 0);
    }

    #[test]
    fn test_fencing_token_next() {
        let t0 = FencingToken::INITIAL;
        let t1 = t0.next();
        let t2 = t1.next();

        assert_eq!(t0.value(), 0);
        assert_eq!(t1.value(), 1);
        assert_eq!(t2.value(), 2);
    }

    #[test]
    fn test_fencing_token_stale() {
        let old = FencingToken::new(1);
        let current = FencingToken::new(3);

        assert!(old.is_stale(&current));
        assert!(!current.is_stale(&old));
        assert!(!current.is_stale(&current));
    }

    #[test]
    fn test_fencing_token_validate() {
        let token = FencingToken::new(5);
        let current = FencingToken::new(5);

        assert!(token.validate(&current).is_ok());
    }

    #[test]
    fn test_fencing_token_validate_stale() {
        let old_token = FencingToken::new(3);
        let current = FencingToken::new(5);

        let result = old_token.validate(&current);
        assert!(matches!(result, Err(FencingError::StaleToken { .. })));
    }

    #[test]
    fn test_atomic_fencing_token() {
        let atomic = AtomicFencingToken::new(FencingToken::INITIAL);

        assert_eq!(atomic.load(), FencingToken::INITIAL);

        let new_token = atomic.fetch_increment();
        assert_eq!(new_token, FencingToken::new(1));
        assert_eq!(atomic.load(), FencingToken::new(1));
    }

    #[test]
    fn test_atomic_fencing_token_cas() {
        let atomic = AtomicFencingToken::new(FencingToken::new(5));

        // Successful CAS
        let result = atomic.compare_exchange(FencingToken::new(5), FencingToken::new(6));
        assert!(result.is_ok());
        assert_eq!(atomic.load(), FencingToken::new(6));

        // Failed CAS (wrong expected value)
        let result = atomic.compare_exchange(FencingToken::new(5), FencingToken::new(7));
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), FencingToken::new(6)); // Returns actual value
    }

    #[test]
    fn test_occ_result() {
        let success: OccResult<i32> = OccResult::Success(42);
        assert!(success.is_success());
        assert!(!success.is_conflict());
        assert_eq!(success.ok(), Some(42));

        let conflict: OccResult<i32> = OccResult::VersionConflict {
            read_version: Version::new(1),
            current_version: Version::new(2),
        };
        assert!(!conflict.is_success());
        assert!(conflict.is_conflict());
        assert_eq!(conflict.ok(), None);
    }

    #[test]
    fn test_versioned() {
        let v = Versioned::new("hello", Version::new(5));
        assert_eq!(v.value, "hello");
        assert_eq!(v.version, Version::new(5));

        let mapped = v.map(|s| s.len());
        assert_eq!(mapped.value, 5);
        assert_eq!(mapped.version, Version::new(5));
    }
}

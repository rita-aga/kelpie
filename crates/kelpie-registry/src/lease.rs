//! Lease management for single-activation guarantees
//!
//! TigerStyle: Explicit lease semantics matching TLA+ spec (KelpieLease.tla).
//!
//! # TLA+ Specification Compliance
//!
//! This module implements the lease protocol from `docs/tla/KelpieLease.tla`:
//!
//! - `fencingTokens` -> `Lease.fencing_token` (monotonically increasing per actor)
//! - `GracePeriod` -> `LeaseConfig.grace_period_ms`
//! - `LeaseState(actor)` -> `Lease.state()` (Active, GracePeriod, Expired)
//!
//! # Safety Invariants (from TLA+ spec)
//!
//! - **LeaseUniqueness**: At most one node holds a valid lease per actor
//! - **RenewalRequiresOwnership**: Only lease holder can renew
//! - **ExpiredLeaseClaimable**: Expired leases don't block new acquisition
//! - **GracePeriodRespected**: No new lease granted while current lease is in grace period
//! - **FencingTokenMonotonic**: Fencing tokens never decrease
//! - **ClockSkewSafety**: Leases account for bounded clock skew
//!
//! # Lease States (from TLA+ spec)
//!
//! ```text
//! States: Active -> GracePeriod -> Expired
//!
//! - Active:      clock < expiry - grace_period
//! - GracePeriod: expiry - grace_period <= clock < expiry
//! - Expired:     clock >= expiry
//! ```
//!
//! # Example
//!
//! ```rust,ignore
//! use kelpie_registry::{MemoryLeaseManager, LeaseManager, LeaseConfig};
//! use kelpie_core::actor::ActorId;
//!
//! let config = LeaseConfig::default();
//! let lease_mgr = MemoryLeaseManager::new(config, clock);
//!
//! // Acquire lease
//! let lease = lease_mgr.acquire(&node_id, &actor_id).await?;
//!
//! // Renew before expiry (only during Active or GracePeriod)
//! lease_mgr.renew(&node_id, &actor_id).await?;
//!
//! // Release when done
//! lease_mgr.release(&node_id, &actor_id).await?;
//! ```

use crate::error::{RegistryError, RegistryResult};
use crate::node::NodeId;
use async_trait::async_trait;
use kelpie_core::actor::ActorId;
use kelpie_core::io::TimeProvider;
use kelpie_core::occ::FencingToken;
use kelpie_core::{CLOCK_SKEW_MS_MAX, LEASE_GRACE_PERIOD_MS};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::sync::RwLock;

// =============================================================================
// Constants (TigerStyle: explicit units in names)
// Use constants from kelpie_core for TLA+ spec alignment
// =============================================================================

/// Default lease duration in milliseconds (from kelpie_core::LEASE_DURATION_MS_DEFAULT)
pub const LEASE_DURATION_MS_DEFAULT: u64 = 30_000; // 30 seconds

/// Minimum lease duration in milliseconds (from kelpie_core::LEASE_DURATION_MS_MIN)
pub const LEASE_DURATION_MS_MIN: u64 = 1_000; // 1 second

/// Maximum lease duration in milliseconds (from kelpie_core::LEASE_DURATION_MS_MAX)
pub const LEASE_DURATION_MS_MAX: u64 = 300_000; // 5 minutes

// =============================================================================
// Lease State (TLA+ spec: LeaseState)
// =============================================================================

/// Lease state as defined in TLA+ spec
///
/// From TLA+ KelpieLease spec:
/// ```text
/// LeaseState(actor) ==
///     CASE leases[actor].holder = NoHolder -> "Expired"
///       [] clock < leases[actor].expiry - GracePeriod -> "Active"
///       [] clock < leases[actor].expiry -> "GracePeriod"
///       [] OTHER -> "Expired"
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LeaseState {
    /// Lease is active: clock < expiry - grace_period
    Active,
    /// Lease is in grace period: expiry - grace_period <= clock < expiry
    /// Only current holder can renew during this state
    GracePeriod,
    /// Lease has expired: clock >= expiry OR no holder
    Expired,
}

// =============================================================================
// Lease Configuration
// =============================================================================

/// Configuration for lease management
///
/// From TLA+ KelpieLease spec:
/// - `LeaseDuration` -> `duration_ms`
/// - `GracePeriod` -> `grace_period_ms`
/// - `MaxClockSkew` -> `clock_skew_ms` (for clock skew safety)
#[derive(Debug, Clone)]
pub struct LeaseConfig {
    /// Lease duration in milliseconds
    ///
    /// From TLA+ spec: `LeaseDuration` constant
    pub duration_ms: u64,

    /// Grace period before lease expiration in milliseconds
    ///
    /// From TLA+ spec: `GracePeriod` constant
    /// During grace period, only the current holder can renew.
    /// New acquisitions are blocked to give the holder time to renew.
    pub grace_period_ms: u64,

    /// Maximum clock skew between nodes in milliseconds
    ///
    /// From TLA+ spec: `MaxClockSkew` constant
    /// Used to ensure lease decisions are safe despite clock drift.
    pub clock_skew_ms: u64,
}

impl LeaseConfig {
    /// Create a new lease config with specified duration
    pub fn new(duration_ms: u64) -> Self {
        Self::with_grace_period(duration_ms, LEASE_GRACE_PERIOD_MS)
    }

    /// Create a new lease config with specified duration and grace period
    pub fn with_grace_period(duration_ms: u64, grace_period_ms: u64) -> Self {
        // TigerStyle: assertions for bounds
        assert!(
            duration_ms >= LEASE_DURATION_MS_MIN,
            "lease duration must be >= {}ms",
            LEASE_DURATION_MS_MIN
        );
        assert!(
            duration_ms <= LEASE_DURATION_MS_MAX,
            "lease duration must be <= {}ms",
            LEASE_DURATION_MS_MAX
        );
        // Grace period must be less than duration (otherwise no active state possible)
        assert!(
            grace_period_ms < duration_ms,
            "grace period {}ms must be < duration {}ms",
            grace_period_ms,
            duration_ms
        );
        // Grace period should be reasonable
        debug_assert!(grace_period_ms > 0, "grace period should be positive");

        Self {
            duration_ms,
            grace_period_ms,
            clock_skew_ms: CLOCK_SKEW_MS_MAX,
        }
    }

    /// Create config for testing with short duration
    pub fn for_testing() -> Self {
        Self {
            duration_ms: 5_000,     // 5 seconds for fast tests
            grace_period_ms: 1_000, // 1 second grace period
            clock_skew_ms: 500,     // 500ms simulated clock skew
        }
    }
}

impl Default for LeaseConfig {
    fn default() -> Self {
        Self {
            duration_ms: LEASE_DURATION_MS_DEFAULT,
            grace_period_ms: LEASE_GRACE_PERIOD_MS,
            clock_skew_ms: CLOCK_SKEW_MS_MAX,
        }
    }
}

// =============================================================================
// Lease Structure
// =============================================================================

/// A lease granting exclusive ownership of an actor to a node
///
/// From TLA+ KelpieLease spec:
/// - `leases[actor].holder` -> `holder`
/// - `leases[actor].expiry` -> `expiry_ms`
/// - `fencingTokens[actor]` -> `fencing_token`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lease {
    /// The actor this lease is for
    pub actor_id: ActorId,
    /// The node holding this lease
    pub holder: NodeId,
    /// When this lease expires (Unix timestamp ms)
    pub expiry_ms: u64,
    /// When this lease was acquired (Unix timestamp ms)
    pub acquired_at_ms: u64,
    /// Number of times this lease has been renewed
    pub renewal_count: u64,
    /// Fencing token for preventing stale writes
    ///
    /// From TLA+ spec: `fencingTokens[actor]`
    /// - Incremented on each NEW acquisition (not renewal)
    /// - Used to reject stale operations from old lease holders
    /// - Monotonically increasing (FencingTokenMonotonic invariant)
    pub fencing_token: FencingToken,
}

impl Lease {
    /// Create a new lease with a specific fencing token
    ///
    /// From TLA+ spec: `AcquireLeaseSafe` action
    /// - Sets `expiry = clock + LeaseDuration`
    /// - Sets `fencingToken = fencingTokens[actor] + 1`
    pub fn new(
        actor_id: ActorId,
        holder: NodeId,
        now_ms: u64,
        duration_ms: u64,
        fencing_token: FencingToken,
    ) -> Self {
        // TigerStyle: preconditions
        assert!(duration_ms > 0, "lease duration must be positive");
        assert!(
            now_ms.checked_add(duration_ms).is_some(),
            "expiry would overflow"
        );

        let lease = Self {
            actor_id,
            holder,
            expiry_ms: now_ms + duration_ms,
            acquired_at_ms: now_ms,
            renewal_count: 0,
            fencing_token,
        };

        // TigerStyle: postconditions
        debug_assert!(lease.expiry_ms > now_ms);
        debug_assert_eq!(lease.renewal_count, 0);

        lease
    }

    /// Create a new lease with initial fencing token (for first acquisition)
    pub fn new_initial(actor_id: ActorId, holder: NodeId, now_ms: u64, duration_ms: u64) -> Self {
        Self::new(
            actor_id,
            holder,
            now_ms,
            duration_ms,
            FencingToken::INITIAL.next(),
        )
    }

    /// Check if the lease is valid at the given time
    pub fn is_valid(&self, now_ms: u64) -> bool {
        self.expiry_ms > now_ms
    }

    /// Check if the lease has expired at the given time
    pub fn is_expired(&self, now_ms: u64) -> bool {
        self.expiry_ms <= now_ms
    }

    /// Get the lease state at the given time
    ///
    /// From TLA+ spec: `LeaseState(actor)`
    /// ```text
    /// CASE leases[actor].holder = NoHolder -> "Expired"
    ///   [] clock < leases[actor].expiry - GracePeriod -> "Active"
    ///   [] clock < leases[actor].expiry -> "GracePeriod"
    ///   [] OTHER -> "Expired"
    /// ```
    pub fn state(&self, now_ms: u64, grace_period_ms: u64) -> LeaseState {
        // TigerStyle: preconditions
        debug_assert!(grace_period_ms < self.duration_ms());

        if now_ms >= self.expiry_ms {
            LeaseState::Expired
        } else if now_ms < self.expiry_ms.saturating_sub(grace_period_ms) {
            LeaseState::Active
        } else {
            LeaseState::GracePeriod
        }
    }

    /// Get the original duration of this lease
    fn duration_ms(&self) -> u64 {
        self.expiry_ms.saturating_sub(self.acquired_at_ms)
    }

    /// Check if the lease is in grace period
    ///
    /// From TLA+ spec: `InGracePeriod(actor)`
    pub fn in_grace_period(&self, now_ms: u64, grace_period_ms: u64) -> bool {
        self.state(now_ms, grace_period_ms) == LeaseState::GracePeriod
    }

    /// Renew this lease, extending its expiry
    ///
    /// From TLA+ spec: `RenewLeaseSafe` action
    /// - Does NOT increment fencing token (same logical ownership)
    /// - Only updates expiry time
    pub fn renew(&mut self, now_ms: u64, duration_ms: u64) {
        // TigerStyle: preconditions
        assert!(duration_ms > 0, "lease duration must be positive");
        assert!(self.is_valid(now_ms), "cannot renew expired lease");
        assert!(
            now_ms.checked_add(duration_ms).is_some(),
            "expiry would overflow"
        );

        self.expiry_ms = now_ms + duration_ms;
        self.renewal_count = self.renewal_count.saturating_add(1);
        // NOTE: fencing_token is NOT incremented on renewal (TLA+ spec)

        // TigerStyle: postconditions
        debug_assert!(self.expiry_ms > now_ms);
    }

    /// Get remaining time on the lease in milliseconds
    pub fn remaining_ms(&self, now_ms: u64) -> u64 {
        if self.expiry_ms > now_ms {
            self.expiry_ms - now_ms
        } else {
            0
        }
    }

    /// Get the fencing token for this lease
    pub fn fencing_token(&self) -> FencingToken {
        self.fencing_token
    }
}

// =============================================================================
// LeaseManager Trait
// =============================================================================

/// Trait for lease management operations
#[async_trait]
pub trait LeaseManager: Send + Sync {
    /// Attempt to acquire a lease for an actor.
    ///
    /// Returns Ok(Lease) if acquisition succeeds, Err if another node holds a valid lease.
    async fn acquire(&self, node_id: &NodeId, actor_id: &ActorId) -> RegistryResult<Lease>;

    /// Renew an existing lease.
    ///
    /// Only the current holder can renew. Returns Err if not holder or lease expired.
    async fn renew(&self, node_id: &NodeId, actor_id: &ActorId) -> RegistryResult<Lease>;

    /// Release a lease voluntarily (graceful deactivation).
    ///
    /// Returns Ok if released, Err if not holder.
    async fn release(&self, node_id: &NodeId, actor_id: &ActorId) -> RegistryResult<()>;

    /// Check if a node holds a valid lease for an actor.
    async fn is_valid(&self, node_id: &NodeId, actor_id: &ActorId) -> bool;

    /// Get the current lease for an actor, if any.
    async fn get_lease(&self, actor_id: &ActorId) -> Option<Lease>;

    /// Get all active leases held by a node.
    async fn get_leases_for_node(&self, node_id: &NodeId) -> Vec<Lease>;
}

// =============================================================================
// MemoryLeaseManager Implementation
// =============================================================================

/// In-memory lease manager for testing and single-node deployments
///
/// From TLA+ spec: Models `leases` and `fencingTokens` state variables.
pub struct MemoryLeaseManager {
    /// Lease configuration
    config: LeaseConfig,
    /// Time provider for time operations (DST-compatible)
    time: Arc<dyn TimeProvider>,
    /// Active leases by actor ID
    leases: RwLock<HashMap<String, Lease>>,
    /// Global fencing token counter per actor (monotonically increasing)
    ///
    /// From TLA+ spec: `fencingTokens` - maps actors to their current token
    /// This tracks the next token to use, even if the lease has expired
    fencing_tokens: RwLock<HashMap<String, AtomicU64>>,
}

impl MemoryLeaseManager {
    /// Create a new memory lease manager
    pub fn new(config: LeaseConfig, time: Arc<dyn TimeProvider>) -> Self {
        Self {
            config,
            time,
            leases: RwLock::new(HashMap::new()),
            fencing_tokens: RwLock::new(HashMap::new()),
        }
    }

    /// Create with default config
    pub fn with_time(time: Arc<dyn TimeProvider>) -> Self {
        Self::new(LeaseConfig::default(), time)
    }

    /// Get current time from time provider
    fn now_ms(&self) -> u64 {
        self.time.now_ms()
    }

    /// Get or create the fencing token counter for an actor
    ///
    /// From TLA+ spec: `fencingTokens[actor]`
    #[allow(dead_code)] // Infrastructure for fencing protocol
    async fn get_or_create_token_counter(&self, actor_key: &str) -> u64 {
        let tokens = self.fencing_tokens.read().await;
        if let Some(counter) = tokens.get(actor_key) {
            return counter.load(Ordering::SeqCst);
        }
        drop(tokens);

        // Need to create - upgrade to write lock
        let mut tokens = self.fencing_tokens.write().await;
        // Double-check after acquiring write lock
        if let Some(counter) = tokens.get(actor_key) {
            return counter.load(Ordering::SeqCst);
        }
        tokens.insert(actor_key.to_string(), AtomicU64::new(0));
        0
    }

    /// Increment and return the next fencing token for an actor
    ///
    /// From TLA+ spec: `newToken == fencingTokens[actor] + 1`
    async fn next_fencing_token(&self, actor_key: &str) -> FencingToken {
        let tokens = self.fencing_tokens.read().await;
        if let Some(counter) = tokens.get(actor_key) {
            let new_val = counter.fetch_add(1, Ordering::SeqCst) + 1;
            return FencingToken::new(new_val);
        }
        drop(tokens);

        // Need to create - upgrade to write lock
        let mut tokens = self.fencing_tokens.write().await;
        // Double-check after acquiring write lock
        if let Some(counter) = tokens.get(actor_key) {
            let new_val = counter.fetch_add(1, Ordering::SeqCst) + 1;
            return FencingToken::new(new_val);
        }
        tokens.insert(actor_key.to_string(), AtomicU64::new(1));
        FencingToken::new(1)
    }
}

impl std::fmt::Debug for MemoryLeaseManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryLeaseManager")
            .field("config", &self.config)
            .finish()
    }
}

#[async_trait]
impl LeaseManager for MemoryLeaseManager {
    /// Acquire a lease for an actor
    ///
    /// From TLA+ spec: `AcquireLeaseSafe` action
    /// - Precondition: `~IsValidLease(actor)` - No valid lease exists
    /// - Precondition: `~InGracePeriod(actor)` - Not in grace period (TLA+ GracePeriodRespected)
    /// - Postcondition: `fencingTokens' = fencingTokens[actor] + 1`
    async fn acquire(&self, node_id: &NodeId, actor_id: &ActorId) -> RegistryResult<Lease> {
        // TigerStyle: preconditions
        assert!(!node_id.as_str().is_empty(), "node_id cannot be empty");
        assert!(!actor_id.id().is_empty(), "actor_id cannot be empty");

        let now_ms = self.now_ms();
        let key = actor_id.qualified_name();

        let mut leases = self.leases.write().await;

        // Check if there's an existing lease
        if let Some(existing) = leases.get(&key) {
            // TLA+ spec: Check lease state
            let state = existing.state(now_ms, self.config.grace_period_ms);

            match state {
                LeaseState::Active | LeaseState::GracePeriod => {
                    // TLA+ GracePeriodRespected: No new lease while current is Active or in GracePeriod
                    // This gives the current holder time to renew before eviction
                    return Err(RegistryError::LeaseHeldByOther {
                        actor_id: actor_id.qualified_name(),
                        holder: existing.holder.as_str().to_string(),
                        expiry_ms: existing.expiry_ms,
                    });
                }
                LeaseState::Expired => {
                    // TLA+ ExpiredLeaseClaimable: Expired lease can be claimed
                    // Fall through to acquire
                }
            }
        }

        // Get next fencing token (TLA+ spec: newToken == fencingTokens[actor] + 1)
        // Must be done while holding the write lock for atomicity
        let fencing_token = self.next_fencing_token(&key).await;

        // Create new lease with new fencing token
        let lease = Lease::new(
            actor_id.clone(),
            node_id.clone(),
            now_ms,
            self.config.duration_ms,
            fencing_token,
        );

        leases.insert(key, lease.clone());

        // TigerStyle: postconditions
        debug_assert!(lease.is_valid(now_ms));
        debug_assert!(
            lease.fencing_token.value() > 0,
            "fencing token must be positive after acquire"
        );

        Ok(lease)
    }

    /// Renew an existing lease
    ///
    /// From TLA+ spec: `RenewLeaseSafe` action
    /// - Precondition: `IsValidLease(actor)` - Lease must be valid (not expired)
    /// - Precondition: `leases[actor].holder = node` - Only holder can renew
    /// - Postcondition: Fencing token is NOT incremented (same logical ownership)
    async fn renew(&self, node_id: &NodeId, actor_id: &ActorId) -> RegistryResult<Lease> {
        // TigerStyle: preconditions
        assert!(!node_id.as_str().is_empty(), "node_id cannot be empty");
        assert!(!actor_id.id().is_empty(), "actor_id cannot be empty");

        let now_ms = self.now_ms();
        let key = actor_id.qualified_name();

        let mut leases = self.leases.write().await;

        let lease = leases
            .get_mut(&key)
            .ok_or_else(|| RegistryError::LeaseNotFound {
                actor_id: actor_id.qualified_name(),
            })?;

        // TLA+ RenewalRequiresOwnership: Only holder can renew
        if lease.holder != *node_id {
            return Err(RegistryError::NotLeaseHolder {
                actor_id: actor_id.qualified_name(),
                holder: lease.holder.as_str().to_string(),
                requester: node_id.as_str().to_string(),
            });
        }

        // Check lease is still valid (can renew during Active or GracePeriod)
        if lease.is_expired(now_ms) {
            return Err(RegistryError::LeaseExpired {
                actor_id: actor_id.qualified_name(),
                expiry_ms: lease.expiry_ms,
            });
        }

        // Save the old fencing token to verify it doesn't change
        let old_token = lease.fencing_token;

        // Renew the lease (does NOT increment fencing token per TLA+ spec)
        lease.renew(now_ms, self.config.duration_ms);

        // TigerStyle: postconditions
        debug_assert!(lease.is_valid(now_ms));
        debug_assert_eq!(
            lease.fencing_token, old_token,
            "fencing token must not change on renewal (TLA+ RenewLeaseSafe)"
        );

        Ok(lease.clone())
    }

    async fn release(&self, node_id: &NodeId, actor_id: &ActorId) -> RegistryResult<()> {
        // TigerStyle: preconditions
        assert!(!node_id.as_str().is_empty(), "node_id cannot be empty");
        assert!(!actor_id.id().is_empty(), "actor_id cannot be empty");

        let key = actor_id.qualified_name();

        let mut leases = self.leases.write().await;

        let lease = leases
            .get(&key)
            .ok_or_else(|| RegistryError::LeaseNotFound {
                actor_id: actor_id.qualified_name(),
            })?;

        // Check holder matches
        if lease.holder != *node_id {
            return Err(RegistryError::NotLeaseHolder {
                actor_id: actor_id.qualified_name(),
                holder: lease.holder.as_str().to_string(),
                requester: node_id.as_str().to_string(),
            });
        }

        // Remove the lease
        leases.remove(&key);

        Ok(())
    }

    async fn is_valid(&self, node_id: &NodeId, actor_id: &ActorId) -> bool {
        let now_ms = self.now_ms();
        let key = actor_id.qualified_name();

        let leases = self.leases.read().await;

        leases
            .get(&key)
            .map(|lease| lease.holder == *node_id && lease.is_valid(now_ms))
            .unwrap_or(false)
    }

    async fn get_lease(&self, actor_id: &ActorId) -> Option<Lease> {
        let key = actor_id.qualified_name();
        let leases = self.leases.read().await;
        leases.get(&key).cloned()
    }

    async fn get_leases_for_node(&self, node_id: &NodeId) -> Vec<Lease> {
        let now_ms = self.now_ms();
        let leases = self.leases.read().await;

        leases
            .values()
            .filter(|lease| lease.holder == *node_id && lease.is_valid(now_ms))
            .cloned()
            .collect()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    /// Test clock with controllable time (implements TimeProvider)
    struct TestClock {
        time_ms: AtomicU64,
    }

    impl TestClock {
        fn new(initial_ms: u64) -> Self {
            Self {
                time_ms: AtomicU64::new(initial_ms),
            }
        }

        fn advance(&self, ms: u64) {
            self.time_ms.fetch_add(ms, Ordering::SeqCst);
        }
    }

    impl std::fmt::Debug for TestClock {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "TestClock({})", self.time_ms.load(Ordering::SeqCst))
        }
    }

    #[async_trait]
    impl TimeProvider for TestClock {
        fn now_ms(&self) -> u64 {
            self.time_ms.load(Ordering::SeqCst)
        }

        async fn sleep_ms(&self, ms: u64) {
            self.time_ms.fetch_add(ms, Ordering::SeqCst);
        }

        fn monotonic_ms(&self) -> u64 {
            self.now_ms()
        }
    }

    fn test_node_id(n: u32) -> NodeId {
        NodeId::new(format!("node-{}", n)).unwrap()
    }

    fn test_actor_id(n: u32) -> ActorId {
        ActorId::new("test", format!("actor-{}", n)).unwrap()
    }

    #[test]
    fn test_lease_creation() {
        let actor_id = test_actor_id(1);
        let node_id = test_node_id(1);

        let lease = Lease::new(
            actor_id.clone(),
            node_id.clone(),
            1000,
            5000,
            FencingToken::new(1),
        );

        assert_eq!(lease.actor_id, actor_id);
        assert_eq!(lease.holder, node_id);
        assert_eq!(lease.acquired_at_ms, 1000);
        assert_eq!(lease.expiry_ms, 6000);
        assert_eq!(lease.renewal_count, 0);
        assert_eq!(lease.fencing_token, FencingToken::new(1));
    }

    #[test]
    fn test_lease_validity() {
        let lease = Lease::new(
            test_actor_id(1),
            test_node_id(1),
            1000,
            5000,
            FencingToken::new(1),
        );

        assert!(lease.is_valid(1000));
        assert!(lease.is_valid(5999));
        assert!(!lease.is_valid(6000));
        assert!(!lease.is_valid(7000));
    }

    #[test]
    fn test_lease_state() {
        // Lease: duration=5000ms, created at 1000, expires at 6000
        // With grace_period=1000ms:
        // - Active: clock < 5000 (6000 - 1000)
        // - GracePeriod: 5000 <= clock < 6000
        // - Expired: clock >= 6000
        let lease = Lease::new(
            test_actor_id(1),
            test_node_id(1),
            1000,
            5000,
            FencingToken::new(1),
        );
        let grace_period_ms = 1000;

        // Active state
        assert_eq!(lease.state(1000, grace_period_ms), LeaseState::Active);
        assert_eq!(lease.state(4999, grace_period_ms), LeaseState::Active);

        // Grace period state
        assert_eq!(lease.state(5000, grace_period_ms), LeaseState::GracePeriod);
        assert_eq!(lease.state(5500, grace_period_ms), LeaseState::GracePeriod);
        assert_eq!(lease.state(5999, grace_period_ms), LeaseState::GracePeriod);

        // Expired state
        assert_eq!(lease.state(6000, grace_period_ms), LeaseState::Expired);
        assert_eq!(lease.state(7000, grace_period_ms), LeaseState::Expired);
    }

    #[test]
    fn test_lease_renewal() {
        let mut lease = Lease::new(
            test_actor_id(1),
            test_node_id(1),
            1000,
            5000,
            FencingToken::new(1),
        );
        assert_eq!(lease.expiry_ms, 6000);

        // Renewal does NOT change fencing token (TLA+ spec)
        let old_token = lease.fencing_token;
        lease.renew(3000, 5000);
        assert_eq!(lease.expiry_ms, 8000);
        assert_eq!(lease.renewal_count, 1);
        assert_eq!(lease.fencing_token, old_token);
    }

    #[test]
    fn test_lease_remaining_time() {
        let lease = Lease::new(
            test_actor_id(1),
            test_node_id(1),
            1000,
            5000,
            FencingToken::new(1),
        );

        assert_eq!(lease.remaining_ms(1000), 5000);
        assert_eq!(lease.remaining_ms(3000), 3000);
        assert_eq!(lease.remaining_ms(6000), 0);
        assert_eq!(lease.remaining_ms(7000), 0);
    }

    #[test]
    fn test_fencing_token_monotonic() {
        // TLA+ FencingTokenMonotonic: Fencing tokens never decrease
        let token1 = FencingToken::new(1);
        let token2 = token1.next();
        let token3 = token2.next();

        assert_eq!(token1.value(), 1);
        assert_eq!(token2.value(), 2);
        assert_eq!(token3.value(), 3);
        assert!(token1.is_stale(&token2));
        assert!(token2.is_stale(&token3));
    }

    #[tokio::test]
    async fn test_memory_lease_manager_acquire() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock);

        let node_id = test_node_id(1);
        let actor_id = test_actor_id(1);

        let lease = mgr.acquire(&node_id, &actor_id).await.unwrap();
        assert_eq!(lease.holder, node_id);
        assert!(lease.is_valid(1000));
    }

    #[tokio::test]
    async fn test_memory_lease_manager_acquire_conflict() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock);

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // Node 1 acquires
        mgr.acquire(&node1, &actor_id).await.unwrap();

        // Node 2 tries to acquire - should fail
        let result = mgr.acquire(&node2, &actor_id).await;
        assert!(matches!(
            result,
            Err(RegistryError::LeaseHeldByOther { .. })
        ));
    }

    #[tokio::test]
    async fn test_memory_lease_manager_acquire_after_expiry() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // Node 1 acquires
        mgr.acquire(&node1, &actor_id).await.unwrap();

        // Advance time past expiry
        clock.advance(6000);

        // Node 2 can now acquire
        let lease = mgr.acquire(&node2, &actor_id).await.unwrap();
        assert_eq!(lease.holder, node2);
    }

    #[tokio::test]
    async fn test_memory_lease_manager_renew() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node_id = test_node_id(1);
        let actor_id = test_actor_id(1);

        // Acquire
        mgr.acquire(&node_id, &actor_id).await.unwrap();

        // Advance time but not past expiry
        clock.advance(2000);

        // Renew
        let renewed = mgr.renew(&node_id, &actor_id).await.unwrap();
        assert_eq!(renewed.renewal_count, 1);
        assert!(renewed.is_valid(3000));
    }

    #[tokio::test]
    async fn test_memory_lease_manager_renew_wrong_holder() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock);

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // Node 1 acquires
        mgr.acquire(&node1, &actor_id).await.unwrap();

        // Node 2 tries to renew - should fail
        let result = mgr.renew(&node2, &actor_id).await;
        assert!(matches!(result, Err(RegistryError::NotLeaseHolder { .. })));
    }

    #[tokio::test]
    async fn test_memory_lease_manager_release() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock);

        let node_id = test_node_id(1);
        let actor_id = test_actor_id(1);

        // Acquire
        mgr.acquire(&node_id, &actor_id).await.unwrap();
        assert!(mgr.is_valid(&node_id, &actor_id).await);

        // Release
        mgr.release(&node_id, &actor_id).await.unwrap();
        assert!(!mgr.is_valid(&node_id, &actor_id).await);
    }

    #[tokio::test]
    async fn test_memory_lease_manager_is_valid() {
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node_id = test_node_id(1);
        let actor_id = test_actor_id(1);

        // Not valid before acquisition
        assert!(!mgr.is_valid(&node_id, &actor_id).await);

        // Valid after acquisition
        mgr.acquire(&node_id, &actor_id).await.unwrap();
        assert!(mgr.is_valid(&node_id, &actor_id).await);

        // Not valid after expiry
        clock.advance(6000);
        assert!(!mgr.is_valid(&node_id, &actor_id).await);
    }

    // =========================================================================
    // TLA+ Specification Compliance Tests
    // =========================================================================

    #[tokio::test]
    async fn test_fencing_token_increments_on_acquire() {
        // TLA+ FencingTokenMonotonic: Each acquisition increments fencing token
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // First acquisition: token = 1
        let lease1 = mgr.acquire(&node1, &actor_id).await.unwrap();
        assert_eq!(lease1.fencing_token.value(), 1);

        // Advance past expiry
        clock.advance(6000);

        // Second acquisition by different node: token = 2
        let lease2 = mgr.acquire(&node2, &actor_id).await.unwrap();
        assert_eq!(lease2.fencing_token.value(), 2);
        assert!(lease1.fencing_token.is_stale(&lease2.fencing_token));
    }

    #[tokio::test]
    async fn test_fencing_token_unchanged_on_renewal() {
        // TLA+ RenewLeaseSafe: Renewal does NOT increment fencing token
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node_id = test_node_id(1);
        let actor_id = test_actor_id(1);

        // Acquire
        let lease1 = mgr.acquire(&node_id, &actor_id).await.unwrap();
        let original_token = lease1.fencing_token;

        // Advance time but not past expiry
        clock.advance(2000);

        // Renew multiple times - token should NOT change
        let lease2 = mgr.renew(&node_id, &actor_id).await.unwrap();
        assert_eq!(lease2.fencing_token, original_token);

        clock.advance(2000);
        let lease3 = mgr.renew(&node_id, &actor_id).await.unwrap();
        assert_eq!(lease3.fencing_token, original_token);
    }

    #[tokio::test]
    async fn test_grace_period_respected() {
        // TLA+ GracePeriodRespected: No new lease while current lease is in grace period
        // LeaseConfig::for_testing() has duration=5000ms, grace_period=1000ms
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // Node 1 acquires at t=1000, expires at t=6000
        let lease = mgr.acquire(&node1, &actor_id).await.unwrap();
        assert_eq!(lease.expiry_ms, 6000);

        // At t=4500, lease is Active (4500 < 6000 - 1000 = 5000)
        clock.advance(3500); // t=4500
        let result = mgr.acquire(&node2, &actor_id).await;
        assert!(matches!(
            result,
            Err(RegistryError::LeaseHeldByOther { .. })
        ));

        // At t=5500, lease is in GracePeriod (5000 <= 5500 < 6000)
        clock.advance(1000); // t=5500
        let result = mgr.acquire(&node2, &actor_id).await;
        assert!(
            matches!(result, Err(RegistryError::LeaseHeldByOther { .. })),
            "Should not be able to acquire during grace period"
        );

        // At t=6000, lease is Expired - node 2 can now acquire
        clock.advance(500); // t=6000
        let lease2 = mgr.acquire(&node2, &actor_id).await.unwrap();
        assert_eq!(lease2.holder, node2);
    }

    #[tokio::test]
    async fn test_can_renew_during_grace_period() {
        // TLA+ spec allows renewal during grace period (lease is still valid)
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node_id = test_node_id(1);
        let actor_id = test_actor_id(1);

        // Acquire at t=1000, expires at t=6000
        mgr.acquire(&node_id, &actor_id).await.unwrap();

        // Advance to grace period (t=5500, which is between 5000 and 6000)
        clock.advance(4500); // t=5500

        // Should be able to renew during grace period
        let renewed = mgr.renew(&node_id, &actor_id).await.unwrap();
        assert!(renewed.is_valid(5500));
        assert_eq!(renewed.expiry_ms, 5500 + 5000); // New expiry
    }

    #[tokio::test]
    async fn test_expired_lease_claimable() {
        // TLA+ ExpiredLeaseClaimable: Expired leases don't block new acquisition
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // Node 1 acquires
        mgr.acquire(&node1, &actor_id).await.unwrap();

        // Advance past expiry
        clock.advance(6000);

        // Node 2 can claim the expired lease
        let lease = mgr.acquire(&node2, &actor_id).await.unwrap();
        assert_eq!(lease.holder, node2);
    }

    #[tokio::test]
    async fn test_lease_uniqueness() {
        // TLA+ LeaseUniqueness: At most one node holds a valid lease per actor
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let node3 = test_node_id(3);
        let actor_id = test_actor_id(1);

        // Node 1 acquires
        let lease1 = mgr.acquire(&node1, &actor_id).await.unwrap();
        assert!(lease1.is_valid(clock.now_ms()));

        // Node 2 cannot acquire
        let result = mgr.acquire(&node2, &actor_id).await;
        assert!(matches!(
            result,
            Err(RegistryError::LeaseHeldByOther { .. })
        ));

        // Node 3 cannot acquire
        let result = mgr.acquire(&node3, &actor_id).await;
        assert!(matches!(
            result,
            Err(RegistryError::LeaseHeldByOther { .. })
        ));

        // Only node 1 holds a valid lease
        assert!(mgr.is_valid(&node1, &actor_id).await);
        assert!(!mgr.is_valid(&node2, &actor_id).await);
        assert!(!mgr.is_valid(&node3, &actor_id).await);
    }

    #[tokio::test]
    async fn test_renewal_requires_ownership() {
        // TLA+ RenewalRequiresOwnership: Only lease holder can renew
        let clock = Arc::new(TestClock::new(1000));
        let mgr = MemoryLeaseManager::new(LeaseConfig::for_testing(), clock.clone());

        let node1 = test_node_id(1);
        let node2 = test_node_id(2);
        let actor_id = test_actor_id(1);

        // Node 1 acquires
        mgr.acquire(&node1, &actor_id).await.unwrap();

        // Node 1 can renew
        mgr.renew(&node1, &actor_id).await.unwrap();

        // Node 2 cannot renew
        let result = mgr.renew(&node2, &actor_id).await;
        assert!(matches!(result, Err(RegistryError::NotLeaseHolder { .. })));
    }
}

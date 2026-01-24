//! Liveness property verification for DST
//!
//! TigerStyle: Bounded liveness checking with explicit timeouts.
//!
//! This module provides tools for verifying liveness properties (temporal properties
//! that assert something good eventually happens) in deterministic simulations.
//!
//! # Temporal Operators
//!
//! - `<>` (eventually): The property holds at some point in the future
//! - `~>` (leads-to): If P holds, then Q eventually holds (P ~> Q ≡ [](P => <>Q))
//! - `[]<>` (infinitely often): The property holds infinitely often
//!
//! # Bounded Liveness
//!
//! Since simulations can't run forever, we use bounded liveness checks:
//! - Set a maximum number of steps or simulated time
//! - If the property doesn't hold within bounds, report a violation
//! - The bounds should be set based on system timeouts (e.g., 2-3x heartbeat timeout)
//!
//! # Example
//!
//! ```rust,ignore
//! use kelpie_dst::{liveness, SimConfig, Simulation, SimClock};
//!
//! #[test]
//! fn test_eventual_activation() {
//!     Simulation::new(SimConfig::from_env_or_random()).run(|env| async move {
//!         // Start claiming
//!         start_claim(&env, "actor-1").await;
//!
//!         // Verify: Claiming ~> (Active ∨ Idle)
//!         liveness::verify_leads_to(
//!             &env.clock,
//!             || is_claiming("actor-1"),
//!             || is_active("actor-1") || is_idle("actor-1"),
//!             10_000, // timeout_ms
//!             100,    // check_interval_ms
//!         ).await?;
//!
//!         Ok(())
//!     });
//! }
//! ```

use crate::clock::SimClock;
use std::fmt;
use std::sync::Arc;

// =============================================================================
// Constants (TigerStyle: explicit units)
// =============================================================================

/// Default check interval in milliseconds
pub const LIVENESS_CHECK_INTERVAL_MS_DEFAULT: u64 = 10;

/// Default timeout for liveness checks in milliseconds
pub const LIVENESS_TIMEOUT_MS_DEFAULT: u64 = 10_000;

/// Maximum steps for bounded liveness checks
pub const LIVENESS_STEPS_MAX: u64 = 100_000;

// =============================================================================
// Error Types
// =============================================================================

/// Error returned when a liveness property is violated
#[derive(Debug, Clone)]
pub struct LivenessViolation {
    /// Name of the property that was violated
    pub property: String,
    /// Human-readable description of what was expected
    pub expected: String,
    /// Time waited before giving up (milliseconds)
    pub waited_ms: u64,
    /// Number of checks performed
    pub checks_performed: u64,
    /// Description of the final state when timeout occurred
    pub final_state: String,
}

impl fmt::Display for LivenessViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Liveness violation: '{}' - expected '{}' but timed out after {}ms ({} checks). Final state: {}",
            self.property, self.expected, self.waited_ms, self.checks_performed, self.final_state
        )
    }
}

impl std::error::Error for LivenessViolation {}

impl From<LivenessViolation> for kelpie_core::Error {
    fn from(v: LivenessViolation) -> Self {
        kelpie_core::Error::Internal {
            message: v.to_string(),
        }
    }
}

/// Result type for liveness checks
pub type LivenessResult<T> = std::result::Result<T, LivenessViolation>;

// =============================================================================
// Bounded Liveness Checker
// =============================================================================

/// Configuration for bounded liveness checks
#[derive(Debug, Clone)]
pub struct BoundedLiveness {
    /// Maximum time to wait in milliseconds
    pub timeout_ms: u64,
    /// Interval between checks in milliseconds
    pub check_interval_ms: u64,
    /// Maximum number of checks (alternative bound)
    pub max_checks: u64,
}

impl BoundedLiveness {
    /// Create a new bounded liveness checker with the given timeout
    pub fn new(timeout_ms: u64) -> Self {
        assert!(timeout_ms > 0, "timeout must be positive");

        Self {
            timeout_ms,
            check_interval_ms: LIVENESS_CHECK_INTERVAL_MS_DEFAULT,
            max_checks: LIVENESS_STEPS_MAX,
        }
    }

    /// Set the check interval
    pub fn with_check_interval_ms(mut self, interval_ms: u64) -> Self {
        assert!(interval_ms > 0, "check interval must be positive");
        self.check_interval_ms = interval_ms;
        self
    }

    /// Set the maximum number of checks
    pub fn with_max_checks(mut self, max: u64) -> Self {
        assert!(max > 0, "max checks must be positive");
        self.max_checks = max;
        self
    }

    /// Verify that a condition eventually becomes true (<> operator)
    ///
    /// # Arguments
    /// * `clock` - The simulation clock
    /// * `property_name` - Human-readable name for error messages
    /// * `condition` - Closure that returns true when the property holds
    /// * `state_description` - Closure that describes the current state for error messages
    pub async fn verify_eventually<F, S>(
        &self,
        clock: &Arc<SimClock>,
        property_name: &str,
        condition: F,
        state_description: S,
    ) -> LivenessResult<()>
    where
        F: Fn() -> bool,
        S: Fn() -> String,
    {
        let start_time_ms = clock.now_ms();
        let deadline_ms = start_time_ms + self.timeout_ms;
        let mut checks = 0u64;

        loop {
            checks += 1;

            // Check if condition holds
            if condition() {
                tracing::debug!(
                    property = property_name,
                    checks = checks,
                    elapsed_ms = clock.now_ms() - start_time_ms,
                    "Liveness property satisfied"
                );
                return Ok(());
            }

            // Check bounds
            if clock.now_ms() >= deadline_ms || checks >= self.max_checks {
                return Err(LivenessViolation {
                    property: property_name.to_string(),
                    expected: format!("condition to become true within {}ms", self.timeout_ms),
                    waited_ms: clock.now_ms() - start_time_ms,
                    checks_performed: checks,
                    final_state: state_description(),
                });
            }

            // Advance time and check again
            clock.advance_ms(self.check_interval_ms);
        }
    }

    /// Verify the leads-to property: P ~> Q (if P holds, Q eventually holds)
    ///
    /// This is equivalent to [](P => <>Q): always, if P then eventually Q.
    ///
    /// # Arguments
    /// * `clock` - The simulation clock
    /// * `property_name` - Human-readable name for error messages
    /// * `precondition` - The trigger condition P
    /// * `postcondition` - The expected eventual outcome Q
    /// * `state_description` - Closure that describes the current state for error messages
    pub async fn verify_leads_to<P, Q, S>(
        &self,
        clock: &Arc<SimClock>,
        property_name: &str,
        precondition: P,
        postcondition: Q,
        state_description: S,
    ) -> LivenessResult<()>
    where
        P: Fn() -> bool,
        Q: Fn() -> bool,
        S: Fn() -> String,
    {
        let start_time_ms = clock.now_ms();
        let deadline_ms = start_time_ms + self.timeout_ms;
        let mut checks = 0u64;
        let mut precondition_seen = false;
        let mut precondition_time_ms = 0u64;

        loop {
            checks += 1;

            let p_holds = precondition();
            let q_holds = postcondition();

            // Track when precondition first holds
            if p_holds && !precondition_seen {
                precondition_seen = true;
                precondition_time_ms = clock.now_ms();
                tracing::debug!(
                    property = property_name,
                    time_ms = precondition_time_ms,
                    "Precondition triggered, waiting for postcondition"
                );
            }

            // If precondition triggered and postcondition now holds, success
            if precondition_seen && q_holds {
                tracing::debug!(
                    property = property_name,
                    checks = checks,
                    elapsed_ms = clock.now_ms() - precondition_time_ms,
                    "Leads-to property satisfied (P ~> Q)"
                );
                return Ok(());
            }

            // Check bounds
            if clock.now_ms() >= deadline_ms || checks >= self.max_checks {
                if !precondition_seen {
                    // Precondition never triggered - this is actually OK for leads-to
                    // (P ~> Q is vacuously true if P never holds)
                    tracing::debug!(
                        property = property_name,
                        "Leads-to vacuously satisfied (precondition never held)"
                    );
                    return Ok(());
                }

                return Err(LivenessViolation {
                    property: property_name.to_string(),
                    expected: format!(
                        "postcondition to hold within {}ms after precondition",
                        self.timeout_ms
                    ),
                    waited_ms: clock.now_ms() - precondition_time_ms,
                    checks_performed: checks,
                    final_state: state_description(),
                });
            }

            // Advance time and check again
            clock.advance_ms(self.check_interval_ms);
        }
    }

    /// Verify that a condition holds infinitely often ([]<> operator)
    ///
    /// In bounded checking, we verify that the condition holds at least `min_occurrences`
    /// times within the timeout.
    ///
    /// # Arguments
    /// * `clock` - The simulation clock
    /// * `property_name` - Human-readable name for error messages
    /// * `condition` - Closure that returns true when the property holds
    /// * `min_occurrences` - Minimum number of times the condition must hold
    /// * `state_description` - Closure that describes the current state for error messages
    pub async fn verify_infinitely_often<F, S>(
        &self,
        clock: &Arc<SimClock>,
        property_name: &str,
        condition: F,
        min_occurrences: u64,
        state_description: S,
    ) -> LivenessResult<u64>
    where
        F: Fn() -> bool,
        S: Fn() -> String,
    {
        assert!(
            min_occurrences > 0,
            "min_occurrences must be positive for []<>"
        );

        let start_time_ms = clock.now_ms();
        let deadline_ms = start_time_ms + self.timeout_ms;
        let mut checks = 0u64;
        let mut occurrences = 0u64;
        let mut was_true = false;

        loop {
            checks += 1;

            let now_true = condition();

            // Count rising edges (false -> true transitions)
            if now_true && !was_true {
                occurrences += 1;
                tracing::trace!(
                    property = property_name,
                    occurrences = occurrences,
                    "Condition became true (occurrence #{})",
                    occurrences
                );
            }
            was_true = now_true;

            // Check if we've seen enough occurrences
            if occurrences >= min_occurrences {
                tracing::debug!(
                    property = property_name,
                    occurrences = occurrences,
                    checks = checks,
                    "Infinitely-often property satisfied"
                );
                return Ok(occurrences);
            }

            // Check bounds
            if clock.now_ms() >= deadline_ms || checks >= self.max_checks {
                return Err(LivenessViolation {
                    property: property_name.to_string(),
                    expected: format!(
                        "condition to hold at least {} times within {}ms (saw {} times)",
                        min_occurrences, self.timeout_ms, occurrences
                    ),
                    waited_ms: clock.now_ms() - start_time_ms,
                    checks_performed: checks,
                    final_state: state_description(),
                });
            }

            // Advance time and check again
            clock.advance_ms(self.check_interval_ms);
        }
    }
}

impl Default for BoundedLiveness {
    fn default() -> Self {
        Self::new(LIVENESS_TIMEOUT_MS_DEFAULT)
    }
}

// =============================================================================
// Convenience Functions
// =============================================================================

/// Verify that a condition eventually becomes true (<> operator)
///
/// This is a convenience wrapper around `BoundedLiveness::verify_eventually`.
pub async fn verify_eventually<F, S>(
    clock: &Arc<SimClock>,
    property_name: &str,
    condition: F,
    timeout_ms: u64,
    check_interval_ms: u64,
    state_description: S,
) -> LivenessResult<()>
where
    F: Fn() -> bool,
    S: Fn() -> String,
{
    BoundedLiveness::new(timeout_ms)
        .with_check_interval_ms(check_interval_ms)
        .verify_eventually(clock, property_name, condition, state_description)
        .await
}

/// Verify the leads-to property: P ~> Q
///
/// This is a convenience wrapper around `BoundedLiveness::verify_leads_to`.
pub async fn verify_leads_to<P, Q, S>(
    clock: &Arc<SimClock>,
    property_name: &str,
    precondition: P,
    postcondition: Q,
    timeout_ms: u64,
    check_interval_ms: u64,
    state_description: S,
) -> LivenessResult<()>
where
    P: Fn() -> bool,
    Q: Fn() -> bool,
    S: Fn() -> String,
{
    BoundedLiveness::new(timeout_ms)
        .with_check_interval_ms(check_interval_ms)
        .verify_leads_to(
            clock,
            property_name,
            precondition,
            postcondition,
            state_description,
        )
        .await
}

// =============================================================================
// State Snapshot Helpers
// =============================================================================

/// A captured system state for liveness checking
///
/// This provides a way to capture and compare system states during liveness verification.
#[derive(Debug, Clone)]
pub struct SystemStateSnapshot {
    /// Time when the snapshot was taken
    pub time_ms: u64,
    /// Arbitrary state fields (name -> value)
    pub fields: std::collections::HashMap<String, String>,
}

impl SystemStateSnapshot {
    /// Create a new empty snapshot
    pub fn new(time_ms: u64) -> Self {
        Self {
            time_ms,
            fields: std::collections::HashMap::new(),
        }
    }

    /// Add a field to the snapshot
    pub fn with_field(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.fields.insert(name.into(), value.into());
        self
    }

    /// Get a field value
    pub fn get(&self, name: &str) -> Option<&String> {
        self.fields.get(name)
    }

    /// Check if a field equals a value
    pub fn field_equals(&self, name: &str, expected: &str) -> bool {
        self.fields
            .get(name)
            .map(|v| v == expected)
            .unwrap_or(false)
    }
}

impl fmt::Display for SystemStateSnapshot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "State@{}ms: {{", self.time_ms)?;
        let mut first = true;
        for (k, v) in &self.fields {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}={}", k, v)?;
            first = false;
        }
        write!(f, "}}")
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_verify_eventually_success() {
        let clock = Arc::new(SimClock::from_millis(0));
        let counter = Arc::new(std::sync::atomic::AtomicU64::new(0));

        // Condition becomes true after 5 checks
        let counter_ref = counter.clone();
        let condition = move || {
            let val = counter_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            val >= 5
        };

        let result = BoundedLiveness::new(1000)
            .with_check_interval_ms(10)
            .verify_eventually(&clock, "test_property", condition, || {
                "counter state".to_string()
            })
            .await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_verify_eventually_timeout() {
        let clock = Arc::new(SimClock::from_millis(0));

        // Condition never becomes true
        let condition = || false;

        let result = BoundedLiveness::new(100)
            .with_check_interval_ms(10)
            .verify_eventually(&clock, "never_true", condition, || {
                "always false".to_string()
            })
            .await;

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.property, "never_true");
        assert!(err.waited_ms >= 100);
    }

    #[tokio::test]
    #[allow(clippy::disallowed_methods)] // tokio::spawn is fine in tests
    async fn test_verify_leads_to_success() {
        let clock = Arc::new(SimClock::from_millis(0));
        let phase = Arc::new(std::sync::atomic::AtomicU64::new(0));

        // Phase 0 -> Phase 1 -> Phase 2
        // Precondition: phase == 1
        // Postcondition: phase == 2
        let phase_pre = phase.clone();
        let precondition = move || phase_pre.load(std::sync::atomic::Ordering::SeqCst) == 1;

        let phase_post = phase.clone();
        let postcondition = move || phase_post.load(std::sync::atomic::Ordering::SeqCst) == 2;

        // Spawn a "background" process that advances phases
        let clock_spawn = clock.clone();
        let phase_spawn = phase.clone();
        tokio::spawn(async move {
            // After 50ms, go to phase 1
            while clock_spawn.now_ms() < 50 {
                tokio::task::yield_now().await;
            }
            phase_spawn.store(1, std::sync::atomic::Ordering::SeqCst);

            // After 100ms, go to phase 2
            while clock_spawn.now_ms() < 100 {
                tokio::task::yield_now().await;
            }
            phase_spawn.store(2, std::sync::atomic::Ordering::SeqCst);
        });

        let phase_desc = phase.clone();
        let result = BoundedLiveness::new(500)
            .with_check_interval_ms(10)
            .verify_leads_to(
                &clock,
                "phase_transition",
                precondition,
                postcondition,
                move || {
                    format!(
                        "phase={}",
                        phase_desc.load(std::sync::atomic::Ordering::SeqCst)
                    )
                },
            )
            .await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_verify_leads_to_vacuous() {
        let clock = Arc::new(SimClock::from_millis(0));

        // Precondition never holds - leads-to is vacuously true
        let precondition = || false;
        let postcondition = || false;

        let result = BoundedLiveness::new(100)
            .with_check_interval_ms(10)
            .verify_leads_to(&clock, "vacuous", precondition, postcondition, || {
                "n/a".to_string()
            })
            .await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_verify_infinitely_often_success() {
        let clock = Arc::new(SimClock::from_millis(0));
        let counter = std::sync::atomic::AtomicU64::new(0);

        // Condition alternates every 20ms
        let condition = || {
            counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            (clock.now_ms() / 20) % 2 == 0
        };

        let result = BoundedLiveness::new(1000)
            .with_check_interval_ms(10)
            .verify_infinitely_often(
                &clock,
                "alternating",
                condition,
                5, // Expect at least 5 occurrences
                || "counter state".to_string(),
            )
            .await;

        assert!(result.is_ok());
        assert!(result.unwrap() >= 5);
    }

    #[test]
    fn test_system_state_snapshot() {
        let snapshot = SystemStateSnapshot::new(1000)
            .with_field("node_state", "Claiming")
            .with_field("lease_holder", "node-1");

        assert_eq!(snapshot.time_ms, 1000);
        assert!(snapshot.field_equals("node_state", "Claiming"));
        assert!(!snapshot.field_equals("node_state", "Active"));
        assert_eq!(snapshot.get("lease_holder"), Some(&"node-1".to_string()));

        let display = format!("{}", snapshot);
        assert!(display.contains("1000ms"));
        assert!(display.contains("node_state=Claiming"));
    }

    #[test]
    fn test_bounded_liveness_builder() {
        let liveness = BoundedLiveness::new(5000)
            .with_check_interval_ms(50)
            .with_max_checks(1000);

        assert_eq!(liveness.timeout_ms, 5000);
        assert_eq!(liveness.check_interval_ms, 50);
        assert_eq!(liveness.max_checks, 1000);
    }
}

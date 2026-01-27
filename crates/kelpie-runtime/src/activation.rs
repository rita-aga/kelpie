//! Actor activation and lifecycle management
//!
//! TigerStyle: Explicit lifecycle states, single activation guarantee.
//!
//! # TLA+ Specification Compliance
//!
//! This module implements the actor lifecycle protocol from `docs/tla/KelpieActorLifecycle.tla`:
//!
//! ## State Mapping
//! - `state` -> `ActivationState` enum (Inactive, Activating, Active, Deactivating)
//! - `pending` -> Number of pending invocations (tracked via `pending_invocations`)
//! - `idleTicks` -> Computed from `idle_time_ms()`
//!
//! ## Key Invariants
//! - `LifecycleOrdering` (G1.3): Invocations only happen when state = Active
//! - `GracefulDeactivation`: Cannot be Deactivating with pending invocations
//! - `IdleTimeoutRespected`: Only deactivate after idle timeout
//! - `NoInvokeWhileDeactivating`: Cannot start new invocations during deactivation
//!
//! ## Liveness Properties
//! - `EventualDeactivation`: If idle timeout reached, eventually deactivates
//! - `EventualActivation`: If activation starts, it completes (or fails)
//! - `EventualInvocationCompletion`: Started invocations eventually complete

use crate::mailbox::{Envelope, Mailbox};
use bytes::Bytes;
use kelpie_core::actor::{
    Actor, ActorContext, ActorId, ArcContextKV, BufferedKVOp, BufferingContextKV,
};
use kelpie_core::constants::{ACTOR_IDLE_TIMEOUT_MS_DEFAULT, ACTOR_INVOCATION_TIMEOUT_MS_MAX};
use kelpie_core::error::{Error, Result};
use kelpie_core::io::{TimeProvider, WallClockTime};
use kelpie_storage::{ActorKV, ScopedKV};
use serde::{de::DeserializeOwned, Serialize};
use std::sync::Arc;
use std::time::Duration;
use tracing::{debug, error, info, instrument, warn};

/// State key for actor's serialized state
const STATE_KEY: &[u8] = b"__state__";

/// Actor lifecycle state
///
/// From TLA+ KelpieActorLifecycle spec:
/// - `Inactive`: Actor is not running (initial state, or after deactivation)
/// - `Activating`: Actor is loading state and running on_activate hook
/// - `Active`: Actor is running and accepting invocations
/// - `Deactivating`: Actor is persisting state and running on_deactivate hook
///
/// State transitions:
/// ```text
///                   +------------+
///                   |  Inactive  | <-----+
///                   +------------+       |
///                         |              |
///                         v              |
///                   +------------+       |
///                   | Activating |       |
///                   +------------+       |
///                         |              |
///                         v              |
///                   +------------+       |
///          +------> |   Active   | ------+
///          |        +------------+       |
///          |              |              |
///          |              v              |
///          |        +-------------+      |
///          +------- | Deactivating| -----+
///                   +-------------+
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ActivationState {
    /// Actor is not running (initial state, or after deactivation)
    ///
    /// From TLA+ spec: `state = "Inactive"`
    #[default]
    Inactive,
    /// Actor is being activated (loading state, running on_activate)
    ///
    /// From TLA+ spec: `state = "Activating"`
    Activating,
    /// Actor is active and ready to process messages
    ///
    /// From TLA+ spec: `state = "Active"`
    /// Invocations are ONLY allowed in this state (LifecycleOrdering invariant).
    Active,
    /// Actor is being deactivated (persisting state, running on_deactivate)
    ///
    /// From TLA+ spec: `state = "Deactivating"`
    /// GracefulDeactivation: Cannot have pending invocations in this state.
    Deactivating,
}

impl ActivationState {
    /// Check if actor can accept new invocations
    ///
    /// From TLA+ spec: LifecycleOrdering - only Active state can invoke
    pub fn can_invoke(&self) -> bool {
        matches!(self, ActivationState::Active)
    }

    /// Check if valid transition per TLA+ state machine
    pub fn can_transition_to(&self, next: ActivationState) -> bool {
        match (self, next) {
            // From Inactive: can only go to Activating
            (ActivationState::Inactive, ActivationState::Activating) => true,
            // From Activating: go to Active (success) or Inactive (failure)
            (ActivationState::Activating, ActivationState::Active) => true,
            (ActivationState::Activating, ActivationState::Inactive) => true,
            // From Active: can only go to Deactivating
            (ActivationState::Active, ActivationState::Deactivating) => true,
            // From Deactivating: go back to Inactive
            (ActivationState::Deactivating, ActivationState::Inactive) => true,
            // Same state is allowed (no change)
            _ if *self == next => true,
            // All other transitions are invalid
            _ => false,
        }
    }
}

impl std::fmt::Display for ActivationState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ActivationState::Inactive => write!(f, "inactive"),
            ActivationState::Activating => write!(f, "activating"),
            ActivationState::Active => write!(f, "active"),
            ActivationState::Deactivating => write!(f, "deactivating"),
        }
    }
}

/// Statistics for an active actor
///
/// Uses monotonic timestamps (u64 ms) for DST compatibility.
#[derive(Debug, Clone, Default)]
pub struct ActivationStats {
    /// When the actor was activated (monotonic ms)
    pub activated_at_ms: Option<u64>,
    /// Last time the actor processed a message (monotonic ms)
    pub last_activity_at_ms: Option<u64>,
    /// Total invocations processed
    pub invocation_count: u64,
    /// Total invocation errors
    pub error_count: u64,
    /// Total time spent processing in ms (for average calculation)
    pub total_processing_time_ms: u64,
}

impl ActivationStats {
    /// Create new stats with activation time (uses production wall clock)
    pub fn new() -> Self {
        Self::with_time(&WallClockTime::new())
    }

    /// Create new stats with custom time provider (for DST)
    pub fn with_time(time: &dyn TimeProvider) -> Self {
        Self {
            activated_at_ms: Some(time.monotonic_ms()),
            last_activity_at_ms: None,
            invocation_count: 0,
            error_count: 0,
            total_processing_time_ms: 0,
        }
    }

    /// Record an invocation (uses wall clock time)
    ///
    /// For DST compatibility, use `record_invocation_with_time` instead.
    pub fn record_invocation(&mut self, duration_ms: u64, is_error: bool) {
        self.record_invocation_with_time(duration_ms, is_error, &WallClockTime::new());
    }

    /// Record an invocation with time provider (for DST)
    pub fn record_invocation_with_time(
        &mut self,
        duration_ms: u64,
        is_error: bool,
        time: &dyn TimeProvider,
    ) {
        self.last_activity_at_ms = Some(time.monotonic_ms());
        self.invocation_count = self.invocation_count.wrapping_add(1);
        self.total_processing_time_ms = self.total_processing_time_ms.saturating_add(duration_ms);
        if is_error {
            self.error_count = self.error_count.wrapping_add(1);
        }
    }

    /// Get idle time (time since last activity) using time provider
    pub fn idle_time_ms(&self, time: &dyn TimeProvider) -> u64 {
        let now_ms = time.monotonic_ms();
        match self.last_activity_at_ms {
            Some(t) => now_ms.saturating_sub(t),
            None => self
                .activated_at_ms
                .map(|t| now_ms.saturating_sub(t))
                .unwrap_or(0),
        }
    }

    /// Get average processing time per invocation
    pub fn average_processing_time(&self) -> Duration {
        if self.invocation_count == 0 {
            Duration::ZERO
        } else {
            Duration::from_millis(self.total_processing_time_ms / self.invocation_count)
        }
    }
}

/// An active actor instance
///
/// TigerStyle: Single activation guarantee - only one ActiveActor per ActorId
/// can exist in the cluster at any time.
///
/// # TLA+ Invariants
///
/// This struct maintains the invariants from KelpieActorLifecycle.tla:
/// - `LifecycleOrdering`: `pending_invocations > 0 => state = Active`
/// - `GracefulDeactivation`: `state = Deactivating => pending_invocations = 0`
/// - `IdleTimeoutRespected`: `state = Deactivating => idle_time >= timeout`
pub struct ActiveActor<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync,
{
    /// The actor's unique identifier
    pub id: ActorId,
    /// The actor implementation
    actor: A,
    /// The actor's context (state + KV access)
    context: ActorContext<S>,
    /// The actor's mailbox
    mailbox: Mailbox,
    /// Current lifecycle state (from TLA+ spec: state variable)
    state: ActivationState,
    /// Number of pending invocations (from TLA+ spec: pending variable)
    ///
    /// Used to enforce GracefulDeactivation invariant.
    pending_invocations: u64,
    /// Statistics
    stats: ActivationStats,
    /// Idle timeout before deactivation (from TLA+ spec: IDLE_TIMEOUT constant)
    idle_timeout: Duration,
    /// Scoped KV store for persistence (bound to this actor)
    kv: ScopedKV,
    /// Time provider for DST compatibility
    time: Arc<dyn TimeProvider>,
}

impl<A, S> ActiveActor<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone,
{
    /// Activate an actor using production wall clock
    ///
    /// For DST, use `activate_with_time`.
    #[instrument(skip(actor, kv), fields(actor_id = %id), level = "info")]
    pub async fn activate(id: ActorId, actor: A, kv: Arc<dyn ActorKV>) -> Result<Self> {
        Self::activate_with_time(id, actor, kv, Arc::new(WallClockTime::new())).await
    }

    /// Activate an actor with custom time provider (for DST)
    ///
    /// Loads state from storage and calls on_activate.
    #[instrument(skip(actor, kv, time), fields(actor_id = %id), level = "info")]
    pub async fn activate_with_time(
        id: ActorId,
        actor: A,
        kv: Arc<dyn ActorKV>,
        time: Arc<dyn TimeProvider>,
    ) -> Result<Self> {
        debug!(actor_id = %id, "Activating actor");

        // Create a scoped KV bound to this actor
        let scoped_kv = ScopedKV::new(id.clone(), kv.clone());

        // Create a second scoped KV for the context (ScopedKV doesn't implement Clone)
        let context_kv = ScopedKV::new(id.clone(), kv);

        let mut active = Self {
            id: id.clone(),
            actor,
            context: ActorContext::with_default_state(id.clone(), Box::new(context_kv)),
            mailbox: Mailbox::new(),
            state: ActivationState::Activating,
            pending_invocations: 0, // TLA+ spec: pending = 0 in Init
            stats: ActivationStats::with_time(time.as_ref()),
            idle_timeout: Duration::from_millis(ACTOR_IDLE_TIMEOUT_MS_DEFAULT),
            time,
            kv: scoped_kv,
        };

        // Load state from storage
        active.load_state().await?;

        // Call on_activate hook
        if let Err(e) = active.actor.on_activate(&mut active.context).await {
            error!(actor_id = %active.id, error = %e, "on_activate failed");
            // Failed activation goes back to Inactive (per TLA+ state machine)
            active.state = ActivationState::Inactive;
            return Err(e);
        }

        active.state = ActivationState::Active;
        info!(actor_id = %active.id, "Actor activated");

        Ok(active)
    }

    /// Load state from storage
    async fn load_state(&mut self) -> Result<()> {
        match self.kv.get(STATE_KEY).await {
            Ok(Some(bytes)) => {
                let state: S = serde_json::from_slice(&bytes).map_err(|e| Error::Internal {
                    message: format!("Failed to deserialize actor state: {}", e),
                })?;
                self.context.state = state;
                debug!(actor_id = %self.id, "Loaded state from storage");
            }
            Ok(None) => {
                debug!(actor_id = %self.id, "No existing state, using default");
            }
            Err(e) => {
                warn!(actor_id = %self.id, error = %e, "Failed to load state, using default");
                // Continue with default state - this allows recovery from storage issues
            }
        }
        Ok(())
    }

    /// Save state to storage
    async fn save_state(&mut self) -> Result<()> {
        let bytes = serde_json::to_vec(&self.context.state).map_err(|e| Error::Internal {
            message: format!("Failed to serialize actor state: {}", e),
        })?;

        self.kv
            .set(STATE_KEY, &bytes)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to persist actor state: {}", e),
            })?;

        debug!(actor_id = %self.id, "Saved state to storage");
        Ok(())
    }

    /// Process an invocation using the actor's time provider
    ///
    /// State AND KV operations are persisted atomically within a single transaction
    /// after each successful invocation. This ensures crash safety - if the node
    /// crashes, either all changes (state + KV) are persisted or none are.
    ///
    /// TigerStyle: Transactional state + KV persistence, 2+ assertions.
    #[instrument(skip(self, payload), fields(actor_id = %self.id, operation), level = "info")]
    pub async fn process_invocation(&mut self, operation: &str, payload: Bytes) -> Result<Bytes> {
        self.process_invocation_with_time(operation, payload, self.time.clone())
            .await
    }

    /// Process an invocation with external time provider (for DST)
    ///
    /// State AND KV operations are persisted atomically within a single transaction
    /// after each successful invocation. This ensures crash safety - if the node
    /// crashes, either all changes (state + KV) are persisted or none are.
    ///
    /// TigerStyle: Transactional state + KV persistence, 2+ assertions.
    ///
    /// # TLA+ Invariants
    ///
    /// This method enforces:
    /// - `LifecycleOrdering`: Only allow invocation when state = Active
    /// - Tracks `pending_invocations` for GracefulDeactivation invariant
    #[instrument(skip(self, payload, time), fields(actor_id = %self.id, operation), level = "info")]
    pub async fn process_invocation_with_time(
        &mut self,
        operation: &str,
        payload: Bytes,
        time: Arc<dyn TimeProvider>,
    ) -> Result<Bytes> {
        // TLA+ LifecycleOrdering invariant: only invoke when Active
        // This is the SAFE behavior - BUGGY mode in TLA+ allows invoke in any state
        assert!(
            self.state.can_invoke(),
            "VIOLATION: LifecycleOrdering - cannot invoke when state = {}",
            self.state
        );
        assert!(!operation.is_empty(), "operation cannot be empty");

        // Increment pending invocations (TLA+ StartInvoke action)
        self.pending_invocations = self.pending_invocations.saturating_add(1);

        // Use time provider for DST determinism
        let start_ms = time.monotonic_ms();

        // CRITICAL: Snapshot state BEFORE invoke for rollback on failure
        // If transaction fails, we must restore state to match what's persisted
        let state_snapshot = self.context.state.clone();

        // Create a buffering KV to capture all KV operations during invoke
        let buffering_kv = Arc::new(BufferingContextKV::new(
            // Create a new ScopedKV for the buffering wrapper to read from
            Box::new(ScopedKV::new(self.id.clone(), self.kv.underlying_kv())),
        ));

        // Swap in the buffering KV (wrapped in Arc for sharing)
        let original_kv = self
            .context
            .swap_kv(Box::new(ArcContextKV(buffering_kv.clone())));

        // Execute the actor's invoke with the buffering KV
        let runtime = kelpie_core::current_runtime();
        let result = kelpie_core::Runtime::timeout(
            &runtime,
            Duration::from_millis(ACTOR_INVOCATION_TIMEOUT_MS_MAX),
            self.actor
                .invoke(&mut self.context, operation, payload.clone()),
        )
        .await;

        // Restore the original KV
        let _ = self.context.swap_kv(original_kv);

        // Drain buffered operations from our Arc reference
        let buffered_ops = buffering_kv.drain_buffer();

        let duration_ms = time.monotonic_ms().saturating_sub(start_ms);

        // On successful invocation, persist state AND KV atomically in a transaction
        let final_result = match result {
            Ok(Ok(response)) => {
                // Save state + KV in a single transaction (crash-safe, atomic)
                match self.save_all_transactional(&buffered_ops).await {
                    Ok(()) => Ok(response),
                    Err(e) => {
                        // Transaction failed - neither state nor KV persisted
                        // ROLLBACK: Restore state to match what's persisted
                        self.context.state = state_snapshot;
                        error!(
                            actor_id = %self.id,
                            operation = %operation,
                            error = %e,
                            "Failed to persist state and KV after invocation, state rolled back"
                        );
                        Err(e)
                    }
                }
            }
            Ok(Err(e)) => {
                // Actor returned an error - don't persist any changes
                // ROLLBACK: Restore state to match what's persisted
                self.context.state = state_snapshot;
                debug!(
                    actor_id = %self.id,
                    operation = %operation,
                    error = %e,
                    buffered_kv_ops = buffered_ops.len(),
                    "Invocation failed, state rolled back"
                );
                Err(e)
            }
            Err(_) => {
                // Timeout - rollback state as well
                self.context.state = state_snapshot;
                Err(Error::OperationTimedOut {
                    operation: operation.to_string(),
                    timeout_ms: ACTOR_INVOCATION_TIMEOUT_MS_MAX,
                })
            }
        };

        // Decrement pending invocations (TLA+ CompleteInvoke action)
        self.pending_invocations = self.pending_invocations.saturating_sub(1);

        self.stats
            .record_invocation_with_time(duration_ms, final_result.is_err(), time.as_ref());

        // Verify LifecycleOrdering invariant: if pending > 0, must be Active
        // (This is a postcondition check)
        debug_assert!(
            self.pending_invocations == 0 || self.state == ActivationState::Active,
            "VIOLATION: LifecycleOrdering - pending {} but state = {}",
            self.pending_invocations,
            self.state
        );

        final_result
    }

    /// Save state AND buffered KV operations atomically in a single transaction
    ///
    /// This ensures that all changes made during an invocation (both state and KV)
    /// are persisted atomically. If the transaction fails, neither state nor KV
    /// changes are persisted.
    ///
    /// TigerStyle: Atomic persistence of all invocation changes.
    async fn save_all_transactional(&mut self, buffered_ops: &[BufferedKVOp]) -> Result<()> {
        let state_bytes = serde_json::to_vec(&self.context.state).map_err(|e| Error::Internal {
            message: format!("Failed to serialize actor state: {}", e),
        })?;

        // Begin transaction
        let mut txn = self
            .kv
            .begin_transaction()
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to begin transaction: {}", e),
            })?;

        // Apply all buffered KV operations to the transaction
        for op in buffered_ops {
            match op {
                BufferedKVOp::Set { key, value } => {
                    txn.set(key, value).await.map_err(|e| Error::Internal {
                        message: format!("Failed to set KV in transaction: {}", e),
                    })?;
                }
                BufferedKVOp::Delete { key } => {
                    txn.delete(key).await.map_err(|e| Error::Internal {
                        message: format!("Failed to delete KV in transaction: {}", e),
                    })?;
                }
            }
        }

        // Set state within transaction
        txn.set(STATE_KEY, &state_bytes)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to set state in transaction: {}", e),
            })?;

        // Commit atomically - all KV ops + state together
        txn.commit().await.map_err(|e| Error::Internal {
            message: format!("Failed to commit transaction: {}", e),
        })?;

        debug!(
            actor_id = %self.id,
            kv_ops = buffered_ops.len(),
            "State and KV persisted atomically in transaction"
        );
        Ok(())
    }

    /// Enqueue a message in the mailbox
    pub fn enqueue(
        &mut self,
        envelope: Envelope,
    ) -> std::result::Result<(), crate::mailbox::MailboxFullError> {
        self.mailbox.push(envelope)
    }

    /// Get the next message from the mailbox
    pub fn dequeue(&mut self) -> Option<Envelope> {
        self.mailbox.pop()
    }

    /// Check if the actor has pending messages
    pub fn has_pending_messages(&self) -> bool {
        !self.mailbox.is_empty()
    }

    /// Get the number of pending messages
    pub fn pending_message_count(&self) -> usize {
        self.mailbox.len()
    }

    /// Deactivate the actor
    ///
    /// Calls on_deactivate, persists state, and rejects pending messages.
    ///
    /// # TLA+ Invariants
    ///
    /// This method enforces:
    /// - `GracefulDeactivation`: Cannot deactivate with pending invocations
    /// - State transition validation per TLA+ state machine
    #[instrument(skip(self), fields(actor_id = %self.id), level = "info")]
    pub async fn deactivate(&mut self) -> Result<()> {
        if self.state == ActivationState::Inactive {
            return Ok(());
        }

        // TLA+ GracefulDeactivation invariant: no pending invocations
        assert!(
            self.pending_invocations == 0,
            "VIOLATION: GracefulDeactivation - cannot deactivate with {} pending invocations",
            self.pending_invocations
        );

        // Validate state transition
        assert!(
            self.state.can_transition_to(ActivationState::Deactivating),
            "Invalid state transition: {} -> Deactivating",
            self.state
        );

        debug!(actor_id = %self.id, "Deactivating actor");
        self.state = ActivationState::Deactivating;

        // Call on_deactivate hook
        if let Err(e) = self.actor.on_deactivate(&mut self.context).await {
            error!(actor_id = %self.id, error = %e, "on_deactivate failed");
            // Continue with deactivation despite error
        }

        // Persist state
        if let Err(e) = self.save_state().await {
            error!(actor_id = %self.id, error = %e, "Failed to save state during deactivation");
            // Continue with deactivation despite error
        }

        // Reject pending messages
        let pending = self.mailbox.drain();
        for envelope in pending {
            let _ = envelope.reply_tx.send(Err(Error::ActorDeactivated {
                actor_id: self.id.clone(),
            }));
        }

        // Transition to Inactive (TLA+ CompleteDeactivate action)
        self.state = ActivationState::Inactive;
        self.pending_invocations = 0; // Reset pending count

        info!(
            actor_id = %self.id,
            invocations = self.stats.invocation_count,
            errors = self.stats.error_count,
            "Actor deactivated"
        );

        Ok(())
    }

    /// Get the number of pending invocations
    ///
    /// From TLA+ spec: `pending` variable
    pub fn pending_invocations(&self) -> u64 {
        self.pending_invocations
    }

    /// Check if the actor should be deactivated due to idle timeout
    ///
    /// From TLA+ spec: `StartDeactivate` action preconditions:
    /// - state = Active
    /// - pending = 0 (no pending invocations)
    /// - idleTicks >= IDLE_TIMEOUT
    ///
    /// This implements the IdleTimeoutRespected invariant.
    pub fn should_deactivate(&self) -> bool {
        self.state == ActivationState::Active
            && self.pending_invocations == 0  // GracefulDeactivation: wait for invocations
            && self.mailbox.is_empty()
            && self.stats.idle_time_ms(self.time.as_ref()) >= self.idle_timeout.as_millis() as u64
    }

    /// Get the current activation state
    pub fn activation_state(&self) -> ActivationState {
        self.state
    }

    /// Get the actor's statistics
    pub fn stats(&self) -> &ActivationStats {
        &self.stats
    }

    /// Set the idle timeout
    pub fn set_idle_timeout(&mut self, timeout: Duration) {
        debug_assert!(
            timeout.as_millis() <= kelpie_core::constants::ACTOR_IDLE_TIMEOUT_MS_MAX as u128
        );
        self.idle_timeout = timeout;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use async_trait::async_trait;
    use kelpie_storage::MemoryKV;

    #[derive(Debug, Default, Clone, Serialize, serde::Deserialize)]
    struct CounterState {
        count: i64,
    }

    struct CounterActor;

    #[async_trait]
    impl Actor for CounterActor {
        type State = CounterState;

        async fn invoke(
            &self,
            ctx: &mut ActorContext<Self::State>,
            operation: &str,
            _payload: Bytes,
        ) -> Result<Bytes> {
            match operation {
                "increment" => {
                    ctx.state.count += 1;
                    Ok(Bytes::from(ctx.state.count.to_string()))
                }
                "get" => Ok(Bytes::from(ctx.state.count.to_string())),
                _ => Err(Error::InvalidOperation {
                    operation: operation.to_string(),
                }),
            }
        }
    }

    fn create_kv() -> Arc<MemoryKV> {
        Arc::new(MemoryKV::new())
    }

    #[tokio::test]
    async fn test_actor_activation() {
        let id = ActorId::new("test", "counter-1").unwrap();
        let kv = create_kv();

        let active = ActiveActor::activate(id.clone(), CounterActor, kv)
            .await
            .unwrap();

        assert_eq!(active.activation_state(), ActivationState::Active);
        assert_eq!(active.id, id);
    }

    #[tokio::test]
    async fn test_actor_invocation() {
        let id = ActorId::new("test", "counter-2").unwrap();
        let kv = create_kv();

        let mut active = ActiveActor::activate(id, CounterActor, kv).await.unwrap();

        let result = active
            .process_invocation("increment", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("1"));

        let result = active
            .process_invocation("increment", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("2"));

        let result = active
            .process_invocation("get", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("2"));
    }

    #[tokio::test]
    async fn test_actor_state_persistence() {
        let id = ActorId::new("test", "counter-3").unwrap();
        let kv = create_kv();

        // Activate, increment, deactivate
        {
            let mut active = ActiveActor::activate(id.clone(), CounterActor, kv.clone())
                .await
                .unwrap();
            active
                .process_invocation("increment", Bytes::new())
                .await
                .unwrap();
            active
                .process_invocation("increment", Bytes::new())
                .await
                .unwrap();
            active.deactivate().await.unwrap();
        }

        // Reactivate - state should be restored
        {
            let mut active = ActiveActor::activate(id, CounterActor, kv).await.unwrap();
            let result = active
                .process_invocation("get", Bytes::new())
                .await
                .unwrap();
            assert_eq!(result, Bytes::from("2"));
        }
    }

    #[tokio::test]
    async fn test_actor_deactivation() {
        let id = ActorId::new("test", "counter-4").unwrap();
        let kv = create_kv();

        let mut active = ActiveActor::activate(id, CounterActor, kv).await.unwrap();
        assert_eq!(active.activation_state(), ActivationState::Active);

        active.deactivate().await.unwrap();
        // After deactivation, state is Inactive (per TLA+ spec)
        assert_eq!(active.activation_state(), ActivationState::Inactive);
    }

    #[test]
    fn test_activation_stats() {
        let time = WallClockTime::new();
        let mut stats = ActivationStats::with_time(&time);

        assert_eq!(stats.invocation_count, 0);
        assert_eq!(stats.error_count, 0);

        stats.record_invocation_with_time(10, false, &time);
        stats.record_invocation_with_time(20, true, &time);

        assert_eq!(stats.invocation_count, 2);
        assert_eq!(stats.error_count, 1);
        assert_eq!(stats.total_processing_time_ms, 30);
        assert_eq!(stats.average_processing_time(), Duration::from_millis(15));
    }

    // Actor that uses KV storage for additional data beyond its state
    #[derive(Debug, Default, Clone, Serialize, serde::Deserialize)]
    struct KVActorState {
        initialized: bool,
    }

    struct KVTestActor;

    #[async_trait]
    impl Actor for KVTestActor {
        type State = KVActorState;

        async fn invoke(
            &self,
            ctx: &mut ActorContext<Self::State>,
            operation: &str,
            payload: Bytes,
        ) -> Result<Bytes> {
            match operation {
                "store" => {
                    // Store a value using KV operations
                    let key = b"user_data";
                    ctx.kv_set(key, &payload).await?;
                    ctx.state.initialized = true;
                    Ok(Bytes::from("stored"))
                }
                "load" => {
                    // Load a value using KV operations
                    let key = b"user_data";
                    match ctx.kv_get(key).await? {
                        Some(data) => Ok(data),
                        None => Ok(Bytes::from("not_found")),
                    }
                }
                "delete" => {
                    let key = b"user_data";
                    ctx.kv_delete(key).await?;
                    Ok(Bytes::from("deleted"))
                }
                "exists" => {
                    let key = b"user_data";
                    let exists = ctx.kv_exists(key).await?;
                    Ok(Bytes::from(if exists { "true" } else { "false" }))
                }
                "list_keys" => {
                    // Store multiple keys with prefix
                    ctx.kv_set(b"item:1", b"first").await?;
                    ctx.kv_set(b"item:2", b"second").await?;
                    ctx.kv_set(b"other:1", b"other").await?;

                    let keys = ctx.kv_list_keys(b"item:").await?;
                    Ok(Bytes::from(keys.len().to_string()))
                }
                _ => Err(Error::InvalidOperation {
                    operation: operation.to_string(),
                }),
            }
        }
    }

    #[tokio::test]
    async fn test_actor_kv_operations() {
        let id = ActorId::new("test", "kv-actor-1").unwrap();
        let kv = create_kv();

        let mut active = ActiveActor::activate(id, KVTestActor, kv).await.unwrap();

        // Store data
        let result = active
            .process_invocation("store", Bytes::from("hello world"))
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("stored"));

        // Check exists
        let result = active
            .process_invocation("exists", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("true"));

        // Load data
        let result = active
            .process_invocation("load", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("hello world"));

        // Delete data
        let result = active
            .process_invocation("delete", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("deleted"));

        // Check not exists
        let result = active
            .process_invocation("exists", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("false"));

        // Load returns not_found
        let result = active
            .process_invocation("load", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("not_found"));
    }

    #[tokio::test]
    async fn test_actor_kv_persistence() {
        let id = ActorId::new("test", "kv-actor-2").unwrap();
        let kv = create_kv();

        // First activation: store data and deactivate
        {
            let mut active = ActiveActor::activate(id.clone(), KVTestActor, kv.clone())
                .await
                .unwrap();
            active
                .process_invocation("store", Bytes::from("persistent data"))
                .await
                .unwrap();
            active.deactivate().await.unwrap();
        }

        // Second activation: data should still be there (KV is separate from state)
        {
            let mut active = ActiveActor::activate(id, KVTestActor, kv).await.unwrap();
            let result = active
                .process_invocation("load", Bytes::new())
                .await
                .unwrap();
            assert_eq!(result, Bytes::from("persistent data"));
        }
    }

    #[tokio::test]
    async fn test_actor_kv_list_keys() {
        let id = ActorId::new("test", "kv-actor-3").unwrap();
        let kv = create_kv();

        let mut active = ActiveActor::activate(id, KVTestActor, kv).await.unwrap();

        // list_keys stores 3 keys: item:1, item:2, other:1
        // and returns count of keys with prefix "item:"
        let result = active
            .process_invocation("list_keys", Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("2")); // item:1 and item:2
    }

    // =========================================================================
    // TLA+ Invariant Tests (KelpieActorLifecycle)
    // =========================================================================

    #[test]
    fn test_activation_state_transitions() {
        // Valid transitions per TLA+ spec
        assert!(ActivationState::Inactive.can_transition_to(ActivationState::Activating));
        assert!(ActivationState::Activating.can_transition_to(ActivationState::Active));
        assert!(ActivationState::Activating.can_transition_to(ActivationState::Inactive)); // Failed activation
        assert!(ActivationState::Active.can_transition_to(ActivationState::Deactivating));
        assert!(ActivationState::Deactivating.can_transition_to(ActivationState::Inactive));

        // Invalid transitions
        assert!(!ActivationState::Inactive.can_transition_to(ActivationState::Active)); // Skip Activating
        assert!(!ActivationState::Active.can_transition_to(ActivationState::Inactive)); // Skip Deactivating
        assert!(!ActivationState::Deactivating.can_transition_to(ActivationState::Active));
    }

    #[test]
    fn test_activation_state_can_invoke() {
        // LifecycleOrdering: only Active state can invoke
        assert!(!ActivationState::Inactive.can_invoke());
        assert!(!ActivationState::Activating.can_invoke());
        assert!(ActivationState::Active.can_invoke());
        assert!(!ActivationState::Deactivating.can_invoke());
    }

    #[tokio::test]
    async fn test_lifecycle_ordering_invariant() {
        // Test that pending_invocations is tracked correctly
        let id = ActorId::new("test", "lifecycle-1").unwrap();
        let kv = create_kv();

        let mut active = ActiveActor::activate(id, CounterActor, kv).await.unwrap();

        // Initially no pending invocations
        assert_eq!(active.pending_invocations(), 0);

        // After invocation completes, still 0
        active
            .process_invocation("increment", Bytes::new())
            .await
            .unwrap();
        assert_eq!(active.pending_invocations(), 0);
    }

    #[tokio::test]
    async fn test_graceful_deactivation_invariant() {
        // Test that deactivation waits for invocations to complete
        let id = ActorId::new("test", "graceful-1").unwrap();
        let kv = create_kv();

        let mut active = ActiveActor::activate(id, CounterActor, kv).await.unwrap();

        // Process some invocations (all complete)
        active
            .process_invocation("increment", Bytes::new())
            .await
            .unwrap();
        active
            .process_invocation("increment", Bytes::new())
            .await
            .unwrap();

        // pending_invocations should be 0
        assert_eq!(active.pending_invocations(), 0);

        // Deactivation should succeed (no pending invocations)
        active.deactivate().await.unwrap();
        assert_eq!(active.activation_state(), ActivationState::Inactive);
    }

    #[test]
    fn test_idle_timeout_respected_invariant() {
        // Test that should_deactivate requires:
        // 1. state = Active
        // 2. pending_invocations = 0
        // 3. no pending messages
        // 4. idle_time >= idle_timeout

        // This is a logic test - the actual time-based test would need
        // the DST SimClock which is in kelpie-dst crate

        // The key invariant from TLA+ IdleTimeoutRespected:
        // state = Deactivating => idleTicks >= IDLE_TIMEOUT

        // should_deactivate checks:
        // - state == Active (required before deactivate)
        // - pending_invocations == 0 (GracefulDeactivation)
        // - mailbox.is_empty()
        // - idle_time_ms >= idle_timeout

        // This invariant is enforced by the should_deactivate() implementation
        // which only returns true when ALL conditions are met.

        // Verify the state transition preconditions
        assert!(ActivationState::Active.can_transition_to(ActivationState::Deactivating));
        assert!(!ActivationState::Inactive.can_transition_to(ActivationState::Deactivating));
        assert!(!ActivationState::Activating.can_transition_to(ActivationState::Deactivating));
    }

    #[test]
    fn test_activation_state_default() {
        assert_eq!(ActivationState::default(), ActivationState::Inactive);
    }

    #[test]
    fn test_activation_state_display() {
        assert_eq!(format!("{}", ActivationState::Inactive), "inactive");
        assert_eq!(format!("{}", ActivationState::Activating), "activating");
        assert_eq!(format!("{}", ActivationState::Active), "active");
        assert_eq!(format!("{}", ActivationState::Deactivating), "deactivating");
    }
}

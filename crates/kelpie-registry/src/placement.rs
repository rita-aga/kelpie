//! Actor placement tracking
//!
//! TigerStyle: Explicit placement with single activation guarantee.
//!
//! # TLA+ Specification Compliance
//!
//! This module implements the placement protocol from `docs/tla/KelpieSingleActivation.tla`
//! and migration protocol from `docs/tla/KelpieMigration.tla`:
//!
//! ## Single Activation (KelpieSingleActivation.tla)
//! - `fdb_holder` -> `ActorPlacement.node_id`
//! - `fdb_version` -> `ActorPlacement.generation` (monotonically increasing)
//! - `node_state` -> Managed by registry state machine
//!
//! ## Migration Protocol (KelpieMigration.tla)
//! - `migration_phase` -> `MigrationPhase` enum (Idle, Preparing, Transferring, Completing, Completed, Failed)
//! - `actor_activation` -> `ActorActivation` enum (Active, Inactive, Migrating)
//!
//! Key invariants:
//! - `MigrationAtomicity`: Complete migration transfers full state
//! - `NoStateLoss`: Actor state is never lost during migration
//! - `SingleActivationDuringMigration`: At most one active instance during migration
//! - `MigrationRollback`: Failed migration leaves actor recoverable
//!
//! The `generation` field serves as the OCC version for conflict detection.

use crate::error::{RegistryError, RegistryResult};
use crate::node::NodeId;
use kelpie_core::actor::ActorId;
use kelpie_core::io::{TimeProvider, WallClockTime};
use kelpie_core::occ::Version;
use serde::{Deserialize, Serialize};

// =============================================================================
// Migration State Types (from TLA+ KelpieMigration spec)
// =============================================================================

/// Migration phase - tracks the 3-phase migration protocol
///
/// From TLA+ KelpieMigration spec:
/// - `Idle`: No migration in progress
/// - `Preparing`: Target node being prepared
/// - `Transferring`: State being transferred
/// - `Completing`: Finalizing migration on target
/// - `Completed`: Migration successful
/// - `Failed`: Migration failed, needs recovery
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[allow(dead_code)] // Infrastructure for migration protocol, used in tests
pub enum MigrationPhase {
    /// No migration in progress
    #[default]
    Idle,
    /// Phase 1: Target node being prepared
    Preparing,
    /// Phase 2: State being transferred from source to target
    Transferring,
    /// Phase 3: Finalizing migration on target
    Completing,
    /// Migration completed successfully
    Completed,
    /// Migration failed, recovery pending
    Failed,
}

#[allow(dead_code)] // Infrastructure for migration protocol, used in tests
impl MigrationPhase {
    /// Check if migration is in progress
    pub fn is_in_progress(&self) -> bool {
        matches!(
            self,
            MigrationPhase::Preparing | MigrationPhase::Transferring | MigrationPhase::Completing
        )
    }

    /// Check if migration can be started
    pub fn can_start(&self) -> bool {
        matches!(self, MigrationPhase::Idle | MigrationPhase::Completed)
    }

    /// Valid phase transitions per TLA+ spec
    pub fn can_transition_to(&self, next: MigrationPhase) -> bool {
        match (self, next) {
            // From Idle
            (MigrationPhase::Idle, MigrationPhase::Preparing) => true,
            // From Preparing
            (MigrationPhase::Preparing, MigrationPhase::Transferring) => true,
            (MigrationPhase::Preparing, MigrationPhase::Failed) => true, // Fault
            // From Transferring
            (MigrationPhase::Transferring, MigrationPhase::Completing) => true,
            (MigrationPhase::Transferring, MigrationPhase::Failed) => true, // Fault
            // From Completing
            (MigrationPhase::Completing, MigrationPhase::Completed) => true,
            (MigrationPhase::Completing, MigrationPhase::Failed) => true, // Fault
            // From Completed - can start new migration
            (MigrationPhase::Completed, MigrationPhase::Idle) => true,
            // From Failed - can recover to Idle
            (MigrationPhase::Failed, MigrationPhase::Idle) => true,
            _ => false,
        }
    }
}

/// Actor activation state during migration
///
/// From TLA+ KelpieMigration spec:
/// - `Active`: Actor is running and accepting requests
/// - `Inactive`: Actor is not running
/// - `Migrating`: Actor is being migrated (deactivated on source)
///
/// Critical invariant: `SingleActivationDuringMigration` - actor cannot be
/// Active at multiple locations simultaneously.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[allow(dead_code)] // Infrastructure for migration protocol, used in tests
pub enum ActorActivation {
    /// Actor is running and accepting requests
    #[default]
    Active,
    /// Actor is not running
    Inactive,
    /// Actor is being migrated (deactivated on source, not yet active on target)
    Migrating,
}

#[allow(dead_code)] // Infrastructure for migration protocol, used in tests
impl ActorActivation {
    /// Check if actor can accept requests
    pub fn can_accept_requests(&self) -> bool {
        matches!(self, ActorActivation::Active)
    }
}

/// Migration state for an actor
///
/// Tracks the full migration context from TLA+ spec:
/// - `migration_source`: Where actor is moving FROM
/// - `migration_target`: Where actor is moving TO
/// - `target_received_state`: State received at target during transfer
///
/// Used to verify `MigrationAtomicity` invariant.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)] // Infrastructure for migration protocol, used in tests
pub struct MigrationState {
    /// Current migration phase
    pub phase: MigrationPhase,
    /// Source node (where actor is moving FROM)
    pub source_node: Option<NodeId>,
    /// Target node (where actor is moving TO)
    pub target_node: Option<NodeId>,
    /// Whether state was transferred (for MigrationAtomicity check)
    pub state_transferred: bool,
    /// Actor activation state
    pub activation: ActorActivation,
    /// Recovery pending flag
    pub recovery_pending: bool,
    /// When migration started (for timeout detection)
    pub started_at_ms: Option<u64>,
}

impl Default for MigrationState {
    fn default() -> Self {
        Self {
            phase: MigrationPhase::Idle,
            source_node: None,
            target_node: None,
            state_transferred: false,
            activation: ActorActivation::Active,
            recovery_pending: false,
            started_at_ms: None,
        }
    }
}

#[allow(dead_code)] // Infrastructure for migration protocol, used in tests
impl MigrationState {
    /// Create a new idle migration state
    pub fn new() -> Self {
        Self::default()
    }

    /// Start a migration (transition to Preparing phase)
    ///
    /// Corresponds to TLA+ `StartMigration` action:
    /// - Deactivates actor on source (prevents dual activation)
    /// - Records migration info
    /// - Moves to Preparing phase
    pub fn start(
        &mut self,
        source: NodeId,
        target: NodeId,
        timestamp_ms: u64,
    ) -> RegistryResult<()> {
        // Preconditions from TLA+ spec
        assert!(self.phase.can_start(), "migration already in progress");
        assert!(
            self.activation == ActorActivation::Active,
            "actor must be active to migrate"
        );
        assert!(source != target, "source and target must be different");

        // Deactivate actor on source (prevents dual activation)
        self.activation = ActorActivation::Migrating;

        // Record migration info
        self.source_node = Some(source);
        self.target_node = Some(target);
        self.state_transferred = false;

        // Move to Preparing phase
        self.phase = MigrationPhase::Preparing;
        self.started_at_ms = Some(timestamp_ms);
        self.recovery_pending = false;

        Ok(())
    }

    /// Target accepts prepare (transition to Transferring phase)
    ///
    /// Corresponds to TLA+ `PrepareTarget` action.
    pub fn prepare_accepted(&mut self) -> RegistryResult<()> {
        assert!(
            self.phase == MigrationPhase::Preparing,
            "not in preparing phase"
        );
        self.phase = MigrationPhase::Transferring;
        Ok(())
    }

    /// State transfer complete (transition to Completing phase)
    ///
    /// Corresponds to TLA+ `TransferState` action.
    /// Sets `state_transferred = true` to satisfy MigrationAtomicity.
    pub fn transfer_complete(&mut self) -> RegistryResult<()> {
        assert!(
            self.phase == MigrationPhase::Transferring,
            "not in transferring phase"
        );
        // Mark state as transferred (required for MigrationAtomicity)
        self.state_transferred = true;
        self.phase = MigrationPhase::Completing;
        Ok(())
    }

    /// Complete migration (transition to Completed phase)
    ///
    /// Corresponds to TLA+ `CompleteMigration` action:
    /// - Activates actor on target
    /// - Clears migration state
    ///
    /// CRITICAL: Only call this if `state_transferred == true` to maintain
    /// `MigrationAtomicity` invariant.
    pub fn complete(&mut self) -> RegistryResult<()> {
        assert!(
            self.phase == MigrationPhase::Completing,
            "not in completing phase"
        );
        // Verify MigrationAtomicity - state must have been transferred
        assert!(
            self.state_transferred,
            "VIOLATION: MigrationAtomicity - state not transferred"
        );

        // Activate on target
        self.activation = ActorActivation::Active;

        // Mark complete
        self.phase = MigrationPhase::Completed;

        // Clear migration info
        self.source_node = None;
        self.target_node = None;
        self.started_at_ms = None;

        Ok(())
    }

    /// Handle migration failure
    ///
    /// Corresponds to TLA+ `HandleMigrationFailure` action.
    pub fn fail(&mut self) -> RegistryResult<()> {
        assert!(self.phase.is_in_progress(), "migration not in progress");
        self.phase = MigrationPhase::Failed;
        self.recovery_pending = true;
        Ok(())
    }

    /// Recover from failed migration
    ///
    /// Corresponds to TLA+ `RecoverActor` action.
    /// Returns the node where actor should be recovered.
    pub fn recover(&mut self, fallback_node: &NodeId) -> RegistryResult<NodeId> {
        assert!(self.recovery_pending, "no recovery pending");

        // Priority: source first, then target, then fallback
        let recovery_node = self
            .source_node
            .clone()
            .or_else(|| self.target_node.clone())
            .unwrap_or_else(|| fallback_node.clone());

        // Reset state
        self.activation = ActorActivation::Active;
        self.recovery_pending = false;
        self.phase = MigrationPhase::Idle;
        self.source_node = None;
        self.target_node = None;
        self.state_transferred = false;
        self.started_at_ms = None;

        Ok(recovery_node)
    }

    /// Reset to idle (after completed migration)
    pub fn reset(&mut self) {
        *self = Self::default();
    }
}

/// Information about where an actor is placed
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActorPlacement {
    /// The actor's unique identifier
    pub actor_id: ActorId,
    /// The node where the actor is currently active
    pub node_id: NodeId,
    /// When the actor was activated (Unix timestamp ms)
    pub activated_at_ms: u64,
    /// When this placement was last updated (Unix timestamp ms)
    pub updated_at_ms: u64,
    /// Generation/version for detecting stale placements
    pub generation: u64,
}

impl ActorPlacement {
    /// Create a new placement record using production wall clock
    ///
    /// For DST, use `with_timestamp` or `new_with_time`.
    pub fn new(actor_id: ActorId, node_id: NodeId) -> Self {
        Self::new_with_time(actor_id, node_id, &WallClockTime::new())
    }

    /// Create a new placement record with injected time provider (for DST)
    pub fn new_with_time(actor_id: ActorId, node_id: NodeId, time: &dyn TimeProvider) -> Self {
        Self::with_timestamp(actor_id, node_id, time.now_ms())
    }

    /// Create a placement with a specific timestamp (for testing/simulation)
    pub fn with_timestamp(actor_id: ActorId, node_id: NodeId, timestamp_ms: u64) -> Self {
        Self {
            actor_id,
            node_id,
            activated_at_ms: timestamp_ms,
            updated_at_ms: timestamp_ms,
            generation: 1,
        }
    }

    /// Update the node for this placement (for migration)
    pub fn migrate_to(&mut self, new_node: NodeId, timestamp_ms: u64) {
        debug_assert!(timestamp_ms >= self.updated_at_ms);
        self.node_id = new_node;
        self.updated_at_ms = timestamp_ms;
        self.generation = self.generation.saturating_add(1);
    }

    /// Check if this placement is stale compared to another
    pub fn is_stale(&self, other: &ActorPlacement) -> bool {
        debug_assert_eq!(self.actor_id, other.actor_id);
        self.generation < other.generation
    }

    /// Touch the placement to update the timestamp
    pub fn touch(&mut self, timestamp_ms: u64) {
        debug_assert!(timestamp_ms >= self.updated_at_ms);
        self.updated_at_ms = timestamp_ms;
    }

    /// Get the version for OCC (maps to fdb_version in TLA+ spec)
    pub fn version(&self) -> Version {
        Version::new(self.generation)
    }

    /// Bump the generation/version (called on writes)
    ///
    /// Corresponds to TLA+: `fdb_version' = fdb_version + 1`
    pub fn bump_version(&mut self) {
        self.generation = self.generation.saturating_add(1);
    }
}

/// Strategy for selecting a node for actor placement
#[derive(Debug, Clone, Copy, Default)]
pub enum PlacementStrategy {
    /// Place on node with least actors (load balancing)
    #[default]
    LeastLoaded,
    /// Place on random available node
    Random,
    /// Place on specific node (for affinity)
    Affinity,
    /// Round-robin across nodes
    RoundRobin,
}

/// Context for making placement decisions
#[derive(Debug, Clone)]
pub struct PlacementContext {
    /// The actor to place
    pub actor_id: ActorId,
    /// Preferred node (for affinity)
    pub preferred_node: Option<NodeId>,
    /// Strategy to use
    pub strategy: PlacementStrategy,
}

impl PlacementContext {
    /// Create a new placement context
    pub fn new(actor_id: ActorId) -> Self {
        Self {
            actor_id,
            preferred_node: None,
            strategy: PlacementStrategy::default(),
        }
    }

    /// Set preferred node
    pub fn with_preferred_node(mut self, node_id: NodeId) -> Self {
        self.preferred_node = Some(node_id);
        self.strategy = PlacementStrategy::Affinity;
        self
    }

    /// Set placement strategy
    pub fn with_strategy(mut self, strategy: PlacementStrategy) -> Self {
        self.strategy = strategy;
        self
    }
}

/// Result of a placement decision
#[derive(Debug, Clone)]
pub enum PlacementDecision {
    /// Actor is already placed on a node
    Existing(ActorPlacement),
    /// Actor should be placed on this node
    New(NodeId),
    /// No suitable node available for placement
    NoCapacity,
}

/// Validation for placement operations
pub fn validate_placement(
    actor_id: &ActorId,
    existing: Option<&ActorPlacement>,
    requested_node: &NodeId,
) -> RegistryResult<()> {
    // TigerStyle: Explicit validation with 2+ assertions
    debug_assert!(!actor_id.id().is_empty());
    debug_assert!(!requested_node.as_str().is_empty());

    // Check for conflict
    if let Some(existing) = existing {
        if existing.node_id != *requested_node {
            return Err(RegistryError::actor_already_registered(
                actor_id,
                existing.node_id.as_str(),
            ));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_actor_id() -> ActorId {
        ActorId::new("test", "actor-1").unwrap()
    }

    fn test_node_id() -> NodeId {
        NodeId::new("node-1").unwrap()
    }

    fn test_node_id_2() -> NodeId {
        NodeId::new("node-2").unwrap()
    }

    #[test]
    fn test_actor_placement_new() {
        let placement = ActorPlacement::new(test_actor_id(), test_node_id());

        assert_eq!(placement.actor_id, test_actor_id());
        assert_eq!(placement.node_id, test_node_id());
        assert_eq!(placement.generation, 1);
    }

    #[test]
    fn test_actor_placement_migrate() {
        let mut placement = ActorPlacement::with_timestamp(test_actor_id(), test_node_id(), 1000);

        let new_node = NodeId::new("node-2").unwrap();
        placement.migrate_to(new_node.clone(), 2000);

        assert_eq!(placement.node_id, new_node);
        assert_eq!(placement.updated_at_ms, 2000);
        assert_eq!(placement.generation, 2);
    }

    #[test]
    fn test_actor_placement_stale() {
        let p1 = ActorPlacement::with_timestamp(test_actor_id(), test_node_id(), 1000);
        let mut p2 = ActorPlacement::with_timestamp(test_actor_id(), test_node_id(), 1000);
        p2.generation = 2;

        assert!(p1.is_stale(&p2));
        assert!(!p2.is_stale(&p1));
    }

    #[test]
    fn test_placement_context() {
        let ctx = PlacementContext::new(test_actor_id());
        assert!(ctx.preferred_node.is_none());
        assert!(matches!(ctx.strategy, PlacementStrategy::LeastLoaded));

        let ctx = ctx.with_preferred_node(test_node_id());
        assert!(ctx.preferred_node.is_some());
        assert!(matches!(ctx.strategy, PlacementStrategy::Affinity));
    }

    #[test]
    fn test_validate_placement_no_conflict() {
        let result = validate_placement(&test_actor_id(), None, &test_node_id());
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_placement_same_node() {
        let placement = ActorPlacement::new(test_actor_id(), test_node_id());
        let result = validate_placement(&test_actor_id(), Some(&placement), &test_node_id());
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_placement_conflict() {
        let placement = ActorPlacement::new(test_actor_id(), test_node_id());
        let other_node = NodeId::new("node-2").unwrap();
        let result = validate_placement(&test_actor_id(), Some(&placement), &other_node);
        assert!(matches!(
            result,
            Err(RegistryError::ActorAlreadyRegistered { .. })
        ));
    }

    // =========================================================================
    // Migration Phase Tests (TLA+ KelpieMigration)
    // =========================================================================

    #[test]
    fn test_migration_phase_default() {
        let phase = MigrationPhase::default();
        assert_eq!(phase, MigrationPhase::Idle);
        assert!(!phase.is_in_progress());
        assert!(phase.can_start());
    }

    #[test]
    fn test_migration_phase_transitions() {
        // Valid transitions
        assert!(MigrationPhase::Idle.can_transition_to(MigrationPhase::Preparing));
        assert!(MigrationPhase::Preparing.can_transition_to(MigrationPhase::Transferring));
        assert!(MigrationPhase::Preparing.can_transition_to(MigrationPhase::Failed));
        assert!(MigrationPhase::Transferring.can_transition_to(MigrationPhase::Completing));
        assert!(MigrationPhase::Transferring.can_transition_to(MigrationPhase::Failed));
        assert!(MigrationPhase::Completing.can_transition_to(MigrationPhase::Completed));
        assert!(MigrationPhase::Completing.can_transition_to(MigrationPhase::Failed));
        assert!(MigrationPhase::Completed.can_transition_to(MigrationPhase::Idle));
        assert!(MigrationPhase::Failed.can_transition_to(MigrationPhase::Idle));

        // Invalid transitions
        assert!(!MigrationPhase::Idle.can_transition_to(MigrationPhase::Completed));
        assert!(!MigrationPhase::Preparing.can_transition_to(MigrationPhase::Completed));
        assert!(!MigrationPhase::Completed.can_transition_to(MigrationPhase::Transferring));
    }

    #[test]
    fn test_migration_phase_in_progress() {
        assert!(!MigrationPhase::Idle.is_in_progress());
        assert!(MigrationPhase::Preparing.is_in_progress());
        assert!(MigrationPhase::Transferring.is_in_progress());
        assert!(MigrationPhase::Completing.is_in_progress());
        assert!(!MigrationPhase::Completed.is_in_progress());
        assert!(!MigrationPhase::Failed.is_in_progress());
    }

    #[test]
    fn test_actor_activation_default() {
        let activation = ActorActivation::default();
        assert_eq!(activation, ActorActivation::Active);
        assert!(activation.can_accept_requests());
    }

    #[test]
    fn test_actor_activation_states() {
        assert!(ActorActivation::Active.can_accept_requests());
        assert!(!ActorActivation::Inactive.can_accept_requests());
        assert!(!ActorActivation::Migrating.can_accept_requests());
    }

    #[test]
    fn test_migration_state_default() {
        let state = MigrationState::default();
        assert_eq!(state.phase, MigrationPhase::Idle);
        assert_eq!(state.activation, ActorActivation::Active);
        assert!(state.source_node.is_none());
        assert!(state.target_node.is_none());
        assert!(!state.state_transferred);
        assert!(!state.recovery_pending);
    }

    #[test]
    fn test_migration_state_start() {
        let mut state = MigrationState::new();

        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();

        assert_eq!(state.phase, MigrationPhase::Preparing);
        assert_eq!(state.activation, ActorActivation::Migrating);
        assert_eq!(state.source_node, Some(test_node_id()));
        assert_eq!(state.target_node, Some(test_node_id_2()));
        assert!(!state.state_transferred);
        assert_eq!(state.started_at_ms, Some(1000));
    }

    #[test]
    fn test_migration_state_full_flow() {
        let mut state = MigrationState::new();

        // Phase 1: Start migration
        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();
        assert_eq!(state.phase, MigrationPhase::Preparing);
        assert_eq!(state.activation, ActorActivation::Migrating);

        // Target accepts prepare
        state.prepare_accepted().unwrap();
        assert_eq!(state.phase, MigrationPhase::Transferring);

        // Phase 2: Transfer state
        state.transfer_complete().unwrap();
        assert_eq!(state.phase, MigrationPhase::Completing);
        assert!(state.state_transferred);

        // Phase 3: Complete migration
        state.complete().unwrap();
        assert_eq!(state.phase, MigrationPhase::Completed);
        assert_eq!(state.activation, ActorActivation::Active);
        assert!(state.source_node.is_none());
        assert!(state.target_node.is_none());
    }

    #[test]
    fn test_migration_atomicity_invariant() {
        // This test verifies the MigrationAtomicity invariant from TLA+ spec:
        // If migration completes, full state was transferred

        let mut state = MigrationState::new();
        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();
        state.prepare_accepted().unwrap();
        state.transfer_complete().unwrap();

        // At this point, state_transferred MUST be true
        assert!(
            state.state_transferred,
            "MigrationAtomicity: state must be transferred before completion"
        );

        // Now complete() will succeed
        state.complete().unwrap();
    }

    #[test]
    #[should_panic(expected = "MigrationAtomicity")]
    fn test_migration_atomicity_violation() {
        // Verify that completing without transfer violates MigrationAtomicity

        let mut state = MigrationState::new();
        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();
        state.prepare_accepted().unwrap();

        // Skip transfer_complete() - this simulates the buggy path in TLA+ spec
        state.phase = MigrationPhase::Completing;

        // This should panic because state_transferred is false
        state.complete().unwrap();
    }

    #[test]
    fn test_migration_failure_and_recovery() {
        let mut state = MigrationState::new();
        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();
        state.prepare_accepted().unwrap();

        // Simulate failure during transfer
        state.fail().unwrap();
        assert_eq!(state.phase, MigrationPhase::Failed);
        assert!(state.recovery_pending);

        // Recover (should go back to source node)
        let fallback = NodeId::new("fallback").unwrap();
        let recovery_node = state.recover(&fallback).unwrap();

        // Should recover to source node (priority)
        assert_eq!(recovery_node, test_node_id());
        assert_eq!(state.phase, MigrationPhase::Idle);
        assert_eq!(state.activation, ActorActivation::Active);
        assert!(!state.recovery_pending);
    }

    #[test]
    fn test_migration_single_activation_invariant() {
        // This test verifies SingleActivationDuringMigration invariant:
        // Actor cannot be Active at multiple locations simultaneously

        let mut state = MigrationState::new();

        // Initially Active
        assert!(state.activation.can_accept_requests());

        // After starting migration, actor is Migrating (not Active on either node)
        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();
        assert!(!state.activation.can_accept_requests());
        assert_eq!(state.activation, ActorActivation::Migrating);

        // During transfer, still Migrating
        state.prepare_accepted().unwrap();
        state.transfer_complete().unwrap();
        assert!(!state.activation.can_accept_requests());

        // Only after complete() is actor Active again (on target)
        state.complete().unwrap();
        assert!(state.activation.can_accept_requests());
    }

    #[test]
    #[should_panic(expected = "source and target must be different")]
    fn test_migration_same_node_rejected() {
        let mut state = MigrationState::new();
        state.start(test_node_id(), test_node_id(), 1000).unwrap();
    }

    #[test]
    fn test_migration_state_reset() {
        let mut state = MigrationState::new();
        state.start(test_node_id(), test_node_id_2(), 1000).unwrap();
        state.prepare_accepted().unwrap();
        state.transfer_complete().unwrap();
        state.complete().unwrap();

        // Reset after completed migration
        state.reset();

        assert_eq!(state.phase, MigrationPhase::Idle);
        assert_eq!(state.activation, ActorActivation::Active);
        assert!(state.source_node.is_none());
    }
}

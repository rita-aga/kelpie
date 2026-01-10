//! Actor abstractions for Kelpie
//!
//! TigerStyle: Explicit types, assertions, bounded operations.

use crate::constants::*;
use crate::error::{Error, Result};
use async_trait::async_trait;
use bytes::Bytes;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::fmt;
use std::hash::Hash;

// =============================================================================
// ActorId
// =============================================================================

/// Unique identifier for an actor
///
/// Actor IDs consist of a namespace and an id, providing logical grouping
/// and unique identification within the cluster.
///
/// # TigerStyle
/// - Explicit validation on construction
/// - Immutable after creation
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct ActorId {
    namespace: String,
    id: String,
}

impl ActorId {
    /// Create a new ActorId with validation
    ///
    /// # Errors
    /// Returns error if namespace or id exceeds length limits or contains invalid characters.
    pub fn new(namespace: impl Into<String>, id: impl Into<String>) -> Result<Self> {
        let namespace = namespace.into();
        let id = id.into();

        // TigerStyle: Explicit validation
        debug_assert!(!namespace.is_empty(), "namespace must not be empty");
        debug_assert!(!id.is_empty(), "id must not be empty");

        if namespace.len() > ACTOR_NAMESPACE_LENGTH_BYTES_MAX {
            return Err(Error::InvalidActorId {
                id: format!("{}:{}", namespace, id),
                reason: format!(
                    "namespace length {} exceeds limit {}",
                    namespace.len(),
                    ACTOR_NAMESPACE_LENGTH_BYTES_MAX
                ),
            });
        }

        if id.len() > ACTOR_ID_LENGTH_BYTES_MAX {
            return Err(Error::ActorIdTooLong {
                length: id.len(),
                limit: ACTOR_ID_LENGTH_BYTES_MAX,
            });
        }

        // Validate characters (alphanumeric, dash, underscore, dot)
        let valid_chars = |s: &str| {
            s.chars()
                .all(|c| c.is_alphanumeric() || c == '-' || c == '_' || c == '.')
        };

        if !valid_chars(&namespace) {
            return Err(Error::InvalidActorId {
                id: format!("{}:{}", namespace, id),
                reason: "namespace contains invalid characters".into(),
            });
        }

        if !valid_chars(&id) {
            return Err(Error::InvalidActorId {
                id: format!("{}:{}", namespace, id),
                reason: "id contains invalid characters".into(),
            });
        }

        Ok(Self { namespace, id })
    }

    /// Create ActorId without validation (for internal use only)
    ///
    /// # Safety
    /// Caller must ensure namespace and id are valid.
    #[doc(hidden)]
    pub fn new_unchecked(namespace: String, id: String) -> Self {
        debug_assert!(namespace.len() <= ACTOR_NAMESPACE_LENGTH_BYTES_MAX);
        debug_assert!(id.len() <= ACTOR_ID_LENGTH_BYTES_MAX);
        Self { namespace, id }
    }

    /// Get the namespace
    pub fn namespace(&self) -> &str {
        &self.namespace
    }

    /// Get the id
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Get the full qualified name (namespace:id)
    pub fn qualified_name(&self) -> String {
        format!("{}:{}", self.namespace, self.id)
    }

    /// Convert to bytes for storage keys
    pub fn to_key_bytes(&self) -> Vec<u8> {
        let qualified = self.qualified_name();
        debug_assert!(
            qualified.len() <= ACTOR_ID_LENGTH_BYTES_MAX + ACTOR_NAMESPACE_LENGTH_BYTES_MAX + 1
        );
        qualified.into_bytes()
    }
}

impl fmt::Display for ActorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.namespace, self.id)
    }
}

// =============================================================================
// ActorRef
// =============================================================================

/// Reference to an actor (location-transparent)
///
/// ActorRef provides location transparency - callers only need the actor's ID
/// to communicate with it. Routing and placement are handled internally.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActorRef {
    /// The actor's unique identifier
    pub id: ActorId,
    // Note: Internal routing hints may be added in future phases
    // but are hidden from the public API
}

impl ActorRef {
    /// Create a new ActorRef from an ActorId
    pub fn new(id: ActorId) -> Self {
        Self { id }
    }

    /// Create a new ActorRef with the given namespace and id
    pub fn from_parts(namespace: impl Into<String>, id: impl Into<String>) -> Result<Self> {
        Ok(Self {
            id: ActorId::new(namespace, id)?,
        })
    }
}

impl From<ActorId> for ActorRef {
    fn from(id: ActorId) -> Self {
        Self::new(id)
    }
}

// =============================================================================
// Actor Trait
// =============================================================================

/// Actor trait - implement to create actors
///
/// # TigerStyle
/// - Single-threaded execution guarantee (no concurrent invocations)
/// - Explicit lifecycle hooks (on_activate, on_deactivate)
/// - State is serializable for persistence
#[async_trait]
pub trait Actor: Send + Sync + 'static {
    /// The actor's state type
    ///
    /// Must be serializable for persistence and default-constructible
    /// for fresh actor activation.
    type State: Serialize + DeserializeOwned + Default + Send + Sync;

    /// Handle an invocation
    ///
    /// This is called for each message sent to the actor. Execution is
    /// guaranteed to be single-threaded - no concurrent invocations.
    ///
    /// # Arguments
    /// * `ctx` - Actor context providing state access and runtime operations
    /// * `operation` - The operation name
    /// * `payload` - The message payload as bytes
    ///
    /// # Returns
    /// Response payload as bytes, or an error
    async fn invoke(
        &self,
        ctx: &mut ActorContext<Self::State>,
        operation: &str,
        payload: Bytes,
    ) -> Result<Bytes>;

    /// Called when the actor is activated
    ///
    /// Override to perform initialization logic when an actor is
    /// loaded into memory.
    async fn on_activate(&self, _ctx: &mut ActorContext<Self::State>) -> Result<()> {
        Ok(())
    }

    /// Called before the actor is deactivated
    ///
    /// Override to perform cleanup logic before an actor is
    /// removed from memory.
    async fn on_deactivate(&self, _ctx: &mut ActorContext<Self::State>) -> Result<()> {
        Ok(())
    }
}

// =============================================================================
// ActorContext
// =============================================================================

/// Context provided to an actor during invocation
///
/// Provides access to:
/// - Actor's persistent state
/// - Per-actor KV store
/// - Ability to invoke other actors
pub struct ActorContext<S> {
    /// The actor's unique identifier
    pub id: ActorId,

    /// The actor's in-memory state
    pub state: S,
    // These will be populated in later phases:
    // kv: Box<dyn ActorKV>,
    // runtime: ActorRuntime,
}

impl<S> ActorContext<S>
where
    S: Serialize + DeserializeOwned + Default + Send + Sync,
{
    /// Create a new ActorContext
    pub fn new(id: ActorId, state: S) -> Self {
        Self { id, state }
    }

    /// Create a new ActorContext with default state
    pub fn with_default_state(id: ActorId) -> Self {
        Self {
            id,
            state: S::default(),
        }
    }

    // These methods will be implemented in later phases:

    // /// Get a value from the actor's KV store
    // pub async fn get(&self, key: &[u8]) -> Result<Option<Bytes>> { ... }

    // /// Set a value in the actor's KV store (transactional)
    // pub async fn set(&mut self, key: &[u8], value: &[u8]) -> Result<()> { ... }

    // /// Delete a value from the actor's KV store
    // pub async fn delete(&mut self, key: &[u8]) -> Result<()> { ... }

    // /// Invoke another actor
    // pub async fn invoke(
    //     &self,
    //     target: &ActorRef,
    //     operation: &str,
    //     payload: Bytes,
    // ) -> Result<Bytes> { ... }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_actor_id_valid() {
        let id = ActorId::new("agents", "agent-123").unwrap();
        assert_eq!(id.namespace(), "agents");
        assert_eq!(id.id(), "agent-123");
        assert_eq!(id.qualified_name(), "agents:agent-123");
    }

    #[test]
    fn test_actor_id_invalid_chars() {
        let result = ActorId::new("agents", "agent/123");
        assert!(result.is_err());
    }

    #[test]
    fn test_actor_id_too_long() {
        let long_id = "a".repeat(ACTOR_ID_LENGTH_BYTES_MAX + 1);
        let result = ActorId::new("agents", long_id);
        assert!(matches!(result, Err(Error::ActorIdTooLong { .. })));
    }

    #[test]
    fn test_actor_ref_from_parts() {
        let actor_ref = ActorRef::from_parts("agents", "agent-456").unwrap();
        assert_eq!(actor_ref.id.qualified_name(), "agents:agent-456");
    }

    #[test]
    fn test_actor_id_display() {
        let id = ActorId::new("ns", "id").unwrap();
        assert_eq!(format!("{}", id), "ns:id");
    }
}

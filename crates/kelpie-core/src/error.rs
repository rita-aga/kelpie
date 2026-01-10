//! Error types for Kelpie
//!
//! TigerStyle: Explicit error types with context, using thiserror.

use thiserror::Error;

/// Result type alias for Kelpie operations
pub type Result<T> = std::result::Result<T, Error>;

/// Kelpie error types
#[derive(Error, Debug)]
pub enum Error {
    // =========================================================================
    // Actor Errors
    // =========================================================================
    #[error("Actor not found: {id}")]
    ActorNotFound { id: String },

    #[error("Actor already exists: {id}")]
    ActorAlreadyExists { id: String },

    #[error("Actor activation failed: {id}, reason: {reason}")]
    ActorActivationFailed { id: String, reason: String },

    #[error("Actor deactivation failed: {id}, reason: {reason}")]
    ActorDeactivationFailed { id: String, reason: String },

    #[error("Actor invocation timeout: {id}, operation: {operation}")]
    ActorInvocationTimeout { id: String, operation: String },

    #[error("Actor invocation failed: {id}, operation: {operation}, reason: {reason}")]
    ActorInvocationFailed {
        id: String,
        operation: String,
        reason: String,
    },

    #[error("Actor mailbox full: {id}, depth: {depth}, max: {max}")]
    ActorMailboxFull {
        id: String,
        depth: usize,
        max: usize,
    },

    // =========================================================================
    // Validation Errors
    // =========================================================================
    #[error("Invalid actor ID: {id}, reason: {reason}")]
    InvalidActorId { id: String, reason: String },

    #[error("Actor ID too long: {length} bytes exceeds limit of {limit} bytes")]
    ActorIdTooLong { length: usize, limit: usize },

    #[error("Actor state too large: {size} bytes exceeds limit of {limit} bytes")]
    ActorStateTooLarge { size: usize, limit: usize },

    #[error("Message too large: {size} bytes exceeds limit of {limit} bytes")]
    MessageTooLarge { size: usize, limit: usize },

    // =========================================================================
    // Storage Errors
    // =========================================================================
    #[error("Storage read failed: {key}, reason: {reason}")]
    StorageReadFailed { key: String, reason: String },

    #[error("Storage write failed: {key}, reason: {reason}")]
    StorageWriteFailed { key: String, reason: String },

    #[error("Transaction failed: {reason}")]
    TransactionFailed { reason: String },

    #[error("Transaction conflict: {reason}")]
    TransactionConflict { reason: String },

    #[error("Transaction too large: {size} bytes exceeds limit of {limit} bytes")]
    TransactionTooLarge { size: usize, limit: usize },

    // =========================================================================
    // Registry Errors
    // =========================================================================
    #[error("Registry lookup failed: {reason}")]
    RegistryLookupFailed { reason: String },

    #[error("Registry update failed: {reason}")]
    RegistryUpdateFailed { reason: String },

    #[error("Node not found: {node_id}")]
    NodeNotFound { node_id: String },

    #[error("Node unavailable: {node_id}")]
    NodeUnavailable { node_id: String },

    // =========================================================================
    // Cluster Errors
    // =========================================================================
    #[error("Cluster join failed: {reason}")]
    ClusterJoinFailed { reason: String },

    #[error("Cluster leave failed: {reason}")]
    ClusterLeaveFailed { reason: String },

    #[error("Migration failed: actor {actor_id} from {from_node} to {to_node}, reason: {reason}")]
    MigrationFailed {
        actor_id: String,
        from_node: String,
        to_node: String,
        reason: String,
    },

    // =========================================================================
    // WASM Errors
    // =========================================================================
    #[error("WASM module load failed: {reason}")]
    WasmModuleLoadFailed { reason: String },

    #[error("WASM execution failed: {reason}")]
    WasmExecutionFailed { reason: String },

    #[error("WASM module too large: {size} bytes exceeds limit of {limit} bytes")]
    WasmModuleTooLarge { size: usize, limit: usize },

    // =========================================================================
    // Configuration Errors
    // =========================================================================
    #[error("Invalid configuration: {field}, reason: {reason}")]
    InvalidConfiguration { field: String, reason: String },

    // =========================================================================
    // Internal Errors
    // =========================================================================
    #[error("Internal error: {reason}")]
    Internal { reason: String },

    #[error("Serialization failed: {reason}")]
    SerializationFailed { reason: String },

    #[error("Deserialization failed: {reason}")]
    DeserializationFailed { reason: String },

    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

impl Error {
    /// Create an actor not found error
    pub fn actor_not_found(id: impl Into<String>) -> Self {
        Self::ActorNotFound { id: id.into() }
    }

    /// Create an actor invocation failed error
    pub fn invocation_failed(
        id: impl Into<String>,
        operation: impl Into<String>,
        reason: impl Into<String>,
    ) -> Self {
        Self::ActorInvocationFailed {
            id: id.into(),
            operation: operation.into(),
            reason: reason.into(),
        }
    }

    /// Create a storage write failed error
    pub fn storage_write_failed(key: impl Into<String>, reason: impl Into<String>) -> Self {
        Self::StorageWriteFailed {
            key: key.into(),
            reason: reason.into(),
        }
    }

    /// Create a transaction failed error
    pub fn transaction_failed(reason: impl Into<String>) -> Self {
        Self::TransactionFailed {
            reason: reason.into(),
        }
    }

    /// Create an internal error
    pub fn internal(reason: impl Into<String>) -> Self {
        Self::Internal {
            reason: reason.into(),
        }
    }

    /// Check if this error is retriable
    pub fn is_retriable(&self) -> bool {
        matches!(
            self,
            Self::TransactionConflict { .. }
                | Self::NodeUnavailable { .. }
                | Self::ActorInvocationTimeout { .. }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_display() {
        let err = Error::actor_not_found("test-actor");
        assert!(err.to_string().contains("test-actor"));
    }

    #[test]
    fn test_error_is_retriable() {
        assert!(Error::TransactionConflict {
            reason: "test".into()
        }
        .is_retriable());
        assert!(!Error::ActorNotFound { id: "test".into() }.is_retriable());
    }
}

//! Sandbox execution environment for Kelpie agents
//!
//! TigerStyle: Secure isolation with explicit lifecycle and state management.
//!
//! # Overview
//!
//! Sandboxes provide isolated execution environments for agent tools:
//! - Process/VM isolation for security
//! - Filesystem and network isolation
//! - State checkpointing (pause/resume)
//! - Resource limits (CPU, memory, disk)
//!
//! # Sandbox Types
//!
//! - **MockSandbox**: In-memory simulation for testing
//! - **ProcessSandbox**: OS process isolation (cross-platform)
//! - **FirecrackerSandbox**: MicroVM isolation (Linux only, feature-gated)
//!
//! # Usage
//!
//! ```ignore
//! use kelpie_sandbox::{SandboxPool, SandboxConfig};
//!
//! // Create a pool of pre-warmed sandboxes
//! let pool = SandboxPool::new(SandboxConfig::default(), 10).await?;
//!
//! // Acquire a sandbox
//! let sandbox = pool.acquire().await?;
//!
//! // Execute a command
//! let output = sandbox.exec("echo", &["hello"]).await?;
//!
//! // Release back to pool (or let it drop)
//! pool.release(sandbox).await;
//! ```

mod config;
mod error;
mod exec;
mod mock;
mod pool;
mod snapshot;
mod traits;

pub use config::{ResourceLimits, SandboxConfig};
pub use error::{SandboxError, SandboxResult};
pub use exec::{ExecOptions, ExecOutput, ExitStatus};
pub use mock::MockSandbox;
pub use pool::{PoolConfig, SandboxPool};
pub use snapshot::{Snapshot, SnapshotMetadata};
pub use traits::{Sandbox, SandboxFactory, SandboxState};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sandbox_module_compiles() {
        // Smoke test
        let _config = SandboxConfig::default();
    }
}

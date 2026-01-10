//! Kelpie Runtime
//!
//! Actor runtime and dispatcher for Kelpie virtual actors.
//!
//! # Overview
//!
//! The runtime provides:
//! - Single-threaded actor execution
//! - On-demand actor activation
//! - Actor mailbox management
//! - Lifecycle management (activate/deactivate)
//!
//! # TigerStyle
//! - Single activation guarantee (one actor instance per ID)
//! - Explicit lifecycle states
//! - Bounded mailboxes (no silent message drops)

pub mod activation;
pub mod dispatcher;
pub mod handle;
pub mod mailbox;
pub mod runtime;

pub use activation::{ActivationState, ActivationStats, ActiveActor};
pub use dispatcher::{
    ActorFactory, CloneFactory, Dispatcher, DispatcherCommand, DispatcherConfig, DispatcherHandle,
};
pub use handle::{ActorHandle, ActorHandleBuilder};
pub use mailbox::{Envelope, Mailbox, MailboxFullError};
pub use runtime::{Runtime, RuntimeBuilder, RuntimeConfig};

//! Actor-based agent implementation
//!
//! TigerStyle: AgentActor implements the Actor trait from kelpie-runtime,
//! providing single activation guarantee, automatic lifecycle, and state persistence.

pub mod agent_actor;
pub mod llm_trait;
pub mod state;

pub use agent_actor::AgentActor;
pub use llm_trait::{LlmClient, LlmMessage, LlmResponse, LlmToolCall};
pub use state::AgentActorState;

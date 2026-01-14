//! AgentActor state definition
//!
//! TigerStyle: Explicit state structure, serializable, with documented fields.

use crate::models::{AgentState, Block};
use serde::{Deserialize, Serialize};

/// State for AgentActor
///
/// This is the in-memory state of an agent actor. It's loaded on activation
/// and persisted on deactivation.
///
/// TigerStyle: All fields have clear purpose and units where applicable.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AgentActorState {
    /// Agent metadata (id, name, type, model, system prompt, etc.)
    /// This is the source of truth for agent configuration.
    pub agent: Option<AgentState>,

    /// Current session ID (for checkpoint/resume)
    pub session_id: Option<String>,

    /// Current iteration count in agent loop
    pub iteration: u32,

    /// Whether the agent is paused (waiting for user input)
    pub is_paused: bool,

    /// Unix timestamp in milliseconds when pause expires
    pub pause_until_ms: Option<u64>,
}

impl AgentActorState {
    /// Create a new AgentActorState from AgentState
    pub fn from_agent(agent: AgentState) -> Self {
        Self {
            agent: Some(agent),
            session_id: None,
            iteration: 0,
            is_paused: false,
            pause_until_ms: None,
        }
    }

    /// Get a reference to the agent state
    ///
    /// Returns None if agent hasn't been created yet.
    pub fn agent(&self) -> Option<&AgentState> {
        self.agent.as_ref()
    }

    /// Get a mutable reference to the agent state
    pub fn agent_mut(&mut self) -> Option<&mut AgentState> {
        self.agent.as_mut()
    }

    /// Get a block by label
    pub fn get_block(&self, label: &str) -> Option<&Block> {
        self.agent
            .as_ref()?
            .blocks
            .iter()
            .find(|b| b.label == label)
    }

    /// Update a block by label
    pub fn update_block<F>(&mut self, label: &str, f: F) -> bool
    where
        F: FnOnce(&mut Block),
    {
        if let Some(agent) = &mut self.agent {
            if let Some(block) = agent.blocks.iter_mut().find(|b| b.label == label) {
                f(block);
                return true;
            }
        }
        false
    }
}

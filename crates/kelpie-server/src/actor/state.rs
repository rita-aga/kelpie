//! AgentActor state definition
//!
//! TigerStyle: Explicit state structure, serializable, with documented fields.

use crate::models::{AgentState, Block, Message};
use serde::{Deserialize, Serialize};

/// Maximum messages to keep in memory (Phase 6.7)
const MAX_MESSAGES_DEFAULT: usize = 100;

/// State for AgentActor
///
/// This is the in-memory state of an agent actor. It's loaded on activation
/// and persisted on deactivation.
///
/// TigerStyle: All fields have clear purpose and units where applicable.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentActorState {
    /// Agent metadata (id, name, type, model, system prompt, etc.)
    /// This is the source of truth for agent configuration.
    pub agent: Option<AgentState>,

    /// Message history (Phase 6.7)
    ///
    /// Recent messages kept in memory for LLM context.
    /// Truncated to max_messages to prevent memory bloat.
    #[serde(default)]
    pub messages: Vec<Message>,

    /// Maximum messages to keep in memory (Phase 6.7)
    #[serde(default = "default_max_messages")]
    pub max_messages: usize,

    /// Current session ID (for checkpoint/resume)
    pub session_id: Option<String>,

    /// Current iteration count in agent loop
    pub iteration: u32,

    /// Whether the agent is paused (waiting for user input)
    pub is_paused: bool,

    /// Unix timestamp in milliseconds when pause expires
    pub pause_until_ms: Option<u64>,
}

fn default_max_messages() -> usize {
    MAX_MESSAGES_DEFAULT
}

impl Default for AgentActorState {
    fn default() -> Self {
        Self {
            agent: None,
            messages: Vec::new(),
            max_messages: MAX_MESSAGES_DEFAULT,
            session_id: None,
            iteration: 0,
            is_paused: false,
            pause_until_ms: None,
        }
    }
}

impl AgentActorState {
    /// Create a new AgentActorState from AgentState
    pub fn from_agent(agent: AgentState) -> Self {
        Self {
            agent: Some(agent),
            messages: Vec::new(),
            max_messages: MAX_MESSAGES_DEFAULT,
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

    /// Add message to history (Phase 6.7)
    ///
    /// Automatically truncates to max_messages to prevent memory bloat.
    ///
    /// # Arguments
    /// * `message` - Message to add to history
    ///
    /// # TigerStyle
    /// - Explicit truncation with assertion
    /// - Clear size limit documented
    pub fn add_message(&mut self, message: Message) {
        self.messages.push(message);

        // Truncate if exceeds max
        if self.messages.len() > self.max_messages {
            let start = self.messages.len() - self.max_messages;
            self.messages = self.messages[start..].to_vec();

            // TigerStyle: Assert postcondition
            assert!(
                self.messages.len() <= self.max_messages,
                "messages should be truncated to max_messages"
            );
        }
    }

    /// Get recent messages (Phase 6.7)
    ///
    /// Returns the last N messages, or all messages if fewer than N.
    ///
    /// # Arguments
    /// * `limit` - Maximum number of messages to return
    ///
    /// # Returns
    /// Slice of most recent messages (up to limit)
    pub fn recent_messages(&self, limit: usize) -> &[Message] {
        let start = self.messages.len().saturating_sub(limit);
        &self.messages[start..]
    }

    /// Get all messages in history (Phase 6.7)
    pub fn all_messages(&self) -> &[Message] {
        &self.messages
    }

    /// Clear message history (Phase 6.7)
    pub fn clear_messages(&mut self) {
        self.messages.clear();
    }
}

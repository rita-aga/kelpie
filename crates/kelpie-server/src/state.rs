//! Server state management
//!
//! TigerStyle: Thread-safe shared state with explicit locking.

use crate::models::{AgentState, Block, Message, ToolDefinition};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::Instant;

/// Maximum agents per server instance
pub const AGENTS_COUNT_MAX: usize = 100_000;

/// Maximum messages per agent
pub const MESSAGES_PER_AGENT_MAX: usize = 10_000;

/// Server-wide shared state
#[derive(Clone)]
pub struct AppState {
    inner: Arc<AppStateInner>,
}

struct AppStateInner {
    /// Agent storage by ID
    agents: RwLock<HashMap<String, AgentState>>,
    /// Messages by agent ID
    messages: RwLock<HashMap<String, Vec<Message>>>,
    /// Tool definitions by ID (for future use)
    #[allow(dead_code)]
    tools: RwLock<HashMap<String, ToolDefinition>>,
    /// Server start time for uptime calculation
    start_time: Instant,
}

impl AppState {
    /// Create new server state
    pub fn new() -> Self {
        Self {
            inner: Arc::new(AppStateInner {
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
            }),
        }
    }

    /// Get server uptime in seconds
    pub fn uptime_seconds(&self) -> u64 {
        self.inner.start_time.elapsed().as_secs()
    }

    // =========================================================================
    // Agent operations
    // =========================================================================

    /// Create a new agent
    pub fn create_agent(&self, agent: AgentState) -> Result<AgentState, StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if agents.len() >= AGENTS_COUNT_MAX {
            return Err(StateError::LimitExceeded {
                resource: "agents",
                limit: AGENTS_COUNT_MAX,
            });
        }

        if agents.contains_key(&agent.id) {
            return Err(StateError::AlreadyExists {
                resource: "agent",
                id: agent.id.clone(),
            });
        }

        let result = agent.clone();
        agents.insert(agent.id.clone(), agent);

        // Initialize empty message list for the agent
        let mut messages = self
            .inner
            .messages
            .write()
            .map_err(|_| StateError::LockPoisoned)?;
        messages.insert(result.id.clone(), Vec::new());

        Ok(result)
    }

    /// Get an agent by ID
    pub fn get_agent(&self, id: &str) -> Result<Option<AgentState>, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(agents.get(id).cloned())
    }

    /// List all agents with pagination
    pub fn list_agents(
        &self,
        limit: usize,
        cursor: Option<&str>,
    ) -> Result<(Vec<AgentState>, Option<String>), StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let mut all_agents: Vec<_> = agents.values().cloned().collect();
        all_agents.sort_by(|a, b| a.created_at.cmp(&b.created_at));

        // Apply cursor (skip until we find the cursor ID)
        let start_idx = if let Some(cursor_id) = cursor {
            all_agents
                .iter()
                .position(|a| a.id == cursor_id)
                .map(|i| i + 1)
                .unwrap_or(0)
        } else {
            0
        };

        let page: Vec<_> = all_agents
            .into_iter()
            .skip(start_idx)
            .take(limit + 1)
            .collect();

        // Determine next cursor
        let (items, next_cursor) = if page.len() > limit {
            let items: Vec<_> = page.into_iter().take(limit).collect();
            let next_cursor = items.last().map(|a| a.id.clone());
            (items, next_cursor)
        } else {
            (page, None)
        };

        Ok((items, next_cursor))
    }

    /// Update an agent
    pub fn update_agent(
        &self,
        id: &str,
        update: impl FnOnce(&mut AgentState),
    ) -> Result<AgentState, StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get_mut(id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: id.to_string(),
        })?;

        update(agent);
        Ok(agent.clone())
    }

    /// Delete an agent
    pub fn delete_agent(&self, id: &str) -> Result<(), StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if agents.remove(id).is_none() {
            return Err(StateError::NotFound {
                resource: "agent",
                id: id.to_string(),
            });
        }

        // Also delete messages
        let mut messages = self
            .inner
            .messages
            .write()
            .map_err(|_| StateError::LockPoisoned)?;
        messages.remove(id);

        Ok(())
    }

    /// Get agent count
    pub fn agent_count(&self) -> Result<usize, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(agents.len())
    }

    // =========================================================================
    // Block operations
    // =========================================================================

    /// Get a memory block by agent ID and block ID
    pub fn get_block(&self, agent_id: &str, block_id: &str) -> Result<Option<Block>, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        Ok(agent.blocks.iter().find(|b| b.id == block_id).cloned())
    }

    /// Update a memory block
    pub fn update_block(
        &self,
        agent_id: &str,
        block_id: &str,
        update: impl FnOnce(&mut Block),
    ) -> Result<Block, StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        let block = agent
            .blocks
            .iter_mut()
            .find(|b| b.id == block_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "block",
                id: block_id.to_string(),
            })?;

        update(block);
        Ok(block.clone())
    }

    /// List blocks for an agent
    pub fn list_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        Ok(agent.blocks.clone())
    }

    // =========================================================================
    // Message operations
    // =========================================================================

    /// Add a message to an agent's history
    pub fn add_message(&self, agent_id: &str, message: Message) -> Result<Message, StateError> {
        let mut messages = self
            .inner
            .messages
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent_messages = messages
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        if agent_messages.len() >= MESSAGES_PER_AGENT_MAX {
            return Err(StateError::LimitExceeded {
                resource: "messages",
                limit: MESSAGES_PER_AGENT_MAX,
            });
        }

        let result = message.clone();
        agent_messages.push(message);
        Ok(result)
    }

    /// List messages for an agent with pagination
    pub fn list_messages(
        &self,
        agent_id: &str,
        limit: usize,
        before: Option<&str>,
    ) -> Result<Vec<Message>, StateError> {
        let messages = self
            .inner
            .messages
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent_messages = messages.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        // If before is specified, find messages before that ID
        let end_idx = if let Some(before_id) = before {
            agent_messages
                .iter()
                .position(|m| m.id == before_id)
                .unwrap_or(agent_messages.len())
        } else {
            agent_messages.len()
        };

        let start_idx = end_idx.saturating_sub(limit);
        Ok(agent_messages[start_idx..end_idx].to_vec())
    }

    // =========================================================================
    // Tool operations (for future use)
    // =========================================================================

    /// Register a tool definition
    #[allow(dead_code)]
    pub fn register_tool(&self, tool: ToolDefinition) -> Result<ToolDefinition, StateError> {
        let mut tools = self
            .inner
            .tools
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let result = tool.clone();
        tools.insert(tool.id.clone(), tool);
        Ok(result)
    }

    /// Get a tool by ID
    #[allow(dead_code)]
    pub fn get_tool(&self, id: &str) -> Result<Option<ToolDefinition>, StateError> {
        let tools = self
            .inner
            .tools
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(tools.get(id).cloned())
    }

    /// List all tools
    #[allow(dead_code)]
    pub fn list_tools(&self) -> Result<Vec<ToolDefinition>, StateError> {
        let tools = self
            .inner
            .tools
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(tools.values().cloned().collect())
    }
}

impl Default for AppState {
    fn default() -> Self {
        Self::new()
    }
}

/// State operation errors
#[derive(Debug, Clone)]
pub enum StateError {
    /// Resource not found
    NotFound { resource: &'static str, id: String },
    /// Resource already exists
    AlreadyExists { resource: &'static str, id: String },
    /// Limit exceeded
    LimitExceeded {
        resource: &'static str,
        limit: usize,
    },
    /// Lock poisoned (shouldn't happen in practice)
    LockPoisoned,
}

impl std::fmt::Display for StateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StateError::NotFound { resource, id } => {
                write!(f, "{} with id '{}' not found", resource, id)
            }
            StateError::AlreadyExists { resource, id } => {
                write!(f, "{} with id '{}' already exists", resource, id)
            }
            StateError::LimitExceeded { resource, limit } => {
                write!(f, "{} limit ({}) exceeded", resource, limit)
            }
            StateError::LockPoisoned => write!(f, "internal lock error"),
        }
    }
}

impl std::error::Error for StateError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{AgentType, CreateAgentRequest, CreateBlockRequest};

    fn create_test_agent(name: &str) -> AgentState {
        AgentState::from_request(CreateAgentRequest {
            name: name.to_string(),
            agent_type: AgentType::default(),
            model: None,
            system: None,
            description: None,
            memory_blocks: vec![CreateBlockRequest {
                label: "persona".to_string(),
                value: "I am a test agent".to_string(),
                description: None,
                limit: None,
            }],
            tool_ids: vec![],
            tags: vec![],
            metadata: serde_json::json!({}),
        })
    }

    #[test]
    fn test_create_and_get_agent() {
        let state = AppState::new();
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();

        let created = state.create_agent(agent).unwrap();
        assert_eq!(created.name, "test-agent");

        let retrieved = state.get_agent(&agent_id).unwrap().unwrap();
        assert_eq!(retrieved.id, agent_id);
        assert_eq!(retrieved.blocks.len(), 1);
    }

    #[test]
    fn test_list_agents_pagination() {
        let state = AppState::new();

        for i in 0..5 {
            let agent = create_test_agent(&format!("agent-{}", i));
            state.create_agent(agent).unwrap();
        }

        // First page
        let (page1, cursor1) = state.list_agents(2, None).unwrap();
        assert_eq!(page1.len(), 2);
        assert!(cursor1.is_some());

        // Second page
        let (page2, cursor2) = state.list_agents(2, cursor1.as_deref()).unwrap();
        assert_eq!(page2.len(), 2);
        assert!(cursor2.is_some());

        // Third page (last)
        let (page3, cursor3) = state.list_agents(2, cursor2.as_deref()).unwrap();
        assert_eq!(page3.len(), 1);
        assert!(cursor3.is_none());
    }

    #[test]
    fn test_delete_agent() {
        let state = AppState::new();
        let agent = create_test_agent("to-delete");
        let agent_id = agent.id.clone();

        state.create_agent(agent).unwrap();
        assert!(state.get_agent(&agent_id).unwrap().is_some());

        state.delete_agent(&agent_id).unwrap();
        assert!(state.get_agent(&agent_id).unwrap().is_none());
    }

    #[test]
    fn test_update_block() {
        let state = AppState::new();
        let agent = create_test_agent("block-test");
        let agent_id = agent.id.clone();
        let block_id = agent.blocks[0].id.clone();

        state.create_agent(agent).unwrap();

        let updated = state
            .update_block(&agent_id, &block_id, |block| {
                block.value = "Updated value".to_string();
            })
            .unwrap();

        assert_eq!(updated.value, "Updated value");
    }

    #[test]
    fn test_messages() {
        let state = AppState::new();
        let agent = create_test_agent("msg-test");
        let agent_id = agent.id.clone();

        state.create_agent(agent).unwrap();

        // Add messages
        for i in 0..5 {
            let msg = Message {
                id: format!("msg-{}", i),
                agent_id: agent_id.clone(),
                role: crate::models::MessageRole::User,
                content: format!("Message {}", i),
                tool_call_id: None,
                tool_calls: None,
                created_at: chrono::Utc::now(),
            };
            state.add_message(&agent_id, msg).unwrap();
        }

        // List last 3
        let messages = state.list_messages(&agent_id, 3, None).unwrap();
        assert_eq!(messages.len(), 3);
        assert_eq!(messages[0].content, "Message 2");
        assert_eq!(messages[2].content, "Message 4");
    }
}

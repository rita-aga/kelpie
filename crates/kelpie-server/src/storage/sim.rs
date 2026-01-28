//! SimStorage - In-memory AgentStorage for testing
//!
//! TigerStyle: Deterministic in-memory storage for DST compatibility.
//!
//! This implementation provides:
//! - Full AgentStorage trait implementation
//! - Thread-safe concurrent access via RwLock
//! - Optional fault injection for DST testing
//! - No external dependencies (no FDB required)
//!
//! Use Cases:
//! - Unit tests
//! - DST (Deterministic Simulation Testing)
//! - Local development without FDB
//! - CI pipelines

use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::RwLock;

use crate::models::{AgentGroup, Block, Identity, Job, MCPServer, Message, Project};

use super::traits::{AgentStorage, StorageError};
use super::types::{AgentMetadata, CustomToolRecord, SessionState};

#[cfg(feature = "dst")]
use kelpie_dst::fault::FaultInjector;
#[cfg(feature = "dst")]
use std::sync::Arc;

/// In-memory storage implementation for testing and development
///
/// TigerStyle: All fields use RwLock for thread-safe concurrent access.
/// Data is stored in HashMaps, providing O(1) lookups.
pub struct SimStorage {
    /// Agent metadata by ID
    agents: RwLock<HashMap<String, AgentMetadata>>,
    /// Blocks by agent_id -> label -> Block
    blocks: RwLock<HashMap<String, HashMap<String, Block>>>,
    /// Sessions by agent_id -> session_id -> SessionState
    sessions: RwLock<HashMap<String, HashMap<String, SessionState>>>,
    /// Custom tools by name
    custom_tools: RwLock<HashMap<String, CustomToolRecord>>,
    /// Messages by agent_id (ordered by insertion)
    messages: RwLock<HashMap<String, Vec<Message>>>,
    /// MCP servers by ID
    mcp_servers: RwLock<HashMap<String, MCPServer>>,
    /// Agent groups by ID
    agent_groups: RwLock<HashMap<String, AgentGroup>>,
    /// Identities by ID
    identities: RwLock<HashMap<String, Identity>>,
    /// Projects by ID
    projects: RwLock<HashMap<String, Project>>,
    /// Jobs by ID
    jobs: RwLock<HashMap<String, Job>>,
    /// Optional fault injector for DST
    #[cfg(feature = "dst")]
    fault_injector: Option<Arc<FaultInjector>>,
}

impl SimStorage {
    /// Create a new empty SimStorage
    pub fn new() -> Self {
        Self {
            agents: RwLock::new(HashMap::new()),
            blocks: RwLock::new(HashMap::new()),
            sessions: RwLock::new(HashMap::new()),
            custom_tools: RwLock::new(HashMap::new()),
            messages: RwLock::new(HashMap::new()),
            mcp_servers: RwLock::new(HashMap::new()),
            agent_groups: RwLock::new(HashMap::new()),
            identities: RwLock::new(HashMap::new()),
            projects: RwLock::new(HashMap::new()),
            jobs: RwLock::new(HashMap::new()),
            #[cfg(feature = "dst")]
            fault_injector: None,
        }
    }

    /// Create SimStorage with fault injection for DST
    #[cfg(feature = "dst")]
    pub fn with_fault_injector(fault_injector: Arc<FaultInjector>) -> Self {
        Self {
            agents: RwLock::new(HashMap::new()),
            blocks: RwLock::new(HashMap::new()),
            sessions: RwLock::new(HashMap::new()),
            custom_tools: RwLock::new(HashMap::new()),
            messages: RwLock::new(HashMap::new()),
            mcp_servers: RwLock::new(HashMap::new()),
            agent_groups: RwLock::new(HashMap::new()),
            identities: RwLock::new(HashMap::new()),
            projects: RwLock::new(HashMap::new()),
            jobs: RwLock::new(HashMap::new()),
            fault_injector: Some(fault_injector),
        }
    }

    /// Check if fault should be injected for an operation
    #[cfg(feature = "dst")]
    #[allow(dead_code)]
    fn should_inject_fault(&self, operation: &str) -> bool {
        if let Some(injector) = &self.fault_injector {
            injector.should_inject(operation).is_some()
        } else {
            false
        }
    }

    #[cfg(not(feature = "dst"))]
    #[allow(dead_code)]
    fn should_inject_fault(&self, _operation: &str) -> bool {
        false
    }

    /// Helper to create fault-injected error
    #[cfg(feature = "dst")]
    fn fault_error(operation: &str) -> StorageError {
        StorageError::FaultInjected {
            operation: operation.to_string(),
        }
    }

    /// Helper for read lock errors
    fn lock_error(operation: &str) -> StorageError {
        StorageError::Internal {
            message: format!("{}: lock poisoned", operation),
        }
    }
}

impl Default for SimStorage {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl AgentStorage for SimStorage {
    // =========================================================================
    // Agent Metadata Operations
    // =========================================================================

    async fn save_agent(&self, agent: &AgentMetadata) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_agent") {
            return Err(Self::fault_error("save_agent"));
        }

        let mut agents = self
            .agents
            .write()
            .map_err(|_| Self::lock_error("save_agent"))?;
        agents.insert(agent.id.clone(), agent.clone());
        Ok(())
    }

    async fn load_agent(&self, id: &str) -> Result<Option<AgentMetadata>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_agent") {
            return Err(Self::fault_error("load_agent"));
        }

        let agents = self
            .agents
            .read()
            .map_err(|_| Self::lock_error("load_agent"))?;
        Ok(agents.get(id).cloned())
    }

    async fn delete_agent(&self, id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_agent") {
            return Err(Self::fault_error("delete_agent"));
        }

        // Delete agent metadata
        {
            let mut agents = self
                .agents
                .write()
                .map_err(|_| Self::lock_error("delete_agent"))?;
            agents.remove(id);
        }

        // Cascade: delete blocks
        {
            let mut blocks = self
                .blocks
                .write()
                .map_err(|_| Self::lock_error("delete_agent_blocks"))?;
            blocks.remove(id);
        }

        // Cascade: delete sessions
        {
            let mut sessions = self
                .sessions
                .write()
                .map_err(|_| Self::lock_error("delete_agent_sessions"))?;
            sessions.remove(id);
        }

        // Cascade: delete messages
        {
            let mut messages = self
                .messages
                .write()
                .map_err(|_| Self::lock_error("delete_agent_messages"))?;
            messages.remove(id);
        }

        Ok(())
    }

    async fn list_agents(&self) -> Result<Vec<AgentMetadata>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_agents") {
            return Err(Self::fault_error("list_agents"));
        }

        let agents = self
            .agents
            .read()
            .map_err(|_| Self::lock_error("list_agents"))?;
        Ok(agents.values().cloned().collect())
    }

    // =========================================================================
    // Core Memory Block Operations
    // =========================================================================

    async fn save_blocks(&self, agent_id: &str, blocks: &[Block]) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_blocks") {
            return Err(Self::fault_error("save_blocks"));
        }

        let mut all_blocks = self
            .blocks
            .write()
            .map_err(|_| Self::lock_error("save_blocks"))?;

        let agent_blocks = all_blocks.entry(agent_id.to_string()).or_default();
        for block in blocks {
            agent_blocks.insert(block.label.clone(), block.clone());
        }
        Ok(())
    }

    async fn load_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_blocks") {
            return Err(Self::fault_error("load_blocks"));
        }

        let all_blocks = self
            .blocks
            .read()
            .map_err(|_| Self::lock_error("load_blocks"))?;

        Ok(all_blocks
            .get(agent_id)
            .map(|blocks| blocks.values().cloned().collect())
            .unwrap_or_default())
    }

    async fn update_block(
        &self,
        agent_id: &str,
        label: &str,
        value: &str,
    ) -> Result<Block, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("update_block") {
            return Err(Self::fault_error("update_block"));
        }

        let mut all_blocks = self
            .blocks
            .write()
            .map_err(|_| Self::lock_error("update_block"))?;

        let agent_blocks = all_blocks.entry(agent_id.to_string()).or_default();

        let block = agent_blocks
            .get_mut(label)
            .ok_or_else(|| StorageError::NotFound {
                resource: "block",
                id: format!("{}:{}", agent_id, label),
            })?;

        block.value = value.to_string();
        Ok(block.clone())
    }

    async fn append_block(
        &self,
        agent_id: &str,
        label: &str,
        content: &str,
    ) -> Result<Block, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("append_block") {
            return Err(Self::fault_error("append_block"));
        }

        let mut all_blocks = self
            .blocks
            .write()
            .map_err(|_| Self::lock_error("append_block"))?;

        let agent_blocks = all_blocks.entry(agent_id.to_string()).or_default();

        let block = agent_blocks
            .entry(label.to_string())
            .or_insert_with(|| Block {
                id: uuid::Uuid::new_v4().to_string(),
                label: label.to_string(),
                value: String::new(),
                description: None,
                limit: None,
                created_at: chrono::Utc::now(),
                updated_at: chrono::Utc::now(),
            });

        block.value.push_str(content);
        block.updated_at = chrono::Utc::now();
        Ok(block.clone())
    }

    // =========================================================================
    // Session State Operations
    // =========================================================================

    async fn save_session(&self, state: &SessionState) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_session") {
            return Err(Self::fault_error("save_session"));
        }

        let mut all_sessions = self
            .sessions
            .write()
            .map_err(|_| Self::lock_error("save_session"))?;

        let agent_sessions = all_sessions.entry(state.agent_id.clone()).or_default();
        agent_sessions.insert(state.session_id.clone(), state.clone());
        Ok(())
    }

    async fn load_session(
        &self,
        agent_id: &str,
        session_id: &str,
    ) -> Result<Option<SessionState>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_session") {
            return Err(Self::fault_error("load_session"));
        }

        let all_sessions = self
            .sessions
            .read()
            .map_err(|_| Self::lock_error("load_session"))?;

        Ok(all_sessions
            .get(agent_id)
            .and_then(|sessions| sessions.get(session_id))
            .cloned())
    }

    async fn delete_session(&self, agent_id: &str, session_id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_session") {
            return Err(Self::fault_error("delete_session"));
        }

        let mut all_sessions = self
            .sessions
            .write()
            .map_err(|_| Self::lock_error("delete_session"))?;

        if let Some(agent_sessions) = all_sessions.get_mut(agent_id) {
            agent_sessions.remove(session_id);
        }
        Ok(())
    }

    async fn list_sessions(&self, agent_id: &str) -> Result<Vec<SessionState>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_sessions") {
            return Err(Self::fault_error("list_sessions"));
        }

        let all_sessions = self
            .sessions
            .read()
            .map_err(|_| Self::lock_error("list_sessions"))?;

        Ok(all_sessions
            .get(agent_id)
            .map(|sessions| sessions.values().cloned().collect())
            .unwrap_or_default())
    }

    // =========================================================================
    // Custom Tool Operations
    // =========================================================================

    async fn save_custom_tool(&self, tool: &CustomToolRecord) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_custom_tool") {
            return Err(Self::fault_error("save_custom_tool"));
        }

        let mut tools = self
            .custom_tools
            .write()
            .map_err(|_| Self::lock_error("save_custom_tool"))?;
        tools.insert(tool.name.clone(), tool.clone());
        Ok(())
    }

    async fn load_custom_tool(&self, name: &str) -> Result<Option<CustomToolRecord>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_custom_tool") {
            return Err(Self::fault_error("load_custom_tool"));
        }

        let tools = self
            .custom_tools
            .read()
            .map_err(|_| Self::lock_error("load_custom_tool"))?;
        Ok(tools.get(name).cloned())
    }

    async fn delete_custom_tool(&self, name: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_custom_tool") {
            return Err(Self::fault_error("delete_custom_tool"));
        }

        let mut tools = self
            .custom_tools
            .write()
            .map_err(|_| Self::lock_error("delete_custom_tool"))?;
        tools.remove(name);
        Ok(())
    }

    async fn list_custom_tools(&self) -> Result<Vec<CustomToolRecord>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_custom_tools") {
            return Err(Self::fault_error("list_custom_tools"));
        }

        let tools = self
            .custom_tools
            .read()
            .map_err(|_| Self::lock_error("list_custom_tools"))?;
        Ok(tools.values().cloned().collect())
    }

    // =========================================================================
    // Message Operations
    // =========================================================================

    async fn append_message(&self, agent_id: &str, message: &Message) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("append_message") {
            return Err(Self::fault_error("append_message"));
        }

        let mut all_messages = self
            .messages
            .write()
            .map_err(|_| Self::lock_error("append_message"))?;

        let agent_messages = all_messages.entry(agent_id.to_string()).or_default();
        agent_messages.push(message.clone());
        Ok(())
    }

    async fn load_messages(
        &self,
        agent_id: &str,
        limit: usize,
    ) -> Result<Vec<Message>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_messages") {
            return Err(Self::fault_error("load_messages"));
        }

        let all_messages = self
            .messages
            .read()
            .map_err(|_| Self::lock_error("load_messages"))?;

        let messages = all_messages
            .get(agent_id)
            .map(|msgs| {
                let start = msgs.len().saturating_sub(limit);
                msgs[start..].to_vec()
            })
            .unwrap_or_default();

        Ok(messages)
    }

    async fn load_messages_since(
        &self,
        agent_id: &str,
        since_ms: u64,
    ) -> Result<Vec<Message>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_messages_since") {
            return Err(Self::fault_error("load_messages_since"));
        }

        let all_messages = self
            .messages
            .read()
            .map_err(|_| Self::lock_error("load_messages_since"))?;

        let messages = all_messages
            .get(agent_id)
            .map(|msgs| {
                msgs.iter()
                    .filter(|m| m.created_at.timestamp_millis() as u64 > since_ms)
                    .cloned()
                    .collect()
            })
            .unwrap_or_default();

        Ok(messages)
    }

    async fn count_messages(&self, agent_id: &str) -> Result<usize, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("count_messages") {
            return Err(Self::fault_error("count_messages"));
        }

        let all_messages = self
            .messages
            .read()
            .map_err(|_| Self::lock_error("count_messages"))?;

        Ok(all_messages.get(agent_id).map(|m| m.len()).unwrap_or(0))
    }

    async fn delete_messages(&self, agent_id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_messages") {
            return Err(Self::fault_error("delete_messages"));
        }

        let mut all_messages = self
            .messages
            .write()
            .map_err(|_| Self::lock_error("delete_messages"))?;
        all_messages.remove(agent_id);
        Ok(())
    }

    // =========================================================================
    // MCP Server Operations
    // =========================================================================

    async fn save_mcp_server(&self, server: &MCPServer) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_mcp_server") {
            return Err(Self::fault_error("save_mcp_server"));
        }

        let mut servers = self
            .mcp_servers
            .write()
            .map_err(|_| Self::lock_error("save_mcp_server"))?;
        servers.insert(server.id.clone(), server.clone());
        Ok(())
    }

    async fn load_mcp_server(&self, id: &str) -> Result<Option<MCPServer>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_mcp_server") {
            return Err(Self::fault_error("load_mcp_server"));
        }

        let servers = self
            .mcp_servers
            .read()
            .map_err(|_| Self::lock_error("load_mcp_server"))?;
        Ok(servers.get(id).cloned())
    }

    async fn delete_mcp_server(&self, id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_mcp_server") {
            return Err(Self::fault_error("delete_mcp_server"));
        }

        let mut servers = self
            .mcp_servers
            .write()
            .map_err(|_| Self::lock_error("delete_mcp_server"))?;
        servers.remove(id);
        Ok(())
    }

    async fn list_mcp_servers(&self) -> Result<Vec<MCPServer>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_mcp_servers") {
            return Err(Self::fault_error("list_mcp_servers"));
        }

        let servers = self
            .mcp_servers
            .read()
            .map_err(|_| Self::lock_error("list_mcp_servers"))?;
        Ok(servers.values().cloned().collect())
    }

    // =========================================================================
    // Agent Group Operations
    // =========================================================================

    async fn save_agent_group(&self, group: &AgentGroup) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_agent_group") {
            return Err(Self::fault_error("save_agent_group"));
        }

        let mut groups = self
            .agent_groups
            .write()
            .map_err(|_| Self::lock_error("save_agent_group"))?;
        groups.insert(group.id.clone(), group.clone());
        Ok(())
    }

    async fn load_agent_group(&self, id: &str) -> Result<Option<AgentGroup>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_agent_group") {
            return Err(Self::fault_error("load_agent_group"));
        }

        let groups = self
            .agent_groups
            .read()
            .map_err(|_| Self::lock_error("load_agent_group"))?;
        Ok(groups.get(id).cloned())
    }

    async fn delete_agent_group(&self, id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_agent_group") {
            return Err(Self::fault_error("delete_agent_group"));
        }

        let mut groups = self
            .agent_groups
            .write()
            .map_err(|_| Self::lock_error("delete_agent_group"))?;
        groups.remove(id);
        Ok(())
    }

    async fn list_agent_groups(&self) -> Result<Vec<AgentGroup>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_agent_groups") {
            return Err(Self::fault_error("list_agent_groups"));
        }

        let groups = self
            .agent_groups
            .read()
            .map_err(|_| Self::lock_error("list_agent_groups"))?;
        Ok(groups.values().cloned().collect())
    }

    // =========================================================================
    // Identity Operations
    // =========================================================================

    async fn save_identity(&self, identity: &Identity) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_identity") {
            return Err(Self::fault_error("save_identity"));
        }

        let mut identities = self
            .identities
            .write()
            .map_err(|_| Self::lock_error("save_identity"))?;
        identities.insert(identity.id.clone(), identity.clone());
        Ok(())
    }

    async fn load_identity(&self, id: &str) -> Result<Option<Identity>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_identity") {
            return Err(Self::fault_error("load_identity"));
        }

        let identities = self
            .identities
            .read()
            .map_err(|_| Self::lock_error("load_identity"))?;
        Ok(identities.get(id).cloned())
    }

    async fn delete_identity(&self, id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_identity") {
            return Err(Self::fault_error("delete_identity"));
        }

        let mut identities = self
            .identities
            .write()
            .map_err(|_| Self::lock_error("delete_identity"))?;
        identities.remove(id);
        Ok(())
    }

    async fn list_identities(&self) -> Result<Vec<Identity>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_identities") {
            return Err(Self::fault_error("list_identities"));
        }

        let identities = self
            .identities
            .read()
            .map_err(|_| Self::lock_error("list_identities"))?;
        Ok(identities.values().cloned().collect())
    }

    // =========================================================================
    // Project Operations
    // =========================================================================

    async fn save_project(&self, project: &Project) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_project") {
            return Err(Self::fault_error("save_project"));
        }

        let mut projects = self
            .projects
            .write()
            .map_err(|_| Self::lock_error("save_project"))?;
        projects.insert(project.id.clone(), project.clone());
        Ok(())
    }

    async fn load_project(&self, id: &str) -> Result<Option<Project>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_project") {
            return Err(Self::fault_error("load_project"));
        }

        let projects = self
            .projects
            .read()
            .map_err(|_| Self::lock_error("load_project"))?;
        Ok(projects.get(id).cloned())
    }

    async fn delete_project(&self, id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_project") {
            return Err(Self::fault_error("delete_project"));
        }

        let mut projects = self
            .projects
            .write()
            .map_err(|_| Self::lock_error("delete_project"))?;
        projects.remove(id);
        Ok(())
    }

    async fn list_projects(&self) -> Result<Vec<Project>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_projects") {
            return Err(Self::fault_error("list_projects"));
        }

        let projects = self
            .projects
            .read()
            .map_err(|_| Self::lock_error("list_projects"))?;
        Ok(projects.values().cloned().collect())
    }

    // =========================================================================
    // Job Operations
    // =========================================================================

    async fn save_job(&self, job: &Job) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("save_job") {
            return Err(Self::fault_error("save_job"));
        }

        let mut jobs = self
            .jobs
            .write()
            .map_err(|_| Self::lock_error("save_job"))?;
        jobs.insert(job.id.clone(), job.clone());
        Ok(())
    }

    async fn load_job(&self, id: &str) -> Result<Option<Job>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("load_job") {
            return Err(Self::fault_error("load_job"));
        }

        let jobs = self.jobs.read().map_err(|_| Self::lock_error("load_job"))?;
        Ok(jobs.get(id).cloned())
    }

    async fn delete_job(&self, id: &str) -> Result<(), StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("delete_job") {
            return Err(Self::fault_error("delete_job"));
        }

        let mut jobs = self
            .jobs
            .write()
            .map_err(|_| Self::lock_error("delete_job"))?;
        jobs.remove(id);
        Ok(())
    }

    async fn list_jobs(&self) -> Result<Vec<Job>, StorageError> {
        #[cfg(feature = "dst")]
        if self.should_inject_fault("list_jobs") {
            return Err(Self::fault_error("list_jobs"));
        }

        let jobs = self
            .jobs
            .read()
            .map_err(|_| Self::lock_error("list_jobs"))?;
        Ok(jobs.values().cloned().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_sim_storage_agent_crud() {
        use crate::models::AgentType;
        let storage = SimStorage::new();

        // Create agent
        let agent = AgentMetadata {
            id: "test-agent".to_string(),
            name: "Test Agent".to_string(),
            agent_type: AgentType::MemgptAgent,
            model: Some("claude-3-opus".to_string()),
            embedding: None,
            system: Some("You are a test agent".to_string()),
            description: None,
            tool_ids: vec![],
            tags: vec![],
            metadata: serde_json::Value::Null,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };

        storage.save_agent(&agent).await.unwrap();

        // Read agent
        let loaded = storage.load_agent("test-agent").await.unwrap();
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().name, "Test Agent");

        // List agents
        let agents = storage.list_agents().await.unwrap();
        assert_eq!(agents.len(), 1);

        // Delete agent
        storage.delete_agent("test-agent").await.unwrap();
        let loaded = storage.load_agent("test-agent").await.unwrap();
        assert!(loaded.is_none());
    }

    #[tokio::test]
    async fn test_sim_storage_messages() {
        use crate::models::MessageRole;
        let storage = SimStorage::new();

        // Append messages
        let msg1 = Message {
            id: "msg-1".to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "user_message".to_string(),
            role: MessageRole::User,
            content: "Hello".to_string(),
            tool_call_id: None,
            tool_calls: vec![],
            tool_call: None,
            tool_return: None,
            status: None,
            created_at: chrono::Utc::now(),
        };

        let msg2 = Message {
            id: "msg-2".to_string(),
            agent_id: "agent-1".to_string(),
            message_type: "assistant_message".to_string(),
            role: MessageRole::Assistant,
            content: "Hi there!".to_string(),
            tool_call_id: None,
            tool_calls: vec![],
            tool_call: None,
            tool_return: None,
            status: None,
            created_at: chrono::Utc::now(),
        };

        storage.append_message("agent-1", &msg1).await.unwrap();
        storage.append_message("agent-1", &msg2).await.unwrap();

        // Load messages
        let messages = storage.load_messages("agent-1", 10).await.unwrap();
        assert_eq!(messages.len(), 2);

        // Count messages
        let count = storage.count_messages("agent-1").await.unwrap();
        assert_eq!(count, 2);

        // Delete messages
        storage.delete_messages("agent-1").await.unwrap();
        let count = storage.count_messages("agent-1").await.unwrap();
        assert_eq!(count, 0);
    }

    #[tokio::test]
    async fn test_sim_storage_cascading_delete() {
        use crate::models::AgentType;
        let storage = SimStorage::new();

        // Create agent with blocks and messages
        let agent = AgentMetadata {
            id: "agent-cascade".to_string(),
            name: "Cascade Test".to_string(),
            agent_type: AgentType::MemgptAgent,
            model: None,
            embedding: None,
            system: None,
            description: None,
            tool_ids: vec![],
            tags: vec![],
            metadata: serde_json::Value::Null,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        storage.save_agent(&agent).await.unwrap();

        // Add blocks
        let block = Block {
            id: "block-1".to_string(),
            label: "persona".to_string(),
            value: "I am a test".to_string(),
            description: None,
            limit: None,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        storage
            .save_blocks("agent-cascade", &[block])
            .await
            .unwrap();

        // Add messages
        let msg = Message {
            id: "msg-cascade".to_string(),
            agent_id: "agent-cascade".to_string(),
            message_type: "user_message".to_string(),
            role: crate::models::MessageRole::User,
            content: "Test".to_string(),
            tool_call_id: None,
            tool_calls: vec![],
            tool_call: None,
            tool_return: None,
            status: None,
            created_at: chrono::Utc::now(),
        };
        storage.append_message("agent-cascade", &msg).await.unwrap();

        // Verify data exists
        assert_eq!(storage.load_blocks("agent-cascade").await.unwrap().len(), 1);
        assert_eq!(storage.count_messages("agent-cascade").await.unwrap(), 1);

        // Delete agent - should cascade
        storage.delete_agent("agent-cascade").await.unwrap();

        // Verify all data is gone
        assert!(storage.load_agent("agent-cascade").await.unwrap().is_none());
        assert_eq!(storage.load_blocks("agent-cascade").await.unwrap().len(), 0);
        assert_eq!(storage.count_messages("agent-cascade").await.unwrap(), 0);
    }
}

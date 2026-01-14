//! Simulated agent environment for deterministic testing
//!
//! TigerStyle: High-level test harness for agent-level DST tests.

use crate::clock::SimClock;
use crate::fault::FaultInjector;
use crate::llm::{SimChatMessage, SimCompletionResponse, SimLlmClient, SimToolDefinition};
use crate::rng::DeterministicRng;
use crate::storage::SimStorage;
use std::collections::HashMap;
use std::sync::Arc;

/// Simulated agent environment for high-level DST tests
///
/// Provides a convenient interface for testing agent-level functionality
/// without requiring full server infrastructure.
pub struct SimAgentEnv {
    /// Simulated storage
    pub storage: SimStorage,
    /// Simulated LLM client
    pub llm: Arc<SimLlmClient>,
    /// Simulated clock
    pub clock: SimClock,
    /// Fault injector
    pub faults: Arc<FaultInjector>,
    /// Deterministic RNG
    pub rng: DeterministicRng,
    /// Agent metadata cache (for test assertions)
    agents: HashMap<String, AgentTestState>,
}

/// Test representation of agent state
#[derive(Debug, Clone)]
pub struct AgentTestState {
    pub id: String,
    pub name: String,
    pub agent_type: String,
    pub model: Option<String>,
    pub system: Option<String>,
    pub blocks: Vec<BlockTestState>,
    pub tool_ids: Vec<String>,
}

/// Test representation of memory block
#[derive(Debug, Clone)]
pub struct BlockTestState {
    pub label: String,
    pub value: String,
}

/// Configuration for creating a test agent
#[derive(Debug, Clone)]
pub struct AgentTestConfig {
    pub name: String,
    pub agent_type: String,
    pub model: Option<String>,
    pub system: Option<String>,
    pub blocks: Vec<BlockTestState>,
    pub tools: Vec<String>,
}

impl Default for AgentTestConfig {
    fn default() -> Self {
        Self {
            name: "test-agent".to_string(),
            agent_type: "letta_v1".to_string(),
            model: Some("test-model".to_string()),
            system: Some("You are a helpful assistant.".to_string()),
            blocks: vec![
                BlockTestState {
                    label: "persona".to_string(),
                    value: "Test persona".to_string(),
                },
                BlockTestState {
                    label: "human".to_string(),
                    value: "Test human".to_string(),
                },
            ],
            tools: vec!["shell".to_string()],
        }
    }
}

impl SimAgentEnv {
    /// Create a new simulated agent environment
    pub fn new(
        storage: SimStorage,
        llm: Arc<SimLlmClient>,
        clock: SimClock,
        faults: Arc<FaultInjector>,
        rng: DeterministicRng,
    ) -> Self {
        Self {
            storage,
            llm,
            clock,
            faults,
            rng,
            agents: HashMap::new(),
        }
    }

    /// Create a test agent (stores in cache, returns ID)
    ///
    /// This is a placeholder for Phase 3 when AgentActor is implemented.
    /// For now, it just stores the config in memory for test assertions.
    pub fn create_agent(&mut self, config: AgentTestConfig) -> Result<String, String> {
        // Generate deterministic agent ID
        let agent_id = format!("agent-{}", self.rng.next_u64());

        // Store agent state
        let state = AgentTestState {
            id: agent_id.clone(),
            name: config.name,
            agent_type: config.agent_type,
            model: config.model,
            system: config.system,
            blocks: config.blocks,
            tool_ids: config.tools,
        };

        self.agents.insert(agent_id.clone(), state);

        Ok(agent_id)
    }

    /// Send a message to an agent and get response
    ///
    /// This is a placeholder for Phase 3 when AgentActor is implemented.
    /// For now, it directly calls the LLM client.
    pub async fn send_message(
        &self,
        agent_id: &str,
        message: &str,
    ) -> Result<SimCompletionResponse, String> {
        // Get agent state
        let agent = self
            .agents
            .get(agent_id)
            .ok_or_else(|| format!("Agent not found: {}", agent_id))?;

        // Build messages
        let mut messages = vec![];

        // Add system message if present
        if let Some(system) = &agent.system {
            messages.push(SimChatMessage {
                role: "system".to_string(),
                content: system.clone(),
            });
        }

        // Add memory blocks as context
        for block in &agent.blocks {
            messages.push(SimChatMessage {
                role: "system".to_string(),
                content: format!("{}: {}", block.label, block.value),
            });
        }

        // Add user message
        messages.push(SimChatMessage {
            role: "user".to_string(),
            content: message.to_string(),
        });

        // Build tools
        let tools: Vec<SimToolDefinition> = agent
            .tool_ids
            .iter()
            .map(|name| SimToolDefinition {
                name: name.clone(),
                description: format!("Tool: {}", name),
            })
            .collect();

        // Call LLM
        self.llm.complete_with_tools(messages, tools).await
    }

    /// Get agent state for test assertions
    pub fn get_agent(&self, agent_id: &str) -> Result<AgentTestState, String> {
        self.agents
            .get(agent_id)
            .cloned()
            .ok_or_else(|| format!("Agent not found: {}", agent_id))
    }

    /// Update agent state (for testing modifications)
    pub fn update_agent(&mut self, agent_id: &str, state: AgentTestState) -> Result<(), String> {
        if !self.agents.contains_key(agent_id) {
            return Err(format!("Agent not found: {}", agent_id));
        }
        self.agents.insert(agent_id.to_string(), state);
        Ok(())
    }

    /// Delete agent
    pub fn delete_agent(&mut self, agent_id: &str) -> Result<(), String> {
        self.agents
            .remove(agent_id)
            .ok_or_else(|| format!("Agent not found: {}", agent_id))?;
        Ok(())
    }

    /// Advance simulated time
    pub fn advance_time_ms(&self, ms: u64) {
        self.clock.advance_ms(ms);
    }

    /// Get current simulated time
    pub fn now_ms(&self) -> u64 {
        self.clock.now_ms()
    }

    /// Fork RNG for independent stream
    pub fn fork_rng(&self) -> DeterministicRng {
        self.rng.fork()
    }

    /// Get list of all agent IDs (for testing)
    pub fn list_agents(&self) -> Vec<String> {
        self.agents.keys().cloned().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::FaultInjectorBuilder;

    fn create_test_env() -> SimAgentEnv {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let storage = SimStorage::new(rng.fork(), faults.clone());
        let llm = Arc::new(SimLlmClient::new(rng.fork(), faults.clone()));
        let clock = SimClock::default();

        SimAgentEnv::new(storage, llm, clock, faults, rng)
    }

    #[test]
    fn test_sim_agent_env_create_agent() {
        let mut env = create_test_env();

        let config = AgentTestConfig::default();
        let agent_id = env.create_agent(config.clone()).unwrap();

        assert!(!agent_id.is_empty());

        let agent = env.get_agent(&agent_id).unwrap();
        assert_eq!(agent.name, config.name);
        assert_eq!(agent.agent_type, config.agent_type);
    }

    #[tokio::test]
    async fn test_sim_agent_env_send_message() {
        let mut env = create_test_env();

        let config = AgentTestConfig::default();
        let agent_id = env.create_agent(config).unwrap();

        let response = env.send_message(&agent_id, "Hello").await.unwrap();

        assert!(!response.content.is_empty());
        assert!(response.prompt_tokens > 0);
    }

    #[test]
    fn test_sim_agent_env_get_agent() {
        let mut env = create_test_env();

        let config = AgentTestConfig {
            name: "test-agent".to_string(),
            agent_type: "letta_v1".to_string(),
            ..Default::default()
        };

        let agent_id = env.create_agent(config).unwrap();
        let agent = env.get_agent(&agent_id).unwrap();

        assert_eq!(agent.name, "test-agent");
        assert_eq!(agent.agent_type, "letta_v1");
    }

    #[test]
    fn test_sim_agent_env_update_agent() {
        let mut env = create_test_env();

        let config = AgentTestConfig::default();
        let agent_id = env.create_agent(config).unwrap();

        let mut agent = env.get_agent(&agent_id).unwrap();
        agent.name = "updated-name".to_string();

        env.update_agent(&agent_id, agent).unwrap();

        let updated = env.get_agent(&agent_id).unwrap();
        assert_eq!(updated.name, "updated-name");
    }

    #[test]
    fn test_sim_agent_env_delete_agent() {
        let mut env = create_test_env();

        let config = AgentTestConfig::default();
        let agent_id = env.create_agent(config).unwrap();

        env.delete_agent(&agent_id).unwrap();

        let result = env.get_agent(&agent_id);
        assert!(result.is_err());
    }

    #[test]
    fn test_sim_agent_env_list_agents() {
        let mut env = create_test_env();

        let config1 = AgentTestConfig {
            name: "agent-1".to_string(),
            ..Default::default()
        };
        let config2 = AgentTestConfig {
            name: "agent-2".to_string(),
            ..Default::default()
        };

        let _id1 = env.create_agent(config1).unwrap();
        let _id2 = env.create_agent(config2).unwrap();

        let agents = env.list_agents();
        assert_eq!(agents.len(), 2);
    }

    #[test]
    fn test_sim_agent_env_time_advancement() {
        let env = create_test_env();

        let start = env.now_ms();
        env.advance_time_ms(1000);
        let end = env.now_ms();

        assert_eq!(end - start, 1000);
    }

    #[test]
    fn test_sim_agent_env_determinism() {
        let seed = 12345;

        let create_and_run = || {
            let rng = DeterministicRng::new(seed);
            let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
            let storage = SimStorage::new(rng.fork(), faults.clone());
            let llm = Arc::new(SimLlmClient::new(rng.fork(), faults.clone()));
            let clock = SimClock::default();

            let mut env = SimAgentEnv::new(storage, llm, clock, faults, rng);

            let config = AgentTestConfig::default();
            env.create_agent(config).unwrap()
        };

        let id1 = create_and_run();
        let id2 = create_and_run();

        assert_eq!(id1, id2);
    }
}

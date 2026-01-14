//! Simulated LLM client for deterministic testing
//!
//! TigerStyle: Deterministic responses, fault injection, hash-based response generation.

use crate::fault::{FaultInjector, FaultType};
use crate::rng::DeterministicRng;
use serde_json::Value;
use std::collections::HashMap;
use std::sync::Arc;

/// Chat message for LLM simulation
#[derive(Debug, Clone)]
pub struct SimChatMessage {
    pub role: String,
    pub content: String,
}

/// Tool call from simulated LLM
#[derive(Debug, Clone)]
pub struct SimToolCall {
    pub id: String,
    pub name: String,
    pub input: Value,
}

/// Response from simulated LLM completion
#[derive(Debug, Clone)]
pub struct SimCompletionResponse {
    pub content: String,
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub tool_calls: Vec<SimToolCall>,
    pub stop_reason: String,
}

/// Tool definition for simulated LLM
#[derive(Debug, Clone)]
pub struct SimToolDefinition {
    pub name: String,
    pub description: String,
}

/// Simulated LLM client for deterministic testing
///
/// Provides deterministic, reproducible LLM responses for testing agent loops.
/// Responses are generated based on message content hash + RNG state.
pub struct SimLlmClient {
    /// Deterministic RNG for response generation
    rng: DeterministicRng,
    /// Fault injector for simulating LLM failures
    faults: Arc<FaultInjector>,
    /// Canned responses by prompt pattern
    responses: HashMap<String, String>,
    /// Tool call probability (0.0-1.0)
    tool_call_probability: f64,
}

impl SimLlmClient {
    /// Create a new simulated LLM client
    pub fn new(rng: DeterministicRng, faults: Arc<FaultInjector>) -> Self {
        Self {
            rng,
            faults,
            responses: Self::default_responses(),
            tool_call_probability: 0.3,
        }
    }

    /// Set tool call probability
    pub fn with_tool_call_probability(mut self, probability: f64) -> Self {
        assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be in [0, 1]"
        );
        self.tool_call_probability = probability;
        self
    }

    /// Add a canned response for a specific pattern
    pub fn with_response(
        mut self,
        pattern: impl Into<String>,
        response: impl Into<String>,
    ) -> Self {
        self.responses.insert(pattern.into(), response.into());
        self
    }

    /// Complete a chat conversation with optional tools
    pub async fn complete_with_tools(
        &self,
        messages: Vec<SimChatMessage>,
        tools: Vec<SimToolDefinition>,
    ) -> Result<SimCompletionResponse, String> {
        // Check for faults first
        if let Some(fault) = self.faults.should_inject("llm_complete") {
            return match fault {
                FaultType::LlmTimeout => Err("LLM request timed out".to_string()),
                FaultType::LlmFailure => Err("LLM provider error: Internal error".to_string()),
                FaultType::LlmRateLimited => {
                    Err("LLM provider error: Rate limit exceeded".to_string())
                }
                _ => Err(format!("Unexpected fault: {:?}", fault)),
            };
        }

        // Generate deterministic response
        let message_hash = self.hash_messages(&messages);
        let content = self.generate_response(&messages, message_hash);

        // Decide if we should generate tool calls
        let tool_calls = if !tools.is_empty() && self.rng.next_bool(self.tool_call_probability) {
            self.generate_tool_calls(&tools)
        } else {
            vec![]
        };

        // Calculate token counts (deterministic based on content)
        let prompt_tokens = messages.iter().map(|m| m.content.len() as u64 / 4).sum();
        let completion_tokens = content.len() as u64 / 4 + tool_calls.len() as u64 * 10;

        let stop_reason = if tool_calls.is_empty() {
            "end_turn".to_string()
        } else {
            "tool_use".to_string()
        };

        Ok(SimCompletionResponse {
            content,
            prompt_tokens,
            completion_tokens,
            tool_calls,
            stop_reason,
        })
    }

    /// Continue conversation with tool result
    pub async fn continue_with_tool_result(
        &self,
        messages: Vec<SimChatMessage>,
        _tools: Vec<SimToolDefinition>,
        _tool_results: Vec<(String, String)>, // (tool_use_id, result)
    ) -> Result<SimCompletionResponse, String> {
        // Check for faults
        if let Some(fault) = self.faults.should_inject("llm_continue") {
            return match fault {
                FaultType::LlmTimeout => Err("LLM request timed out".to_string()),
                FaultType::LlmFailure => Err("LLM provider error: Internal error".to_string()),
                FaultType::LlmRateLimited => {
                    Err("LLM provider error: Rate limit exceeded".to_string())
                }
                _ => Err(format!("Unexpected fault: {:?}", fault)),
            };
        }

        // Generate response after tool execution (usually no more tools)
        let message_hash = self.hash_messages(&messages);
        let content = self.generate_response(&messages, message_hash);

        let prompt_tokens = messages.iter().map(|m| m.content.len() as u64 / 4).sum();
        let completion_tokens = content.len() as u64 / 4;

        Ok(SimCompletionResponse {
            content,
            prompt_tokens,
            completion_tokens,
            tool_calls: vec![],
            stop_reason: "end_turn".to_string(),
        })
    }

    /// Hash messages to generate deterministic key
    fn hash_messages(&self, messages: &[SimChatMessage]) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        for msg in messages {
            msg.role.hash(&mut hasher);
            msg.content.hash(&mut hasher);
        }
        hasher.finish()
    }

    /// Generate response content based on messages
    fn generate_response(&self, messages: &[SimChatMessage], hash: u64) -> String {
        // Check for canned responses
        for msg in messages.iter().rev() {
            for (pattern, response) in &self.responses {
                if msg.content.contains(pattern) {
                    return response.clone();
                }
            }
        }

        // Default: Generate deterministic response based on hash + RNG
        let response_variants = [
            "I understand. Let me help you with that.",
            "Based on the information provided, here's what I can do.",
            "I'll process that request now.",
            "Let me analyze this for you.",
            "I can assist with that task.",
        ];

        let index = (hash as usize)
            .wrapping_add(self.rng.next_u64() as usize)
            .wrapping_rem(response_variants.len());
        response_variants[index].to_string()
    }

    /// Generate tool calls
    fn generate_tool_calls(&self, tools: &[SimToolDefinition]) -> Vec<SimToolCall> {
        if tools.is_empty() {
            return vec![];
        }

        // Pick a random tool (deterministic) - use wrapping to prevent overflow
        let tool_index = (self.rng.next_u64() as usize).wrapping_rem(tools.len());
        let tool = &tools[tool_index];

        // Generate tool call ID
        let call_id = format!("toolu_{}", self.rng.next_u64());

        // Generate simple input based on tool name
        let input = match tool.name.as_str() {
            "shell" => serde_json::json!({
                "command": "echo 'test'"
            }),
            "core_memory_append" => serde_json::json!({
                "label": "persona",
                "content": "Test content"
            }),
            "conversation_search" => serde_json::json!({
                "query": "test query"
            }),
            _ => serde_json::json!({
                "action": "test"
            }),
        };

        vec![SimToolCall {
            id: call_id,
            name: tool.name.clone(),
            input,
        }]
    }

    /// Default canned responses
    fn default_responses() -> HashMap<String, String> {
        let mut responses = HashMap::new();
        responses.insert("2+2".to_string(), "2 + 2 equals 4.".to_string());
        responses.insert(
            "hello".to_string(),
            "Hello! How can I help you today?".to_string(),
        );
        responses.insert("test".to_string(), "This is a test response.".to_string());
        responses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::{FaultConfig, FaultInjectorBuilder};

    #[tokio::test]
    async fn test_sim_llm_basic() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let client = SimLlmClient::new(rng, faults);

        let messages = vec![SimChatMessage {
            role: "user".to_string(),
            content: "What is 2+2?".to_string(),
        }];

        let response = client.complete_with_tools(messages, vec![]).await.unwrap();

        assert!(!response.content.is_empty());
        assert_eq!(response.stop_reason, "end_turn");
        assert!(response.tool_calls.is_empty());
    }

    #[tokio::test]
    async fn test_sim_llm_with_canned_response() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let client = SimLlmClient::new(rng, faults);

        let messages = vec![SimChatMessage {
            role: "user".to_string(),
            content: "What is 2+2?".to_string(),
        }];

        let response = client.complete_with_tools(messages, vec![]).await.unwrap();

        assert_eq!(response.content, "2 + 2 equals 4.");
    }

    #[tokio::test]
    async fn test_sim_llm_with_tools() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let client = SimLlmClient::new(rng, faults).with_tool_call_probability(1.0);

        let messages = vec![SimChatMessage {
            role: "user".to_string(),
            content: "Run a shell command".to_string(),
        }];

        let tools = vec![SimToolDefinition {
            name: "shell".to_string(),
            description: "Execute a shell command".to_string(),
        }];

        let response = client.complete_with_tools(messages, tools).await.unwrap();

        assert_eq!(response.stop_reason, "tool_use");
        assert_eq!(response.tool_calls.len(), 1);
        assert_eq!(response.tool_calls[0].name, "shell");
    }

    #[tokio::test]
    async fn test_sim_llm_timeout_fault() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::LlmTimeout, 1.0))
                .build(),
        );
        let client = SimLlmClient::new(rng, faults);

        let messages = vec![SimChatMessage {
            role: "user".to_string(),
            content: "test".to_string(),
        }];

        let result = client.complete_with_tools(messages, vec![]).await;
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("timed out"));
    }

    #[tokio::test]
    async fn test_sim_llm_failure_fault() {
        let rng = DeterministicRng::new(42);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::LlmFailure, 1.0))
                .build(),
        );
        let client = SimLlmClient::new(rng, faults);

        let messages = vec![SimChatMessage {
            role: "user".to_string(),
            content: "test".to_string(),
        }];

        let result = client.complete_with_tools(messages, vec![]).await;
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Internal error"));
    }

    #[tokio::test]
    async fn test_sim_llm_determinism() {
        let seed = 12345;

        let run_test = || async {
            let rng = DeterministicRng::new(seed);
            let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
            let client = SimLlmClient::new(rng, faults);

            let messages = vec![SimChatMessage {
                role: "user".to_string(),
                content: "Tell me a story".to_string(),
            }];

            client.complete_with_tools(messages, vec![]).await.unwrap()
        };

        let response1 = run_test().await;
        let response2 = run_test().await;

        assert_eq!(response1.content, response2.content);
        assert_eq!(response1.prompt_tokens, response2.prompt_tokens);
        assert_eq!(response1.completion_tokens, response2.completion_tokens);
    }
}

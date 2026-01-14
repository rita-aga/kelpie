//! LLM client trait for AgentActor
//!
//! TigerStyle: Trait abstraction allows both real LLM and SimLlmClient

use async_trait::async_trait;
use kelpie_core::Result;
use serde_json::Value;

/// Chat message for LLM
#[derive(Debug, Clone)]
pub struct LlmMessage {
    pub role: String,
    pub content: String,
}

/// Response from LLM completion
#[derive(Debug, Clone)]
pub struct LlmResponse {
    pub content: String,
    pub tool_calls: Vec<LlmToolCall>,
}

/// Tool call from LLM
#[derive(Debug, Clone)]
pub struct LlmToolCall {
    pub id: String,
    pub name: String,
    pub input: Value,
}

/// LLM client trait - abstraction over real and simulated LLM
#[async_trait]
pub trait LlmClient: Send + Sync {
    /// Complete a chat conversation
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse>;
}

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

/// Adapter to use crate::llm::LlmClient with the actor LlmClient trait
///
/// Phase 6.4: Enables production AppState to use real LLM with actor service
pub struct RealLlmAdapter {
    client: crate::llm::LlmClient,
}

impl RealLlmAdapter {
    /// Create adapter from real LLM client
    pub fn new(client: crate::llm::LlmClient) -> Self {
        Self { client }
    }
}

#[async_trait]
impl LlmClient for RealLlmAdapter {
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse> {
        // Convert actor LlmMessage to llm::ChatMessage
        let chat_messages: Vec<crate::llm::ChatMessage> = messages
            .into_iter()
            .map(|m| crate::llm::ChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();

        // Call real LLM without tools (simplified for actor invocation)
        let response = self
            .client
            .complete_with_tools(chat_messages, vec![])
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: format!("LLM completion failed: {}", e),
            })?;

        // Convert CompletionResponse to LlmResponse
        Ok(LlmResponse {
            content: response.content,
            tool_calls: response
                .tool_calls
                .into_iter()
                .map(|tc| LlmToolCall {
                    id: tc.id,
                    name: tc.name,
                    input: tc.input,
                })
                .collect(),
        })
    }
}

//! LLM client trait for AgentActor
//!
//! TigerStyle: Trait abstraction allows both real LLM and SimLlmClient

use async_trait::async_trait;
use futures::stream::{self, Stream, StreamExt};
use kelpie_core::Result;
use serde_json::Value;
use std::pin::Pin;

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

/// Stream chunk from LLM streaming (Phase 7.7)
///
/// Represents incremental pieces of LLM response as they arrive.
#[derive(Debug, Clone)]
pub enum StreamChunk {
    /// Content delta (token or partial token)
    ContentDelta { delta: String },

    /// Tool call starting
    ToolCallStart {
        id: String,
        name: String,
        input: Value,
    },

    /// Tool call argument delta (streaming tool input)
    ToolCallDelta {
        id: String,
        delta: String,
    },

    /// Stream complete
    Done { stop_reason: String },
}

/// LLM client trait - abstraction over real and simulated LLM
///
/// Phase 7.7: Extended with streaming support via stream_complete()
#[async_trait]
pub trait LlmClient: Send + Sync {
    /// Complete a chat conversation (batch mode)
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse>;

    /// Complete with streaming (Phase 7.7)
    ///
    /// Returns stream of chunks as they arrive from LLM.
    /// Default implementation converts batch complete() to stream.
    ///
    /// # Arguments
    /// * `messages` - Conversation history
    ///
    /// # Returns
    /// Stream of StreamChunk items
    ///
    /// # Errors
    /// Returns error if LLM call fails
    async fn stream_complete(
        &self,
        messages: Vec<LlmMessage>,
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>> {
        // Default: convert batch to stream for backward compatibility
        let response = self.complete(messages).await?;

        // Create stream from batch response
        let mut chunks = Vec::new();

        // Add content as single delta
        if !response.content.is_empty() {
            chunks.push(Ok(StreamChunk::ContentDelta {
                delta: response.content,
            }));
        }

        // Add tool calls as ToolCallStart chunks
        for tool_call in response.tool_calls {
            chunks.push(Ok(StreamChunk::ToolCallStart {
                id: tool_call.id,
                name: tool_call.name,
                input: tool_call.input,
            }));
        }

        // Add done chunk
        chunks.push(Ok(StreamChunk::Done {
            stop_reason: "end_turn".to_string(),
        }));

        Ok(Box::pin(stream::iter(chunks)))
    }
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

    /// Stream complete with real LLM streaming (Phase 7.8)
    ///
    /// Uses crate::llm::LlmClient.stream_complete_with_tools() for true token streaming.
    async fn stream_complete(
        &self,
        messages: Vec<LlmMessage>,
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>> {
        // Convert actor LlmMessage to llm::ChatMessage
        let chat_messages: Vec<crate::llm::ChatMessage> = messages
            .into_iter()
            .map(|m| crate::llm::ChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();

        // Call real LLM streaming without tools (simplified for actor invocation)
        let stream = self
            .client
            .stream_complete_with_tools(chat_messages, vec![])
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: format!("LLM streaming failed: {}", e),
            })?;

        // Convert StreamDelta to StreamChunk
        let chunk_stream = stream.map(|delta_result| {
            delta_result
                .map_err(|e| kelpie_core::Error::Internal {
                    message: format!("Stream error: {}", e),
                })
                .and_then(|delta| match delta {
                    crate::llm::StreamDelta::ContentDelta { text } => Ok(StreamChunk::ContentDelta {
                        delta: text,
                    }),
                    crate::llm::StreamDelta::ToolCallStart { id, name } => {
                        Ok(StreamChunk::ToolCallStart {
                            id,
                            name,
                            input: serde_json::Value::Null, // Will be filled by deltas
                        })
                    }
                    crate::llm::StreamDelta::ToolCallDelta { delta } => {
                        Ok(StreamChunk::ToolCallDelta {
                            id: "".to_string(), // TODO: track tool call ID
                            delta,
                        })
                    }
                    crate::llm::StreamDelta::Done { stop_reason } => Ok(StreamChunk::Done {
                        stop_reason,
                    }),
                })
        });

        Ok(Box::pin(chunk_stream))
    }
}

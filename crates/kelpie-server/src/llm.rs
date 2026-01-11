//! LLM client for agent message processing
//!
//! TigerStyle: Explicit configuration, OpenAI-compatible API support.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::env;

/// LLM provider configuration
#[derive(Debug, Clone)]
pub struct LlmConfig {
    /// API base URL (OpenAI-compatible)
    pub base_url: String,
    /// API key
    pub api_key: String,
    /// Model to use
    pub model: String,
    /// Max tokens in response
    pub max_tokens: u32,
}

impl LlmConfig {
    /// Create config from environment variables
    ///
    /// Supports:
    /// - OPENAI_API_KEY + OPENAI_BASE_URL (default: api.openai.com)
    /// - ANTHROPIC_API_KEY (uses Anthropic's OpenAI-compatible endpoint)
    pub fn from_env() -> Option<Self> {
        // Try Anthropic first
        if let Ok(api_key) = env::var("ANTHROPIC_API_KEY") {
            return Some(Self {
                base_url: "https://api.anthropic.com/v1".to_string(),
                api_key,
                model: env::var("KELPIE_MODEL")
                    .unwrap_or_else(|_| "claude-sonnet-4-20250514".to_string()),
                max_tokens: 1024,
            });
        }

        // Try OpenAI
        if let Ok(api_key) = env::var("OPENAI_API_KEY") {
            return Some(Self {
                base_url: env::var("OPENAI_BASE_URL")
                    .unwrap_or_else(|_| "https://api.openai.com/v1".to_string()),
                api_key,
                model: env::var("KELPIE_MODEL").unwrap_or_else(|_| "gpt-4o-mini".to_string()),
                max_tokens: 1024,
            });
        }

        None
    }

    /// Check if using Anthropic API
    pub fn is_anthropic(&self) -> bool {
        self.base_url.contains("anthropic.com")
    }
}

/// Chat message for LLM API
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatMessage {
    pub role: String,
    pub content: String,
}

/// OpenAI-compatible chat completion request
#[derive(Debug, Serialize)]
struct ChatCompletionRequest {
    model: String,
    messages: Vec<ChatMessage>,
    max_tokens: u32,
}

/// OpenAI-compatible chat completion response
#[derive(Debug, Deserialize)]
struct ChatCompletionResponse {
    choices: Vec<ChatChoice>,
    usage: Option<ApiUsage>,
}

#[derive(Debug, Deserialize)]
struct ChatChoice {
    message: ChatMessage,
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct ApiUsage {
    prompt_tokens: u64,
    completion_tokens: u64,
    total_tokens: u64,
}

/// Anthropic messages API request
#[derive(Debug, Serialize)]
struct AnthropicRequest {
    model: String,
    messages: Vec<AnthropicMessage>,
    max_tokens: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    system: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    tools: Vec<ToolDefinition>,
}

/// Anthropic message (supports tool results)
#[derive(Debug, Clone, Serialize, Deserialize)]
struct AnthropicMessage {
    role: String,
    content: AnthropicMessageContent,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
enum AnthropicMessageContent {
    Text(String),
    Blocks(Vec<AnthropicContentBlock>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnthropicContentBlock {
    #[serde(rename = "text")]
    Text { text: String },
    #[serde(rename = "tool_use")]
    ToolUse {
        id: String,
        name: String,
        input: Value,
    },
    #[serde(rename = "tool_result")]
    ToolResult {
        tool_use_id: String,
        content: String,
    },
}

/// Anthropic messages API response
#[derive(Debug, Deserialize)]
struct AnthropicResponse {
    content: Vec<AnthropicResponseContent>,
    usage: AnthropicUsage,
    stop_reason: String,
}

#[derive(Debug, Deserialize)]
struct AnthropicResponseContent {
    #[serde(rename = "type")]
    content_type: String,
    #[serde(default)]
    text: Option<String>,
    #[serde(default)]
    id: Option<String>,
    #[serde(default)]
    name: Option<String>,
    #[serde(default)]
    input: Option<Value>,
}

#[derive(Debug, Deserialize)]
struct AnthropicUsage {
    input_tokens: u64,
    output_tokens: u64,
}

/// Tool definition for LLM
#[derive(Debug, Clone, Serialize)]
pub struct ToolDefinition {
    pub name: String,
    pub description: String,
    pub input_schema: Value,
}

impl ToolDefinition {
    pub fn shell() -> Self {
        Self {
            name: "shell".to_string(),
            description: "Execute a shell command. Use this to run commands, check files, or perform system operations.".to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "command": {
                        "type": "string",
                        "description": "The shell command to execute"
                    }
                },
                "required": ["command"]
            }),
        }
    }
}

/// Tool call from LLM
#[derive(Debug, Clone, Deserialize)]
pub struct ToolCall {
    pub id: String,
    pub name: String,
    pub input: Value,
}

/// Response from LLM completion
#[derive(Debug)]
pub struct CompletionResponse {
    pub content: String,
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub tool_calls: Vec<ToolCall>,
    pub stop_reason: String,
}

/// LLM client
#[derive(Clone)]
pub struct LlmClient {
    config: LlmConfig,
    client: reqwest::Client,
}

impl LlmClient {
    /// Create a new LLM client
    pub fn new(config: LlmConfig) -> Self {
        Self {
            config,
            client: reqwest::Client::new(),
        }
    }

    /// Create from environment, returns None if no API key configured
    pub fn from_env() -> Option<Self> {
        LlmConfig::from_env().map(Self::new)
    }

    /// Complete a chat conversation (without tools)
    #[allow(dead_code)]
    pub async fn complete(&self, messages: Vec<ChatMessage>) -> Result<CompletionResponse, String> {
        self.complete_with_tools(messages, vec![]).await
    }

    /// Complete a chat conversation with tool support
    pub async fn complete_with_tools(
        &self,
        messages: Vec<ChatMessage>,
        tools: Vec<ToolDefinition>,
    ) -> Result<CompletionResponse, String> {
        if self.config.is_anthropic() {
            self.complete_anthropic(messages, tools).await
        } else {
            self.complete_openai(messages).await
        }
    }

    /// Continue conversation with tool result
    pub async fn continue_with_tool_result(
        &self,
        messages: Vec<ChatMessage>,
        tools: Vec<ToolDefinition>,
        assistant_content: Vec<AnthropicContentBlock>,
        tool_results: Vec<(String, String)>, // (tool_use_id, result)
    ) -> Result<CompletionResponse, String> {
        if !self.config.is_anthropic() {
            return Err("Tool use only supported with Anthropic API".to_string());
        }

        // Build messages with tool results
        let (system, mut anthropic_messages) = self.prepare_anthropic_messages(messages);

        // Add assistant message with tool use
        anthropic_messages.push(AnthropicMessage {
            role: "assistant".to_string(),
            content: AnthropicMessageContent::Blocks(assistant_content),
        });

        // Add tool results
        let tool_result_blocks: Vec<AnthropicContentBlock> = tool_results
            .into_iter()
            .map(|(id, result)| AnthropicContentBlock::ToolResult {
                tool_use_id: id,
                content: result,
            })
            .collect();

        anthropic_messages.push(AnthropicMessage {
            role: "user".to_string(),
            content: AnthropicMessageContent::Blocks(tool_result_blocks),
        });

        self.call_anthropic(anthropic_messages, system, tools).await
    }

    fn prepare_anthropic_messages(
        &self,
        messages: Vec<ChatMessage>,
    ) -> (Option<String>, Vec<AnthropicMessage>) {
        let mut system = None;
        let mut anthropic_messages = Vec::new();

        for msg in messages {
            if msg.role == "system" {
                system = Some(msg.content);
            } else {
                anthropic_messages.push(AnthropicMessage {
                    role: msg.role,
                    content: AnthropicMessageContent::Text(msg.content),
                });
            }
        }

        (system, anthropic_messages)
    }

    async fn complete_openai(
        &self,
        messages: Vec<ChatMessage>,
    ) -> Result<CompletionResponse, String> {
        let request = ChatCompletionRequest {
            model: self.config.model.clone(),
            messages,
            max_tokens: self.config.max_tokens,
        };

        let response = self
            .client
            .post(format!("{}/chat/completions", self.config.base_url))
            .header("Authorization", format!("Bearer {}", self.config.api_key))
            .header("Content-Type", "application/json")
            .json(&request)
            .send()
            .await
            .map_err(|e| format!("HTTP request failed: {}", e))?;

        if !response.status().is_success() {
            let status = response.status();
            let body = response.text().await.unwrap_or_default();
            return Err(format!("API error {}: {}", status, body));
        }

        let completion: ChatCompletionResponse = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse response: {}", e))?;

        let choice = completion
            .choices
            .into_iter()
            .next()
            .ok_or("No completion choices returned")?;

        let usage = completion.usage.unwrap_or(ApiUsage {
            prompt_tokens: 0,
            completion_tokens: 0,
            total_tokens: 0,
        });

        Ok(CompletionResponse {
            content: choice.message.content,
            prompt_tokens: usage.prompt_tokens,
            completion_tokens: usage.completion_tokens,
            tool_calls: vec![],
            stop_reason: "end_turn".to_string(),
        })
    }

    async fn complete_anthropic(
        &self,
        messages: Vec<ChatMessage>,
        tools: Vec<ToolDefinition>,
    ) -> Result<CompletionResponse, String> {
        let (system, anthropic_messages) = self.prepare_anthropic_messages(messages);
        self.call_anthropic(anthropic_messages, system, tools).await
    }

    async fn call_anthropic(
        &self,
        messages: Vec<AnthropicMessage>,
        system: Option<String>,
        tools: Vec<ToolDefinition>,
    ) -> Result<CompletionResponse, String> {
        let request = AnthropicRequest {
            model: self.config.model.clone(),
            messages,
            max_tokens: self.config.max_tokens,
            system,
            tools,
        };

        let response = self
            .client
            .post(format!("{}/messages", self.config.base_url))
            .header("x-api-key", &self.config.api_key)
            .header("anthropic-version", "2023-06-01")
            .header("Content-Type", "application/json")
            .json(&request)
            .send()
            .await
            .map_err(|e| format!("HTTP request failed: {}", e))?;

        if !response.status().is_success() {
            let status = response.status();
            let body = response.text().await.unwrap_or_default();
            return Err(format!("API error {}: {}", status, body));
        }

        let completion: AnthropicResponse = response
            .json()
            .await
            .map_err(|e| format!("Failed to parse response: {}", e))?;

        // Extract text content
        let content = completion
            .content
            .iter()
            .filter(|c| c.content_type == "text")
            .filter_map(|c| c.text.clone())
            .collect::<Vec<_>>()
            .join("");

        // Extract tool calls
        let tool_calls = completion
            .content
            .iter()
            .filter(|c| c.content_type == "tool_use")
            .filter_map(|c| {
                Some(ToolCall {
                    id: c.id.clone()?,
                    name: c.name.clone()?,
                    input: c.input.clone()?,
                })
            })
            .collect();

        Ok(CompletionResponse {
            content,
            prompt_tokens: completion.usage.input_tokens,
            completion_tokens: completion.usage.output_tokens,
            tool_calls,
            stop_reason: completion.stop_reason,
        })
    }
}

// Re-export for use in messages.rs
pub use self::AnthropicContentBlock as ContentBlock;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_detection() {
        // This test just verifies the code compiles and runs
        let _ = LlmConfig::from_env();
    }
}

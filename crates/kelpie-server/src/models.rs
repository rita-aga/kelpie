//! API models for Letta-compatible REST API
//!
//! TigerStyle: These models mirror Letta's API schema for compatibility.

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

// =============================================================================
// Agent Models
// =============================================================================

/// Agent type enumeration (matches Letta's agent types)
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
#[allow(clippy::enum_variant_names)] // Matches Letta's API naming
pub enum AgentType {
    #[default]
    MemgptAgent,
    LettaV1Agent,
    ReactAgent,
}

/// Request to create a new agent
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateAgentRequest {
    /// Name of the agent
    #[serde(default = "default_agent_name")]
    pub name: String,
    /// Agent type
    #[serde(default)]
    pub agent_type: AgentType,
    /// Model to use (e.g., "openai/gpt-4o")
    pub model: Option<String>,
    /// System prompt
    pub system: Option<String>,
    /// Description of the agent
    pub description: Option<String>,
    /// Initial memory blocks (inline creation)
    #[serde(default)]
    pub memory_blocks: Vec<CreateBlockRequest>,
    /// Existing block IDs to attach (letta-code compatibility)
    #[serde(default)]
    pub block_ids: Vec<String>,
    /// Tool IDs to attach
    #[serde(default)]
    pub tool_ids: Vec<String>,
    /// Tags for organization
    #[serde(default)]
    pub tags: Vec<String>,
    /// Additional metadata
    #[serde(default)]
    pub metadata: serde_json::Value,
}

fn default_agent_name() -> String {
    "Nameless Agent".to_string()
}

/// Request to update an agent
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UpdateAgentRequest {
    /// New name
    pub name: Option<String>,
    /// New system prompt
    pub system: Option<String>,
    /// New description
    pub description: Option<String>,
    /// New tags
    pub tags: Option<Vec<String>>,
    /// New metadata
    pub metadata: Option<serde_json::Value>,
}

/// Agent state response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentState {
    /// Unique identifier
    pub id: String,
    /// Agent name
    pub name: String,
    /// Agent type
    pub agent_type: AgentType,
    /// Model being used
    pub model: Option<String>,
    /// System prompt
    pub system: Option<String>,
    /// Description
    pub description: Option<String>,
    /// Memory blocks
    pub blocks: Vec<Block>,
    /// Attached tool IDs
    pub tool_ids: Vec<String>,
    /// Tags
    pub tags: Vec<String>,
    /// Metadata
    pub metadata: serde_json::Value,
    /// Creation timestamp
    pub created_at: DateTime<Utc>,
    /// Last update timestamp
    pub updated_at: DateTime<Utc>,
}

impl AgentState {
    /// Create a new agent state from a create request
    pub fn from_request(request: CreateAgentRequest) -> Self {
        let now = Utc::now();
        let id = Uuid::new_v4().to_string();

        let blocks = request
            .memory_blocks
            .into_iter()
            .map(Block::from_request)
            .collect();

        Self {
            id,
            name: request.name,
            agent_type: request.agent_type,
            model: request.model,
            system: request.system,
            description: request.description,
            blocks,
            tool_ids: request.tool_ids,
            tags: request.tags,
            metadata: request.metadata,
            created_at: now,
            updated_at: now,
        }
    }

    /// Apply an update to the agent state
    pub fn apply_update(&mut self, update: UpdateAgentRequest) {
        if let Some(name) = update.name {
            self.name = name;
        }
        if let Some(system) = update.system {
            self.system = Some(system);
        }
        if let Some(description) = update.description {
            self.description = Some(description);
        }
        if let Some(tags) = update.tags {
            self.tags = tags;
        }
        if let Some(metadata) = update.metadata {
            self.metadata = metadata;
        }
        self.updated_at = Utc::now();
    }
}

// =============================================================================
// Memory Block Models
// =============================================================================

/// Request to create a memory block
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateBlockRequest {
    /// Label for the block (e.g., "persona", "human", "task")
    pub label: String,
    /// Initial value/content
    pub value: String,
    /// Description for LLM understanding
    pub description: Option<String>,
    /// Maximum size limit
    pub limit: Option<usize>,
}

/// Request to update a memory block
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UpdateBlockRequest {
    /// New value
    pub value: Option<String>,
    /// New description
    pub description: Option<String>,
    /// New limit
    pub limit: Option<usize>,
}

/// Memory block response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Block {
    /// Unique identifier
    pub id: String,
    /// Block label
    pub label: String,
    /// Current value
    pub value: String,
    /// Description
    pub description: Option<String>,
    /// Size limit
    pub limit: Option<usize>,
    /// Creation timestamp
    pub created_at: DateTime<Utc>,
    /// Last update timestamp
    pub updated_at: DateTime<Utc>,
}

impl Block {
    /// Create a block from a create request
    pub fn from_request(request: CreateBlockRequest) -> Self {
        let now = Utc::now();
        Self {
            id: Uuid::new_v4().to_string(),
            label: request.label,
            value: request.value,
            description: request.description,
            limit: request.limit,
            created_at: now,
            updated_at: now,
        }
    }

    /// Apply an update
    pub fn apply_update(&mut self, update: UpdateBlockRequest) {
        if let Some(value) = update.value {
            self.value = value;
        }
        if let Some(description) = update.description {
            self.description = Some(description);
        }
        if let Some(limit) = update.limit {
            self.limit = Some(limit);
        }
        self.updated_at = Utc::now();
    }
}

// =============================================================================
// Message Models
// =============================================================================

/// Message role
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum MessageRole {
    User,
    Assistant,
    System,
    Tool,
}

/// Request to send a message to an agent
/// Supports multiple formats for letta-code compatibility
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateMessageRequest {
    /// Message role (defaults to "user" if not provided)
    #[serde(default = "default_role")]
    pub role: MessageRole,
    /// Message content - supports both "content" and "text" field names
    #[serde(alias = "text", default)]
    pub content: String,
    /// Optional tool call ID (for tool responses)
    pub tool_call_id: Option<String>,
    /// Optional messages array (letta-code sends this format)
    /// If provided, takes precedence over content field
    pub messages: Option<Vec<LettaMessage>>,
    /// Optional message field (another letta-code format)
    #[serde(alias = "message")]
    pub msg: Option<String>,
}

fn default_role() -> MessageRole {
    MessageRole::User
}

/// Letta message format (used in messages array)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LettaMessage {
    /// Role (user, assistant, system, tool)
    #[serde(default = "default_role")]
    pub role: MessageRole,
    /// Content - can be string or array of content blocks
    #[serde(default, deserialize_with = "deserialize_content")]
    pub content: Option<String>,
    /// Alternative text field
    pub text: Option<String>,
}

/// Deserialize content that can be either a string or an array of content blocks
fn deserialize_content<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de::{self, Visitor};
    use std::fmt;

    struct ContentVisitor;

    impl<'de> Visitor<'de> for ContentVisitor {
        type Value = Option<String>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a string or an array of content blocks")
        }

        fn visit_none<E>(self) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(None)
        }

        fn visit_unit<E>(self) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(None)
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(Some(value.to_string()))
        }

        fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(Some(value))
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: de::SeqAccess<'de>,
        {
            // Content is an array of content blocks, extract text from them
            let mut texts = Vec::new();
            while let Some(block) = seq.next_element::<serde_json::Value>()? {
                // Extract text from content block
                if let Some(text) = block.get("text").and_then(|t| t.as_str()) {
                    texts.push(text.to_string());
                }
            }
            if texts.is_empty() {
                Ok(None)
            } else {
                Ok(Some(texts.join("\n")))
            }
        }
    }

    deserializer.deserialize_any(ContentVisitor)
}

impl LettaMessage {
    /// Get the effective text content from either content or text field
    pub fn get_text(&self) -> Option<&str> {
        self.content.as_deref().or(self.text.as_deref())
    }
}

impl CreateMessageRequest {
    /// Get the effective content and role from the request
    /// Handles multiple formats for letta-code compatibility
    pub fn effective_content(&self) -> Option<(MessageRole, String)> {
        // If messages array provided, use first message with content
        if let Some(ref msgs) = self.messages {
            for msg in msgs {
                if let Some(text) = msg.get_text() {
                    if !text.is_empty() {
                        return Some((msg.role.clone(), text.to_string()));
                    }
                }
            }
        }
        // Check msg field
        if let Some(ref msg) = self.msg {
            if !msg.is_empty() {
                return Some((self.role.clone(), msg.clone()));
            }
        }
        // Fall back to direct content
        if !self.content.is_empty() {
            return Some((self.role.clone(), self.content.clone()));
        }
        None
    }
}

/// Message response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    /// Unique identifier
    pub id: String,
    /// Agent ID
    pub agent_id: String,
    /// Message role
    pub role: MessageRole,
    /// Message content
    pub content: String,
    /// Tool call ID if this is a tool response
    pub tool_call_id: Option<String>,
    /// Tool calls made by assistant
    pub tool_calls: Option<Vec<ToolCall>>,
    /// Creation timestamp
    pub created_at: DateTime<Utc>,
}

/// Tool call in a message
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolCall {
    /// Tool call ID
    pub id: String,
    /// Tool name
    pub name: String,
    /// Tool arguments as JSON
    pub arguments: serde_json::Value,
}

/// Response from sending a message
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessageResponse {
    /// Messages generated (may include multiple for tool use)
    pub messages: Vec<Message>,
    /// Usage statistics
    pub usage: Option<UsageStats>,
    /// Stop reason (for letta-code compatibility)
    #[serde(default = "default_stop_reason")]
    pub stop_reason: String,
}

fn default_stop_reason() -> String {
    "end_turn".to_string()
}

/// Token usage statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UsageStats {
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub total_tokens: u64,
}

// =============================================================================
// Tool Models
// =============================================================================

/// Tool definition (reserved for future LLM tool integration)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ToolDefinition {
    /// Unique identifier
    pub id: String,
    /// Tool name
    pub name: String,
    /// Description for LLM
    pub description: String,
    /// JSON schema for parameters
    pub parameters: serde_json::Value,
    /// Whether this is a built-in tool
    pub builtin: bool,
}

// =============================================================================
// API Response Wrappers
// =============================================================================

/// List response with pagination
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ListResponse<T> {
    /// Items in this page
    pub items: Vec<T>,
    /// Total count
    pub total: usize,
    /// Cursor for next page
    pub cursor: Option<String>,
}

/// Error response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorResponse {
    /// Error code
    pub code: String,
    /// Human-readable message
    pub message: String,
    /// Additional details
    pub details: Option<serde_json::Value>,
}

impl ErrorResponse {
    pub fn new(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            message: message.into(),
            details: None,
        }
    }

    pub fn not_found(resource: &str, id: &str) -> Self {
        Self::new(
            "not_found",
            format!("{} with id '{}' not found", resource, id),
        )
    }

    pub fn bad_request(message: impl Into<String>) -> Self {
        Self::new("bad_request", message)
    }

    pub fn internal(message: impl Into<String>) -> Self {
        Self::new("internal_error", message)
    }
}

// =============================================================================
// Health Check
// =============================================================================

/// Health check response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthResponse {
    pub status: String,
    pub version: String,
    pub uptime_seconds: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_agent_state() {
        let request = CreateAgentRequest {
            name: "test-agent".to_string(),
            agent_type: AgentType::LettaV1Agent,
            model: Some("openai/gpt-4o".to_string()),
            system: Some("You are a helpful assistant.".to_string()),
            description: Some("A test agent".to_string()),
            memory_blocks: vec![CreateBlockRequest {
                label: "persona".to_string(),
                value: "I am a helpful AI.".to_string(),
                description: Some("Agent persona".to_string()),
                limit: Some(1000),
            }],
            block_ids: vec![],
            tool_ids: vec![],
            tags: vec!["test".to_string()],
            metadata: serde_json::json!({}),
        };

        let state = AgentState::from_request(request);
        assert_eq!(state.name, "test-agent");
        assert_eq!(state.blocks.len(), 1);
        assert_eq!(state.blocks[0].label, "persona");
    }

    #[test]
    fn test_update_agent() {
        let request = CreateAgentRequest {
            name: "test-agent".to_string(),
            agent_type: AgentType::default(),
            model: None,
            system: None,
            description: None,
            memory_blocks: vec![],
            block_ids: vec![],
            tool_ids: vec![],
            tags: vec![],
            metadata: serde_json::json!({}),
        };

        let mut state = AgentState::from_request(request);
        let original_updated_at = state.updated_at;

        // Small delay to ensure timestamp changes
        std::thread::sleep(std::time::Duration::from_millis(10));

        state.apply_update(UpdateAgentRequest {
            name: Some("updated-agent".to_string()),
            description: Some("Updated description".to_string()),
            ..Default::default()
        });

        assert_eq!(state.name, "updated-agent");
        assert_eq!(state.description, Some("Updated description".to_string()));
        assert!(state.updated_at > original_updated_at);
    }

    #[test]
    fn test_error_response() {
        let err = ErrorResponse::not_found("Agent", "abc123");
        assert_eq!(err.code, "not_found");
        assert!(err.message.contains("abc123"));
    }
}

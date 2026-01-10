//! Tool traits and core abstractions
//!
//! TigerStyle: Explicit tool interface with typed parameters.

use crate::error::ToolResult;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::time::Duration;

/// Default tool execution timeout (30 seconds)
pub const TOOL_TIMEOUT_MS_DEFAULT: u64 = 30_000;

/// Maximum tool output size (1MB)
#[allow(dead_code)]
pub const TOOL_OUTPUT_SIZE_BYTES_MAX: usize = 1024 * 1024;

/// Tool parameter type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ParamType {
    /// String value
    String,
    /// Integer value
    Integer,
    /// Floating point value
    Number,
    /// Boolean value
    Boolean,
    /// Array of values
    Array,
    /// Object/map of values
    Object,
}

impl std::fmt::Display for ParamType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamType::String => write!(f, "string"),
            ParamType::Integer => write!(f, "integer"),
            ParamType::Number => write!(f, "number"),
            ParamType::Boolean => write!(f, "boolean"),
            ParamType::Array => write!(f, "array"),
            ParamType::Object => write!(f, "object"),
        }
    }
}

/// Tool parameter definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolParam {
    /// Parameter name
    pub name: String,
    /// Parameter type
    pub param_type: ParamType,
    /// Whether the parameter is required
    pub required: bool,
    /// Description of the parameter
    pub description: String,
    /// Default value (if any)
    pub default: Option<Value>,
    /// Allowed values (enum constraint)
    pub enum_values: Option<Vec<Value>>,
}

impl ToolParam {
    /// Create a new required string parameter
    pub fn string(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            param_type: ParamType::String,
            required: true,
            description: description.into(),
            default: None,
            enum_values: None,
        }
    }

    /// Create a new required integer parameter
    pub fn integer(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            param_type: ParamType::Integer,
            required: true,
            description: description.into(),
            default: None,
            enum_values: None,
        }
    }

    /// Create a new required boolean parameter
    pub fn boolean(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            param_type: ParamType::Boolean,
            required: true,
            description: description.into(),
            default: None,
            enum_values: None,
        }
    }

    /// Make this parameter optional
    pub fn optional(mut self) -> Self {
        self.required = false;
        self
    }

    /// Set a default value
    pub fn with_default(mut self, default: impl Into<Value>) -> Self {
        self.default = Some(default.into());
        self.required = false;
        self
    }

    /// Set allowed values (enum constraint)
    pub fn with_enum(mut self, values: Vec<Value>) -> Self {
        self.enum_values = Some(values);
        self
    }
}

/// Tool capability flags
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToolCapability {
    /// Tool requires network access
    pub requires_network: bool,
    /// Tool requires filesystem access
    pub requires_filesystem: bool,
    /// Tool can modify state
    pub can_modify_state: bool,
    /// Tool execution is deterministic
    pub is_deterministic: bool,
    /// Tool is safe to run without confirmation
    pub is_safe: bool,
}

impl ToolCapability {
    /// Create capabilities for a read-only, safe tool
    pub fn read_only() -> Self {
        Self {
            requires_network: false,
            requires_filesystem: true,
            can_modify_state: false,
            is_deterministic: true,
            is_safe: true,
        }
    }

    /// Create capabilities for a tool that can modify state
    pub fn read_write() -> Self {
        Self {
            requires_network: false,
            requires_filesystem: true,
            can_modify_state: true,
            is_deterministic: false,
            is_safe: false,
        }
    }

    /// Create capabilities for a network tool
    pub fn network() -> Self {
        Self {
            requires_network: true,
            requires_filesystem: false,
            can_modify_state: false,
            is_deterministic: false,
            is_safe: false,
        }
    }
}

impl Default for ToolCapability {
    fn default() -> Self {
        Self::read_only()
    }
}

/// Metadata about a tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolMetadata {
    /// Unique tool name
    pub name: String,
    /// Human-readable description
    pub description: String,
    /// Tool version
    pub version: String,
    /// Tool parameters
    pub parameters: Vec<ToolParam>,
    /// Tool capabilities
    pub capabilities: ToolCapability,
    /// Execution timeout in milliseconds
    pub timeout_ms: u64,
}

impl ToolMetadata {
    /// Create new tool metadata
    pub fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            version: "1.0.0".to_string(),
            parameters: Vec::new(),
            capabilities: ToolCapability::default(),
            timeout_ms: TOOL_TIMEOUT_MS_DEFAULT,
        }
    }

    /// Add a parameter
    pub fn with_param(mut self, param: ToolParam) -> Self {
        self.parameters.push(param);
        self
    }

    /// Set capabilities
    pub fn with_capabilities(mut self, capabilities: ToolCapability) -> Self {
        self.capabilities = capabilities;
        self
    }

    /// Set timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout_ms = timeout.as_millis() as u64;
        self
    }

    /// Set version
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = version.into();
        self
    }

    /// Get a parameter by name
    pub fn get_param(&self, name: &str) -> Option<&ToolParam> {
        self.parameters.iter().find(|p| p.name == name)
    }

    /// Check if a parameter is required
    pub fn is_param_required(&self, name: &str) -> bool {
        self.get_param(name).map(|p| p.required).unwrap_or(false)
    }
}

/// Input to a tool execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolInput {
    /// Tool name
    pub tool_name: String,
    /// Parameters as key-value pairs
    pub params: HashMap<String, Value>,
    /// Optional context (e.g., working directory, environment)
    pub context: HashMap<String, Value>,
}

impl ToolInput {
    /// Create a new tool input
    pub fn new(tool_name: impl Into<String>) -> Self {
        Self {
            tool_name: tool_name.into(),
            params: HashMap::new(),
            context: HashMap::new(),
        }
    }

    /// Add a parameter
    pub fn with_param(mut self, name: impl Into<String>, value: impl Into<Value>) -> Self {
        self.params.insert(name.into(), value.into());
        self
    }

    /// Add context
    pub fn with_context(mut self, key: impl Into<String>, value: impl Into<Value>) -> Self {
        self.context.insert(key.into(), value.into());
        self
    }

    /// Get a string parameter
    pub fn get_string(&self, name: &str) -> Option<&str> {
        self.params.get(name).and_then(|v| v.as_str())
    }

    /// Get an integer parameter
    pub fn get_i64(&self, name: &str) -> Option<i64> {
        self.params.get(name).and_then(|v| v.as_i64())
    }

    /// Get a boolean parameter
    pub fn get_bool(&self, name: &str) -> Option<bool> {
        self.params.get(name).and_then(|v| v.as_bool())
    }

    /// Get an array parameter
    pub fn get_array(&self, name: &str) -> Option<&Vec<Value>> {
        self.params.get(name).and_then(|v| v.as_array())
    }

    /// Check if a parameter exists
    pub fn has_param(&self, name: &str) -> bool {
        self.params.contains_key(name)
    }
}

/// Output from a tool execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolOutput {
    /// Whether execution was successful
    pub success: bool,
    /// Result data (on success)
    pub result: Option<Value>,
    /// Error message (on failure)
    pub error: Option<String>,
    /// Execution duration in milliseconds
    pub duration_ms: u64,
    /// Additional metadata from execution
    pub metadata: HashMap<String, Value>,
}

impl ToolOutput {
    /// Create a successful output
    pub fn success(result: impl Into<Value>) -> Self {
        Self {
            success: true,
            result: Some(result.into()),
            error: None,
            duration_ms: 0,
            metadata: HashMap::new(),
        }
    }

    /// Create a failed output
    pub fn failure(error: impl Into<String>) -> Self {
        Self {
            success: false,
            result: None,
            error: Some(error.into()),
            duration_ms: 0,
            metadata: HashMap::new(),
        }
    }

    /// Set duration
    pub fn with_duration(mut self, duration_ms: u64) -> Self {
        self.duration_ms = duration_ms;
        self
    }

    /// Add metadata
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<Value>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Check if execution was successful
    pub fn is_success(&self) -> bool {
        self.success
    }

    /// Get the result as a string
    pub fn result_string(&self) -> Option<String> {
        self.result.as_ref().map(|v| {
            if let Some(s) = v.as_str() {
                s.to_string()
            } else {
                v.to_string()
            }
        })
    }
}

/// Core trait for tools
///
/// Tools are callable units that perform specific actions.
/// They can be built-in or discovered via MCP.
#[async_trait]
pub trait Tool: Send + Sync {
    /// Get tool metadata
    fn metadata(&self) -> &ToolMetadata;

    /// Get tool name (convenience method)
    fn name(&self) -> &str {
        &self.metadata().name
    }

    /// Validate input parameters
    fn validate(&self, input: &ToolInput) -> ToolResult<()> {
        let metadata = self.metadata();

        // Check required parameters
        for param in &metadata.parameters {
            if param.required && !input.has_param(&param.name) {
                return Err(crate::error::ToolError::MissingParameter {
                    tool: metadata.name.clone(),
                    param: param.name.clone(),
                });
            }
        }

        Ok(())
    }

    /// Execute the tool with the given input
    async fn execute(&self, input: ToolInput) -> ToolResult<ToolOutput>;
}

/// Type-erased tool for dynamic dispatch
pub type DynTool = Box<dyn Tool>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tool_param_string() {
        let param = ToolParam::string("name", "A name parameter");
        assert_eq!(param.name, "name");
        assert_eq!(param.param_type, ParamType::String);
        assert!(param.required);
    }

    #[test]
    fn test_tool_param_optional() {
        let param = ToolParam::string("name", "A name").optional();
        assert!(!param.required);
    }

    #[test]
    fn test_tool_param_with_default() {
        let param = ToolParam::string("name", "A name").with_default("default");
        assert!(!param.required);
        assert_eq!(param.default, Some(Value::String("default".to_string())));
    }

    #[test]
    fn test_tool_metadata_builder() {
        let metadata = ToolMetadata::new("test-tool", "A test tool")
            .with_param(ToolParam::string("input", "Input text"))
            .with_capabilities(ToolCapability::read_only())
            .with_timeout(Duration::from_secs(60));

        assert_eq!(metadata.name, "test-tool");
        assert_eq!(metadata.parameters.len(), 1);
        assert_eq!(metadata.timeout_ms, 60_000);
    }

    #[test]
    fn test_tool_input_builder() {
        let input = ToolInput::new("shell")
            .with_param("command", "ls -la")
            .with_param("timeout", 5000)
            .with_context("workdir", "/tmp");

        assert_eq!(input.tool_name, "shell");
        assert_eq!(input.get_string("command"), Some("ls -la"));
        assert_eq!(input.get_i64("timeout"), Some(5000));
    }

    #[test]
    fn test_tool_output_success() {
        let output = ToolOutput::success("result data").with_duration(100);

        assert!(output.is_success());
        assert_eq!(output.duration_ms, 100);
        assert!(output.result_string().is_some());
    }

    #[test]
    fn test_tool_output_failure() {
        let output = ToolOutput::failure("something went wrong");

        assert!(!output.is_success());
        assert_eq!(output.error, Some("something went wrong".to_string()));
    }

    #[test]
    fn test_tool_capability_presets() {
        let read_only = ToolCapability::read_only();
        assert!(!read_only.can_modify_state);
        assert!(read_only.is_safe);

        let read_write = ToolCapability::read_write();
        assert!(read_write.can_modify_state);
        assert!(!read_write.is_safe);

        let network = ToolCapability::network();
        assert!(network.requires_network);
        assert!(!network.requires_filesystem);
    }

    #[test]
    fn test_param_type_display() {
        assert_eq!(ParamType::String.to_string(), "string");
        assert_eq!(ParamType::Integer.to_string(), "integer");
        assert_eq!(ParamType::Boolean.to_string(), "boolean");
    }
}

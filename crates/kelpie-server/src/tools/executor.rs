//! Custom Tool Executor
//!
//! TigerStyle: Unified executor for custom tools with sandbox isolation.
//!
//! Supports multiple languages/runtimes:
//! - Python (via ProcessSandbox)
//! - JavaScript/Node (via ProcessSandbox)
//! - Shell/Bash (via ProcessSandbox)
//! - WASM (via WasmRuntime)

use kelpie_sandbox::{
    ExecOptions, PoolConfig, ProcessSandbox, ProcessSandboxFactory, Sandbox, SandboxConfig,
    SandboxPool,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

// =============================================================================
// TigerStyle Constants
// =============================================================================

/// Maximum source code size in bytes
pub const EXECUTOR_SOURCE_CODE_BYTES_MAX: usize = 1_000_000; // 1MB

/// Maximum output size in bytes
pub const EXECUTOR_OUTPUT_BYTES_MAX: usize = 1_000_000; // 1MB

/// Default execution timeout in milliseconds
pub const EXECUTOR_TIMEOUT_MS_DEFAULT: u64 = 30_000;

/// Maximum execution timeout in milliseconds
pub const EXECUTOR_TIMEOUT_MS_MAX: u64 = 300_000; // 5 minutes

/// Maximum concurrent tool executions
pub const EXECUTOR_CONCURRENT_EXECUTIONS_MAX: usize = 10;

// =============================================================================
// Tool Language
// =============================================================================

/// Language/runtime for custom tool execution
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ToolLanguage {
    Python,
    JavaScript,
    Shell,
    Wasm,
}

impl ToolLanguage {
    /// Get the interpreter command for this language
    pub fn interpreter(&self) -> Option<&'static str> {
        match self {
            ToolLanguage::Python => Some("python3"),
            ToolLanguage::JavaScript => Some("node"),
            ToolLanguage::Shell => Some("bash"),
            ToolLanguage::Wasm => None, // WASM doesn't use an interpreter
        }
    }

    /// Get file extension for this language
    pub fn file_extension(&self) -> &'static str {
        match self {
            ToolLanguage::Python => "py",
            ToolLanguage::JavaScript => "js",
            ToolLanguage::Shell => "sh",
            ToolLanguage::Wasm => "wasm",
        }
    }
}

impl std::fmt::Display for ToolLanguage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToolLanguage::Python => write!(f, "python"),
            ToolLanguage::JavaScript => write!(f, "javascript"),
            ToolLanguage::Shell => write!(f, "shell"),
            ToolLanguage::Wasm => write!(f, "wasm"),
        }
    }
}

// =============================================================================
// Custom Tool Definition
// =============================================================================

/// Extended custom tool definition with language support
#[derive(Debug, Clone)]
pub struct ExtendedToolDefinition {
    /// Tool name
    pub name: String,
    /// Tool description
    pub description: String,
    /// Input schema (JSON Schema)
    pub input_schema: Value,
    /// Source code
    pub source_code: String,
    /// Language/runtime
    pub language: ToolLanguage,
    /// WASM module bytes (only for WASM tools)
    pub wasm_bytes: Option<Vec<u8>>,
    /// Dependencies/requirements
    pub requirements: Vec<String>,
    /// Environment variables to set
    pub env: HashMap<String, String>,
    /// Timeout in milliseconds
    pub timeout_ms: u64,
}

impl ExtendedToolDefinition {
    /// Create a new tool definition
    pub fn new(
        name: impl Into<String>,
        description: impl Into<String>,
        language: ToolLanguage,
        source_code: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            input_schema: serde_json::json!({"type": "object"}),
            source_code: source_code.into(),
            language,
            wasm_bytes: None,
            requirements: Vec::new(),
            env: HashMap::new(),
            timeout_ms: EXECUTOR_TIMEOUT_MS_DEFAULT,
        }
    }

    /// Set input schema
    pub fn with_schema(mut self, schema: Value) -> Self {
        self.input_schema = schema;
        self
    }

    /// Add a requirement
    pub fn with_requirement(mut self, req: impl Into<String>) -> Self {
        self.requirements.push(req.into());
        self
    }

    /// Set WASM bytes
    pub fn with_wasm_bytes(mut self, bytes: Vec<u8>) -> Self {
        self.wasm_bytes = Some(bytes);
        self
    }

    /// Set timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout_ms = timeout.as_millis() as u64;
        self
    }

    /// Add environment variable
    pub fn with_env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.env.insert(key.into(), value.into());
        self
    }
}

// =============================================================================
// Execution Result
// =============================================================================

/// Result of tool execution
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    /// Output from the tool
    pub output: String,
    /// Whether execution succeeded
    pub success: bool,
    /// Execution time in milliseconds
    pub duration_ms: u64,
    /// Error message if failed
    pub error: Option<String>,
}

impl ExecutionResult {
    /// Create a successful result
    pub fn success(output: impl Into<String>, duration_ms: u64) -> Self {
        Self {
            output: output.into(),
            success: true,
            duration_ms,
            error: None,
        }
    }

    /// Create a failed result
    pub fn failure(error: impl Into<String>, duration_ms: u64) -> Self {
        let error_str = error.into();
        Self {
            output: error_str.clone(),
            success: false,
            duration_ms,
            error: Some(error_str),
        }
    }
}

// =============================================================================
// Tool Executor
// =============================================================================

/// Executor for custom tools with sandbox isolation
pub struct ToolExecutor {
    /// Sandbox pool for process-based execution
    sandbox_pool: Option<Arc<SandboxPool<ProcessSandboxFactory>>>,
    /// WASM runtime for WASM tools
    #[cfg(feature = "wasm")]
    wasm_runtime: Option<Arc<kelpie_wasm::WasmRuntime>>,
    /// Execution statistics
    stats: RwLock<ExecutorStats>,
}

/// Executor statistics
#[derive(Debug, Clone, Default)]
pub struct ExecutorStats {
    pub total_executions: u64,
    pub successful_executions: u64,
    pub failed_executions: u64,
    pub executions_by_language: HashMap<String, u64>,
}

impl ToolExecutor {
    /// Create a new tool executor without sandbox pool
    pub fn new() -> Self {
        Self {
            sandbox_pool: None,
            #[cfg(feature = "wasm")]
            wasm_runtime: None,
            stats: RwLock::new(ExecutorStats::default()),
        }
    }

    /// Create with a sandbox pool for process-based execution
    pub fn with_sandbox_pool(mut self, pool: Arc<SandboxPool<ProcessSandboxFactory>>) -> Self {
        self.sandbox_pool = Some(pool);
        self
    }

    /// Create with WASM runtime
    #[cfg(feature = "wasm")]
    pub fn with_wasm_runtime(mut self, runtime: Arc<kelpie_wasm::WasmRuntime>) -> Self {
        self.wasm_runtime = Some(runtime);
        self
    }

    /// Execute a custom tool
    pub async fn execute(&self, tool: &ExtendedToolDefinition, input: &Value) -> ExecutionResult {
        let start = std::time::Instant::now();

        // TigerStyle: Validate inputs
        assert!(!tool.name.is_empty(), "tool name cannot be empty");
        assert!(
            tool.source_code.len() <= EXECUTOR_SOURCE_CODE_BYTES_MAX,
            "source code exceeds maximum size"
        );
        assert!(
            tool.timeout_ms <= EXECUTOR_TIMEOUT_MS_MAX,
            "timeout exceeds maximum"
        );

        let result = match tool.language {
            ToolLanguage::Python => self.execute_python(tool, input).await,
            ToolLanguage::JavaScript => self.execute_javascript(tool, input).await,
            ToolLanguage::Shell => self.execute_shell(tool, input).await,
            ToolLanguage::Wasm => self.execute_wasm(tool, input).await,
        };

        // Update stats
        {
            let mut stats = self.stats.write().await;
            stats.total_executions += 1;
            if result.success {
                stats.successful_executions += 1;
            } else {
                stats.failed_executions += 1;
            }
            *stats
                .executions_by_language
                .entry(tool.language.to_string())
                .or_insert(0) += 1;
        }

        // Validate output size
        if result.output.len() > EXECUTOR_OUTPUT_BYTES_MAX {
            let duration = start.elapsed().as_millis() as u64;
            return ExecutionResult::failure(
                format!(
                    "Output too large: {} bytes (max: {} bytes)",
                    result.output.len(),
                    EXECUTOR_OUTPUT_BYTES_MAX
                ),
                duration,
            );
        }

        result
    }

    /// Execute Python tool
    async fn execute_python(
        &self,
        tool: &ExtendedToolDefinition,
        input: &Value,
    ) -> ExecutionResult {
        let start = std::time::Instant::now();

        // Build Python wrapper script
        let mut script = String::new();
        script.push_str("import json\nimport sys\n\n");
        script.push_str(&tool.source_code);
        script.push_str("\n\n");
        script.push_str("def _kelpie_call(args):\n");
        script.push_str(&format!("    fn = globals().get(\"{}\")\n", tool.name));
        script.push_str("    if fn is None:\n");
        script.push_str(&format!(
            "        raise RuntimeError(\"Tool function '{}' not found\")\n",
            tool.name
        ));
        script.push_str("    if isinstance(args, dict):\n");
        script.push_str("        try:\n");
        script.push_str("            return fn(**args)\n");
        script.push_str("        except TypeError:\n");
        script.push_str("            return fn(args)\n");
        script.push_str("    return fn(args)\n\n");
        script.push_str("def _kelpie_main():\n");
        script.push_str("    payload = sys.stdin.read()\n");
        script.push_str("    args = json.loads(payload) if payload else {}\n");
        script.push_str("    result = _kelpie_call(args)\n");
        script.push_str("    if not isinstance(result, str):\n");
        script.push_str("        try:\n");
        script.push_str("            result = json.dumps(result)\n");
        script.push_str("        except Exception:\n");
        script.push_str("            result = str(result)\n");
        script.push_str("    sys.stdout.write(result)\n\n");
        script.push_str("if __name__ == \"__main__\":\n");
        script.push_str("    _kelpie_main()\n");

        self.execute_in_sandbox("python3", &["-c", &script], tool, input, start)
            .await
    }

    /// Execute JavaScript tool
    async fn execute_javascript(
        &self,
        tool: &ExtendedToolDefinition,
        input: &Value,
    ) -> ExecutionResult {
        let start = std::time::Instant::now();

        // Build JavaScript wrapper script
        let mut script = String::new();
        script.push_str(&tool.source_code);
        script.push_str("\n\n");
        script.push_str("(async function() {\n");
        script.push_str("  let input = '';\n");
        script.push_str("  process.stdin.setEncoding('utf8');\n");
        script.push_str("  for await (const chunk of process.stdin) {\n");
        script.push_str("    input += chunk;\n");
        script.push_str("  }\n");
        script.push_str("  const args = input ? JSON.parse(input) : {};\n");
        script.push_str(&format!(
            "  const fn = typeof {} === 'function' ? {} : null;\n",
            tool.name, tool.name
        ));
        script.push_str("  if (!fn) {\n");
        script.push_str(&format!(
            "    throw new Error(\"Tool function '{}' not found\");\n",
            tool.name
        ));
        script.push_str("  }\n");
        script.push_str("  let result = await fn(args);\n");
        script.push_str("  if (typeof result !== 'string') {\n");
        script.push_str("    result = JSON.stringify(result);\n");
        script.push_str("  }\n");
        script.push_str("  process.stdout.write(result);\n");
        script.push_str("})();\n");

        self.execute_in_sandbox("node", &["-e", &script], tool, input, start)
            .await
    }

    /// Execute Shell tool
    async fn execute_shell(&self, tool: &ExtendedToolDefinition, input: &Value) -> ExecutionResult {
        let start = std::time::Instant::now();

        // Build shell wrapper
        let mut script = String::new();
        script.push_str("#!/bin/bash\n");
        script.push_str("set -e\n\n");

        // Export input as environment variables if it's an object
        if let Some(obj) = input.as_object() {
            for (key, value) in obj {
                let val_str = match value {
                    Value::String(s) => s.clone(),
                    _ => value.to_string(),
                };
                // Escape single quotes for bash
                let escaped = val_str.replace('\'', "'\\''");
                script.push_str(&format!(
                    "export TOOL_{}='{}'\n",
                    key.to_uppercase(),
                    escaped
                ));
            }
        }

        script.push('\n');
        script.push_str(&tool.source_code);

        self.execute_in_sandbox("bash", &["-c", &script], tool, input, start)
            .await
    }

    /// Execute WASM tool
    #[allow(unused_variables)]
    async fn execute_wasm(&self, tool: &ExtendedToolDefinition, input: &Value) -> ExecutionResult {
        let start = std::time::Instant::now();

        #[cfg(feature = "wasm")]
        {
            let wasm_bytes = match &tool.wasm_bytes {
                Some(bytes) => bytes.clone(),
                None => {
                    return ExecutionResult::failure(
                        "WASM tool missing wasm_bytes",
                        start.elapsed().as_millis() as u64,
                    );
                }
            };

            let runtime = match &self.wasm_runtime {
                Some(rt) => Arc::clone(rt),
                None => {
                    return ExecutionResult::failure(
                        "WASM runtime not configured",
                        start.elapsed().as_millis() as u64,
                    );
                }
            };

            match runtime.execute(&wasm_bytes, input.clone()).await {
                Ok(output) => ExecutionResult::success(output, start.elapsed().as_millis() as u64),
                Err(e) => {
                    ExecutionResult::failure(e.to_string(), start.elapsed().as_millis() as u64)
                }
            }
        }

        #[cfg(not(feature = "wasm"))]
        {
            ExecutionResult::failure(
                "WASM support not enabled (compile with --features wasm)",
                start.elapsed().as_millis() as u64,
            )
        }
    }

    /// Execute command in sandbox
    async fn execute_in_sandbox(
        &self,
        command: &str,
        args: &[&str],
        tool: &ExtendedToolDefinition,
        input: &Value,
        start: std::time::Instant,
    ) -> ExecutionResult {
        // If we have a pool, use it; otherwise create a one-off sandbox
        if let Some(pool) = &self.sandbox_pool {
            let sandbox = match pool.acquire().await {
                Ok(s) => s,
                Err(e) => {
                    return ExecutionResult::failure(
                        format!("Failed to acquire sandbox: {}", e),
                        start.elapsed().as_millis() as u64,
                    );
                }
            };

            let result = self
                .run_in_sandbox(&sandbox, command, args, tool, input, start)
                .await;

            // Release sandbox back to pool
            pool.release(sandbox).await;

            result
        } else {
            // Create a one-off sandbox
            let mut sandbox = ProcessSandbox::new(SandboxConfig::default());
            if let Err(e) = sandbox.start().await {
                return ExecutionResult::failure(
                    format!("Failed to start sandbox: {}", e),
                    start.elapsed().as_millis() as u64,
                );
            }

            let result = self
                .run_in_sandbox(&sandbox, command, args, tool, input, start)
                .await;

            let _ = sandbox.stop().await;
            result
        }
    }

    /// Run command in a sandbox
    async fn run_in_sandbox(
        &self,
        sandbox: &ProcessSandbox,
        command: &str,
        args: &[&str],
        tool: &ExtendedToolDefinition,
        input: &Value,
        start: std::time::Instant,
    ) -> ExecutionResult {
        // Build execution options
        let mut exec_opts = ExecOptions::new()
            .with_timeout(Duration::from_millis(tool.timeout_ms))
            .with_max_output(EXECUTOR_OUTPUT_BYTES_MAX as u64)
            .with_stdin(serde_json::to_vec(input).unwrap_or_default());

        // Add tool-specific environment variables
        for (key, value) in &tool.env {
            exec_opts = exec_opts.with_env(key, value.clone());
        }

        // Execute
        let output = match sandbox.exec(command, args, exec_opts).await {
            Ok(output) => output,
            Err(e) => {
                return ExecutionResult::failure(
                    format!("Execution failed: {}", e),
                    start.elapsed().as_millis() as u64,
                );
            }
        };

        let duration = start.elapsed().as_millis() as u64;

        if output.is_success() {
            ExecutionResult::success(output.stdout_string(), duration)
        } else {
            let stderr = output.stderr_string();
            ExecutionResult::failure(
                if stderr.is_empty() {
                    format!(
                        "Tool execution failed with exit code: {:?}",
                        output.status.code
                    )
                } else {
                    stderr
                },
                duration,
            )
        }
    }

    /// Get execution statistics
    pub async fn stats(&self) -> ExecutorStats {
        self.stats.read().await.clone()
    }

    /// Reset statistics
    pub async fn reset_stats(&self) {
        *self.stats.write().await = ExecutorStats::default();
    }
}

impl Default for ToolExecutor {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Factory Functions
// =============================================================================

/// Create a sandbox pool for tool execution
pub async fn create_sandbox_pool(
    min_size: usize,
    max_size: usize,
) -> Result<Arc<SandboxPool<ProcessSandboxFactory>>, String> {
    let factory = ProcessSandboxFactory::new();
    let config = PoolConfig::new(SandboxConfig::default())
        .with_min_size(min_size)
        .with_max_size(max_size);

    let pool = SandboxPool::new(factory, config)
        .map_err(|e| format!("Failed to create sandbox pool: {}", e))?;

    pool.warm_up()
        .await
        .map_err(|e| format!("Failed to warm up sandbox pool: {}", e))?;

    Ok(Arc::new(pool))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tool_language_interpreter() {
        assert_eq!(ToolLanguage::Python.interpreter(), Some("python3"));
        assert_eq!(ToolLanguage::JavaScript.interpreter(), Some("node"));
        assert_eq!(ToolLanguage::Shell.interpreter(), Some("bash"));
        assert_eq!(ToolLanguage::Wasm.interpreter(), None);
    }

    #[test]
    fn test_tool_definition_builder() {
        let tool = ExtendedToolDefinition::new(
            "test",
            "A test tool",
            ToolLanguage::Python,
            "def test(x): return x * 2",
        )
        .with_requirement("numpy")
        .with_timeout(Duration::from_secs(60))
        .with_env("DEBUG", "1");

        assert_eq!(tool.name, "test");
        assert_eq!(tool.language, ToolLanguage::Python);
        assert_eq!(tool.requirements, vec!["numpy"]);
        assert_eq!(tool.timeout_ms, 60_000);
        assert_eq!(tool.env.get("DEBUG"), Some(&"1".to_string()));
    }

    #[test]
    fn test_execution_result() {
        let success = ExecutionResult::success("output", 100);
        assert!(success.success);
        assert_eq!(success.output, "output");
        assert!(success.error.is_none());

        let failure = ExecutionResult::failure("error", 50);
        assert!(!failure.success);
        assert_eq!(failure.output, "error");
        assert_eq!(failure.error, Some("error".to_string()));
    }

    #[tokio::test]
    async fn test_executor_creation() {
        let executor = ToolExecutor::new();
        let stats = executor.stats().await;
        assert_eq!(stats.total_executions, 0);
    }
}

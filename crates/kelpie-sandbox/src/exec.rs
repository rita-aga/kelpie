//! Command execution types
//!
//! TigerStyle: Explicit input/output with structured results.

use bytes::Bytes;
use serde::{Deserialize, Serialize};
use std::time::Duration;

/// Exit status of a command
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExitStatus {
    /// Exit code (0 = success)
    pub code: i32,
    /// Whether the process was killed by a signal
    pub signal: Option<i32>,
}

impl ExitStatus {
    /// Create a successful exit status
    pub fn success() -> Self {
        Self {
            code: 0,
            signal: None,
        }
    }

    /// Create an exit status with a code
    pub fn with_code(code: i32) -> Self {
        Self { code, signal: None }
    }

    /// Create an exit status for signal termination
    pub fn with_signal(signal: i32) -> Self {
        Self {
            code: 128 + signal,
            signal: Some(signal),
        }
    }

    /// Check if the command succeeded
    pub fn is_success(&self) -> bool {
        self.code == 0 && self.signal.is_none()
    }

    /// Check if the command was killed by a signal
    pub fn is_signal(&self) -> bool {
        self.signal.is_some()
    }
}

impl Default for ExitStatus {
    fn default() -> Self {
        Self::success()
    }
}

/// Options for command execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecOptions {
    /// Working directory for the command
    pub workdir: Option<String>,
    /// Environment variables (in addition to sandbox defaults)
    pub env: Vec<(String, String)>,
    /// Timeout for execution (overrides sandbox default)
    pub timeout_ms: Option<u64>,
    /// Whether to capture stdout
    pub capture_stdout: bool,
    /// Whether to capture stderr
    pub capture_stderr: bool,
    /// Stdin input
    pub stdin: Option<Bytes>,
    /// Maximum output size to capture (bytes)
    pub max_output_bytes: u64,
}

impl ExecOptions {
    /// Create with default options
    pub fn new() -> Self {
        Self::default()
    }

    /// Set working directory
    pub fn with_workdir(mut self, workdir: impl Into<String>) -> Self {
        self.workdir = Some(workdir.into());
        self
    }

    /// Add environment variable
    pub fn with_env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.env.push((key.into(), value.into()));
        self
    }

    /// Set timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout_ms = Some(timeout.as_millis() as u64);
        self
    }

    /// Set stdin input
    pub fn with_stdin(mut self, stdin: impl Into<Bytes>) -> Self {
        self.stdin = Some(stdin.into());
        self
    }

    /// Set max output size
    pub fn with_max_output(mut self, bytes: u64) -> Self {
        self.max_output_bytes = bytes;
        self
    }

    /// Disable stdout capture
    pub fn no_stdout(mut self) -> Self {
        self.capture_stdout = false;
        self
    }

    /// Disable stderr capture
    pub fn no_stderr(mut self) -> Self {
        self.capture_stderr = false;
        self
    }
}

impl Default for ExecOptions {
    fn default() -> Self {
        Self {
            workdir: None,
            env: Vec::new(),
            timeout_ms: None,
            capture_stdout: true,
            capture_stderr: true,
            stdin: None,
            max_output_bytes: 10 * 1024 * 1024, // 10MB default
        }
    }
}

/// Output from command execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecOutput {
    /// Exit status
    pub status: ExitStatus,
    /// Stdout content
    pub stdout: Bytes,
    /// Stderr content
    pub stderr: Bytes,
    /// Execution duration in milliseconds
    pub duration_ms: u64,
    /// Whether stdout was truncated
    pub stdout_truncated: bool,
    /// Whether stderr was truncated
    pub stderr_truncated: bool,
}

impl ExecOutput {
    /// Create a new exec output
    pub fn new(status: ExitStatus, stdout: Bytes, stderr: Bytes, duration_ms: u64) -> Self {
        Self {
            status,
            stdout,
            stderr,
            duration_ms,
            stdout_truncated: false,
            stderr_truncated: false,
        }
    }

    /// Create a successful output
    pub fn success(stdout: impl Into<Bytes>) -> Self {
        Self::new(ExitStatus::success(), stdout.into(), Bytes::new(), 0)
    }

    /// Create a failed output
    pub fn failure(code: i32, stderr: impl Into<Bytes>) -> Self {
        Self::new(ExitStatus::with_code(code), Bytes::new(), stderr.into(), 0)
    }

    /// Check if execution was successful
    pub fn is_success(&self) -> bool {
        self.status.is_success()
    }

    /// Get stdout as string (lossy UTF-8 conversion)
    pub fn stdout_string(&self) -> String {
        String::from_utf8_lossy(&self.stdout).into_owned()
    }

    /// Get stderr as string (lossy UTF-8 conversion)
    pub fn stderr_string(&self) -> String {
        String::from_utf8_lossy(&self.stderr).into_owned()
    }

    /// Set duration
    pub fn with_duration(mut self, duration_ms: u64) -> Self {
        self.duration_ms = duration_ms;
        self
    }
}

impl Default for ExecOutput {
    fn default() -> Self {
        Self::success(Bytes::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exit_status_success() {
        let status = ExitStatus::success();
        assert!(status.is_success());
        assert!(!status.is_signal());
        assert_eq!(status.code, 0);
    }

    #[test]
    fn test_exit_status_with_code() {
        let status = ExitStatus::with_code(1);
        assert!(!status.is_success());
        assert!(!status.is_signal());
        assert_eq!(status.code, 1);
    }

    #[test]
    fn test_exit_status_with_signal() {
        let status = ExitStatus::with_signal(9); // SIGKILL
        assert!(!status.is_success());
        assert!(status.is_signal());
        assert_eq!(status.signal, Some(9));
        assert_eq!(status.code, 137); // 128 + 9
    }

    #[test]
    fn test_exec_options_builder() {
        let opts = ExecOptions::new()
            .with_workdir("/tmp")
            .with_env("FOO", "bar")
            .with_timeout(Duration::from_secs(5))
            .with_stdin(Bytes::from("input"));

        assert_eq!(opts.workdir, Some("/tmp".to_string()));
        assert_eq!(opts.env.len(), 1);
        assert_eq!(opts.timeout_ms, Some(5000));
        assert!(opts.stdin.is_some());
    }

    #[test]
    fn test_exec_output_success() {
        let output = ExecOutput::success("hello world");
        assert!(output.is_success());
        assert_eq!(output.stdout_string(), "hello world");
    }

    #[test]
    fn test_exec_output_failure() {
        let output = ExecOutput::failure(1, "error message");
        assert!(!output.is_success());
        assert_eq!(output.stderr_string(), "error message");
    }

    #[test]
    fn test_exec_output_string_conversion() {
        let output = ExecOutput::new(
            ExitStatus::success(),
            Bytes::from("stdout"),
            Bytes::from("stderr"),
            100,
        );

        assert_eq!(output.stdout_string(), "stdout");
        assert_eq!(output.stderr_string(), "stderr");
        assert_eq!(output.duration_ms, 100);
    }
}

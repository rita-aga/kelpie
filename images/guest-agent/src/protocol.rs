//! Protocol definitions for host-guest communication
//!
//! TigerStyle: Explicit types, clear semantics, version tracking

use serde::{Deserialize, Serialize};

/// Protocol version
/// TigerStyle: Explicit version constant for compatibility checking
pub const PROTOCOL_VERSION: u32 = 1;

/// Request from host to guest
///
/// TigerStyle: Exhaustive enum, clear variants
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Request {
    /// Ping request for health check
    Ping,

    /// Execute a command
    Exec {
        command: String,
        args: Vec<String>,
        #[serde(default)]
        stdin: Option<String>,
    },

    /// Read a file
    ReadFile { path: String },

    /// Write a file
    WriteFile {
        path: String,
        #[serde(with = "serde_bytes_base64")]
        contents: Vec<u8>,
    },

    /// List directory contents
    ListDir { path: String },
}

/// Response from guest to host
///
/// TigerStyle: Exhaustive enum, explicit error variant
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Response {
    /// Pong response to Ping
    Pong,

    /// Generic success
    Success,

    /// Command execution result
    ExecResult(ExecOutput),

    /// File contents
    FileContents {
        #[serde(with = "serde_bytes_base64")]
        contents: Vec<u8>,
    },

    /// Directory listing
    DirectoryListing { files: Vec<String> },

    /// Error response
    Error { message: String },
}

/// Output from command execution
///
/// TigerStyle: Explicit fields, clear semantics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecOutput {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
}

/// Helper module for base64 encoding of binary data in JSON
///
/// TigerStyle: Explicit encoding, no silent data loss
mod serde_bytes_base64 {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&base64_encode(bytes))
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        base64_decode(&s).map_err(serde::de::Error::custom)
    }

    fn base64_encode(bytes: &[u8]) -> String {
        use std::fmt::Write;
        let mut result = String::new();
        for chunk in bytes.chunks(3) {
            let b1 = chunk[0];
            let b2 = chunk.get(1).copied().unwrap_or(0);
            let b3 = chunk.get(2).copied().unwrap_or(0);

            let n = ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);

            let chars = [
                BASE64_CHARS[(n >> 18) as usize],
                BASE64_CHARS[((n >> 12) & 0x3F) as usize],
                if chunk.len() > 1 {
                    BASE64_CHARS[((n >> 6) & 0x3F) as usize]
                } else {
                    '='
                },
                if chunk.len() > 2 {
                    BASE64_CHARS[(n & 0x3F) as usize]
                } else {
                    '='
                },
            ];

            for c in chars {
                write!(&mut result, "{}", c).unwrap();
            }
        }
        result
    }

    fn base64_decode(s: &str) -> Result<Vec<u8>, String> {
        let mut result = Vec::new();
        let bytes: Vec<u8> = s
            .chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| {
                BASE64_CHARS
                    .iter()
                    .position(|&x| x == c)
                    .ok_or_else(|| format!("Invalid base64 character: {}", c))
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(|i| i as u8)
            .collect();

        for chunk in bytes.chunks(4) {
            let b1 = chunk[0];
            let b2 = chunk.get(1).copied().unwrap_or(0);
            let b3 = chunk.get(2).copied().unwrap_or(0);
            let b4 = chunk.get(3).copied().unwrap_or(0);

            let n = ((b1 as u32) << 18) | ((b2 as u32) << 12) | ((b3 as u32) << 6) | (b4 as u32);

            result.push((n >> 16) as u8);
            if chunk.len() > 2 && chunk[2] != 64 {
                // 64 is '='
                result.push((n >> 8) as u8);
            }
            if chunk.len() > 3 && chunk[3] != 64 {
                result.push(n as u8);
            }
        }

        Ok(result)
    }

    const BASE64_CHARS: &[char] = &[
        'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R',
        'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j',
        'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1',
        '2', '3', '4', '5', '6', '7', '8', '9', '+', '/', '=',
    ];
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_request_serialization() {
        let req = Request::Ping;
        let json = serde_json::to_string(&req).unwrap();
        assert!(json.contains("\"type\":\"ping\""));

        let deserialized: Request = serde_json::from_str(&json).unwrap();
        matches!(deserialized, Request::Ping);
    }

    #[test]
    fn test_exec_request() {
        let req = Request::Exec {
            command: "echo".to_string(),
            args: vec!["hello".to_string()],
            stdin: None,
        };

        let json = serde_json::to_string(&req).unwrap();
        let deserialized: Request = serde_json::from_str(&json).unwrap();

        match deserialized {
            Request::Exec { command, args, .. } => {
                assert_eq!(command, "echo");
                assert_eq!(args, vec!["hello"]);
            }
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_response_serialization() {
        let resp = Response::ExecResult(ExecOutput {
            exit_code: 0,
            stdout: "hello\n".to_string(),
            stderr: String::new(),
        });

        let json = serde_json::to_string(&resp).unwrap();
        let deserialized: Response = serde_json::from_str(&json).unwrap();

        match deserialized {
            Response::ExecResult(output) => {
                assert_eq!(output.exit_code, 0);
                assert_eq!(output.stdout, "hello\n");
            }
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_binary_data_encoding() {
        let data = vec![0u8, 1, 2, 3, 255];
        let req = Request::WriteFile {
            path: "/test".to_string(),
            contents: data.clone(),
        };

        let json = serde_json::to_string(&req).unwrap();
        let deserialized: Request = serde_json::from_str(&json).unwrap();

        match deserialized {
            Request::WriteFile { contents, .. } => {
                assert_eq!(contents, data);
            }
            _ => panic!("Wrong variant"),
        }
    }
}

//! Memory Editing Tools for Letta Compatibility
//!
//! TigerStyle: Thin wrappers around AppState memory operations.
//!
//! Implements the 9 Letta memory tools:
//! - core_memory_append: Append to a core memory block
//! - core_memory_replace: Replace content in a core memory block
//! - archival_memory_insert: Insert into archival memory
//! - archival_memory_search: Search archival memory
//! - conversation_search: Search conversation history

use crate::state::AppState;
use crate::tools::{BuiltinToolHandler, UnifiedToolRegistry};
use serde_json::{json, Value};
use std::sync::Arc;

/// Register all memory tools with the unified registry
pub async fn register_memory_tools(registry: &UnifiedToolRegistry, state: AppState) {
    // core_memory_append
    register_core_memory_append(registry, state.clone()).await;

    // core_memory_replace
    register_core_memory_replace(registry, state.clone()).await;

    // archival_memory_insert
    register_archival_memory_insert(registry, state.clone()).await;

    // archival_memory_search
    register_archival_memory_search(registry, state.clone()).await;

    // conversation_search
    register_conversation_search(registry, state.clone()).await;

    // conversation_search_date
    register_conversation_search_date(registry, state).await;

    tracing::info!(
        "Registered memory tools: core_memory_append, core_memory_replace, archival_memory_insert, archival_memory_search, conversation_search, conversation_search_date"
    );
}

async fn register_core_memory_append(registry: &UnifiedToolRegistry, state: AppState) {
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let state = state.clone();
        let input = input.clone();
        Box::pin(async move {
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let label = match input.get("label").and_then(|v| v.as_str()) {
                Some(l) => l.to_string(),
                None => return "Error: missing required parameter 'label'".to_string(),
            };

            let content = match input.get("content").and_then(|v| v.as_str()) {
                Some(c) => c.to_string(),
                None => return "Error: missing required parameter 'content'".to_string(),
            };

            // BUG-001 FIX: Use atomic append_or_create to eliminate TOCTOU race
            // The old implementation had a race between get_block_by_label and update:
            //   1. Thread A checks: block doesn't exist
            //   2. Thread B checks: block doesn't exist
            //   3. Thread A creates block
            //   4. Thread B creates duplicate block (race condition!)
            //
            // The new atomic method holds the write lock for the entire operation.
            match state.append_or_create_block_by_label(&agent_id, &label, &content) {
                Ok(_) => format!("Successfully updated memory block '{}'", label),
                Err(e) => format!("Error: {}", e),
            }
        })
    });

    registry
        .register_builtin(
            "core_memory_append",
            "Append content to a core memory block. The block will be created if it doesn't exist. Core memory blocks are always visible in the LLM context window.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The agent ID whose memory to modify"
                    },
                    "label": {
                        "type": "string",
                        "description": "Block label (e.g., 'persona', 'human', 'facts', 'goals', 'scratch')"
                    },
                    "content": {
                        "type": "string",
                        "description": "Content to append to the block"
                    }
                },
                "required": ["agent_id", "label", "content"]
            }),
            handler,
        )
        .await;
}

async fn register_core_memory_replace(registry: &UnifiedToolRegistry, state: AppState) {
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let state = state.clone();
        let input = input.clone();
        Box::pin(async move {
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let label = match input.get("label").and_then(|v| v.as_str()) {
                Some(l) => l.to_string(),
                None => return "Error: missing required parameter 'label'".to_string(),
            };

            let old_content = match input.get("old_content").and_then(|v| v.as_str()) {
                Some(c) => c.to_string(),
                None => return "Error: missing required parameter 'old_content'".to_string(),
            };

            let new_content = input
                .get("new_content")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_string();

            // Get current block
            let current_block = match state.get_block_by_label(&agent_id, &label) {
                Ok(Some(b)) => b,
                Ok(None) => return format!("Error: block '{}' not found", label),
                Err(e) => return format!("Error: {}", e),
            };

            // Check if old_content exists
            if !current_block.value.contains(&old_content) {
                return format!(
                    "Error: content '{}' not found in block '{}'",
                    old_content, label
                );
            }

            // Perform replacement
            match state.update_block_by_label(&agent_id, &label, |block| {
                block.value = block.value.replace(&old_content, &new_content);
            }) {
                Ok(_) => format!("Successfully replaced content in memory block '{}'", label),
                Err(e) => format!("Error: {}", e),
            }
        })
    });

    registry
        .register_builtin(
            "core_memory_replace",
            "Replace content in a core memory block. The old content must exist in the block.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The agent ID whose memory to modify"
                    },
                    "label": {
                        "type": "string",
                        "description": "Block label"
                    },
                    "old_content": {
                        "type": "string",
                        "description": "Content to find and replace"
                    },
                    "new_content": {
                        "type": "string",
                        "description": "Replacement content (can be empty to delete)"
                    }
                },
                "required": ["agent_id", "label", "old_content", "new_content"]
            }),
            handler,
        )
        .await;
}

async fn register_archival_memory_insert(registry: &UnifiedToolRegistry, state: AppState) {
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let state = state.clone();
        let input = input.clone();
        Box::pin(async move {
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let content = match input.get("content").and_then(|v| v.as_str()) {
                Some(c) => c.to_string(),
                None => return "Error: missing required parameter 'content'".to_string(),
            };

            match state.add_archival(&agent_id, content, None) {
                Ok(entry) => format!(
                    "Successfully inserted into archival memory. Entry ID: {}",
                    entry.id
                ),
                Err(e) => format!("Error: {}", e),
            }
        })
    });

    registry
        .register_builtin(
            "archival_memory_insert",
            "Insert content into archival memory with embedding for semantic search. Use this for long-term knowledge that doesn't need to be in the main context window.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The agent ID whose archival memory to modify"
                    },
                    "content": {
                        "type": "string",
                        "description": "Content to store in archival memory"
                    }
                },
                "required": ["agent_id", "content"]
            }),
            handler,
        )
        .await;
}

async fn register_archival_memory_search(registry: &UnifiedToolRegistry, state: AppState) {
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let state = state.clone();
        let input = input.clone();
        Box::pin(async move {
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let query = match input.get("query").and_then(|v| v.as_str()) {
                Some(q) => q.to_string(),
                None => return "Error: missing required parameter 'query'".to_string(),
            };

            let page = input.get("page").and_then(|v| v.as_i64()).unwrap_or(0) as usize;

            let page_size = 10;
            let offset = page * page_size;

            match state.search_archival(&agent_id, Some(&query), page_size + offset) {
                Ok(entries) => {
                    let page_entries: Vec<_> =
                        entries.into_iter().skip(offset).take(page_size).collect();

                    if page_entries.is_empty() {
                        "No results found".to_string()
                    } else {
                        let results: Vec<String> = page_entries
                            .iter()
                            .map(|e| format!("[{}] {}", e.id, e.content))
                            .collect();
                        format!(
                            "Found {} results (page {}):\n{}",
                            results.len(),
                            page,
                            results.join("\n---\n")
                        )
                    }
                }
                Err(e) => format!("Error: {}", e),
            }
        })
    });

    registry
        .register_builtin(
            "archival_memory_search",
            "Search archival memory using semantic search. Returns paginated results.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The agent ID whose archival memory to search"
                    },
                    "query": {
                        "type": "string",
                        "description": "Search query"
                    },
                    "page": {
                        "type": "integer",
                        "description": "Page number (0-indexed)",
                        "default": 0
                    }
                },
                "required": ["agent_id", "query"]
            }),
            handler,
        )
        .await;
}

async fn register_conversation_search(registry: &UnifiedToolRegistry, state: AppState) {
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let state = state.clone();
        let input = input.clone();
        Box::pin(async move {
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let query = match input.get("query").and_then(|v| v.as_str()) {
                Some(q) => q.to_string(),
                None => return "Error: missing required parameter 'query'".to_string(),
            };

            let page = input.get("page").and_then(|v| v.as_i64()).unwrap_or(0) as usize;

            let page_size = 10;

            // Get all messages and filter
            match state.list_messages(&agent_id, 1000, None) {
                Ok(messages) => {
                    let query_lower = query.to_lowercase();
                    let matching: Vec<_> = messages
                        .iter()
                        .filter(|m| m.content.to_lowercase().contains(&query_lower))
                        .skip(page * page_size)
                        .take(page_size)
                        .collect();

                    if matching.is_empty() {
                        "No matching conversations found".to_string()
                    } else {
                        let results: Vec<String> = matching
                            .iter()
                            .map(|m| format!("[{:?}]: {}", m.role, m.content))
                            .collect();
                        format!(
                            "Found {} results (page {}):\n{}",
                            results.len(),
                            page,
                            results.join("\n---\n")
                        )
                    }
                }
                Err(e) => format!("Error: {}", e),
            }
        })
    });

    registry
        .register_builtin(
            "conversation_search",
            "Search past conversation messages. Returns paginated results matching the query.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The agent ID whose conversations to search"
                    },
                    "query": {
                        "type": "string",
                        "description": "Search query"
                    },
                    "page": {
                        "type": "integer",
                        "description": "Page number (0-indexed)",
                        "default": 0
                    }
                },
                "required": ["agent_id", "query"]
            }),
            handler,
        )
        .await;
}

async fn register_conversation_search_date(registry: &UnifiedToolRegistry, state: AppState) {
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let state = state.clone();
        let input = input.clone();
        Box::pin(async move {
            let agent_id = match input.get("agent_id").and_then(|v| v.as_str()) {
                Some(id) => id.to_string(),
                None => return "Error: missing required parameter 'agent_id'".to_string(),
            };

            let query = match input.get("query").and_then(|v| v.as_str()) {
                Some(q) => q.to_string(),
                None => return "Error: missing required parameter 'query'".to_string(),
            };

            // Parse start_date (optional)
            let start_date = match input.get("start_date") {
                Some(val) => match parse_date_param(val) {
                    Ok(dt) => Some(dt),
                    Err(e) => return format!("Error parsing start_date: {}", e),
                },
                None => None,
            };

            // Parse end_date (optional)
            let end_date = match input.get("end_date") {
                Some(val) => match parse_date_param(val) {
                    Ok(dt) => Some(dt),
                    Err(e) => return format!("Error parsing end_date: {}", e),
                },
                None => None,
            };

            // Validate date range
            if let (Some(start), Some(end)) = (start_date, end_date) {
                if start > end {
                    return "Error: start_date must be before end_date".to_string();
                }
            }

            let page = input.get("page").and_then(|v| v.as_i64()).unwrap_or(0) as usize;
            let page_size = 10;

            // Get all messages and filter
            match state.list_messages(&agent_id, 1000, None) {
                Ok(messages) => {
                    let query_lower = query.to_lowercase();
                    let matching: Vec<_> = messages
                        .iter()
                        .filter(|m| {
                            // Text filter
                            let matches_query = m.content.to_lowercase().contains(&query_lower);

                            // Date filter
                            let matches_dates = match (start_date, end_date) {
                                (Some(start), Some(end)) => {
                                    m.created_at >= start && m.created_at <= end
                                }
                                (Some(start), None) => m.created_at >= start,
                                (None, Some(end)) => m.created_at <= end,
                                (None, None) => true,
                            };

                            matches_query && matches_dates
                        })
                        .skip(page * page_size)
                        .take(page_size)
                        .collect();

                    if matching.is_empty() {
                        "No matching conversations found in date range".to_string()
                    } else {
                        let results: Vec<String> = matching
                            .iter()
                            .map(|m| {
                                format!(
                                    "[{:?}] [{}]: {}",
                                    m.role,
                                    m.created_at.to_rfc3339(),
                                    m.content
                                )
                            })
                            .collect();
                        format!(
                            "Found {} results (page {}):\n{}",
                            results.len(),
                            page,
                            results.join("\n---\n")
                        )
                    }
                }
                Err(e) => format!("Error: {}", e),
            }
        })
    });

    registry
        .register_builtin(
            "conversation_search_date",
            "Search past conversation messages with date filtering. Returns paginated results matching the query within the specified date range. Supports ISO 8601, RFC 3339, and Unix timestamps.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": {
                        "type": "string",
                        "description": "The agent ID whose conversations to search"
                    },
                    "query": {
                        "type": "string",
                        "description": "Search query"
                    },
                    "start_date": {
                        "type": ["string", "integer"],
                        "description": "Start date (ISO 8601/RFC 3339 string or Unix timestamp). Messages on or after this date will be included."
                    },
                    "end_date": {
                        "type": ["string", "integer"],
                        "description": "End date (ISO 8601/RFC 3339 string or Unix timestamp). Messages on or before this date will be included."
                    },
                    "page": {
                        "type": "integer",
                        "description": "Page number (0-indexed)",
                        "default": 0
                    }
                },
                "required": ["agent_id", "query"]
            }),
            handler,
        )
        .await;
}

/// Parse date parameter from JSON value
///
/// Supports:
/// - ISO 8601: "2024-01-15T10:00:00Z"
/// - RFC 3339: "2024-01-15T10:00:00+00:00"
/// - Unix timestamp: 1705315200 (seconds since epoch)
fn parse_date_param(val: &Value) -> Result<chrono::DateTime<chrono::Utc>, String> {
    use chrono::{DateTime, TimeZone, Utc};

    match val {
        // String: try ISO 8601 / RFC 3339
        Value::String(s) => {
            DateTime::parse_from_rfc3339(s)
                .map(|dt| dt.with_timezone(&Utc))
                .or_else(|_| {
                    // Try ISO 8601 without timezone (assume UTC)
                    chrono::NaiveDateTime::parse_from_str(s, "%Y-%m-%dT%H:%M:%S")
                        .map(|ndt| Utc.from_utc_datetime(&ndt))
                })
                .or_else(|_| {
                    // Try date only (assume start of day UTC)
                    chrono::NaiveDate::parse_from_str(s, "%Y-%m-%d").map(|nd| {
                        Utc.from_utc_datetime(&nd.and_hms_opt(0, 0, 0).unwrap())
                    })
                })
                .map_err(|e| {
                    format!(
                        "Invalid date format '{}'. Expected ISO 8601/RFC 3339 or Unix timestamp. Error: {}",
                        s, e
                    )
                })
        }
        // Number: treat as Unix timestamp (seconds)
        Value::Number(n) => {
            if let Some(ts) = n.as_i64() {
                Utc.timestamp_opt(ts, 0).single().ok_or_else(|| {
                    format!("Invalid Unix timestamp: {} (out of range)", ts)
                })
            } else {
                Err(format!("Invalid timestamp: {}", n))
            }
        }
        _ => Err(format!(
            "Invalid date type: expected string or number, got {:?}",
            val
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{AgentState, AgentType, CreateAgentRequest, CreateBlockRequest};

    fn create_test_agent(name: &str) -> AgentState {
        AgentState::from_request(CreateAgentRequest {
            name: name.to_string(),
            agent_type: AgentType::default(),
            model: None,
            system: None,
            description: None,
            memory_blocks: vec![CreateBlockRequest {
                label: "persona".to_string(),
                value: "I am a test agent".to_string(),
                description: None,
                limit: None,
            }],
            block_ids: vec![],
            tool_ids: vec![],
            tags: vec![],
            metadata: json!({}),
        })
    }

    #[tokio::test]
    async fn test_memory_tools_registration() {
        let state = AppState::new();
        let registry = state.tool_registry();

        register_memory_tools(registry, state.clone()).await;

        // Verify tools are registered
        assert!(registry.has_tool("core_memory_append").await);
        assert!(registry.has_tool("core_memory_replace").await);
        assert!(registry.has_tool("archival_memory_insert").await);
        assert!(registry.has_tool("archival_memory_search").await);
        assert!(registry.has_tool("conversation_search").await);
    }

    #[tokio::test]
    async fn test_core_memory_append_integration() {
        let state = AppState::new();

        // Create agent
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Execute append
        let result = registry
            .execute(
                "core_memory_append",
                &json!({
                    "agent_id": agent_id,
                    "label": "facts",
                    "content": "User likes pizza"
                }),
            )
            .await;

        assert!(result.success, "Append failed: {}", result.output);
        assert!(result.output.contains("Successfully"));

        // Verify block was created
        let block = state.get_block_by_label(&agent_id, "facts").unwrap();
        assert!(block.is_some());
        assert!(block.unwrap().value.contains("pizza"));
    }

    #[tokio::test]
    async fn test_core_memory_replace_integration() {
        let state = AppState::new();

        // Create agent with existing block
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Execute replace on existing persona block
        let result = registry
            .execute(
                "core_memory_replace",
                &json!({
                    "agent_id": agent_id,
                    "label": "persona",
                    "old_content": "test agent",
                    "new_content": "helpful assistant"
                }),
            )
            .await;

        assert!(result.success, "Replace failed: {}", result.output);

        // Verify replacement
        let block = state
            .get_block_by_label(&agent_id, "persona")
            .unwrap()
            .unwrap();
        assert!(block.value.contains("helpful assistant"));
        assert!(!block.value.contains("test agent"));
    }

    #[tokio::test]
    async fn test_archival_memory_integration() {
        let state = AppState::new();

        // Create agent
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Insert into archival
        let result = registry
            .execute(
                "archival_memory_insert",
                &json!({
                    "agent_id": agent_id,
                    "content": "User's favorite color is blue"
                }),
            )
            .await;

        assert!(result.success, "Insert failed: {}", result.output);
        assert!(result.output.contains("Entry ID"));

        // Search archival
        let result = registry
            .execute(
                "archival_memory_search",
                &json!({
                    "agent_id": agent_id,
                    "query": "blue"
                }),
            )
            .await;

        assert!(result.success, "Search failed: {}", result.output);
        assert!(result.output.contains("blue") || result.output.contains("Found"));
    }

    #[test]
    fn test_parse_date_iso8601() {
        // RFC 3339 with timezone
        let val = json!("2024-01-15T10:00:00Z");
        let dt = parse_date_param(&val).unwrap();
        assert_eq!(dt.timestamp(), 1705312800);

        // RFC 3339 with offset
        let val = json!("2024-01-15T10:00:00+00:00");
        let dt = parse_date_param(&val).unwrap();
        assert_eq!(dt.timestamp(), 1705312800);
    }

    #[test]
    fn test_parse_date_unix_timestamp() {
        use chrono::Datelike;
        // Unix timestamp (seconds)
        let val = json!(1705315200);
        let dt = parse_date_param(&val).unwrap();
        assert_eq!(dt.year(), 2024);
        assert_eq!(dt.month(), 1);
        assert_eq!(dt.day(), 15);
    }

    #[test]
    fn test_parse_date_date_only() {
        use chrono::{Datelike, Timelike};
        // Date only (assumes 00:00:00 UTC)
        let val = json!("2024-01-15");
        let dt = parse_date_param(&val).unwrap();
        assert_eq!(dt.year(), 2024);
        assert_eq!(dt.month(), 1);
        assert_eq!(dt.day(), 15);
        assert_eq!(dt.hour(), 0);
        assert_eq!(dt.minute(), 0);
    }

    #[test]
    fn test_parse_date_invalid() {
        // Invalid format
        let val = json!("not-a-date");
        assert!(parse_date_param(&val).is_err());

        // Invalid type
        let val = json!(true);
        assert!(parse_date_param(&val).is_err());

        // Invalid timestamp (too large)
        let val = json!(99999999999999i64);
        assert!(parse_date_param(&val).is_err());
    }

    #[tokio::test]
    async fn test_conversation_search_date() {
        let state = AppState::new();

        // Create agent
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Add test message (via send_message endpoint simulation)
        // Note: In real usage, messages are added through handle_message
        // For testing, we'll verify the tool executes without error

        // Search with valid date range
        let result = registry
            .execute(
                "conversation_search_date",
                &json!({
                    "agent_id": agent_id,
                    "query": "test",
                    "start_date": "2024-01-01T00:00:00Z",
                    "end_date": "2024-12-31T23:59:59Z"
                }),
            )
            .await;

        assert!(result.success, "Search failed: {}", result.output);
        // Since agent has no messages yet, expect "No matching conversations"
        assert!(result.output.contains("No matching conversations"));
    }

    #[tokio::test]
    async fn test_conversation_search_date_unix_timestamp() {
        let state = AppState::new();

        // Create agent
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Search with Unix timestamps
        let result = registry
            .execute(
                "conversation_search_date",
                &json!({
                    "agent_id": agent_id,
                    "query": "test",
                    "start_date": 1704067200, // 2024-01-01
                    "end_date": 1735689599   // 2024-12-31
                }),
            )
            .await;

        assert!(result.success, "Search failed: {}", result.output);
    }

    #[tokio::test]
    async fn test_conversation_search_date_invalid_range() {
        let state = AppState::new();

        // Create agent
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Search with invalid range (start > end)
        let result = registry
            .execute(
                "conversation_search_date",
                &json!({
                    "agent_id": agent_id,
                    "query": "test",
                    "start_date": "2024-12-31T00:00:00Z",
                    "end_date": "2024-01-01T00:00:00Z"
                }),
            )
            .await;

        // Should fail with error message
        assert!(result.output.contains("Error: start_date must be before end_date"));
    }

    #[tokio::test]
    async fn test_conversation_search_date_invalid_format() {
        let state = AppState::new();

        // Create agent
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();
        state.create_agent(agent).unwrap();

        // Register memory tools
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Search with invalid date format
        let result = registry
            .execute(
                "conversation_search_date",
                &json!({
                    "agent_id": agent_id,
                    "query": "test",
                    "start_date": "not-a-date"
                }),
            )
            .await;

        // Should fail with error message
        assert!(result.output.contains("Error parsing start_date"));
    }

    #[tokio::test]
    async fn test_conversation_search_date_missing_params() {
        let state = AppState::new();
        let registry = state.tool_registry();
        register_memory_tools(registry, state.clone()).await;

        // Missing agent_id
        let result = registry
            .execute(
                "conversation_search_date",
                &json!({
                    "query": "test"
                }),
            )
            .await;

        assert!(result.output.contains("Error: missing required parameter 'agent_id'"));

        // Missing query
        let result = registry
            .execute(
                "conversation_search_date",
                &json!({
                    "agent_id": "test-id"
                }),
            )
            .await;

        assert!(result.output.contains("Error: missing required parameter 'query'"));
    }
}

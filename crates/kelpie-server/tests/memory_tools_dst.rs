//! DST Tests for Memory Editing Tools (Phase 2)
//!
//! TigerStyle: DST-first development - tests written before implementation.
//!
//! Tests memory tools under fault injection:
//! - core_memory_append
//! - core_memory_replace
//! - archival_memory_insert
//! - archival_memory_search
//! - conversation_search
#![cfg(feature = "dst")]

use kelpie_dst::fault::{FaultConfig, FaultInjectorBuilder, FaultType};
use kelpie_dst::rng::DeterministicRng;
use kelpie_server::tools::{BuiltinToolHandler, UnifiedToolRegistry};
use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

// Re-export FaultInjector type for clarity
type FaultInjector = kelpie_dst::fault::FaultInjector;

/// Simulated agent memory state for testing
struct SimAgentMemory {
    /// Core memory blocks by label
    blocks: HashMap<String, String>,
    /// Archival memory entries
    archival: Vec<String>,
    /// Conversation history
    conversations: Vec<(String, String)>, // (role, content)
}

impl SimAgentMemory {
    fn new() -> Self {
        Self {
            blocks: HashMap::new(),
            archival: Vec::new(),
            conversations: Vec::new(),
        }
    }
}

/// Create memory tools registry with fault injection support
async fn create_memory_registry(
    agent_memory: Arc<RwLock<HashMap<String, SimAgentMemory>>>,
    fault_injector: Option<Arc<FaultInjector>>,
) -> UnifiedToolRegistry {
    let registry = UnifiedToolRegistry::new();

    // core_memory_append tool
    let mem = agent_memory.clone();
    let fi = fault_injector.clone();
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let mem = mem.clone();
        let fi = fi.clone();
        let input = input.clone();
        Box::pin(async move {
            // Check for fault injection
            if let Some(ref injector) = fi {
                if let Some(fault_type) = injector.should_inject("core_memory_append") {
                    return format!("Error: simulated fault: {:?}", fault_type);
                }
            }

            let agent_id = input.get("agent_id").and_then(|v| v.as_str()).unwrap_or("");
            let label = input.get("label").and_then(|v| v.as_str()).unwrap_or("");
            let content = input.get("content").and_then(|v| v.as_str()).unwrap_or("");

            if agent_id.is_empty() || label.is_empty() || content.is_empty() {
                return "Error: missing required parameters (agent_id, label, content)".to_string();
            }

            let mut agents = mem.write().await;
            let agent = agents
                .entry(agent_id.to_string())
                .or_insert_with(SimAgentMemory::new);

            if let Some(existing) = agent.blocks.get_mut(label) {
                existing.push('\n');
                existing.push_str(content);
            } else {
                agent.blocks.insert(label.to_string(), content.to_string());
            }

            format!("Successfully appended to memory block '{}'", label)
        })
    });

    registry
        .register_builtin(
            "core_memory_append",
            "Append content to a core memory block. The block will be created if it doesn't exist.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": { "type": "string", "description": "Agent ID" },
                    "label": { "type": "string", "description": "Block label (persona, human, facts, goals, scratch)" },
                    "content": { "type": "string", "description": "Content to append" }
                },
                "required": ["agent_id", "label", "content"]
            }),
            handler,
        )
        .await;

    // core_memory_replace tool
    let mem = agent_memory.clone();
    let fi = fault_injector.clone();
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let mem = mem.clone();
        let fi = fi.clone();
        let input = input.clone();
        Box::pin(async move {
            if let Some(ref injector) = fi {
                if let Some(fault_type) = injector.should_inject("core_memory_replace") {
                    return format!("Error: simulated fault: {:?}", fault_type);
                }
            }

            let agent_id = input.get("agent_id").and_then(|v| v.as_str()).unwrap_or("");
            let label = input.get("label").and_then(|v| v.as_str()).unwrap_or("");
            let old_content = input
                .get("old_content")
                .and_then(|v| v.as_str())
                .unwrap_or("");
            let new_content = input
                .get("new_content")
                .and_then(|v| v.as_str())
                .unwrap_or("");

            if agent_id.is_empty() || label.is_empty() || old_content.is_empty() {
                return "Error: missing required parameters".to_string();
            }

            let mut agents = mem.write().await;
            let agent = match agents.get_mut(agent_id) {
                Some(a) => a,
                None => return format!("Error: agent '{}' not found", agent_id),
            };

            match agent.blocks.get_mut(label) {
                Some(block) => {
                    if !block.contains(old_content) {
                        return format!(
                            "Error: content '{}' not found in block '{}'",
                            old_content, label
                        );
                    }
                    *block = block.replace(old_content, new_content);
                    format!("Successfully replaced content in memory block '{}'", label)
                }
                None => format!("Error: block '{}' not found", label),
            }
        })
    });

    registry
        .register_builtin(
            "core_memory_replace",
            "Replace content in a core memory block.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": { "type": "string" },
                    "label": { "type": "string" },
                    "old_content": { "type": "string" },
                    "new_content": { "type": "string" }
                },
                "required": ["agent_id", "label", "old_content", "new_content"]
            }),
            handler,
        )
        .await;

    // archival_memory_insert tool
    let mem = agent_memory.clone();
    let fi = fault_injector.clone();
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let mem = mem.clone();
        let fi = fi.clone();
        let input = input.clone();
        Box::pin(async move {
            if let Some(ref injector) = fi {
                if let Some(fault_type) = injector.should_inject("archival_memory_insert") {
                    return format!("Error: simulated fault: {:?}", fault_type);
                }
            }

            let agent_id = input.get("agent_id").and_then(|v| v.as_str()).unwrap_or("");
            let content = input.get("content").and_then(|v| v.as_str()).unwrap_or("");

            if agent_id.is_empty() || content.is_empty() {
                return "Error: missing required parameters (agent_id, content)".to_string();
            }

            let mut agents = mem.write().await;
            let agent = agents
                .entry(agent_id.to_string())
                .or_insert_with(SimAgentMemory::new);

            let entry_id = uuid::Uuid::new_v4().to_string();
            agent.archival.push(content.to_string());

            format!(
                "Successfully inserted into archival memory. Entry ID: {}",
                entry_id
            )
        })
    });

    registry
        .register_builtin(
            "archival_memory_insert",
            "Insert content into archival memory with embedding for semantic search.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": { "type": "string" },
                    "content": { "type": "string", "description": "Content to store in archival memory" }
                },
                "required": ["agent_id", "content"]
            }),
            handler,
        )
        .await;

    // archival_memory_search tool
    let mem = agent_memory.clone();
    let fi = fault_injector.clone();
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let mem = mem.clone();
        let fi = fi.clone();
        let input = input.clone();
        Box::pin(async move {
            if let Some(ref injector) = fi {
                if let Some(fault_type) = injector.should_inject("archival_memory_search") {
                    return format!("Error: simulated fault: {:?}", fault_type);
                }
            }

            let agent_id = input.get("agent_id").and_then(|v| v.as_str()).unwrap_or("");
            let query = input.get("query").and_then(|v| v.as_str()).unwrap_or("");

            if agent_id.is_empty() || query.is_empty() {
                return "Error: missing required parameters (agent_id, query)".to_string();
            }

            let agents = mem.read().await;
            let agent = match agents.get(agent_id) {
                Some(a) => a,
                None => return format!("Error: agent '{}' not found", agent_id),
            };

            // Simple text search (in real impl, this would be semantic search via Umi)
            let query_lower = query.to_lowercase();
            let results: Vec<_> = agent
                .archival
                .iter()
                .filter(|e| e.to_lowercase().contains(&query_lower))
                .take(10)
                .collect();

            if results.is_empty() {
                "No results found".to_string()
            } else {
                let joined: Vec<String> = results.iter().map(|s| s.to_string()).collect();
                format!(
                    "Found {} results:\n{}",
                    joined.len(),
                    joined.join("\n---\n")
                )
            }
        })
    });

    registry
        .register_builtin(
            "archival_memory_search",
            "Search archival memory using semantic search.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": { "type": "string" },
                    "query": { "type": "string", "description": "Search query" },
                    "page": { "type": "integer", "description": "Page number (optional)", "default": 0 }
                },
                "required": ["agent_id", "query"]
            }),
            handler,
        )
        .await;

    // conversation_search tool
    let mem = agent_memory;
    let fi = fault_injector;
    let handler: BuiltinToolHandler = Arc::new(move |input: &Value| {
        let mem = mem.clone();
        let fi = fi.clone();
        let input = input.clone();
        Box::pin(async move {
            if let Some(ref injector) = fi {
                if let Some(fault_type) = injector.should_inject("conversation_search") {
                    return format!("Error: simulated fault: {:?}", fault_type);
                }
            }

            let agent_id = input.get("agent_id").and_then(|v| v.as_str()).unwrap_or("");
            let query = input.get("query").and_then(|v| v.as_str()).unwrap_or("");

            if agent_id.is_empty() || query.is_empty() {
                return "Error: missing required parameters (agent_id, query)".to_string();
            }

            let agents = mem.read().await;
            let agent = match agents.get(agent_id) {
                Some(a) => a,
                None => return format!("Error: agent '{}' not found", agent_id),
            };

            let query_lower = query.to_lowercase();
            let results: Vec<_> = agent
                .conversations
                .iter()
                .filter(|(_, content)| content.to_lowercase().contains(&query_lower))
                .take(10)
                .map(|(role, content)| format!("[{}]: {}", role, content))
                .collect();

            if results.is_empty() {
                "No matching conversations found".to_string()
            } else {
                format!(
                    "Found {} results:\n{}",
                    results.len(),
                    results.join("\n---\n")
                )
            }
        })
    });

    registry
        .register_builtin(
            "conversation_search",
            "Search past conversations.",
            json!({
                "type": "object",
                "properties": {
                    "agent_id": { "type": "string" },
                    "query": { "type": "string", "description": "Search query" },
                    "page": { "type": "integer", "description": "Page number (optional)", "default": 0 }
                },
                "required": ["agent_id", "query"]
            }),
            handler,
        )
        .await;

    registry
}

// =============================================================================
// Basic Functionality Tests
// =============================================================================

#[tokio::test]
async fn test_dst_core_memory_append_basic() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12345u64);
    println!("DST seed: {}", seed);

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // Append to new block
    let result = registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "content": "I am a helpful assistant"
            }),
        )
        .await;

    assert!(result.success, "First append should succeed");
    assert!(result.output.contains("Successfully"));

    // Append more content
    let result = registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "content": "I enjoy helping users"
            }),
        )
        .await;

    assert!(result.success, "Second append should succeed");

    // Verify memory state
    let agents = agent_memory.read().await;
    let persona = agents
        .get("agent_001")
        .unwrap()
        .blocks
        .get("persona")
        .unwrap();
    assert!(persona.contains("helpful assistant"));
    assert!(persona.contains("enjoy helping"));
}

#[tokio::test]
async fn test_dst_core_memory_replace_basic() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(22222u64);
    println!("DST seed: {}", seed);

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // First append some content
    registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "content": "I am a helpful assistant"
            }),
        )
        .await;

    // Replace content
    let result = registry
        .execute(
            "core_memory_replace",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "old_content": "helpful",
                "new_content": "friendly"
            }),
        )
        .await;

    assert!(result.success, "Replace should succeed");
    assert!(result.output.contains("Successfully"));

    // Verify
    let agents = agent_memory.read().await;
    let persona = agents
        .get("agent_001")
        .unwrap()
        .blocks
        .get("persona")
        .unwrap();
    assert!(persona.contains("friendly"));
    assert!(!persona.contains("helpful"));
}

#[tokio::test]
async fn test_dst_archival_memory_insert_and_search() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(33333u64);
    println!("DST seed: {}", seed);

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // Insert archival entries
    for i in 0..5 {
        let result = registry
            .execute(
                "archival_memory_insert",
                &json!({
                    "agent_id": "agent_001",
                    "content": format!("User preference {}: likes {} coffee", i, if i % 2 == 0 { "dark" } else { "light" })
                }),
            )
            .await;
        assert!(result.success, "Insert {} should succeed", i);
    }

    // Search for dark coffee
    let result = registry
        .execute(
            "archival_memory_search",
            &json!({
                "agent_id": "agent_001",
                "query": "dark coffee"
            }),
        )
        .await;

    assert!(result.success);
    assert!(result.output.contains("dark"));
    println!("Search results: {}", result.output);
}

#[tokio::test]
async fn test_dst_conversation_search() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(44444u64);
    println!("DST seed: {}", seed);

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));

    // Pre-populate conversations
    {
        let mut agents = agent_memory.write().await;
        let agent = agents
            .entry("agent_001".to_string())
            .or_insert_with(SimAgentMemory::new);
        agent
            .conversations
            .push(("user".to_string(), "What's the weather like?".to_string()));
        agent.conversations.push((
            "assistant".to_string(),
            "I don't have weather data.".to_string(),
        ));
        agent
            .conversations
            .push(("user".to_string(), "Tell me about cats".to_string()));
        agent.conversations.push((
            "assistant".to_string(),
            "Cats are wonderful pets!".to_string(),
        ));
    }

    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // Search for cats
    let result = registry
        .execute(
            "conversation_search",
            &json!({
                "agent_id": "agent_001",
                "query": "cats"
            }),
        )
        .await;

    assert!(result.success);
    assert!(result.output.contains("cats") || result.output.contains("Cats"));
    println!("Conversation search results: {}", result.output);
}

// =============================================================================
// Fault Injection Tests
// =============================================================================

#[tokio::test]
async fn test_dst_core_memory_append_with_faults() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(55555u64);
    println!("DST seed: {}", seed);

    let rng = DeterministicRng::new(seed);
    let injector = Arc::new(
        FaultInjectorBuilder::new(rng)
            .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 1.0)) // Always fail
            .build(),
    );

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), Some(injector)).await;

    let result = registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "content": "test content"
            }),
        )
        .await;

    assert!(!result.success, "Should fail with fault injection");
    assert!(result.output.contains("Error"));
    println!("Fault correctly injected: {}", result.output);
}

#[tokio::test]
async fn test_dst_archival_search_with_faults() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(66666u64);
    println!("DST seed: {}", seed);

    let rng = DeterministicRng::new(seed);
    let injector = Arc::new(
        FaultInjectorBuilder::new(rng)
            .with_fault(FaultConfig::new(FaultType::StorageReadFail, 1.0)) // Always fail
            .build(),
    );

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), Some(injector)).await;

    let result = registry
        .execute(
            "archival_memory_search",
            &json!({
                "agent_id": "agent_001",
                "query": "test"
            }),
        )
        .await;

    assert!(!result.success, "Should fail with fault injection");
    println!("Search fault: {}", result.output);
}

#[tokio::test]
async fn test_dst_memory_tools_partial_faults() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(77777u64);
    println!("DST seed: {}", seed);

    let rng = DeterministicRng::new(seed);
    let injector = Arc::new(
        FaultInjectorBuilder::new(rng)
            .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3)) // 30% failure
            .build(),
    );

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), Some(injector)).await;

    let mut successes = 0;
    let mut failures = 0;

    for i in 0..20 {
        let result = registry
            .execute(
                "core_memory_append",
                &json!({
                    "agent_id": "agent_001",
                    "label": "facts",
                    "content": format!("Fact number {}", i)
                }),
            )
            .await;

        if result.success {
            successes += 1;
        } else {
            failures += 1;
        }
    }

    println!(
        "Partial faults: {} successes, {} failures out of 20",
        successes, failures
    );
    // With 30% failure rate, we expect ~6 failures on average
    assert!(failures > 0, "Should have some failures");
    assert!(successes > 0, "Should have some successes");
}

// =============================================================================
// Error Handling Tests
// =============================================================================

#[tokio::test]
async fn test_dst_core_memory_missing_params() {
    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // Missing content
    let result = registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_001",
                "label": "persona"
                // Missing content
            }),
        )
        .await;

    assert!(!result.success);
    assert!(result.output.contains("Error") || result.output.contains("missing"));
}

#[tokio::test]
async fn test_dst_core_memory_replace_not_found() {
    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // Try to replace in non-existent block
    let result = registry
        .execute(
            "core_memory_replace",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "old_content": "foo",
                "new_content": "bar"
            }),
        )
        .await;

    assert!(!result.success);
    assert!(result.output.contains("not found"));
}

#[tokio::test]
async fn test_dst_archival_search_no_agent() {
    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    let result = registry
        .execute(
            "archival_memory_search",
            &json!({
                "agent_id": "nonexistent_agent",
                "query": "test"
            }),
        )
        .await;

    assert!(!result.success);
    assert!(result.output.contains("not found"));
}

// =============================================================================
// Determinism Test
// =============================================================================

#[tokio::test]
async fn test_dst_memory_tools_determinism() {
    let seed = 88888u64;
    println!("DST seed: {}", seed);

    // Run the same sequence twice with the same seed
    let mut results_run1 = Vec::new();
    let mut results_run2 = Vec::new();

    for run in [&mut results_run1, &mut results_run2] {
        let rng = DeterministicRng::new(seed);
        let injector = Arc::new(
            FaultInjectorBuilder::new(rng)
                .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.5))
                .build(),
        );

        let agent_memory = Arc::new(RwLock::new(HashMap::new()));
        let registry = create_memory_registry(agent_memory.clone(), Some(injector)).await;

        for i in 0..10 {
            let result = registry
                .execute(
                    "core_memory_append",
                    &json!({
                        "agent_id": "agent_001",
                        "label": "facts",
                        "content": format!("Fact {}", i)
                    }),
                )
                .await;
            run.push(if result.success { "OK" } else { "FAIL" });
        }
    }

    println!("Run 1: {:?}", results_run1);
    println!("Run 2: {:?}", results_run2);
    assert_eq!(
        results_run1, results_run2,
        "Same seed should produce same results"
    );
}

// =============================================================================
// Multi-Agent Isolation Test
// =============================================================================

#[tokio::test]
async fn test_dst_memory_agent_isolation() {
    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(99999u64);
    println!("DST seed: {}", seed);

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = create_memory_registry(agent_memory.clone(), None).await;

    // Agent 1 stores data
    registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_001",
                "label": "persona",
                "content": "Agent 1 is a coder"
            }),
        )
        .await;

    // Agent 2 stores different data
    registry
        .execute(
            "core_memory_append",
            &json!({
                "agent_id": "agent_002",
                "label": "persona",
                "content": "Agent 2 is a writer"
            }),
        )
        .await;

    // Verify isolation
    let agents = agent_memory.read().await;

    let agent1_persona = agents
        .get("agent_001")
        .unwrap()
        .blocks
        .get("persona")
        .unwrap();
    let agent2_persona = agents
        .get("agent_002")
        .unwrap()
        .blocks
        .get("persona")
        .unwrap();

    assert!(agent1_persona.contains("coder"));
    assert!(!agent1_persona.contains("writer"));
    assert!(agent2_persona.contains("writer"));
    assert!(!agent2_persona.contains("coder"));

    println!(
        "Agent isolation verified: Agent 1 = '{}', Agent 2 = '{}'",
        agent1_persona, agent2_persona
    );
}

// =============================================================================
// Concurrent Access Test
// =============================================================================

#[tokio::test]
async fn test_dst_memory_concurrent_access() {
    use kelpie_core::{Runtime, CurrentRuntime};
    let runtime = current_runtime();

    let seed = std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(11111u64);
    println!("DST seed: {}", seed);

    let agent_memory = Arc::new(RwLock::new(HashMap::new()));
    let registry = Arc::new(create_memory_registry(agent_memory.clone(), None).await);

    // Spawn concurrent append operations
    let mut handles = Vec::new();
    for i in 0..10 {
        let reg = registry.clone();
        let handle = runtime.spawn(async move {
            reg.execute(
                "core_memory_append",
                &json!({
                    "agent_id": "agent_001",
                    "label": "facts",
                    "content": format!("Concurrent fact {}", i)
                }),
            )
            .await
        });
        handles.push(handle);
    }

    // Wait for all
    let results: Vec<_> = futures::future::join_all(handles).await;
    let success_count = results
        .iter()
        .filter(|r| r.as_ref().map(|r| r.success).unwrap_or(false))
        .count();

    println!("Concurrent access: {} / 10 succeeded", success_count);
    assert_eq!(success_count, 10, "All concurrent appends should succeed");

    // Verify all facts were stored
    let agents = agent_memory.read().await;
    let facts = agents
        .get("agent_001")
        .unwrap()
        .blocks
        .get("facts")
        .unwrap();
    for i in 0..10 {
        assert!(
            facts.contains(&format!("Concurrent fact {}", i)),
            "Missing fact {}",
            i
        );
    }
}

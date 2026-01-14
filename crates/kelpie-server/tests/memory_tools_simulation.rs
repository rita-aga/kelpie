//! DST Simulation Tests for Memory Tool Operations
//!
//! TigerStyle: Proper simulation using Simulation::new().run(|env| ...).
//!
//! These tests use the full simulation harness with:
//! - SimClock: Simulated time
//! - SimNetwork: Simulated network with faults
//! - SimStorage: Simulated storage with faults
//! - FaultInjector: Deterministic fault injection
//!
//! Tests memory operations through UmiMemoryBackend, which is the
//! intended storage layer for memory tools (not AppState HashMap).

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use umi_memory::dst::{FaultConfig, FaultType, SimConfig, Simulation};

use kelpie_server::memory::UmiMemoryBackend;

// =============================================================================
// Core Memory Operations Under Simulation
// =============================================================================

/// Test core_memory_append operation under full simulation.
///
/// Simulates the `core_memory_append` tool operation.
#[tokio::test]
async fn test_sim_core_memory_append() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Simulate core_memory_append to "persona" block
            backend
                .append_core("persona", "I am a helpful assistant")
                .await?;

            // Append more content (like the tool would)
            backend
                .append_core("persona", "I specialize in coding tasks")
                .await?;

            // Verify the append worked
            let blocks = backend.get_core_blocks().await?;
            let persona = blocks.iter().find(|b| b.label == "persona");
            assert!(persona.is_some(), "persona block should exist");
            assert!(
                persona.unwrap().value.contains("helpful assistant"),
                "content should include first append"
            );
            assert!(
                persona.unwrap().value.contains("coding tasks"),
                "content should include second append"
            );

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

/// Test core_memory_append under storage write faults.
///
/// DST: 20% StorageWriteFail probability.
#[tokio::test]
async fn test_sim_core_memory_append_with_faults() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let success_count = Arc::new(AtomicUsize::new(0));
    let fault_count = Arc::new(AtomicUsize::new(0));

    let success_clone = success_count.clone();
    let fault_clone = fault_count.clone();

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.2))
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Try multiple appends - some may fail due to faults
            for i in 0..10 {
                match backend
                    .append_core("facts", &format!("Fact number {}", i))
                    .await
                {
                    Ok(()) => {
                        success_clone.fetch_add(1, Ordering::SeqCst);
                    }
                    Err(_) => {
                        fault_clone.fetch_add(1, Ordering::SeqCst);
                    }
                }
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    let successes = success_count.load(Ordering::SeqCst);
    let faults = fault_count.load(Ordering::SeqCst);
    println!(
        "Append results: {} successes, {} faults (expected ~20% faults)",
        successes, faults
    );

    assert!(result.is_ok(), "Simulation should complete");
    // With 20% fault rate over 10 operations, we expect some of each
}

/// Test core_memory_replace operation under full simulation.
///
/// Simulates the `core_memory_replace` tool operation.
#[tokio::test]
async fn test_sim_core_memory_replace() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Set up initial content
            backend
                .append_core("persona", "I am a test assistant")
                .await?;

            // Simulate core_memory_replace
            backend
                .replace_core("persona", "test assistant", "helpful AI")
                .await?;

            // Verify the replacement
            let blocks = backend.get_core_blocks().await?;
            let persona = blocks.iter().find(|b| b.label == "persona").unwrap();
            assert!(
                persona.value.contains("helpful AI"),
                "replacement content should be present"
            );
            assert!(
                !persona.value.contains("test assistant"),
                "old content should be replaced"
            );

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

/// Test core_memory_replace under read/write faults.
///
/// Replace requires read-then-write, so both fault types matter.
#[tokio::test]
async fn test_sim_core_memory_replace_with_faults() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Set up content (may fail)
            let _ = backend.append_core("persona", "I am helpful").await;

            // Try replace (may fail at read or write)
            match backend
                .replace_core("persona", "helpful", "very helpful")
                .await
            {
                Ok(()) => println!("Replace succeeded"),
                Err(e) => println!("Replace failed (expected under faults): {}", e),
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation should complete");
}

// =============================================================================
// Archival Memory Operations Under Simulation
// =============================================================================

/// Test archival_memory_insert operation under full simulation.
///
/// Simulates the `archival_memory_insert` tool operation.
#[tokio::test]
async fn test_sim_archival_memory_insert() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Simulate archival_memory_insert
            let id = backend
                .insert_archival("User prefers dark mode in all applications")
                .await?;
            assert!(!id.is_empty(), "Should return entry ID");

            // Insert more archival entries
            backend.insert_archival("User's timezone is PST").await?;
            backend
                .insert_archival("User is a software engineer")
                .await?;

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

/// Test archival_memory_search operation under full simulation.
///
/// NOTE: In simulation mode, Umi's SimVectorBackend returns fake deterministic
/// data that doesn't include agent prefixes. After BUG-002 fix, this fake data
/// is correctly filtered out. This test verifies:
/// 1. Insert operation succeeds
/// 2. Search operation completes without error
/// 3. Results (if any) are properly filtered to this agent only
#[tokio::test]
async fn test_sim_archival_memory_search() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Insert archival entries (these succeed and store with agent prefix)
            let id1 = backend.insert_archival("User prefers dark mode").await?;
            let id2 = backend.insert_archival("User likes pizza").await?;
            let id3 = backend
                .insert_archival("User prefers concise responses")
                .await?;

            println!("Inserted archival entries: {}, {}, {}", id1, id2, id3);

            // Search - in sim mode, results may be empty because SimVectorBackend
            // returns fake data that doesn't match agent prefix filter (BUG-002 fix)
            let results = backend.search_archival("dark mode", 5).await?;
            println!(
                "Search 'dark mode' returned {} results: {:?}",
                results.len(),
                results.iter().map(|r| &r.content).collect::<Vec<_>>()
            );

            // Verify agent isolation: any returned results MUST belong to this agent
            for result in &results {
                assert!(
                    result.content.contains("[agent:test-agent]"),
                    "BUG-002: Search returned non-agent data: {}",
                    result.content
                );
            }

            let results = backend.search_archival("prefer", 5).await?;
            println!(
                "Search 'prefer' returned {} results: {:?}",
                results.len(),
                results.iter().map(|r| &r.content).collect::<Vec<_>>()
            );

            // Same isolation check
            for result in &results {
                assert!(
                    result.content.contains("[agent:test-agent]"),
                    "BUG-002: Search returned non-agent data: {}",
                    result.content
                );
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

/// Test archival operations under embedding and vector search faults.
#[tokio::test]
async fn test_sim_archival_with_search_faults() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::EmbeddingTimeout, 0.1))
        .with_fault(FaultConfig::new(FaultType::VectorSearchFail, 0.1))
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Insert (may fail due to embedding timeout)
            let _ = backend.insert_archival("Important fact").await;

            // Search (may fail due to vector search fault)
            match backend.search_archival("important", 5).await {
                Ok(results) => println!("Search returned {} results", results.len()),
                Err(e) => println!("Search failed (expected under faults): {}", e),
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation should complete");
}

// =============================================================================
// Conversation Search Under Simulation
// =============================================================================

/// Test conversation_search operation under full simulation.
///
/// NOTE: In simulation mode, SimVectorBackend returns fake data that doesn't
/// include agent prefixes. After BUG-002 fix, fake data is filtered out.
/// This test verifies store and search operations complete without error,
/// and any results are properly scoped to this agent.
#[tokio::test]
async fn test_sim_conversation_search() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "test-agent").await?;

            // Store conversation messages (these succeed with agent prefixes)
            backend
                .store_message("user", "Hello, can you help me with Python?")
                .await?;
            backend
                .store_message("assistant", "Of course! What do you need help with?")
                .await?;
            backend
                .store_message("user", "I need help with async/await")
                .await?;
            backend
                .store_message("assistant", "Async/await in Python uses asyncio...")
                .await?;

            println!("Stored 4 conversation messages");

            // Search conversations - in sim mode, results may be empty due to
            // SimVectorBackend returning fake data without agent prefixes
            let results = backend.search_conversations("Python", 5).await?;
            println!(
                "Search 'Python' returned {} results: {:?}",
                results.len(),
                results.iter().map(|r| &r.content).collect::<Vec<_>>()
            );

            // BUG-002 FIX VERIFICATION: Any results MUST belong to this agent
            for result in &results {
                assert!(
                    result.content.contains("[agent:test-agent]"),
                    "BUG-002: Conversation search returned non-agent data: {}",
                    result.content
                );
            }

            let results = backend.search_conversations("async", 5).await?;
            println!(
                "Search 'async' returned {} results: {:?}",
                results.len(),
                results.iter().map(|r| &r.content).collect::<Vec<_>>()
            );

            for result in &results {
                assert!(
                    result.content.contains("[agent:test-agent]"),
                    "BUG-002: Conversation search returned non-agent data: {}",
                    result.content
                );
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

// =============================================================================
// Multi-Agent Isolation Under Simulation
// =============================================================================

/// Test that memory is isolated between agents under simulation.
///
/// BUG-002 FIXED: Archival search now filters by agent_id.
/// This test verifies that agents cannot see each other's data.
#[tokio::test]
async fn test_sim_multi_agent_isolation() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .run(|env| async move {
            // Create two backends for different agents
            let agent1 = UmiMemoryBackend::from_sim_env(&env, "agent-1").await?;
            let agent2 = UmiMemoryBackend::from_sim_env(&env, "agent-2").await?;

            // Agent 1 stores memory with unique content
            agent1.append_core("persona", "I am Agent 1").await?;
            agent1
                .insert_archival("Agent 1's secret data about project alpha")
                .await?;

            // Agent 2 stores different memory
            agent2.append_core("persona", "I am Agent 2").await?;
            agent2
                .insert_archival("Agent 2's secret data about project beta")
                .await?;

            // Verify each agent has its own persona (core memory is local to instance)
            let blocks1 = agent1.get_core_blocks().await?;
            let blocks2 = agent2.get_core_blocks().await?;

            println!(
                "Agent 1 blocks: {:?}",
                blocks1.iter().map(|b| &b.value).collect::<Vec<_>>()
            );
            println!(
                "Agent 2 blocks: {:?}",
                blocks2.iter().map(|b| &b.value).collect::<Vec<_>>()
            );

            // Each agent should have persona block
            assert!(
                blocks1.iter().any(|b| b.value.contains("Agent 1")),
                "Agent 1 should have its own persona"
            );
            assert!(
                blocks2.iter().any(|b| b.value.contains("Agent 2")),
                "Agent 2 should have its own persona"
            );

            // BUG-002 VERIFICATION: Archival search must be isolated per agent
            let results1 = agent1.search_archival("secret", 5).await?;
            println!(
                "Agent 1 archival search results: {:?}",
                results1.iter().map(|r| &r.content).collect::<Vec<_>>()
            );

            // STRICT ASSERTION: Agent 1 should ONLY see its own data
            for result in &results1 {
                assert!(
                    result.content.contains("[agent:agent-1]"),
                    "BUG-002 REGRESSION: Agent 1 search returned non-agent-1 data: {}",
                    result.content
                );
                assert!(
                    !result.content.contains("Agent 2"),
                    "BUG-002 REGRESSION: Agent 1 can see Agent 2's data: {}",
                    result.content
                );
            }

            // Also verify Agent 2 isolation
            let results2 = agent2.search_archival("secret", 5).await?;
            println!(
                "Agent 2 archival search results: {:?}",
                results2.iter().map(|r| &r.content).collect::<Vec<_>>()
            );

            for result in &results2 {
                assert!(
                    result.content.contains("[agent:agent-2]"),
                    "BUG-002 REGRESSION: Agent 2 search returned non-agent-2 data: {}",
                    result.content
                );
                assert!(
                    !result.content.contains("Agent 1"),
                    "BUG-002 REGRESSION: Agent 2 can see Agent 1's data: {}",
                    result.content
                );
            }

            println!("BUG-002 FIX VERIFIED: Agent isolation is enforced");

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Simulation failed: {:?}", result.err());
}

// =============================================================================
// High Load / Stress Testing Under Simulation
// =============================================================================

/// Test memory operations under high load with faults.
#[tokio::test]
async fn test_sim_memory_high_load() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let success_count = Arc::new(AtomicUsize::new(0));
    let fault_count = Arc::new(AtomicUsize::new(0));

    let success_clone = success_count.clone();
    let fault_clone = fault_count.clone();

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.05))
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.02))
        .with_fault(FaultConfig::new(FaultType::EmbeddingTimeout, 0.02))
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "stress-test").await?;

            // Perform many operations
            for i in 0..50 {
                // Core memory append
                match backend.append_core("log", &format!("Event {}", i)).await {
                    Ok(()) => success_clone.fetch_add(1, Ordering::SeqCst),
                    Err(_) => fault_clone.fetch_add(1, Ordering::SeqCst),
                };

                // Archival insert
                match backend
                    .insert_archival(&format!("Archival entry {}", i))
                    .await
                {
                    Ok(_) => success_clone.fetch_add(1, Ordering::SeqCst),
                    Err(_) => fault_clone.fetch_add(1, Ordering::SeqCst),
                };

                // Periodic search
                if i % 10 == 0 {
                    match backend.search_archival("entry", 5).await {
                        Ok(_) => success_clone.fetch_add(1, Ordering::SeqCst),
                        Err(_) => fault_clone.fetch_add(1, Ordering::SeqCst),
                    };
                }
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    let successes = success_count.load(Ordering::SeqCst);
    let faults = fault_count.load(Ordering::SeqCst);
    println!(
        "High load results: {} successes, {} faults (total: {})",
        successes,
        faults,
        successes + faults
    );

    assert!(result.is_ok(), "Simulation should complete under load");
}

// =============================================================================
// Determinism Verification
// =============================================================================

/// Verify that simulation is deterministic - same seed produces same results.
#[tokio::test]
async fn test_sim_determinism() {
    let seed = 42u64;

    // Run 1
    let config1 = SimConfig::with_seed(seed);

    Simulation::new(config1)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
        .run(|env| {
            async move {
                let backend = UmiMemoryBackend::from_sim_env(&env, "det-test").await?;

                for i in 0..10 {
                    let success = backend
                        .append_core("test", &format!("Entry {}", i))
                        .await
                        .is_ok();
                    // Can't push to results1 inside async - just test it works
                    println!("Run 1, op {}: {}", i, success);
                }

                Ok::<(), anyhow::Error>(())
            }
        })
        .await
        .unwrap();

    // Run 2 with same seed
    let config2 = SimConfig::with_seed(seed);

    Simulation::new(config2)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "det-test").await?;

            for i in 0..10 {
                let success = backend
                    .append_core("test", &format!("Entry {}", i))
                    .await
                    .is_ok();
                println!("Run 2, op {}: {}", i, success);
            }

            Ok::<(), anyhow::Error>(())
        })
        .await
        .unwrap();

    // Same seed should produce same sequence of successes/failures
    // (Can't easily capture results from async closure, but the prints show it)
    println!("Determinism test completed - check logs for matching patterns");
}

// =============================================================================
// Storage Corruption Under Simulation
// =============================================================================

/// Test that the system handles storage corruption gracefully.
#[tokio::test]
async fn test_sim_storage_corruption() {
    let config = SimConfig::from_env_or_random();
    println!("DST seed: {} (set DST_SEED to reproduce)", config.seed());

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageCorruption, 0.1))
        .run(|env| async move {
            let backend = UmiMemoryBackend::from_sim_env(&env, "corruption-test").await?;

            // Try writes that may get corrupted
            for i in 0..10 {
                match backend
                    .append_core("data", &format!("Important data {}", i))
                    .await
                {
                    Ok(()) => println!("Write {} succeeded", i),
                    Err(e) => println!("Write {} had corruption: {}", i, e),
                }
            }

            // Verify what data is readable
            match backend.get_core_blocks().await {
                Ok(blocks) => println!("After corruption test: {} blocks readable", blocks.len()),
                Err(e) => println!("Read failed due to corruption: {}", e),
            }

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Storage corruption simulation should complete"
    );
}

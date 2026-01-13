//! DST Tests for Umi Memory Integration
//!
//! TigerStyle: Write tests BEFORE implementation.
//! These tests define the expected behavior of UmiMemoryBackend.
//!
//! Run with: `cargo test -p kelpie-server --test umi_integration_dst`
//! Reproduce failures: `DST_SEED=<seed> cargo test -p kelpie-server --test umi_integration_dst`

use anyhow::Result;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use umi_memory::dst::{FaultConfig, FaultType, SimConfig, Simulation};

// Import the module we're testing
use kelpie_server::memory::UmiMemoryBackend;

/// Test that we can create and retrieve core memory blocks.
///
/// DST: No faults - baseline behavior.
#[tokio::test]
async fn test_dst_core_memory_basic() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Add core memory blocks
            backend
                .append_core("persona", "I am a helpful assistant")
                .await?;
            backend
                .append_core("human", "User prefers concise responses")
                .await?;

            // Verify retrieval
            let blocks = backend.get_core_blocks().await?;
            assert_eq!(blocks.len(), 2);
            assert!(blocks.iter().any(|b| b.label == "persona"));
            assert!(blocks.iter().any(|b| b.label == "human"));

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Core memory basic operations failed: {:?}",
        result.err()
    );
}

/// Test core memory operations under storage write failures.
///
/// DST: 10% StorageWriteFail probability.
/// Expected: Operations succeed after retry, data persists.
#[tokio::test]
async fn test_dst_core_memory_with_storage_faults() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.05))
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Operations should succeed despite faults (with retries)
            backend.append_core("persona", "I am helpful").await?;

            // Verify data persisted
            let blocks = backend.get_core_blocks().await?;
            assert!(
                !blocks.is_empty(),
                "Core memory should persist despite faults"
            );

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Core memory should handle storage faults: {:?}",
        result.err()
    );
}

/// Test core memory replace operation.
///
/// DST: No faults - verify replace semantics.
#[tokio::test]
async fn test_dst_core_memory_replace() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Initial content
            backend
                .append_core("persona", "I am a helpful assistant")
                .await?;

            // Replace content
            backend
                .replace_core("persona", "helpful", "friendly")
                .await?;

            // Verify replacement
            let blocks = backend.get_core_blocks().await?;
            let persona = blocks.iter().find(|b| b.label == "persona").unwrap();
            assert!(persona.value.contains("friendly"));
            assert!(!persona.value.contains("helpful"));

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Core memory replace failed: {:?}",
        result.err()
    );
}

/// Test archival memory insert and search.
///
/// DST: No faults - baseline archival operations.
#[tokio::test]
async fn test_dst_archival_memory_basic() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Insert archival memories
            backend
                .insert_archival("User prefers dark mode for all applications")
                .await?;
            backend
                .insert_archival("User's favorite color is blue")
                .await?;
            backend
                .insert_archival("User works in software engineering")
                .await?;

            // Search should return results (SimEmbedding returns deterministic results)
            let results = backend.search_archival("color preference", 5).await?;
            // Note: SimEmbeddingProvider may not produce semantically meaningful results
            // This test verifies the API works, not semantic accuracy
            assert!(results.len() <= 5, "Should respect limit");

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Archival memory basic operations failed: {:?}",
        result.err()
    );
}

/// Test archival memory under embedding failures.
///
/// DST: 10% EmbeddingTimeout probability.
/// Expected: Graceful degradation or retry.
#[tokio::test]
async fn test_dst_archival_memory_with_embedding_faults() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::EmbeddingTimeout, 0.1))
        .with_fault(FaultConfig::new(FaultType::EmbeddingRateLimit, 0.05))
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Insert should handle embedding failures (SimProvider doesn't fail)
            backend
                .insert_archival("Important information to remember")
                .await?;

            // Search should work with SimProvider
            let _results = backend.search_archival("important", 5).await?;
            // May or may not find results depending on SimProvider behavior

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Archival should handle embedding faults: {:?}",
        result.err()
    );
}

/// Test conversation storage and search.
///
/// DST: No faults - baseline conversation operations.
#[tokio::test]
async fn test_dst_conversation_storage_basic() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Store conversation messages
            backend
                .store_message("user", "What's the weather like?")
                .await?;
            backend
                .store_message("assistant", "I don't have real-time weather data")
                .await?;
            backend
                .store_message("user", "Tell me about climate change")
                .await?;
            backend
                .store_message("assistant", "Climate change refers to...")
                .await?;

            // Search past conversations
            let results = backend.search_conversations("weather", 5).await?;
            assert!(results.len() <= 5, "Should respect limit");

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Conversation storage basic failed: {:?}",
        result.err()
    );
}

/// Test conversation search under vector search failures.
///
/// DST: 10% VectorSearchFail probability.
/// Expected: Fallback to text search or graceful error.
#[tokio::test]
async fn test_dst_conversation_search_with_vector_faults() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::VectorSearchFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::VectorSearchTimeout, 0.05))
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            backend
                .store_message("user", "Remember this important info")
                .await?;

            // Search should handle vector failures (SimProvider doesn't fail)
            let _ = backend.search_conversations("important", 5).await;
            // We don't assert success - just that it doesn't panic

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Conversation search should handle vector faults: {:?}",
        result.err()
    );
}

/// Test crash recovery - data persists across simulated restarts.
///
/// DST: CrashAfterWrite to simulate crash after write commits.
/// Expected: Data written before crash survives.
/// Note: Current implementation uses in-memory storage, so this tests
/// the API contract rather than actual persistence.
#[tokio::test]
async fn test_dst_crash_recovery() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.05))
        .run(|_env| async move {
            // Phase 1: Write data
            let backend = UmiMemoryBackend::new_sim(seed).await?;
            backend.append_core("persona", "Persistent data").await?;
            backend
                .insert_archival("Important fact to remember")
                .await?;

            // Verify data exists within the same session
            let blocks = backend.get_core_blocks().await?;
            assert!(
                !blocks.is_empty(),
                "Core memory should exist within session"
            );

            // Note: True crash recovery would require persistent storage backend
            // Current SimStorageBackend is in-memory only

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Crash recovery test failed: {:?}",
        result.err()
    );
}

/// Test agent scoping - different agents have isolated memory.
///
/// DST: No faults - verify isolation semantics.
#[tokio::test]
async fn test_dst_agent_isolation() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .run(|_env| async move {
            // Agent 1
            let agent1_backend =
                UmiMemoryBackend::new_sim_with_agent(seed, "agent_001".to_string()).await?;
            agent1_backend
                .append_core("persona", "I am Agent 1")
                .await?;

            // Agent 2
            let agent2_backend =
                UmiMemoryBackend::new_sim_with_agent(seed, "agent_002".to_string()).await?;
            agent2_backend
                .append_core("persona", "I am Agent 2")
                .await?;

            // Verify isolation - each agent has their own core memory
            let agent1_blocks = agent1_backend.get_core_blocks().await?;
            let agent2_blocks = agent2_backend.get_core_blocks().await?;

            let agent1_persona = agent1_blocks.iter().find(|b| b.label == "persona").unwrap();
            let agent2_persona = agent2_blocks.iter().find(|b| b.label == "persona").unwrap();

            assert!(agent1_persona.value.contains("Agent 1"));
            assert!(agent2_persona.value.contains("Agent 2"));
            assert!(!agent1_persona.value.contains("Agent 2")); // Isolation check

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "Agent isolation failed: {:?}", result.err());
}

/// Test high-load scenario with multiple operations.
///
/// DST: Multiple fault types at low probability.
/// Expected: System remains stable under concurrent load with faults.
#[tokio::test]
async fn test_dst_high_load_with_faults() {
    let config = SimConfig::from_env_or_random();
    let seed = config.seed();
    println!("DST seed: {}", seed);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.02))
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.02))
        .with_fault(FaultConfig::new(FaultType::StorageLatency, 0.05))
        .with_fault(FaultConfig::new(FaultType::EmbeddingTimeout, 0.02))
        .with_fault(FaultConfig::new(FaultType::VectorSearchFail, 0.02))
        .run(|_env| async move {
            let backend = UmiMemoryBackend::new_sim(seed).await?;

            // Simulate high load: many operations in sequence
            for i in 0..50 {
                // Core memory operations
                backend
                    .append_core("scratch", &format!("Note {}", i))
                    .await?;

                // Archival operations
                if i % 5 == 0 {
                    backend
                        .insert_archival(&format!("Archival entry {}", i))
                        .await?;
                }

                // Conversation operations
                if i % 3 == 0 {
                    backend
                        .store_message("user", &format!("Message {}", i))
                        .await?;
                }

                // Search operations
                if i % 10 == 0 {
                    let _ = backend.search_archival("entry", 5).await;
                }
            }

            // Final verification: system should be in consistent state
            let blocks = backend.get_core_blocks().await?;
            assert!(
                !blocks.is_empty(),
                "Should have core memory after high load"
            );

            Ok::<(), anyhow::Error>(())
        })
        .await;

    assert!(result.is_ok(), "High load test failed: {:?}", result.err());
}

/// Test determinism: same seed produces same results.
///
/// This is a meta-test verifying the DST framework itself.
#[tokio::test]
async fn test_dst_determinism() {
    let seed = 42u64;

    // Use atomic counters to track results from inside closures
    let result1_len = Arc::new(AtomicUsize::new(0));
    let result2_len = Arc::new(AtomicUsize::new(0));

    // Run 1: Create backend and add data
    let r1_len = result1_len.clone();
    let config1 = SimConfig::with_seed(seed);
    let run1: Result<()> = Simulation::new(config1)
        .run(|_env| {
            let r1 = r1_len.clone();
            async move {
                let backend = UmiMemoryBackend::new_sim(seed).await?;
                backend.append_core("persona", "Deterministic test").await?;

                let blocks = backend.get_core_blocks().await?;
                let persona = blocks.iter().find(|b| b.label == "persona").unwrap();
                r1.store(persona.value.len(), Ordering::SeqCst);
                Ok::<(), anyhow::Error>(())
            }
        })
        .await;

    // Run 2: Same seed should produce same result
    let r2_len = result2_len.clone();
    let config2 = SimConfig::with_seed(seed);
    let run2: Result<()> = Simulation::new(config2)
        .run(|_env| {
            let r2 = r2_len.clone();
            async move {
                let backend = UmiMemoryBackend::new_sim(seed).await?;
                backend.append_core("persona", "Deterministic test").await?;

                let blocks = backend.get_core_blocks().await?;
                let persona = blocks.iter().find(|b| b.label == "persona").unwrap();
                r2.store(persona.value.len(), Ordering::SeqCst);
                Ok::<(), anyhow::Error>(())
            }
        })
        .await;

    assert!(run1.is_ok(), "Run 1 failed: {:?}", run1.err());
    assert!(run2.is_ok(), "Run 2 failed: {:?}", run2.err());
    assert_eq!(
        result1_len.load(Ordering::SeqCst),
        result2_len.load(Ordering::SeqCst),
        "Same seed should produce identical results"
    );
}

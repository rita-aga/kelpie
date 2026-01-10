//! DST tests for memory operations
//!
//! TigerStyle: Deterministic testing of memory tiers under fault injection.

use bytes::Bytes;
use kelpie_core::actor::ActorId;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_memory::{
    Checkpoint, CoreMemory, CoreMemoryConfig, MemoryBlock, MemoryBlockType, SearchQuery,
    WorkingMemory, CORE_MEMORY_SIZE_BYTES_MIN,
};

// =============================================================================
// Core Memory Tests
// =============================================================================

#[test]
fn test_dst_core_memory_basic() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = CoreMemory::with_defaults();

        // Add blocks
        memory.add_block(MemoryBlock::system("You are a helpful assistant."))?;
        memory.add_block(MemoryBlock::persona("Friendly and knowledgeable"))?;
        memory.add_block(MemoryBlock::human("User is a software developer"))?;

        assert_eq!(memory.block_count(), 3);
        assert!(memory.size_bytes() > 0);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_core_memory_update() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = CoreMemory::with_defaults();

        let id = memory.add_block(MemoryBlock::scratch("Initial content"))?;

        memory.update_block(&id, "Updated content")?;

        let block = memory.get_block(&id).unwrap();
        assert_eq!(block.content, "Updated content");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_core_memory_render() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = CoreMemory::with_defaults();

        memory.add_block(MemoryBlock::system("Be helpful"))?;
        memory.add_block(MemoryBlock::persona("Friendly"))?;

        let rendered = memory.render();

        assert!(rendered.contains("<core_memory>"));
        assert!(rendered.contains("</core_memory>"));
        assert!(rendered.contains("Be helpful"));
        assert!(rendered.contains("Friendly"));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_core_memory_capacity_limit() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        // Use minimum capacity
        let mem_config = CoreMemoryConfig::with_max_bytes(CORE_MEMORY_SIZE_BYTES_MIN);
        let mut memory = CoreMemory::new(mem_config);

        // Fill up most of the memory
        memory.add_block(MemoryBlock::scratch("x".repeat(3000)))?;

        // Try to add more than available
        let result = memory.add_block(MemoryBlock::scratch("y".repeat(2000)));

        assert!(result.is_err());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Working Memory Tests
// =============================================================================

#[test]
fn test_dst_working_memory_basic() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("user:session", Bytes::from("active"))?;
        memory.set("counter", Bytes::from("42"))?;

        assert!(memory.exists("user:session"));
        assert!(memory.exists("counter"));

        let value = memory.get("counter").unwrap();
        assert_eq!(value.as_ref(), b"42");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_working_memory_increment() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = WorkingMemory::with_defaults();

        let val = memory.incr("counter", 1)?;
        assert_eq!(val, 1);

        let val = memory.incr("counter", 5)?;
        assert_eq!(val, 6);

        let val = memory.incr("counter", -2)?;
        assert_eq!(val, 4);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_working_memory_append() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = WorkingMemory::with_defaults();

        memory.append("log", "line1\n")?;
        memory.append("log", "line2\n")?;
        memory.append("log", "line3\n")?;

        let value = memory.get("log").unwrap();
        assert_eq!(value.as_ref(), b"line1\nline2\nline3\n");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_working_memory_keys_prefix() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = WorkingMemory::with_defaults();

        memory.set("user:1:name", Bytes::from("Alice"))?;
        memory.set("user:2:name", Bytes::from("Bob"))?;
        memory.set("session:abc", Bytes::from("data"))?;

        let user_keys = memory.keys_with_prefix("user:");
        assert_eq!(user_keys.len(), 2);

        let session_keys = memory.keys_with_prefix("session:");
        assert_eq!(session_keys.len(), 1);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Search Tests
// =============================================================================

#[test]
fn test_dst_search_by_text() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = CoreMemory::with_defaults();

        memory.add_block(MemoryBlock::facts("The capital of France is Paris"))?;
        memory.add_block(MemoryBlock::facts("Python is a programming language"))?;
        memory.add_block(MemoryBlock::facts("The Eiffel Tower is in Paris"))?;

        let query = SearchQuery::new().text("Paris");

        let matches: Vec<_> = memory.blocks().filter(|b| query.matches(b)).collect();

        assert_eq!(matches.len(), 2);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_search_by_type() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let mut memory = CoreMemory::with_defaults();

        memory.add_block(MemoryBlock::facts("Fact 1"))?;
        memory.add_block(MemoryBlock::facts("Fact 2"))?;
        memory.add_block(MemoryBlock::persona("Persona"))?;
        memory.add_block(MemoryBlock::system("System"))?;

        let query = SearchQuery::new().block_type(MemoryBlockType::Facts);

        let matches: Vec<_> = memory.blocks().filter(|b| query.matches(b)).collect();

        assert_eq!(matches.len(), 2);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Checkpoint Tests
// =============================================================================

#[test]
fn test_dst_checkpoint_roundtrip() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let actor_id = ActorId::new("test", "memory-1")?;

        // Create memory with content
        let mut core = CoreMemory::with_defaults();
        core.add_block(MemoryBlock::system("Test system prompt"))?;

        let mut working = WorkingMemory::with_defaults();
        working.set("key", Bytes::from("value"))?;

        // Create checkpoint
        let checkpoint = Checkpoint::new(actor_id, 1, Some(&core), Some(&working))?;

        // Serialize and deserialize
        let bytes = checkpoint.to_bytes()?;
        let restored_checkpoint = Checkpoint::from_bytes(&bytes)?;

        // Restore memory
        let restored_core = restored_checkpoint.restore_core()?.unwrap();
        let restored_working = restored_checkpoint.restore_working()?.unwrap();

        // Verify
        assert_eq!(restored_core.block_count(), 1);
        assert!(restored_working.exists("key"));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_checkpoint_core_only() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let actor_id = ActorId::new("test", "memory-2")?;

        let mut core = CoreMemory::with_defaults();
        core.add_block(MemoryBlock::persona("Helpful assistant"))?;

        let checkpoint = Checkpoint::new(actor_id, 1, Some(&core), None)?;

        let restored_core = checkpoint.restore_core()?.unwrap();
        let restored_working = checkpoint.restore_working()?;

        assert_eq!(restored_core.block_count(), 1);
        assert!(restored_working.is_none());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Determinism Tests
// =============================================================================

#[test]
fn test_dst_memory_deterministic() {
    let seed = 12345;

    let run_test = || {
        let config = SimConfig::new(seed);

        Simulation::new(config).run(|_env| async move {
            let mut core = CoreMemory::with_defaults();
            let mut working = WorkingMemory::with_defaults();

            // Perform operations
            for i in 0..10 {
                core.add_block(MemoryBlock::facts(format!("Fact {}", i)))?;
                working.set(format!("key{}", i), Bytes::from(format!("value{}", i)))?;
            }

            Ok((core.size_bytes(), working.size_bytes()))
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Determinism violated: results differ");
}

// =============================================================================
// Fault Injection Tests (placeholder - memory operations are in-memory)
// =============================================================================

#[test]
fn test_dst_memory_under_simulated_load() {
    let config = SimConfig::from_env_or_random().with_max_steps(100_000);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CPUStarvation, 0.01))
        .run(|_env| async move {
            let mut core = CoreMemory::with_defaults();
            let mut working = WorkingMemory::with_defaults();

            // Stress test with many operations
            for i in 0..100 {
                if core.available_bytes() > 100 {
                    let _ = core.add_block(MemoryBlock::scratch(format!("Note {}", i)));
                }
                working.set(format!("k{}", i), Bytes::from(format!("v{}", i)))?;

                if i % 10 == 0 {
                    working.delete(&format!("k{}", i / 2));
                }
            }

            Ok(())
        });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Integration Tests - Memory + Actor
// =============================================================================

#[test]
fn test_dst_letta_style_memory() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        // Create Letta-style memory layout
        let mut core = CoreMemory::letta_default();

        // Update persona
        let persona_block = core
            .get_first_by_type_mut(MemoryBlockType::Persona)
            .unwrap();
        persona_block.update_content("I am a helpful AI assistant with expertise in coding.");

        // Update human info
        let human_block = core.get_first_by_type_mut(MemoryBlockType::Human).unwrap();
        human_block.update_content("User is a software developer working on Rust projects.");

        // Add facts
        core.add_block(MemoryBlock::facts(
            "User prefers functional programming style.",
        ))?;

        // Render for LLM
        let rendered = core.render();

        assert!(rendered.contains("helpful AI assistant"));
        assert!(rendered.contains("software developer"));
        assert!(rendered.contains("functional programming"));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

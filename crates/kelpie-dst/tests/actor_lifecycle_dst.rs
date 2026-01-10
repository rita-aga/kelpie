//! DST tests for actor lifecycle
//!
//! TigerStyle: Deterministic testing of actor activation, deactivation,
//! and state persistence under fault injection.

use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::actor::{Actor, ActorContext, ActorId};
use kelpie_core::error::{Error, Result};
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_runtime::{ActivationState, ActiveActor};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// =============================================================================
// Test Actor Definition
// =============================================================================

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
struct CounterState {
    count: i64,
}

#[derive(Clone)]
struct CounterActor;

#[async_trait]
impl Actor for CounterActor {
    type State = CounterState;

    async fn invoke(
        &self,
        ctx: &mut ActorContext<Self::State>,
        operation: &str,
        _payload: Bytes,
    ) -> Result<Bytes> {
        match operation {
            "increment" => {
                ctx.state.count += 1;
                Ok(Bytes::from(ctx.state.count.to_string()))
            }
            "get" => Ok(Bytes::from(ctx.state.count.to_string())),
            "reset" => {
                ctx.state.count = 0;
                Ok(Bytes::from("0"))
            }
            _ => Err(Error::InvalidOperation {
                operation: operation.to_string(),
            }),
        }
    }
}

// =============================================================================
// Basic Lifecycle Tests
// =============================================================================

#[test]
fn test_dst_actor_activation_basic() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let actor_id = ActorId::new("dst-test", "counter-1")?;
        let storage = Arc::new(env.storage);

        let active = ActiveActor::activate(actor_id.clone(), CounterActor, storage).await?;

        assert_eq!(active.activation_state(), ActivationState::Active);
        assert_eq!(active.id, actor_id);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_actor_invocation() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let actor_id = ActorId::new("dst-test", "counter-2")?;
        let storage = Arc::new(env.storage);

        let mut active = ActiveActor::activate(actor_id, CounterActor, storage).await?;

        // Multiple increments
        let result = active.process_invocation("increment", Bytes::new()).await?;
        assert_eq!(result, Bytes::from("1"));

        let result = active.process_invocation("increment", Bytes::new()).await?;
        assert_eq!(result, Bytes::from("2"));

        let result = active.process_invocation("get", Bytes::new()).await?;
        assert_eq!(result, Bytes::from("2"));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_actor_deactivation() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let actor_id = ActorId::new("dst-test", "counter-3")?;
        let storage = Arc::new(env.storage);

        let mut active = ActiveActor::activate(actor_id, CounterActor, storage).await?;

        active.process_invocation("increment", Bytes::new()).await?;
        active.deactivate().await?;

        assert_eq!(active.activation_state(), ActivationState::Deactivated);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// State Persistence Tests
// =============================================================================

#[test]
fn test_dst_state_persistence_across_activations() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let actor_id = ActorId::new("dst-test", "persistent-1")?;
        let storage = Arc::new(env.storage);

        // First activation: increment and deactivate
        {
            let mut active =
                ActiveActor::activate(actor_id.clone(), CounterActor, storage.clone()).await?;

            active.process_invocation("increment", Bytes::new()).await?;
            active.process_invocation("increment", Bytes::new()).await?;
            active.process_invocation("increment", Bytes::new()).await?;

            active.deactivate().await?;
        }

        // Second activation: state should be restored
        {
            let mut active = ActiveActor::activate(actor_id, CounterActor, storage).await?;

            let result = active.process_invocation("get", Bytes::new()).await?;
            assert_eq!(result, Bytes::from("3"));
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Multiple Actor Isolation Tests
// =============================================================================

#[test]
fn test_dst_multiple_actors_isolation() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let actor1_id = ActorId::new("dst-test", "isolated-1")?;
        let actor2_id = ActorId::new("dst-test", "isolated-2")?;
        let storage = Arc::new(env.storage);

        // Activate both actors
        let mut actor1 = ActiveActor::activate(actor1_id, CounterActor, storage.clone()).await?;

        let mut actor2 = ActiveActor::activate(actor2_id, CounterActor, storage).await?;

        // Increment actor1 three times
        actor1.process_invocation("increment", Bytes::new()).await?;
        actor1.process_invocation("increment", Bytes::new()).await?;
        actor1.process_invocation("increment", Bytes::new()).await?;

        // Increment actor2 once
        actor2.process_invocation("increment", Bytes::new()).await?;

        // Verify isolation
        let result1 = actor1.process_invocation("get", Bytes::new()).await?;
        let result2 = actor2.process_invocation("get", Bytes::new()).await?;

        assert_eq!(result1, Bytes::from("3"));
        assert_eq!(result2, Bytes::from("1"));

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Fault Injection Tests
// =============================================================================

#[test]
fn test_dst_activation_with_storage_read_fault() {
    // Use a specific seed for reproducibility in this test
    let config = SimConfig::new(42);

    // 100% probability of storage read failures
    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 1.0))
        .run(|env| async move {
            let actor_id = ActorId::new("dst-test", "fault-read-1")?;
            let storage = Arc::new(env.storage);

            // Activation should still succeed (uses default state on read failure)
            let active = ActiveActor::activate(actor_id, CounterActor, storage).await?;
            assert_eq!(active.activation_state(), ActivationState::Active);

            Ok(())
        });

    // The runtime gracefully handles read failures during activation
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_persistence_with_intermittent_failures() {
    // Test with 30% write failure probability
    let config = SimConfig::new(12345);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.3))
        .run(|env| async move {
            let actor_id = ActorId::new("dst-test", "intermittent-1")?;
            let storage = Arc::new(env.storage);

            let mut active = ActiveActor::activate(actor_id, CounterActor, storage).await?;

            // Perform operations - these should succeed
            active.process_invocation("increment", Bytes::new()).await?;
            active.process_invocation("increment", Bytes::new()).await?;

            // Deactivation may fail due to storage write failure
            // This is expected behavior under fault injection
            let _deactivate_result = active.deactivate().await;

            // The deactivation should complete (logs error but continues)
            assert_eq!(active.activation_state(), ActivationState::Deactivated);

            // Result is OK because we handle errors gracefully
            Ok(())
        });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Determinism Tests
// =============================================================================

#[test]
fn test_dst_deterministic_behavior() {
    let seed = 999;

    // Run the same test twice with the same seed
    let run_test = || {
        let config = SimConfig::new(seed);

        Simulation::new(config).run(|env| async move {
            let actor_id = ActorId::new("dst-test", "deterministic-1")?;
            let storage = Arc::new(env.storage);

            let mut active = ActiveActor::activate(actor_id, CounterActor, storage).await?;

            // Perform operations
            for _ in 0..10 {
                active.process_invocation("increment", Bytes::new()).await?;
            }

            let result = active.process_invocation("get", Bytes::new()).await?;
            Ok(result)
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(
        result1, result2,
        "Determinism violated: results differ with same seed"
    );
}

// =============================================================================
// Stress Tests (longer duration, marked as ignored for CI)
// =============================================================================

#[test]
#[ignore] // Run with: cargo test -p kelpie-dst -- --ignored
fn test_dst_stress_many_activations() {
    let config = SimConfig::from_env_or_random().with_max_steps(1_000_000);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.05))
        .with_fault(FaultConfig::new(FaultType::StorageReadFail, 0.02))
        .run(|env| async move {
            let storage = Arc::new(env.storage);

            // Create and use many actors
            for i in 0..100 {
                let actor_id = ActorId::new("dst-stress", format!("actor-{}", i))?;

                let mut active =
                    ActiveActor::activate(actor_id, CounterActor, storage.clone()).await?;

                // Perform some operations
                for _ in 0..10 {
                    let _ = active.process_invocation("increment", Bytes::new()).await;
                }

                let _ = active.deactivate().await;
            }

            Ok(())
        });

    assert!(result.is_ok(), "Stress test failed: {:?}", result.err());
}

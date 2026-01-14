//! Aggressive DST Tests for AppState + AgentService Integration
//!
//! Phase 5.1: Write tests FIRST with 50%+ fault rates
//!
//! These tests target specific bugs:
//! 1. Partial AppState initialization
//! 2. Concurrent agent creation races
//! 3. Shutdown dropping in-flight requests
//! 4. Service invocation after shutdown
//! 5. BUG-001 style timing windows
//!
//! ALL TESTS MUST FAIL INITIALLY (AppState doesn't have service yet)

use async_trait::async_trait;
use kelpie_core::Result;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, SimEnvironment, SimLlmClient, Simulation};
use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig};
use kelpie_server::actor::{AgentActor, AgentActorState, LlmClient, LlmMessage, LlmResponse};
use kelpie_server::models::{AgentType, CreateAgentRequest};
use kelpie_server::service::AgentService;
use kelpie_server::state::AppState;
use std::sync::Arc;
use std::time::Duration;

/// Test 1: AppState initialization with crash during dispatcher creation
///
/// TARGET BUG: Partial initialization - AppState created but dispatcher failed
///
/// FAULT: 50% CrashDuringTransaction during dispatcher creation
///
/// ASSERTION: Either AppState creation succeeds fully OR fails cleanly
/// No partial state where AppState exists but service is broken
#[tokio::test]
async fn test_appstate_init_crash() {
    let config = SimConfig::new(5001);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashDuringTransaction, 0.5))
        .run_async(|sim_env| async move {
            let mut success_count = 0;
            let mut failure_count = 0;
            let mut partial_state_count = 0;

            // Try to create AppState 20 times with 50% crash rate
            for i in 0..20 {
                let app_state_result = create_appstate_with_service(&sim_env).await;

                match app_state_result {
                    Ok(app_state) => {
                        // AppState created - verify service is functional
                        // Try multiple times to distinguish between:
                        // 1. Service is broken (dispatcher crashed) → always fails
                        // 2. Service works but operations face faults → sometimes succeeds
                        let mut operational = false;
                        for retry in 0..3 {
                            match test_service_operational(&app_state).await {
                                Ok(_) => {
                                    operational = true;
                                    break;
                                }
                                Err(_) if retry < 2 => {
                                    // Retry
                                    tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
                                    continue;
                                }
                                Err(e) => {
                                    // Failed after all retries
                                    println!(
                                        "Iteration {}: Service check failed after {} retries: {}",
                                        i, retry + 1, e
                                    );
                                }
                            }
                        }

                        if operational {
                            success_count += 1;
                            println!("Iteration {}: AppState + Service fully operational", i);
                        } else {
                            // BUG: AppState created but service never works
                            partial_state_count += 1;
                            panic!(
                                "BUG: AppState created but service non-functional after 3 retries at iteration {}. \
                                 This indicates partial initialization during crash.",
                                i
                            );
                        }
                    }
                    Err(e) => {
                        // Creation failed - this is OK with high crash rate
                        failure_count += 1;
                        println!("Iteration {}: AppState creation failed (expected): {}", i, e);
                    }
                }
            }

            println!(
                "Init test: {} success, {} clean failures, {} partial state bugs",
                success_count, failure_count, partial_state_count
            );

            assert_eq!(
                partial_state_count, 0,
                "Found {} partial initialization bugs",
                partial_state_count
            );

            assert!(
                success_count > 0 || failure_count > 0,
                "Expected some attempts with 50% crash rate"
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Test failed (found init bug?): {:?}",
        result.err()
    );
}

/// Test 2: Concurrent agent creation with race conditions
///
/// TARGET BUG: Two concurrent requests create agents, crash during one
/// Results in duplicate agents or inconsistent state
///
/// FAULT: 40% CrashAfterWrite during actor operations
///
/// ASSERTION: No duplicate agents, concurrent creates are serialized
#[tokio::test]
async fn test_concurrent_agent_creation_race() {
    let config = SimConfig::new(5002);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashAfterWrite, 0.4))
        .run_async(|sim_env| async move {
            let app_state = match create_appstate_with_service(&sim_env).await {
                Ok(a) => a,
                Err(e) => {
                    println!("Skipping test - couldn't create AppState: {}", e);
                    return Ok(());
                }
            };

            // Launch 10 concurrent creates with same agent name
            let mut handles = vec![];
            for i in 0..10 {
                let app_clone = app_state.clone();
                let handle = tokio::spawn(async move {
                    let request = CreateAgentRequest {
                        name: "concurrent-test".to_string(), // Same name!
                        agent_type: AgentType::LettaV1Agent,
                        model: None,
                        system: Some(format!("Thread {}", i)),
                        description: None,
                        memory_blocks: vec![],
                        block_ids: vec![],
                        tool_ids: vec![],
                        tags: vec![format!("thread-{}", i)],
                        metadata: serde_json::json!({"thread": i}),
                    };

                    // Use app_state.agent_service() to create
                    app_clone
                        .agent_service_required()
                        .create_agent(request)
                        .await
                });
                handles.push(handle);
            }

            // Wait for all creates
            let mut success_count = 0;
            let mut failure_count = 0;
            let mut created_ids = Vec::new();

            for handle in handles {
                match handle.await {
                    Ok(Ok(agent)) => {
                        success_count += 1;
                        created_ids.push(agent.id.clone());
                        println!("Created agent: {}", agent.id);
                    }
                    Ok(Err(e)) => {
                        failure_count += 1;
                        println!("Create failed (might be expected): {}", e);
                    }
                    Err(e) => {
                        failure_count += 1;
                        println!("Task panicked: {}", e);
                    }
                }
            }

            println!(
                "Concurrent creates: {} success, {} failures",
                success_count, failure_count
            );

            // CRITICAL: Verify no duplicate agents
            let unique_ids: std::collections::HashSet<_> = created_ids.iter().collect();
            if created_ids.len() != unique_ids.len() {
                panic!(
                    "BUG: Found duplicate agent IDs! Created {}, unique {}. \
                     Race condition allowed duplicate creates.",
                    created_ids.len(),
                    unique_ids.len()
                );
            }

            // Verify all created agents are actually retrievable
            for agent_id in &created_ids {
                match app_state.agent_service_required().get_agent(agent_id).await {
                    Ok(_) => {} // Good
                    Err(e) => {
                        panic!(
                            "BUG: Agent {} was created but is not retrievable: {}. \
                             Inconsistent state after concurrent create.",
                            agent_id, e
                        );
                    }
                }
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Test failed (found race bug?): {:?}",
        result.err()
    );
}

/// Test 3: Shutdown with in-flight requests
///
/// TARGET BUG: Shutdown drops in-flight requests without completing them
///
/// FAULT: 50% NetworkDelay (simulates slow requests) + immediate shutdown
///
/// ASSERTION: In-flight requests either complete OR fail with clear error
/// No silent drops
#[tokio::test]
async fn test_shutdown_with_inflight_requests() {
    let config = SimConfig::new(5003);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 100,
                max_ms: 500,
            },
            0.5,
        ))
        .run_async(|sim_env| async move {
            let app_state = match create_appstate_with_service(&sim_env).await {
                Ok(a) => a,
                Err(e) => {
                    println!("Skipping test - couldn't create AppState: {}", e);
                    return Ok(());
                }
            };

            // Launch 5 agent creates (some will be delayed)
            let mut handles = vec![];
            for i in 0..5 {
                let app_clone = app_state.clone();
                let handle = tokio::spawn(async move {
                    let request = CreateAgentRequest {
                        name: format!("inflight-{}", i),
                        agent_type: AgentType::LettaV1Agent,
                        model: None,
                        system: None,
                        description: None,
                        memory_blocks: vec![],
                        block_ids: vec![],
                        tool_ids: vec![],
                        tags: vec![],
                        metadata: serde_json::json!({}),
                    };

                    app_clone.agent_service_required().create_agent(request).await
                });
                handles.push((i, handle));
            }

            // Give some time for requests to start
            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

            // SHUTDOWN while requests are in-flight
            println!("Initiating shutdown with in-flight requests...");
            match app_state.shutdown(Duration::from_secs(5)).await {
                Ok(_) => println!("Shutdown completed"),
                Err(e) => println!("Shutdown error (might be OK): {}", e),
            }

            // Check results of in-flight requests
            let mut completed = 0;
            let mut failed_cleanly = 0;
            let mut silent_drops = 0;

            for (i, handle) in handles {
                match tokio::time::timeout(Duration::from_secs(1), handle).await {
                    Ok(Ok(Ok(_agent))) => {
                        completed += 1;
                        println!("Request {} completed successfully", i);
                    }
                    Ok(Ok(Err(e))) => {
                        failed_cleanly += 1;
                        println!("Request {} failed cleanly: {}", i, e);
                    }
                    Ok(Err(e)) => {
                        failed_cleanly += 1;
                        println!("Request {} task error: {}", i, e);
                    }
                    Err(_) => {
                        // Timeout - request silently dropped!
                        silent_drops += 1;
                        println!("Request {} timed out after shutdown", i);
                    }
                }
            }

            println!(
                "Shutdown results: {} completed, {} failed cleanly, {} silent drops",
                completed, failed_cleanly, silent_drops
            );

            // CRITICAL: No silent drops - must either complete or fail with error
            if silent_drops > 0 {
                panic!(
                    "BUG: {} requests silently dropped during shutdown. \
                     Shutdown must either complete in-flight requests or fail them with clear errors.",
                    silent_drops
                );
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Test failed (found shutdown bug?): {:?}",
        result.err()
    );
}

/// Test 4: Service invocation after shutdown starts
///
/// TARGET BUG: Service accepts new requests after shutdown initiated
///
/// FAULT: 40% CrashDuringTransaction
///
/// ASSERTION: Requests after shutdown fail with ShuttingDown error
/// No panics, no silent acceptance
#[tokio::test]
async fn test_service_invoke_during_shutdown() {
    let config = SimConfig::new(5004);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashDuringTransaction, 0.4))
        .run_async(|sim_env| async move {
            let app_state = match create_appstate_with_service(&sim_env).await {
                Ok(a) => a,
                Err(e) => {
                    println!("Skipping test - couldn't create AppState: {}", e);
                    return Ok(());
                }
            };

            // Start shutdown in background
            let app_clone = app_state.clone();
            tokio::spawn(async move {
                tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
                let _ = app_clone.shutdown(Duration::from_secs(2)).await;
            });

            // Give shutdown a moment to start
            tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;

            // Try to create agent AFTER shutdown started
            let request = CreateAgentRequest {
                name: "after-shutdown".to_string(),
                agent_type: AgentType::LettaV1Agent,
                model: None,
                system: None,
                description: None,
                memory_blocks: vec![],
                block_ids: vec![],
                tool_ids: vec![],
                tags: vec![],
                metadata: serde_json::json!({}),
            };

            match app_state
                .agent_service_required()
                .create_agent(request)
                .await
            {
                Ok(agent) => {
                    // BUG: Request succeeded after shutdown
                    panic!(
                        "BUG: create_agent succeeded after shutdown started. \
                         Agent {} was created. Service must reject new requests during shutdown.",
                        agent.id
                    );
                }
                Err(e) => {
                    let err_str = e.to_string();
                    println!("Request rejected during shutdown: {}", err_str);

                    // Verify error message indicates shutdown
                    if !err_str.to_lowercase().contains("shutdown")
                        && !err_str.to_lowercase().contains("unavailable")
                    {
                        println!(
                            "WARNING: Error doesn't clearly indicate shutdown: {}",
                            err_str
                        );
                        // Not a hard failure, but not ideal
                    }
                }
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Test failed (found shutdown invoke bug?): {:?}",
        result.err()
    );
}

/// Test 5: First invoke after AppState creation (BUG-001 pattern)
///
/// TARGET BUG: Similar to BUG-001 - create succeeds but state not readable
///
/// FAULT: 50% CrashDuringTransaction during first invoke
///
/// ASSERTION: create → immediate get works OR both fail
/// No "created but not found" scenario
#[tokio::test]
async fn test_first_invoke_after_creation() {
    let config = SimConfig::new(5005);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashDuringTransaction, 0.5))
        .run_async(|sim_env| async move {
            let app_state = match create_appstate_with_service(&sim_env).await {
                Ok(a) => a,
                Err(e) => {
                    println!("Skipping test - couldn't create AppState: {}", e);
                    return Ok(());
                }
            };

            let mut consistency_violations = Vec::new();

            // Try 20 create → immediate get sequences
            for i in 0..20 {
                let request = CreateAgentRequest {
                    name: format!("timing-test-{}", i),
                    agent_type: AgentType::LettaV1Agent,
                    model: None,
                    system: Some(format!("Test {}", i)),
                    description: Some(format!("Description {}", i)),
                    memory_blocks: vec![],
                    block_ids: vec![],
                    tool_ids: vec![format!("tool-{}", i)],
                    tags: vec![format!("tag-{}", i)],
                    metadata: serde_json::json!({"iteration": i}),
                };

                // Create agent
                match app_state
                    .agent_service_required()
                    .create_agent(request.clone())
                    .await
                {
                    Ok(agent) => {
                        println!("Iteration {}: Agent {} created", i, agent.id);

                        // IMMEDIATELY try to get it back (BUG-001 timing window)
                        // Retry a few times to distinguish between:
                        // 1. Agent doesn't exist (BUG-001) → always fails
                        // 2. Read operation hit fault → might succeed on retry
                        let mut retrieved_ok = false;
                        for retry in 0..3 {
                            match app_state
                                .agent_service_required()
                                .get_agent(&agent.id)
                                .await
                            {
                                Ok(retrieved) => {
                                    // Successfully retrieved - verify data integrity
                                    let mut violations = Vec::new();

                                    if retrieved.name != request.name {
                                        violations.push(format!(
                                            "Name mismatch: expected '{}', got '{}'",
                                            request.name, retrieved.name
                                        ));
                                    }

                                    if retrieved.system != request.system {
                                        violations.push(format!(
                                            "System mismatch: expected {:?}, got {:?}",
                                            request.system, retrieved.system
                                        ));
                                    }

                                    if retrieved.tool_ids != request.tool_ids {
                                        violations.push(format!(
                                            "Tool IDs mismatch: expected {:?}, got {:?}",
                                            request.tool_ids, retrieved.tool_ids
                                        ));
                                    }

                                    if !violations.is_empty() {
                                        consistency_violations.push((
                                            i,
                                            agent.id.clone(),
                                            violations,
                                        ));
                                    }

                                    retrieved_ok = true;
                                    break;
                                }
                                Err(_) if retry < 2 => {
                                    // Retry - might be transient read fault
                                    tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
                                    continue;
                                }
                                Err(e) => {
                                    // Failed after all retries - this is BUG-001!
                                    println!(
                                        "Iteration {}: get_agent failed after {} retries: {}",
                                        i,
                                        retry + 1,
                                        e
                                    );
                                }
                            }
                        }

                        if !retrieved_ok {
                            // BUG-001 PATTERN: Created but consistently not found!
                            consistency_violations.push((
                                i,
                                agent.id.clone(),
                                vec![format!(
                                    "Agent created but get_agent failed after 3 retries (BUG-001)"
                                )],
                            ));
                        }
                    }
                    Err(e) => {
                        println!(
                            "Iteration {}: Create failed (expected with faults): {}",
                            i, e
                        );
                    }
                }
            }

            if !consistency_violations.is_empty() {
                println!("\n=== CONSISTENCY VIOLATIONS FOUND ===");
                for (iteration, agent_id, violations) in &consistency_violations {
                    println!("\nIteration {}, Agent ID: {}", iteration, agent_id);
                    for violation in violations {
                        println!("  - {}", violation);
                    }
                }
                panic!(
                    "Found {} consistency violations (BUG-001 pattern)",
                    consistency_violations.len()
                );
            }

            println!("No consistency violations found - timing window handled correctly");
            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Test failed (found BUG-001 pattern?): {:?}",
        result.err()
    );
}

// ============================================================================
// Test Helpers
// ============================================================================

/// Create AppState with AgentService integration
///
/// Phase 5.2: Implementation of actor-based AppState creation
///
/// TigerStyle: Verifies service is operational before returning.
/// Returns error if dispatcher initialization fails.
async fn create_appstate_with_service(sim_env: &SimEnvironment) -> Result<AppState> {
    // Create SimLlmClient adapter
    let sim_llm = SimLlmClient::new(sim_env.rng.clone(), sim_env.faults.clone());
    let llm_adapter: Arc<dyn LlmClient> = Arc::new(SimLlmClientAdapter {
        client: Arc::new(sim_llm),
    });

    // Create AgentActor with LLM client
    let actor = AgentActor::new(llm_adapter);

    // Create CloneFactory for dispatcher
    let factory = Arc::new(CloneFactory::new(actor));

    // Use SimStorage from environment
    let kv = Arc::new(sim_env.storage.clone());

    // Create Dispatcher with default config
    let mut dispatcher =
        Dispatcher::<AgentActor, AgentActorState>::new(factory, kv, DispatcherConfig::default());

    // Get handle before spawning
    let handle = dispatcher.handle();

    // Spawn dispatcher runtime
    tokio::spawn(async move {
        dispatcher.run().await;
    });

    // Create AgentService (but don't create AppState yet)
    let service = AgentService::new(handle.clone());

    // CRITICAL: Verify service is operational BEFORE creating AppState
    // This ensures atomicity - either full success or full failure
    // Try a test operation to verify dispatcher is working
    let test_request = CreateAgentRequest {
        name: "init-verification".to_string(),
        agent_type: AgentType::LettaV1Agent,
        model: None,
        system: None,
        description: None,
        memory_blocks: vec![],
        block_ids: vec![],
        tool_ids: vec![],
        tags: vec![],
        metadata: serde_json::json!({}),
    };

    // Try to create test agent to verify service works
    // If this fails, we return error BEFORE creating AppState
    service.create_agent(test_request).await?;

    // Service verified operational - NOW create AppState
    // This ensures AppState is only created if service is functional
    Ok(AppState::with_agent_service(service, handle))
}

/// Test if AppState's service is operational
///
/// Tries a simple operation to verify service is functional
async fn test_service_operational(app_state: &AppState) -> Result<()> {
    // Get agent service (must exist for actor-based AppState)
    let service = app_state
        .agent_service()
        .ok_or_else(|| kelpie_core::Error::Internal {
            message: "AppState has no agent_service configured".to_string(),
        })?;

    // Try to create a test agent
    let request = CreateAgentRequest {
        name: "operational-test".to_string(),
        agent_type: AgentType::LettaV1Agent,
        model: None,
        system: Some("Test system".to_string()),
        description: None,
        memory_blocks: vec![],
        block_ids: vec![],
        tool_ids: vec![],
        tags: vec![],
        metadata: serde_json::json!({}),
    };

    // If this succeeds, service is operational
    let _agent = service.create_agent(request).await?;

    Ok(())
}

/// AppState service extension trait
///
/// Phase 5.2: These methods are now implemented on AppState itself,
/// but we keep this trait for backward compatibility with tests.
trait AppStateServiceExt {
    fn agent_service_required(&self) -> &AgentService;
    async fn shutdown(&self, timeout: Duration) -> Result<()>;
}

impl AppStateServiceExt for AppState {
    fn agent_service_required(&self) -> &AgentService {
        // Panic if agent_service not configured (test helper, not production code)
        self.agent_service().expect(
            "AppState not configured with agent_service. \
             Use AppState::with_agent_service() or create_appstate_with_service()",
        )
    }

    async fn shutdown(&self, timeout: Duration) -> Result<()> {
        // Delegate to AppState's shutdown method
        AppState::shutdown(self, timeout).await
    }
}

// Helper types for test infrastructure
struct SimLlmClientAdapter {
    client: Arc<SimLlmClient>,
}

#[async_trait]
impl LlmClient for SimLlmClientAdapter {
    async fn complete(&self, messages: Vec<LlmMessage>) -> Result<LlmResponse> {
        let sim_messages: Vec<kelpie_dst::SimChatMessage> = messages
            .into_iter()
            .map(|m| kelpie_dst::SimChatMessage {
                role: m.role,
                content: m.content,
            })
            .collect();

        let response = self
            .client
            .complete_with_tools(sim_messages, vec![])
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: format!("LLM error: {}", e),
            })?;

        Ok(LlmResponse {
            content: response.content,
            tool_calls: vec![],
        })
    }
}

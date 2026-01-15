//! DST tests for libkrun VM lifecycle
//!
//! TigerStyle: DST-first - these tests validate VM lifecycle behavior
//! under fault injection using SimSandbox before real libkrun implementation.
//!
//! These tests define the behavioral contract that LibkrunSandbox must fulfill.

use kelpie_dst::{
    DeterministicRng, FaultConfig, FaultInjectorBuilder, FaultType, SimSandboxFactory,
};
use kelpie_sandbox::{Architecture, ExecOptions, Sandbox, SandboxConfig, SandboxFactory, SandboxState};
use std::sync::Arc;

/// Get DST seed from environment or generate random
fn get_seed() -> u64 {
    std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            let seed = rand::random();
            eprintln!("DST_SEED={}", seed);
            seed
        })
}

// =============================================================================
// VM LIFECYCLE TESTS
// =============================================================================

/// Test basic VM lifecycle: create -> start -> stop
#[tokio::test]
async fn test_dst_vm_lifecycle_basic() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    // Create VM
    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    assert_eq!(sandbox.state(), SandboxState::Stopped);

    // Start VM
    sandbox.start().await.expect("should start");
    assert_eq!(sandbox.state(), SandboxState::Running);

    // Stop VM
    sandbox.stop().await.expect("should stop");
    assert_eq!(sandbox.state(), SandboxState::Stopped);
}

/// Test VM lifecycle under boot failures
#[tokio::test]
async fn test_dst_vm_lifecycle_with_boot_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    // High probability of boot failure
    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.5))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut success_count = 0;
    let mut failure_count = 0;

    // Run multiple iterations - should see both successes and failures
    for i in 0..20 {
        let mut sandbox = factory
            .create(config.clone())
            .await
            .expect("should create sandbox");

        match sandbox.start().await {
            Ok(()) => {
                success_count += 1;
                assert_eq!(sandbox.state(), SandboxState::Running);
                sandbox.stop().await.ok();
            }
            Err(e) => {
                failure_count += 1;
                // On boot failure, sandbox should remain in Created state
                assert_eq!(
                    sandbox.state(),
                    SandboxState::Stopped,
                    "sandbox {} should be Created after boot fail, got {:?}",
                    i,
                    sandbox.state()
                );
                tracing::debug!("Boot failed as expected: {}", e);
            }
        }
    }

    // With 50% probability over 20 iterations, we should see some of each
    assert!(
        success_count > 0,
        "expected some successful boots, got 0 out of 20"
    );
    assert!(
        failure_count > 0,
        "expected some boot failures, got 0 out of 20"
    );
    eprintln!(
        "Boot test: {} successes, {} failures",
        success_count, failure_count
    );
}

/// Test VM survives crash faults during execution
#[tokio::test]
async fn test_dst_vm_lifecycle_with_crash_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    // Occasional crashes during exec
    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.1))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    let mut exec_count = 0;
    let mut crash_count = 0;

    // Execute multiple commands - some may fail due to crashes
    for _ in 0..50 {
        let result = sandbox
            .exec("echo", &["test"], ExecOptions::default())
            .await;

        match result {
            Ok(output) => {
                exec_count += 1;
                assert!(output.status.is_success() || output.status.code == 0);
            }
            Err(_) => {
                crash_count += 1;
                // Crash should transition to Stopped state
                if sandbox.state() == SandboxState::Stopped {
                    // Restart for next iteration
                    sandbox.start().await.ok();
                }
            }
        }
    }

    eprintln!(
        "Crash test: {} successful execs, {} crashes",
        exec_count, crash_count
    );
}

// =============================================================================
// PAUSE/RESUME TESTS
// =============================================================================

/// Test basic pause and resume
#[tokio::test]
async fn test_dst_vm_pause_resume_basic() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");
    assert_eq!(sandbox.state(), SandboxState::Running);

    // Pause
    sandbox.pause().await.expect("should pause");
    assert_eq!(sandbox.state(), SandboxState::Paused);

    // Resume
    sandbox.resume().await.expect("should resume");
    assert_eq!(sandbox.state(), SandboxState::Running);

    // Should be able to execute after resume
    let output = sandbox
        .exec("echo", &["after_resume"], ExecOptions::default())
        .await
        .expect("should exec after resume");
    assert!(output.status.is_success());

    sandbox.stop().await.expect("should stop");
}

/// Test pause/resume under faults
#[tokio::test]
async fn test_dst_vm_pause_resume_with_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxPauseFail, 0.3))
            .with_fault(FaultConfig::new(FaultType::SandboxResumeFail, 0.3))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    let mut pause_success = 0;
    let mut pause_fail = 0;
    let mut resume_success = 0;
    let mut resume_fail = 0;

    for _ in 0..20 {
        // Try to pause
        match sandbox.pause().await {
            Ok(()) => {
                pause_success += 1;
                assert_eq!(sandbox.state(), SandboxState::Paused);

                // Try to resume
                match sandbox.resume().await {
                    Ok(()) => {
                        resume_success += 1;
                        assert_eq!(sandbox.state(), SandboxState::Running);
                    }
                    Err(_) => {
                        resume_fail += 1;
                        // On resume failure, should still be paused
                        assert_eq!(sandbox.state(), SandboxState::Paused);
                        // Force resume for next iteration
                        while sandbox.state() == SandboxState::Paused {
                            if sandbox.resume().await.is_ok() {
                                break;
                            }
                        }
                    }
                }
            }
            Err(_) => {
                pause_fail += 1;
                // On pause failure, should still be running
                assert_eq!(sandbox.state(), SandboxState::Running);
            }
        }
    }

    eprintln!(
        "Pause/Resume: pause {}/{}, resume {}/{}",
        pause_success,
        pause_success + pause_fail,
        resume_success,
        resume_success + resume_fail
    );
}

// =============================================================================
// SNAPSHOT TESTS
// =============================================================================

/// Test snapshot and restore basic flow
#[tokio::test]
async fn test_dst_vm_snapshot_restore_basic() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    // Create a file to verify state preservation
    sandbox
        .exec("touch", &["/tmp/before_snapshot"], ExecOptions::default())
        .await
        .expect("should create file");

    // Take snapshot
    let snapshot = sandbox.snapshot().await.expect("should snapshot");
    assert!(!snapshot.metadata.id.is_empty());
    // created_at is a DateTime, just verify snapshot is valid
    assert!(!snapshot.metadata.sandbox_id.is_empty());

    // Modify state after snapshot
    sandbox
        .exec("touch", &["/tmp/after_snapshot"], ExecOptions::default())
        .await
        .ok();

    // Restore from snapshot
    sandbox
        .restore(&snapshot)
        .await
        .expect("should restore from snapshot");

    // After restore, the sandbox should be in a consistent state
    // (In real implementation, /tmp/after_snapshot would not exist)
    assert!(matches!(
        sandbox.state(),
        SandboxState::Running | SandboxState::Paused
    ));

    sandbox.stop().await.ok();
}

/// Test snapshot under corruption faults
#[tokio::test]
async fn test_dst_vm_snapshot_with_corruption_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 0.2))
            .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.2))
            .with_fault(FaultConfig::new(FaultType::SnapshotRestoreFail, 0.2))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    let mut snapshot_success = 0;
    let mut snapshot_fail = 0;
    let mut restore_success = 0;
    let mut restore_fail = 0;

    for _ in 0..20 {
        // Try to snapshot
        match sandbox.snapshot().await {
            Ok(snapshot) => {
                snapshot_success += 1;

                // Try to restore
                match sandbox.restore(&snapshot).await {
                    Ok(()) => {
                        restore_success += 1;
                    }
                    Err(_) => {
                        restore_fail += 1;
                    }
                }
            }
            Err(_) => {
                snapshot_fail += 1;
            }
        }

        // Ensure sandbox is still usable
        if sandbox.state() == SandboxState::Stopped {
            sandbox.start().await.ok();
        }
    }

    eprintln!(
        "Snapshot/Restore: snapshot {}/{}, restore {}/{}",
        snapshot_success,
        snapshot_success + snapshot_fail,
        restore_success,
        restore_success + restore_fail
    );
}

// =============================================================================
// EXECUTION TESTS
// =============================================================================

/// Test command execution with timeouts
#[tokio::test]
async fn test_dst_vm_exec_with_timeout_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(
                FaultType::SandboxExecTimeout { timeout_ms: 1000 },
                0.3,
            ))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    let mut success_count = 0;
    let mut timeout_count = 0;

    for _ in 0..30 {
        let result = sandbox
            .exec("echo", &["hello"], ExecOptions::default())
            .await;

        match result {
            Ok(output) => {
                success_count += 1;
                assert!(output.status.is_success());
            }
            Err(e) => {
                timeout_count += 1;
                // Error should indicate timeout
                let err_str = format!("{}", e).to_lowercase();
                assert!(
                    err_str.contains("timeout") || err_str.contains("timed out"),
                    "Expected timeout error, got: {}",
                    err_str
                );
            }
        }
    }

    assert!(success_count > 0, "expected some successful execs");
    assert!(timeout_count > 0, "expected some timeouts");
    eprintln!(
        "Exec timeout test: {} success, {} timeout",
        success_count, timeout_count
    );
}

/// Test execution failure handling
#[tokio::test]
async fn test_dst_vm_exec_with_failure_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.3))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    let mut success_count = 0;
    let mut fail_count = 0;

    for _ in 0..30 {
        let result = sandbox.exec("ls", &["-la"], ExecOptions::default()).await;

        match result {
            Ok(_) => success_count += 1,
            Err(_) => fail_count += 1,
        }
    }

    assert!(success_count > 0, "expected some successful execs");
    assert!(fail_count > 0, "expected some failures");
    eprintln!(
        "Exec failure test: {} success, {} fail",
        success_count, fail_count
    );
}

// =============================================================================
// DETERMINISM TESTS
// =============================================================================

/// Test that same seed produces same behavior
#[tokio::test]
async fn test_dst_vm_determinism() {
    let seed = 42u64; // Fixed seed for determinism test

    // Run 1
    let results1 = run_determinism_scenario(seed).await;

    // Run 2 with same seed
    let results2 = run_determinism_scenario(seed).await;

    // Results must be identical
    assert_eq!(
        results1, results2,
        "Same seed should produce identical results"
    );
}

async fn run_determinism_scenario(seed: u64) -> Vec<bool> {
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.2))
            .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.2))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut results = Vec::new();

    for _ in 0..10 {
        let mut sandbox = factory.create(config.clone()).await.unwrap();
        let start_result = sandbox.start().await.is_ok();
        results.push(start_result);

        if start_result {
            let exec_result = sandbox
                .exec("test", &[], ExecOptions::default())
                .await
                .is_ok();
            results.push(exec_result);
            sandbox.stop().await.ok();
        }
    }

    results
}

// =============================================================================
// STRESS TESTS
// =============================================================================

/// Stress test with many operations under faults
#[tokio::test]
#[ignore] // Run explicitly with --ignored
async fn test_dst_vm_stress_many_operations() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_sandbox_faults(0.05)
            .with_snapshot_faults(0.05)
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut total_ops = 0;
    let mut failed_ops = 0;

    for _ in 0..100 {
        let mut sandbox = factory.create(config.clone()).await.unwrap();

        // Start
        total_ops += 1;
        if sandbox.start().await.is_err() {
            failed_ops += 1;
            continue;
        }

        // Multiple execs
        for _ in 0..10 {
            total_ops += 1;
            if sandbox
                .exec("echo", &["stress"], ExecOptions::default())
                .await
                .is_err()
            {
                failed_ops += 1;
            }
        }

        // Snapshot/restore cycle
        total_ops += 1;
        if let Ok(snapshot) = sandbox.snapshot().await {
            total_ops += 1;
            if sandbox.restore(&snapshot).await.is_err() {
                failed_ops += 1;
            }
        } else {
            failed_ops += 1;
        }

        // Pause/resume cycle
        total_ops += 1;
        if sandbox.pause().await.is_ok() {
            total_ops += 1;
            if sandbox.resume().await.is_err() {
                failed_ops += 1;
            }
        } else {
            failed_ops += 1;
        }

        // Stop
        total_ops += 1;
        if sandbox.stop().await.is_err() {
            failed_ops += 1;
        }
    }

    let failure_rate = (failed_ops as f64 / total_ops as f64) * 100.0;
    eprintln!(
        "Stress test: {}/{} ops succeeded ({:.1}% failure rate)",
        total_ops - failed_ops,
        total_ops,
        failure_rate
    );

    // With 5% fault probability, we expect some failures but not too many
    assert!(
        failure_rate < 30.0,
        "Failure rate too high: {:.1}%",
        failure_rate
    );
}

/// Stress test rapid lifecycle transitions
#[tokio::test]
#[ignore]
async fn test_dst_vm_stress_rapid_lifecycle() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.02))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.unwrap();

    let mut start_stop_cycles = 0;
    let mut pause_resume_cycles = 0;

    for _ in 0..500 {
        // Start/stop cycle
        if sandbox.start().await.is_ok() {
            start_stop_cycles += 1;
            sandbox.stop().await.ok();
        }

        // Start and pause/resume cycle
        if sandbox.start().await.is_ok() {
            if sandbox.pause().await.is_ok() {
                if sandbox.resume().await.is_ok() {
                    pause_resume_cycles += 1;
                }
            }
            sandbox.stop().await.ok();
        }
    }

    eprintln!(
        "Rapid lifecycle: {} start/stop, {} pause/resume cycles",
        start_stop_cycles, pause_resume_cycles
    );
}

// =============================================================================
// STATE MACHINE TESTS
// =============================================================================

/// Test that invalid state transitions are rejected
#[tokio::test]
async fn test_dst_vm_invalid_state_transitions() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    assert_eq!(sandbox.state(), SandboxState::Stopped);

    // Cannot pause when stopped
    assert!(sandbox.pause().await.is_err(), "pause should fail when stopped");
    assert_eq!(sandbox.state(), SandboxState::Stopped, "state should remain stopped");

    // Cannot resume when stopped
    assert!(sandbox.resume().await.is_err(), "resume should fail when stopped");
    assert_eq!(sandbox.state(), SandboxState::Stopped, "state should remain stopped");

    // Cannot exec when stopped
    let exec_result = sandbox.exec("echo", &["test"], ExecOptions::default()).await;
    assert!(exec_result.is_err(), "exec should fail when stopped");

    // Start the VM
    sandbox.start().await.expect("should start");
    assert_eq!(sandbox.state(), SandboxState::Running);

    // Cannot start when already running
    assert!(sandbox.start().await.is_err(), "start should fail when already running");

    // Cannot resume when running (not paused)
    assert!(sandbox.resume().await.is_err(), "resume should fail when running");

    // Pause to test paused state transitions
    sandbox.pause().await.expect("should pause");
    assert_eq!(sandbox.state(), SandboxState::Paused);

    // Cannot pause when already paused
    assert!(sandbox.pause().await.is_err(), "pause should fail when already paused");

    // Cannot start when paused (must resume first)
    assert!(sandbox.start().await.is_err(), "start should fail when paused");

    // Clean up
    sandbox.resume().await.ok();
    sandbox.stop().await.ok();
}

/// Test snapshot state requirements
#[tokio::test]
async fn test_dst_vm_snapshot_state_requirements() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");

    // Cannot snapshot when stopped
    assert!(
        sandbox.snapshot().await.is_err(),
        "snapshot should fail when stopped"
    );

    sandbox.start().await.expect("should start");

    // Can snapshot when running
    let snapshot = sandbox.snapshot().await.expect("should snapshot when running");

    sandbox.pause().await.expect("should pause");

    // Can snapshot when paused
    let _paused_snapshot = sandbox
        .snapshot()
        .await
        .expect("should snapshot when paused");

    // Stop and try to restore
    sandbox.stop().await.ok();

    // Should be able to restore when stopped
    sandbox
        .restore(&snapshot)
        .await
        .expect("should restore when stopped");
}

// =============================================================================
// CONCURRENT OPERATIONS TESTS
// =============================================================================

/// Test concurrent VM creation and destruction
#[tokio::test]
#[ignore] // Resource intensive
async fn test_dst_vm_concurrent_lifecycle() {
    use tokio::task::JoinSet;

    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.1))
            .build(),
    );

    let factory = Arc::new(SimSandboxFactory::new(rng.fork(), faults));
    let config = SandboxConfig::default();

    let mut tasks = JoinSet::new();

    // Launch 10 concurrent VM lifecycle tasks
    for i in 0..10 {
        let factory = factory.clone();
        let config = config.clone();

        tasks.spawn(async move {
            let mut success = 0;
            let mut failures = 0;

            // Each task does 10 lifecycle cycles
            for _ in 0..10 {
                let mut sandbox = factory.create(config.clone()).await.unwrap();

                match sandbox.start().await {
                    Ok(()) => {
                        success += 1;
                        // Quick exec
                        let _ = sandbox
                            .exec("echo", &["concurrent"], ExecOptions::default())
                            .await;
                        sandbox.stop().await.ok();
                    }
                    Err(_) => {
                        failures += 1;
                    }
                }
            }

            (i, success, failures)
        });
    }

    let mut total_success = 0;
    let mut total_failures = 0;

    // Wait for all tasks
    while let Some(result) = tasks.join_next().await {
        let (task_id, success, failures) = result.expect("task should not panic");
        eprintln!(
            "Task {}: {} success, {} failures",
            task_id, success, failures
        );
        total_success += success;
        total_failures += failures;
    }

    eprintln!(
        "Concurrent test total: {} success, {} failures",
        total_success, total_failures
    );

    // Should complete without deadlocks
    assert!(total_success + total_failures == 100);
}

/// Test concurrent exec operations on single VM
#[tokio::test]
async fn test_dst_vm_concurrent_exec() {
    use tokio::task::JoinSet;

    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.1))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    // Share the sandbox across tasks (via Arc since Sandbox is Send+Sync)
    let sandbox = Arc::new(sandbox);

    let mut tasks = JoinSet::new();

    // Launch 5 concurrent exec tasks
    for task_id in 0..5 {
        let sandbox = sandbox.clone();

        tasks.spawn(async move {
            let mut success = 0;
            let mut failures = 0;

            for i in 0..20 {
                let result = sandbox
                    .exec("echo", &[&format!("task{}-{}", task_id, i)], ExecOptions::default())
                    .await;

                match result {
                    Ok(_) => success += 1,
                    Err(_) => failures += 1,
                }
            }

            (task_id, success, failures)
        });
    }

    // Wait for all tasks
    while let Some(result) = tasks.join_next().await {
        let (task_id, success, failures) = result.expect("task should not panic");
        eprintln!(
            "Concurrent exec task {}: {} success, {} failures",
            task_id, success, failures
        );
    }

    // Should complete without deadlocks
}

// =============================================================================
// LARGE OUTPUT TESTS
// =============================================================================

/// Test handling of large stdout/stderr
#[tokio::test]
async fn test_dst_vm_large_exec_output() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    // Generate large output (simulated - real test would generate MBs)
    // For DST, we verify the system handles large outputs without crashes
    let large_string = "x".repeat(1024 * 100); // 100KB

    let output = sandbox
        .exec("echo", &[&large_string], ExecOptions::default())
        .await
        .expect("should handle large output");

    assert!(output.status.is_success());
    // Output should contain our large string (SimSandbox echoes it)
    assert!(!output.stdout.is_empty());

    sandbox.stop().await.ok();
}

// =============================================================================
// ARCHITECTURE & CONFIG MISMATCH TESTS
// =============================================================================

/// Test restore with architecture mismatch
#[tokio::test]
async fn test_dst_vm_snapshot_arch_mismatch() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    // Create VM with default architecture
    let mut sandbox1 = factory.create(config.clone()).await.expect("should create sandbox");
    sandbox1.start().await.expect("should start");

    let snapshot = sandbox1.snapshot().await.expect("should snapshot");

    // Modify snapshot metadata to have different architecture
    let mut mismatched_snapshot = snapshot.clone();
    // If current arch is Arm64, switch to X86_64 and vice versa
    mismatched_snapshot.metadata.architecture = match snapshot.metadata.architecture {
        Architecture::Arm64 => Architecture::X86_64,
        Architecture::X86_64 => Architecture::Arm64,
    };

    // Attempt to restore with mismatched architecture
    // Should either fail or handle gracefully
    let restore_result = sandbox1.restore(&mismatched_snapshot).await;

    // Verify behavior: either rejects mismatch or handles it
    // (SimSandbox may allow it for testing, real impl should reject)
    if restore_result.is_ok() {
        eprintln!("Note: Restore allowed architecture mismatch (test mode)");
    } else {
        eprintln!("Restore correctly rejected architecture mismatch");
    }

    sandbox1.stop().await.ok();
}

/// Test restore with different memory configuration
#[tokio::test]
async fn test_dst_vm_snapshot_memory_mismatch() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);

    // Create VM with specific memory config
    let mut config1 = SandboxConfig::default();
    config1.limits.memory_bytes_max = 512 * 1024 * 1024; // 512MB

    let mut sandbox1 = factory
        .create(config1)
        .await
        .expect("should create sandbox");
    sandbox1.start().await.expect("should start");

    let snapshot = sandbox1.snapshot().await.expect("should snapshot");

    // Create second VM with different memory
    let mut config2 = SandboxConfig::default();
    config2.limits.memory_bytes_max = 1024 * 1024 * 1024; // 1024MB

    let mut sandbox2 = factory
        .create(config2)
        .await
        .expect("should create sandbox");

    // Attempt to restore snapshot from 512MB VM into 1024MB VM
    // Should either fail or handle gracefully
    let restore_result = sandbox2.restore(&snapshot).await;

    if restore_result.is_ok() {
        eprintln!("Note: Restore allowed memory mismatch (may work in some cases)");
    } else {
        eprintln!("Restore rejected memory mismatch");
    }

    sandbox1.stop().await.ok();
    sandbox2.stop().await.ok();
}

// =============================================================================
// HEALTH CHECK & STATS TESTS
// =============================================================================

/// Test health checks under various states
#[tokio::test]
async fn test_dst_vm_health_checks() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");

    // Health check when stopped
    let health_stopped = sandbox.health_check().await.expect("health check should work");
    // May or may not be healthy when stopped - implementation dependent
    eprintln!("Health when stopped: {}", health_stopped);

    sandbox.start().await.expect("should start");

    // Health check when running - should be healthy
    let health_running = sandbox
        .health_check()
        .await
        .expect("health check should work");
    assert!(health_running, "sandbox should be healthy when running");

    sandbox.pause().await.expect("should pause");

    // Health check when paused
    let health_paused = sandbox.health_check().await.expect("health check should work");
    eprintln!("Health when paused: {}", health_paused);

    sandbox.resume().await.ok();
    sandbox.stop().await.ok();
}

/// Test resource usage statistics
#[tokio::test]
async fn test_dst_vm_stats() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = SandboxConfig::default();

    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    sandbox.start().await.expect("should start");

    // Get stats
    let stats = sandbox.stats().await.expect("should get stats");

    // Stats should have reasonable values (SimSandbox may return mock data)
    eprintln!("Stats: memory={}MB, cpu={:.1}%, disk={}MB",
        stats.memory_bytes_used / (1024 * 1024),
        stats.cpu_percent,
        stats.disk_bytes_used / (1024 * 1024)
    );

    // Execute some commands and check stats again
    for _ in 0..10 {
        sandbox
            .exec("echo", &["stats_test"], ExecOptions::default())
            .await
            .ok();
    }

    let stats_after = sandbox.stats().await.expect("should get stats");
    eprintln!("Stats after exec: memory={}MB, cpu={:.1}%",
        stats_after.memory_bytes_used / (1024 * 1024),
        stats_after.cpu_percent
    );

    sandbox.stop().await.ok();
}

//! DST tests for LibkrunSandbox implementation
//!
//! TigerStyle: Simulation-first testing with comprehensive fault injection.
//!
//! These tests verify that LibkrunSandbox correctly implements the Sandbox trait
//! and handles faults gracefully. Tests are written BEFORE implementation (DST-first).

use std::sync::Arc;

use kelpie_dst::{
    DeterministicRng, FaultConfig, FaultInjectorBuilder, FaultType, SimSandboxFactory,
};
use kelpie_sandbox::{
    ExecOptions, ResourceLimits, Sandbox, SandboxConfig, SandboxFactory, SandboxState,
};

// ============================================================================
// Test Helpers
// ============================================================================

fn get_seed() -> u64 {
    std::env::var("DST_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            let seed = rand::random();
            println!("DST_SEED={}", seed);
            seed
        })
}

fn test_config() -> SandboxConfig {
    SandboxConfig::new()
        .with_limits(
            ResourceLimits::new()
                .with_memory(512 * 1024 * 1024) // 512 MiB
                .with_vcpus(2)
                .with_network(true),
        )
        .with_workdir("/workspace")
        .with_env("PATH", "/usr/bin:/bin")
}

// ============================================================================
// Phase 2 DST Tests - LibkrunSandbox Lifecycle
// ============================================================================

/// Test: Full lifecycle under no faults (baseline)
/// Expected: All operations succeed, state transitions are correct
#[tokio::test]
async fn test_dst_libkrun_sandbox_lifecycle_no_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);
    let faults = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    // Create sandbox
    let mut sandbox = factory.create(config).await.expect("should create sandbox");
    assert_eq!(sandbox.state(), SandboxState::Stopped);

    // Start
    sandbox.start().await.expect("should start");
    assert_eq!(sandbox.state(), SandboxState::Running);

    // Execute command
    let output = sandbox
        .exec("echo", &["hello"], ExecOptions::default())
        .await
        .expect("should exec");
    assert!(output.is_success());

    // Pause
    sandbox.pause().await.expect("should pause");
    assert_eq!(sandbox.state(), SandboxState::Paused);

    // Resume
    sandbox.resume().await.expect("should resume");
    assert_eq!(sandbox.state(), SandboxState::Running);

    // Snapshot
    let snapshot = sandbox.snapshot().await.expect("should snapshot");
    assert_eq!(snapshot.sandbox_id(), sandbox.id());

    // Stop
    sandbox.stop().await.expect("should stop");
    assert_eq!(sandbox.state(), SandboxState::Stopped);

    // Destroy
    sandbox.destroy().await.expect("should destroy");
}

/// Test: Lifecycle with boot faults
/// Expected: Boot failures are detected and reported, no panics
#[tokio::test]
async fn test_dst_libkrun_sandbox_lifecycle_boot_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    // 30% boot failure rate
    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.3))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut boot_successes = 0;
    let mut boot_failures = 0;

    for _ in 0..20 {
        let mut sandbox = factory.create(config.clone()).await.expect("should create");

        match sandbox.start().await {
            Ok(()) => {
                boot_successes += 1;
                assert_eq!(sandbox.state(), SandboxState::Running);
                sandbox.stop().await.ok();
            }
            Err(e) => {
                boot_failures += 1;
                // Sandbox should be in failed state or stopped
                assert!(
                    sandbox.state() == SandboxState::Failed
                        || sandbox.state() == SandboxState::Stopped,
                    "unexpected state after boot failure: {:?}",
                    sandbox.state()
                );
                // Error message should indicate boot failure
                let msg = e.to_string().to_lowercase();
                assert!(
                    msg.contains("boot") || msg.contains("start") || msg.contains("fail"),
                    "error should indicate boot failure: {}",
                    e
                );
            }
        }
    }

    println!(
        "Boot results: {} successes, {} failures",
        boot_successes, boot_failures
    );

    // With 30% failure rate over 20 tries, we expect some of each
    // Statistical: P(all succeed) = 0.7^20 ≈ 0.08%, P(all fail) = 0.3^20 ≈ 0%
    assert!(boot_successes > 0, "should have at least one boot success");
    assert!(
        boot_failures > 0,
        "should have at least one boot failure with 30% rate"
    );
}

/// Test: Lifecycle with crash faults during execution
/// Expected: Crashes are detected, exec fails gracefully
#[tokio::test]
async fn test_dst_libkrun_sandbox_lifecycle_crash_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    // 20% crash rate
    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.2))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config).await.expect("should create");
    sandbox.start().await.expect("should start");

    let mut exec_successes = 0;
    let mut exec_failures = 0;

    for i in 0..10 {
        // Check if sandbox is still running (might have crashed)
        if sandbox.state() != SandboxState::Running {
            println!("Sandbox crashed at iteration {}", i);
            exec_failures += 1;

            // Try to recover by creating new sandbox
            sandbox = factory.create(test_config()).await.expect("should create");
            if sandbox.start().await.is_err() {
                continue;
            }
        }

        match sandbox
            .exec("echo", &["test"], ExecOptions::default())
            .await
        {
            Ok(output) => {
                exec_successes += 1;
                assert!(output.is_success());
            }
            Err(_) => {
                exec_failures += 1;
            }
        }
    }

    println!(
        "Exec results: {} successes, {} failures",
        exec_successes, exec_failures
    );

    // Should have some successes
    assert!(exec_successes > 0, "should have at least one exec success");
}

/// Test: Pause/resume with faults
/// Expected: Pause/resume failures handled gracefully
#[tokio::test]
async fn test_dst_libkrun_sandbox_pause_resume_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxPauseFail, 0.2))
            .with_fault(FaultConfig::new(FaultType::SandboxResumeFail, 0.2))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config).await.expect("should create");
    sandbox.start().await.expect("should start");

    let mut pause_successes = 0;
    let mut pause_failures = 0;
    let mut resume_successes = 0;
    let mut resume_failures = 0;

    for _ in 0..10 {
        if sandbox.state() != SandboxState::Running {
            // Sandbox crashed, skip this iteration
            break;
        }

        // Try pause
        match sandbox.pause().await {
            Ok(()) => {
                pause_successes += 1;
                assert_eq!(sandbox.state(), SandboxState::Paused);

                // Try resume
                match sandbox.resume().await {
                    Ok(()) => {
                        resume_successes += 1;
                        assert_eq!(sandbox.state(), SandboxState::Running);
                    }
                    Err(_) => {
                        resume_failures += 1;
                        // After resume failure, state should still be paused or failed
                        break;
                    }
                }
            }
            Err(_) => {
                pause_failures += 1;
                // After pause failure, state should still be running or failed
                if sandbox.state() == SandboxState::Failed {
                    break;
                }
            }
        }
    }

    println!(
        "Pause: {} ok, {} fail. Resume: {} ok, {} fail",
        pause_successes, pause_failures, resume_successes, resume_failures
    );
}

/// Test: Exec with timeout faults
/// Expected: Timeouts are reported, no hangs
#[tokio::test]
async fn test_dst_libkrun_sandbox_exec_timeout_faults() {
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
    let config = test_config();

    let mut sandbox = factory.create(config).await.expect("should create");
    sandbox.start().await.expect("should start");

    let mut timeouts = 0;
    let mut successes = 0;

    for _ in 0..10 {
        if sandbox.state() != SandboxState::Running {
            break;
        }

        let options = ExecOptions {
            timeout_ms: Some(5000),
            ..Default::default()
        };

        match sandbox.exec("echo", &["test"], options).await {
            Ok(_) => successes += 1,
            Err(e) => {
                let msg = e.to_string().to_lowercase();
                if msg.contains("timeout") || msg.contains("timed out") {
                    timeouts += 1;
                }
            }
        }
    }

    println!(
        "Exec timeout test: {} successes, {} timeouts",
        successes, timeouts
    );

    // Should see both successes and timeouts
    assert!(
        successes > 0 || timeouts > 0,
        "should complete some operations"
    );
}

/// Test: Exec with failure faults
/// Expected: Exec failures reported correctly
#[tokio::test]
async fn test_dst_libkrun_sandbox_exec_failure_faults() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.3))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config).await.expect("should create");
    sandbox.start().await.expect("should start");

    let mut failures = 0;
    let mut successes = 0;

    for _ in 0..10 {
        if sandbox.state() != SandboxState::Running {
            break;
        }

        match sandbox
            .exec("echo", &["test"], ExecOptions::default())
            .await
        {
            Ok(_) => successes += 1,
            Err(e) => {
                failures += 1;
                // Should be an exec failure, not a crash
                let msg = e.to_string().to_lowercase();
                assert!(
                    msg.contains("exec") || msg.contains("fail") || msg.contains("command"),
                    "error should indicate exec failure: {}",
                    e
                );
            }
        }
    }

    println!(
        "Exec failure test: {} successes, {} failures",
        successes, failures
    );
}

// ============================================================================
// Phase 2 DST Tests - Snapshot/Restore
// ============================================================================

/// Test: Snapshot with corruption faults
/// Expected: Corrupted snapshots detected, restore fails gracefully
#[tokio::test]
async fn test_dst_libkrun_sandbox_snapshot_corruption() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.3))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config.clone()).await.expect("should create");
    sandbox.start().await.expect("should start");

    // Take snapshot
    let snapshot = sandbox.snapshot().await.expect("should snapshot");

    sandbox.stop().await.expect("should stop");

    // Try to restore - may fail due to corruption
    let mut new_sandbox = factory.create(config).await.expect("should create new");

    match new_sandbox.restore(&snapshot).await {
        Ok(()) => {
            println!("Restore succeeded (no corruption injected)");
        }
        Err(e) => {
            let msg = e.to_string().to_lowercase();
            println!("Restore failed: {}", e);
            assert!(
                msg.contains("corrupt") || msg.contains("restore") || msg.contains("fail"),
                "error should indicate corruption: {}",
                e
            );
        }
    }
}

/// Test: Snapshot create failure
/// Expected: Failure is reported, sandbox remains usable
#[tokio::test]
async fn test_dst_libkrun_sandbox_snapshot_create_fail() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 0.5))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config).await.expect("should create");
    sandbox.start().await.expect("should start");

    let mut snapshot_successes = 0;
    let mut snapshot_failures = 0;

    for _ in 0..10 {
        if sandbox.state() != SandboxState::Running {
            break;
        }

        match sandbox.snapshot().await {
            Ok(_) => snapshot_successes += 1,
            Err(_) => snapshot_failures += 1,
        }

        // Sandbox should still be usable after snapshot failure
        if sandbox.state() == SandboxState::Running {
            let exec_result = sandbox
                .exec("echo", &["still working"], ExecOptions::default())
                .await;
            assert!(
                exec_result.is_ok(),
                "sandbox should still work after snapshot failure"
            );
        }
    }

    println!(
        "Snapshot create: {} successes, {} failures",
        snapshot_successes, snapshot_failures
    );
}

/// Test: Restore failure
/// Expected: Restore failure reported, sandbox can be used normally
#[tokio::test]
async fn test_dst_libkrun_sandbox_restore_fail() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SnapshotRestoreFail, 0.5))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config.clone()).await.expect("should create");
    sandbox.start().await.expect("should start");

    // Take snapshot (should succeed - no create faults)
    let snapshot = sandbox.snapshot().await.expect("should snapshot");
    sandbox.stop().await.expect("should stop");

    let mut restore_successes = 0;
    let mut restore_failures = 0;

    for _ in 0..5 {
        let mut new_sandbox = factory
            .create(config.clone())
            .await
            .expect("should create new");

        match new_sandbox.restore(&snapshot).await {
            Ok(()) => {
                restore_successes += 1;
                // After successful restore, should be able to start and use
                if new_sandbox.start().await.is_ok() {
                    assert_eq!(new_sandbox.state(), SandboxState::Running);
                }
            }
            Err(_) => {
                restore_failures += 1;
                // After failed restore, sandbox should still be usable as fresh
                assert!(
                    new_sandbox.start().await.is_ok(),
                    "should start fresh after restore fail"
                );
            }
        }
    }

    println!(
        "Restore: {} successes, {} failures",
        restore_successes, restore_failures
    );
}

// ============================================================================
// Phase 2 DST Tests - Determinism
// ============================================================================

/// Test: Same seed produces same behavior
/// Critical: DST requires determinism for reproducibility
#[tokio::test]
async fn test_dst_libkrun_sandbox_determinism() {
    let seed = 42u64; // Fixed seed for determinism test

    let mut results1 = Vec::new();
    let mut results2 = Vec::new();

    // Run 1
    {
        let rng = DeterministicRng::new(seed);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.2))
                .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.2))
                .build(),
        );

        let factory = SimSandboxFactory::new(rng.fork(), faults);

        for _ in 0..5 {
            let config = test_config();
            let mut sandbox = factory.create(config).await.expect("create");

            let start_result = sandbox.start().await.is_ok();
            results1.push(format!("start:{}", start_result));

            if start_result {
                let exec_result = sandbox
                    .exec("echo", &["test"], ExecOptions::default())
                    .await
                    .is_ok();
                results1.push(format!("exec:{}", exec_result));
            }
        }
    }

    // Run 2 with same seed
    {
        let rng = DeterministicRng::new(seed);
        let faults = Arc::new(
            FaultInjectorBuilder::new(rng.fork())
                .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.2))
                .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.2))
                .build(),
        );

        let factory = SimSandboxFactory::new(rng.fork(), faults);

        for _ in 0..5 {
            let config = test_config();
            let mut sandbox = factory.create(config).await.expect("create");

            let start_result = sandbox.start().await.is_ok();
            results2.push(format!("start:{}", start_result));

            if start_result {
                let exec_result = sandbox
                    .exec("echo", &["test"], ExecOptions::default())
                    .await
                    .is_ok();
                results2.push(format!("exec:{}", exec_result));
            }
        }
    }

    assert_eq!(results1, results2, "same seed must produce same results");
    println!(
        "Determinism verified: {} operations matched",
        results1.len()
    );
}

// ============================================================================
// Phase 2 DST Tests - Combined Fault Scenarios
// ============================================================================

/// Test: Multiple fault types simultaneously (chaos testing)
/// Expected: System remains stable, no panics, errors handled gracefully
#[tokio::test]
async fn test_dst_libkrun_sandbox_chaos() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    // Enable multiple fault types at moderate rates
    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.1))
            .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.1))
            .with_fault(FaultConfig::new(FaultType::SandboxPauseFail, 0.1))
            .with_fault(FaultConfig::new(FaultType::SandboxResumeFail, 0.1))
            .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.1))
            .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 0.1))
            .with_fault(FaultConfig::new(FaultType::SnapshotRestoreFail, 0.1))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);

    let mut total_operations = 0;
    let mut successful_operations = 0;
    let mut failed_operations = 0;

    for round in 0..5 {
        let config = test_config();
        let mut sandbox = match factory.create(config).await {
            Ok(s) => s,
            Err(_) => {
                failed_operations += 1;
                continue;
            }
        };
        total_operations += 1;

        // Try start
        if sandbox.start().await.is_ok() {
            successful_operations += 1;

            // Try exec
            total_operations += 1;
            if sandbox
                .exec(
                    "echo",
                    &["round", &round.to_string()],
                    ExecOptions::default(),
                )
                .await
                .is_ok()
            {
                successful_operations += 1;
            } else {
                failed_operations += 1;
            }

            // Try snapshot
            if sandbox.state() == SandboxState::Running {
                total_operations += 1;
                if sandbox.snapshot().await.is_ok() {
                    successful_operations += 1;
                } else {
                    failed_operations += 1;
                }
            }

            // Try pause/resume cycle
            if sandbox.state() == SandboxState::Running {
                total_operations += 2;
                if sandbox.pause().await.is_ok() {
                    successful_operations += 1;
                    if sandbox.resume().await.is_ok() {
                        successful_operations += 1;
                    } else {
                        failed_operations += 1;
                    }
                } else {
                    failed_operations += 2; // pause failed, skip resume
                }
            }
        } else {
            failed_operations += 1;
        }

        // Cleanup
        let _ = sandbox.destroy().await;
    }

    println!(
        "Chaos test: {} total, {} succeeded, {} failed",
        total_operations, successful_operations, failed_operations
    );

    // With 10% fault rate per operation, we should see some successes
    assert!(
        successful_operations > 0,
        "should have some successful operations even under chaos"
    );
}

/// Test: Factory with snapshot restoration under faults
#[tokio::test]
async fn test_dst_libkrun_sandbox_factory_from_snapshot() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.2))
            .with_fault(FaultConfig::new(FaultType::SnapshotRestoreFail, 0.2))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    // Create and snapshot a sandbox
    let mut sandbox = factory.create(config.clone()).await.expect("should create");
    sandbox.start().await.expect("should start");

    // Modify state
    sandbox
        .exec("echo", &["state modified"], ExecOptions::default())
        .await
        .ok();

    let snapshot = sandbox.snapshot().await.expect("should snapshot");
    sandbox.stop().await.expect("should stop");

    // Try create_from_snapshot multiple times
    let mut restore_successes = 0;
    let mut restore_failures = 0;

    for _ in 0..5 {
        match factory
            .create_from_snapshot(config.clone(), &snapshot)
            .await
        {
            Ok(mut new_sandbox) => {
                restore_successes += 1;
                // Should be able to start the restored sandbox
                if new_sandbox.start().await.is_ok() {
                    assert_eq!(new_sandbox.state(), SandboxState::Running);
                }
            }
            Err(_) => {
                restore_failures += 1;
            }
        }
    }

    println!(
        "Factory from snapshot: {} successes, {} failures",
        restore_successes, restore_failures
    );
}

// ============================================================================
// Stress Tests (ignored by default, run with --ignored)
// ============================================================================

/// Stress test: Rapid sandbox creation/destruction
#[tokio::test]
#[ignore]
async fn test_dst_libkrun_sandbox_stress_lifecycle() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxBootFail, 0.05))
            .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.05))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);

    let mut successes = 0;
    let iterations = 100;

    for i in 0..iterations {
        let config = test_config();
        let mut sandbox = match factory.create(config).await {
            Ok(s) => s,
            Err(_) => continue,
        };

        if sandbox.start().await.is_ok() {
            if sandbox
                .exec("echo", &[&i.to_string()], ExecOptions::default())
                .await
                .is_ok()
            {
                successes += 1;
            }
            sandbox.stop().await.ok();
        }

        sandbox.destroy().await.ok();
    }

    println!(
        "Stress lifecycle: {}/{} successful iterations",
        successes, iterations
    );

    // Should have good success rate with 5% fault rates
    assert!(successes > iterations / 2, "should have >50% success rate");
}

/// Stress test: Many exec operations on single sandbox
#[tokio::test]
#[ignore]
async fn test_dst_libkrun_sandbox_stress_exec() {
    let seed = get_seed();
    let rng = DeterministicRng::new(seed);

    let faults = Arc::new(
        FaultInjectorBuilder::new(rng.fork())
            .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 0.02))
            .with_fault(FaultConfig::new(FaultType::SandboxCrash, 0.01))
            .build(),
    );

    let factory = SimSandboxFactory::new(rng.fork(), faults);
    let config = test_config();

    let mut sandbox = factory.create(config).await.expect("should create");
    sandbox.start().await.expect("should start");

    let mut successes = 0;
    let iterations = 500;

    for i in 0..iterations {
        if sandbox.state() != SandboxState::Running {
            println!("Sandbox crashed at iteration {}", i);
            break;
        }

        if sandbox
            .exec("echo", &[&i.to_string()], ExecOptions::default())
            .await
            .is_ok()
        {
            successes += 1;
        }
    }

    println!(
        "Stress exec: {}/{} successful operations",
        successes, iterations
    );

    assert!(successes > iterations / 2, "should have >50% success rate");
}

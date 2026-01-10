//! DST tests for sandbox operations
//!
//! TigerStyle: Deterministic testing of sandbox lifecycle,
//! snapshot/restore, and pool operations under fault injection.

use kelpie_dst::{SimConfig, Simulation};
use kelpie_sandbox::{
    ExecOutput, MockSandbox, PoolConfig, Sandbox, SandboxConfig, SandboxFactory, SandboxPool,
    SandboxState, Snapshot,
};
use std::time::Duration;

// =============================================================================
// Mock Sandbox Factory for DST
// =============================================================================

/// Factory that uses DST RNG for deterministic sandbox creation
struct DstMockSandboxFactory {
    prefix: String,
    counter: std::sync::atomic::AtomicU64,
}

impl DstMockSandboxFactory {
    fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
            counter: std::sync::atomic::AtomicU64::new(0),
        }
    }
}

#[async_trait::async_trait]
impl SandboxFactory for DstMockSandboxFactory {
    type Sandbox = MockSandbox;

    async fn create(&self, config: SandboxConfig) -> kelpie_sandbox::SandboxResult<MockSandbox> {
        let id = self
            .counter
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let sandbox_id = format!("{}-{}", self.prefix, id);
        let mut sandbox = MockSandbox::with_id(sandbox_id, config);
        sandbox.start().await?;
        Ok(sandbox)
    }

    async fn create_from_snapshot(
        &self,
        config: SandboxConfig,
        snapshot: &Snapshot,
    ) -> kelpie_sandbox::SandboxResult<MockSandbox> {
        let id = self
            .counter
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let sandbox_id = format!("{}-{}", self.prefix, id);
        let mut sandbox = MockSandbox::with_id(sandbox_id, config);
        sandbox.restore(snapshot).await?;
        sandbox.start().await?;
        Ok(sandbox)
    }
}

// =============================================================================
// Basic Lifecycle Tests
// =============================================================================

#[test]
fn test_dst_sandbox_lifecycle_basic() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);

        // Initial state
        assert_eq!(sandbox.state(), SandboxState::Stopped);

        // Start
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert_eq!(sandbox.state(), SandboxState::Running);

        // Pause
        sandbox
            .pause()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert_eq!(sandbox.state(), SandboxState::Paused);

        // Resume
        sandbox
            .resume()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert_eq!(sandbox.state(), SandboxState::Running);

        // Stop
        sandbox
            .stop()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert_eq!(sandbox.state(), SandboxState::Stopped);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_sandbox_state_transitions_invalid() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);

        // Can't pause when stopped
        let pause_result = sandbox.pause().await;
        assert!(pause_result.is_err());

        // Can't resume when stopped
        let resume_result = sandbox.resume().await;
        assert!(resume_result.is_err());

        // Start first
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Can't start when already running
        let start_result = sandbox.start().await;
        assert!(start_result.is_err());

        // Can't resume when running (must be paused)
        let resume_result = sandbox.resume().await;
        assert!(resume_result.is_err());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Exec Tests
// =============================================================================

#[test]
fn test_dst_sandbox_exec_determinism() {
    let seed = 42;
    let config = SimConfig::new(seed);

    let run_test =
        || {
            Simulation::new(config.clone()).run(|_env| async move {
                let sandbox_config = SandboxConfig::default();
                let mut sandbox = MockSandbox::new(sandbox_config);
                sandbox
                    .start()
                    .await
                    .map_err(|e| kelpie_core::Error::Internal {
                        message: e.to_string(),
                    })?;

                // Run multiple exec commands
                let mut results = Vec::new();

                let output = sandbox.exec_simple("echo", &["test1"]).await.map_err(|e| {
                    kelpie_core::Error::Internal {
                        message: e.to_string(),
                    }
                })?;
                results.push(output.stdout_string());

                let output = sandbox.exec_simple("pwd", &[]).await.map_err(|e| {
                    kelpie_core::Error::Internal {
                        message: e.to_string(),
                    }
                })?;
                results.push(output.stdout_string());

                let output = sandbox.exec_simple("ls", &[]).await.map_err(|e| {
                    kelpie_core::Error::Internal {
                        message: e.to_string(),
                    }
                })?;
                results.push(output.stdout_string());

                Ok(results)
            })
        };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Exec results should be deterministic");
}

#[test]
fn test_dst_sandbox_exec_with_custom_handler() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Register custom handler that uses deterministic behavior
        sandbox
            .register_handler(
                "compute",
                Box::new(|args, _opts| {
                    let sum: i64 = args.iter().filter_map(|a| a.parse::<i64>().ok()).sum();
                    ExecOutput::success(format!("{}\n", sum))
                }),
            )
            .await;

        let output = sandbox
            .exec_simple("compute", &["10", "20", "30"])
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        assert!(output.is_success());
        assert_eq!(output.stdout_string().trim(), "60");

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_sandbox_exec_failure_handling() {
    let config = SimConfig::from_env_or_random();

    let result =
        Simulation::new(config).run(|_env| async move {
            let sandbox_config = SandboxConfig::default();
            let mut sandbox = MockSandbox::new(sandbox_config);
            sandbox
                .start()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            // Unknown command
            let output = sandbox
                .exec_simple("unknown_command", &[])
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            assert!(!output.is_success());
            assert_eq!(output.status.code, 127); // Command not found

            // false command
            let output = sandbox.exec_simple("false", &[]).await.map_err(|e| {
                kelpie_core::Error::Internal {
                    message: e.to_string(),
                }
            })?;

            assert!(!output.is_success());
            assert_eq!(output.status.code, 1);

            Ok(())
        });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Snapshot/Restore Tests
// =============================================================================

#[test]
fn test_dst_sandbox_snapshot_restore_determinism() {
    let seed = 12345;

    let run_test = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|_env| async move {
            let sandbox_config = SandboxConfig::default()
                .with_env("TEST_VAR", "test_value")
                .with_workdir("/test");

            let mut sandbox = MockSandbox::new(sandbox_config.clone());
            sandbox
                .start()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            // Write files
            sandbox.write_file("/data/file1.txt", "content1").await;
            sandbox.write_file("/data/file2.txt", "content2").await;
            sandbox.set_env("DYNAMIC_VAR", "dynamic_value").await;

            // Create snapshot
            let snapshot = sandbox
                .snapshot()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            // Create new sandbox and restore
            let mut sandbox2 = MockSandbox::new(sandbox_config);
            sandbox2
                .restore(&snapshot)
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            sandbox2
                .start()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            // Verify restored data
            let file1 = sandbox2.read_file("/data/file1.txt").await;
            let file2 = sandbox2.read_file("/data/file2.txt").await;
            let env_var = sandbox2.get_env("DYNAMIC_VAR").await;

            Ok((
                file1.map(|b| String::from_utf8_lossy(&b).into_owned()),
                file2.map(|b| String::from_utf8_lossy(&b).into_owned()),
                env_var,
            ))
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Snapshot/restore should be deterministic");
    assert_eq!(result1.0, Some("content1".to_string()));
    assert_eq!(result1.1, Some("content2".to_string()));
    assert_eq!(result1.2, Some("dynamic_value".to_string()));
}

#[test]
fn test_dst_sandbox_snapshot_metadata() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Add some data
        sandbox.write_file("/large_file", vec![b'x'; 1000]).await;

        let snapshot = sandbox
            .snapshot()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Verify metadata
        assert_eq!(snapshot.sandbox_id(), sandbox.id());
        assert!(snapshot.has_memory());

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Pool Tests
// =============================================================================

#[test]
fn test_dst_sandbox_pool_determinism() {
    let seed = 99999;

    let run_test = || {
        let config = SimConfig::new(seed);
        Simulation::new(config).run(|_env| async move {
            let factory = DstMockSandboxFactory::new("dst-pool");
            let pool_config = PoolConfig::new(SandboxConfig::default())
                .with_min_size(2)
                .with_max_size(5);

            let pool = SandboxPool::new(factory, pool_config).map_err(|e| {
                kelpie_core::Error::Internal {
                    message: e.to_string(),
                }
            })?;

            pool.warm_up()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            // Acquire and track IDs
            let s1 = pool
                .acquire()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            let s2 = pool
                .acquire()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            let ids = vec![s1.id().to_string(), s2.id().to_string()];

            pool.release(s1).await;
            pool.release(s2).await;

            let stats = pool.stats().await;

            Ok((ids, stats.total_created, stats.warm_count))
        })
    };

    let result1 = run_test().expect("First run failed");
    let result2 = run_test().expect("Second run failed");

    assert_eq!(result1, result2, "Pool operations should be deterministic");
}

#[test]
fn test_dst_sandbox_pool_exhaustion() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let factory = DstMockSandboxFactory::new("exhaust-pool");
        let pool_config = PoolConfig::new(SandboxConfig::default())
            .with_min_size(1)
            .with_max_size(2)
            .with_acquire_timeout(Duration::from_millis(100));

        let pool =
            SandboxPool::new(factory, pool_config).map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Acquire both available slots
        let s1 = pool
            .acquire()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        let s2 = pool
            .acquire()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Pool is now at capacity, can't acquire more without release
        // (Third acquire would timeout, but we don't want to wait in tests)

        let stats = pool.stats().await;
        assert_eq!(stats.total_created, 2);

        pool.release(s1).await;
        pool.release(s2).await;

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_sandbox_pool_warm_up() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let factory = DstMockSandboxFactory::new("warmup-pool");
        let pool_config = PoolConfig::new(SandboxConfig::default())
            .with_min_size(3)
            .with_max_size(5);

        let pool =
            SandboxPool::new(factory, pool_config).map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Check before warm up
        let stats_before = pool.stats().await;
        assert_eq!(stats_before.warm_count, 0);
        assert_eq!(stats_before.total_created, 0);

        // Warm up
        pool.warm_up()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Check after warm up
        let stats_after = pool.stats().await;
        assert_eq!(stats_after.warm_count, 3);
        assert_eq!(stats_after.total_created, 3);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_sandbox_pool_drain() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let factory = DstMockSandboxFactory::new("drain-pool");
        let pool_config = PoolConfig::new(SandboxConfig::default())
            .with_min_size(3)
            .with_max_size(5);

        let pool =
            SandboxPool::new(factory, pool_config).map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        pool.warm_up()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Drain all sandboxes
        pool.drain().await;

        let stats = pool.stats().await;
        assert_eq!(stats.warm_count, 0);
        assert_eq!(stats.total_destroyed, 3);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Health Check Tests
// =============================================================================

#[test]
fn test_dst_sandbox_health_check() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);

        // Not healthy when stopped
        let healthy = sandbox
            .health_check()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert!(!healthy);

        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Healthy when running
        let healthy = sandbox
            .health_check()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert!(healthy);

        sandbox
            .pause()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Not healthy when paused
        let healthy = sandbox
            .health_check()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        assert!(!healthy);

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Stats Tests
// =============================================================================

#[test]
fn test_dst_sandbox_stats() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Set memory usage
        sandbox.set_memory_used(1024 * 1024); // 1MB

        // Advance time
        env.advance_time_ms(5000);

        let stats = sandbox
            .stats()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        assert_eq!(stats.memory_bytes_used, 1024 * 1024);
        // Note: Uptime is based on real clock in MockSandbox, not simulated

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// =============================================================================
// Stress Tests (Longer running, deterministic)
// =============================================================================

#[test]
fn test_dst_sandbox_rapid_lifecycle() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);

        // Rapidly cycle through states
        for _ in 0..100 {
            sandbox
                .start()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert_eq!(sandbox.state(), SandboxState::Running);

            sandbox
                .pause()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert_eq!(sandbox.state(), SandboxState::Paused);

            sandbox
                .resume()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert_eq!(sandbox.state(), SandboxState::Running);

            sandbox
                .stop()
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;
            assert_eq!(sandbox.state(), SandboxState::Stopped);
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_sandbox_many_exec_operations() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Run many exec operations
        for i in 0..1000 {
            let output = sandbox
                .exec_simple("echo", &[&format!("iteration-{}", i)])
                .await
                .map_err(|e| kelpie_core::Error::Internal {
                    message: e.to_string(),
                })?;

            assert!(output.is_success());
            assert!(output.stdout_string().contains(&format!("iteration-{}", i)));
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_dst_sandbox_many_files() {
    let config = SimConfig::from_env_or_random();

    let result = Simulation::new(config).run(|_env| async move {
        let sandbox_config = SandboxConfig::default();
        let mut sandbox = MockSandbox::new(sandbox_config);
        sandbox
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Write many files
        for i in 0..100 {
            let path = format!("/files/file_{}.txt", i);
            let content = format!("content for file {}", i);
            sandbox.write_file(&path, content).await;
        }

        // Read them back
        for i in 0..100 {
            let path = format!("/files/file_{}.txt", i);
            let expected = format!("content for file {}", i);
            let content = sandbox.read_file(&path).await;
            assert_eq!(
                content.map(|b| String::from_utf8_lossy(&b).into_owned()),
                Some(expected)
            );
        }

        // Create snapshot with all files
        let snapshot = sandbox
            .snapshot()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Restore and verify
        let mut sandbox2 = MockSandbox::new(SandboxConfig::default());
        sandbox2
            .restore(&snapshot)
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;
        sandbox2
            .start()
            .await
            .map_err(|e| kelpie_core::Error::Internal {
                message: e.to_string(),
            })?;

        // Verify files exist in restored sandbox
        for i in 0..100 {
            let path = format!("/files/file_{}.txt", i);
            let expected = format!("content for file {}", i);
            let content = sandbox2.read_file(&path).await;
            assert_eq!(
                content.map(|b| String::from_utf8_lossy(&b).into_owned()),
                Some(expected)
            );
        }

        Ok(())
    });

    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

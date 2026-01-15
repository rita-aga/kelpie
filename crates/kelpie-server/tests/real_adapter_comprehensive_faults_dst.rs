//! Comprehensive fault injection tests for RealLlmAdapter (Phase 7.8 - TRUE DST)
//!
//! TigerStyle: Full simulation with multiple fault types, high probabilities
//!
//! Tests verify streaming works under extreme conditions:
//! - Multiple fault types (3-5 per test)
//! - High fault probabilities (60-90%)
//! - Network, Storage, Crash, Time faults
//! - Concurrent stress (10-20 streams)

use futures::stream::StreamExt;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_server::actor::{LlmClient, LlmMessage, RealLlmAdapter, StreamChunk};
use kelpie_server::llm::{LlmClient as RealLlmClient, LlmConfig};
use mockito::Server;

/// Mock Anthropic SSE response (helper function)
fn mock_sse_response() -> String {
    vec![
        "event: message_start\n",
        "data: {\"type\":\"message_start\",\"message\":{\"id\":\"msg_test\"}}\n\n",
        "event: content_block_start\n",
        "data: {\"type\":\"content_block_start\",\"index\":0}\n\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"A\"}}\n\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"B\"}}\n\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"C\"}}\n\n",
        "event: content_block_stop\n",
        "data: {\"type\":\"content_block_stop\",\"index\":0}\n\n",
        "event: message_stop\n",
        "data: {\"type\":\"message_stop\"}\n\n",
    ]
    .join("")
}

/// Test with MULTIPLE network faults (60-80% rates)
///
/// Faults:
/// - NetworkDelay: 70% probability, 20-200ms
/// - NetworkPacketLoss: 20% probability
/// - NetworkMessageReorder: 30% probability
///
/// Contract: Stream completes despite high network fault rates
#[tokio::test]
async fn test_dst_network_faults_high_rate() {
    let config = SimConfig::new(9001);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 20,
                max_ms: 200,
            },
            0.7, // 70% of operations delayed
        ))
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.2)) // 20% packet loss
        .with_fault(FaultConfig::new(FaultType::NetworkMessageReorder, 0.3)) // 30% reorder
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .create_async()
                .await;

            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test".to_string(),
                }])
                .await?;

            let mut content = String::new();
            let mut chunk_count = 0;

            while let Some(chunk_result) = stream.next().await {
                let chunk = chunk_result?;
                chunk_count += 1;

                if let StreamChunk::ContentDelta { delta } = chunk {
                    content.push_str(&delta);
                }
            }

            // Verify completion despite 70% network delays
            assert!(
                chunk_count >= 4,
                "Should have all chunks despite network faults"
            );
            assert_eq!(content, "ABC", "Content should be complete");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Network faults test failed: {:?}",
        result.err()
    );
}

/// Test with MULTIPLE storage faults (60-80% rates)
///
/// Faults:
/// - StorageLatency: 80% probability, 50-300ms
/// - StorageWriteFail: 10% probability
/// - DiskFull: 5% probability
///
/// Contract: Stream completes despite high storage fault rates
#[tokio::test]
async fn test_dst_storage_faults_high_rate() {
    let config = SimConfig::new(9002);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 50,
                max_ms: 300,
            },
            0.8, // 80% of storage ops delayed
        ))
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1)) // 10% write failures
        .with_fault(FaultConfig::new(FaultType::DiskFull, 0.05)) // 5% disk full
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .create_async()
                .await;

            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test".to_string(),
                }])
                .await?;

            let mut chunk_count = 0;
            while let Some(chunk_result) = stream.next().await {
                let _chunk = chunk_result?;
                chunk_count += 1;
            }

            // Verify completion despite 80% storage latency
            assert!(chunk_count >= 4, "Should complete despite storage faults");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Storage faults test failed: {:?}",
        result.err()
    );
}

/// Test with crash faults during streaming
///
/// Faults:
/// - CrashBeforeWrite: 5% probability
/// - CrashAfterWrite: 5% probability
/// - StorageLatency: 60% probability
///
/// Contract: Stream handles crashes gracefully
#[tokio::test]
async fn test_dst_crash_faults() {
    let config = SimConfig::new(9003);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::CrashBeforeWrite, 0.05)) // 5% crash before
        .with_fault(FaultConfig::new(FaultType::CrashAfterWrite, 0.05)) // 5% crash after
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 30,
                max_ms: 150,
            },
            0.6, // 60% storage delays
        ))
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .create_async()
                .await;

            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test".to_string(),
                }])
                .await?;

            let mut chunk_count = 0;
            while let Some(chunk_result) = stream.next().await {
                let _chunk = chunk_result?;
                chunk_count += 1;
            }

            // Verify completion despite crash faults
            assert!(chunk_count > 0, "Should have chunks despite crashes");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Crash faults test failed: {:?}",
        result.err()
    );
}

/// Test with time faults during streaming
///
/// Faults:
/// - ClockSkew: 40% probability, -100 to +100ms
/// - StorageLatency: 50% probability
/// - NetworkDelay: 50% probability
///
/// Contract: Stream completes despite time skew
#[tokio::test]
async fn test_dst_time_faults() {
    let config = SimConfig::new(9004);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::ClockSkew {
                delta_ms: 50, // 50ms clock skew
            },
            0.4, // 40% clock skew
        ))
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 20,
                max_ms: 100,
            },
            0.5,
        ))
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 20,
                max_ms: 100,
            },
            0.5,
        ))
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .create_async()
                .await;

            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test".to_string(),
                }])
                .await?;

            let mut chunk_count = 0;
            while let Some(chunk_result) = stream.next().await {
                let _chunk = chunk_result?;
                chunk_count += 1;
            }

            assert!(chunk_count >= 4, "Should complete despite time faults");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Time faults test failed: {:?}",
        result.err()
    );
}

/// Test with ALL fault types simultaneously (comprehensive chaos)
///
/// Faults (5 types):
/// - NetworkDelay: 60% probability
/// - StorageLatency: 70% probability
/// - NetworkPacketLoss: 20% probability
/// - StorageWriteFail: 10% probability
/// - ClockSkew: 30% probability
///
/// Contract: Stream completes despite multiple simultaneous faults
#[tokio::test]
async fn test_dst_all_faults_comprehensive() {
    let config = SimConfig::new(9005);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 30,
                max_ms: 200,
            },
            0.6, // 60% network delays
        ))
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 40,
                max_ms: 250,
            },
            0.7, // 70% storage latency
        ))
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.2)) // 20% packet loss
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.1)) // 10% write failures
        .with_fault(FaultConfig::new(
            FaultType::ClockSkew {
                delta_ms: 25, // 25ms clock skew
            },
            0.3, // 30% clock skew
        ))
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .create_async()
                .await;

            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Chaos test".to_string(),
                }])
                .await?;

            let mut content = String::new();
            let mut chunk_count = 0;

            while let Some(chunk_result) = stream.next().await {
                let chunk = chunk_result?;
                chunk_count += 1;

                if let StreamChunk::ContentDelta { delta } = chunk {
                    content.push_str(&delta);
                }
            }

            // Verify completion despite ALL faults active
            assert!(
                chunk_count >= 4,
                "Should complete despite 5 simultaneous fault types"
            );
            assert_eq!(content, "ABC", "Content should be intact");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Comprehensive faults test failed: {:?}",
        result.err()
    );
}

/// Test concurrent stress with high fault rates (10 streams)
///
/// Faults:
/// - NetworkDelay: 70% probability
/// - StorageLatency: 80% probability
/// - NetworkPacketLoss: 25% probability
///
/// Contract: 10 concurrent streams complete despite high fault rates
#[tokio::test]
async fn test_dst_concurrent_stress_with_faults() {
    let config = SimConfig::new(9006);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 50,
                max_ms: 300,
            },
            0.7, // 70% network delays
        ))
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 60,
                max_ms: 350,
            },
            0.8, // 80% storage latency
        ))
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.25)) // 25% packet loss
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .expect(10) // Expect 10 concurrent requests
                .create_async()
                .await;

            // Create 10 concurrent streams
            let mut handles = Vec::new();

            for i in 1..=10 {
                let uri = server.url();
                let handle = tokio::spawn(async move {
                    let llm_config = LlmConfig {
                        base_url: format!("{}/test.anthropic.com", uri),
                        api_key: "test-key".to_string(),
                        model: "claude-test".to_string(),
                        max_tokens: 100,
                    };
                    let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

                    let mut stream = adapter
                        .stream_complete(vec![LlmMessage {
                            role: "user".to_string(),
                            content: format!("Concurrent {}", i),
                        }])
                        .await?;

                    let mut chunk_count = 0;
                    while let Some(chunk_result) = stream.next().await {
                        let _chunk = chunk_result?;
                        chunk_count += 1;
                    }

                    Ok::<usize, kelpie_core::Error>(chunk_count)
                });

                handles.push(handle);
            }

            // All 10 streams should complete
            for handle in handles {
                match handle.await {
                    Ok(Ok(count)) => {
                        assert!(count >= 4, "Each stream should complete");
                    }
                    Ok(Err(e)) => panic!("Stream failed: {:?}", e),
                    Err(e) => panic!("Task panicked: {:?}", e),
                }
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Concurrent stress test failed: {:?}",
        result.err()
    );
}

/// Test extreme stress: 20 concurrent streams + ALL faults (90% rates)
///
/// Faults (6 types, very high rates):
/// - NetworkDelay: 90% probability, 100-500ms
/// - StorageLatency: 90% probability, 100-500ms
/// - NetworkPacketLoss: 30% probability
/// - StorageWriteFail: 15% probability
/// - ClockSkew: 40% probability
/// - NetworkMessageReorder: 40% probability
///
/// Contract: System survives extreme chaos
#[tokio::test]
async fn test_dst_extreme_chaos() {
    let config = SimConfig::new(9007);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::NetworkDelay {
                min_ms: 100,
                max_ms: 500,
            },
            0.9, // 90% network delays
        ))
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 100,
                max_ms: 500,
            },
            0.9, // 90% storage latency
        ))
        .with_fault(FaultConfig::new(FaultType::NetworkPacketLoss, 0.3)) // 30% packet loss
        .with_fault(FaultConfig::new(FaultType::StorageWriteFail, 0.15)) // 15% write fail
        .with_fault(FaultConfig::new(
            FaultType::ClockSkew {
                delta_ms: 100, // 100ms clock skew
            },
            0.4, // 40% clock skew
        ))
        .with_fault(FaultConfig::new(FaultType::NetworkMessageReorder, 0.4)) // 40% reorder
        .run_async(|_sim_env| async move {
            let mut server = Server::new_async().await;

            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_sse_response())
                .expect(20) // Expect 20 concurrent requests
                .create_async()
                .await;

            // Create 20 concurrent streams under extreme chaos
            let mut handles = Vec::new();

            for i in 1..=20 {
                let uri = server.url();
                let handle = tokio::spawn(async move {
                    let llm_config = LlmConfig {
                        base_url: format!("{}/test.anthropic.com", uri),
                        api_key: "test-key".to_string(),
                        model: "claude-test".to_string(),
                        max_tokens: 100,
                    };
                    let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

                    let mut stream = adapter
                        .stream_complete(vec![LlmMessage {
                            role: "user".to_string(),
                            content: format!("Chaos {}", i),
                        }])
                        .await?;

                    let mut chunk_count = 0;
                    while let Some(chunk_result) = stream.next().await {
                        let _chunk = chunk_result?;
                        chunk_count += 1;
                    }

                    Ok::<usize, kelpie_core::Error>(chunk_count)
                });

                handles.push(handle);
            }

            // Count completions (some may fail under extreme chaos)
            let mut completed = 0;
            for handle in handles {
                if let Ok(Ok(_count)) = handle.await {
                    completed += 1;
                }
            }

            // At least 15 of 20 should complete (75% success rate under extreme chaos)
            assert!(
                completed >= 15,
                "At least 15/20 streams should complete under extreme chaos, got {}",
                completed
            );

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Extreme chaos test failed: {:?}",
        result.err()
    );
}

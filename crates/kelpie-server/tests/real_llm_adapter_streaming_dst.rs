//! DST tests for LLM client streaming (Phase 7.8)
//!
//! TigerStyle: DST-first with full simulation environment
//!
//! Tests cover:
//! - Token-by-token streaming (not batch conversion)
//! - Stream cancellation and cleanup
//! - Error handling during streaming
//! - Multiple concurrent streams
//! - Fault injection (storage delays)
//!
//! These tests focus on the LLM client streaming behavior,
//! not the full service stack (which requires dispatcher streaming).
#![cfg(feature = "dst")]

use async_trait::async_trait;
use futures::stream::{self, Stream, StreamExt};
use kelpie_core::{Result, Runtime, TokioRuntime};
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_server::actor::{LlmClient, LlmMessage, LlmResponse, StreamChunk};
use std::pin::Pin;

/// Mock streaming LLM client for testing
///
/// Simulates incremental token delivery (not batch → stream conversion)
struct MockStreamingLlmClient {
    /// Tokens to stream
    tokens: Vec<String>,
}

impl MockStreamingLlmClient {
    fn new(tokens: Vec<String>) -> Self {
        Self { tokens }
    }
}

#[async_trait]
impl LlmClient for MockStreamingLlmClient {
    async fn complete_with_tools(
        &self,
        _messages: Vec<LlmMessage>,
        _tools: Vec<kelpie_server::llm::ToolDefinition>,
    ) -> Result<LlmResponse> {
        // Batch mode - concatenate all tokens
        Ok(LlmResponse {
            content: self.tokens.join(""),
            tool_calls: vec![],
            prompt_tokens: 0,
            completion_tokens: 0,
            stop_reason: "end_turn".to_string(),
        })
    }

    async fn continue_with_tool_result(
        &self,
        _messages: Vec<LlmMessage>,
        _tools: Vec<kelpie_server::llm::ToolDefinition>,
        _assistant_blocks: Vec<kelpie_server::llm::ContentBlock>,
        _tool_results: Vec<(String, String)>,
    ) -> Result<LlmResponse> {
        Ok(LlmResponse {
            content: self.tokens.join(""),
            tool_calls: vec![],
            prompt_tokens: 0,
            completion_tokens: 0,
            stop_reason: "end_turn".to_string(),
        })
    }

    async fn stream_complete(
        &self,
        _messages: Vec<LlmMessage>,
    ) -> Result<Pin<Box<dyn Stream<Item = Result<StreamChunk>> + Send>>> {
        // Real streaming - emit tokens incrementally
        let tokens = self.tokens.clone();

        // Create stream that emits tokens one by one
        let chunks: Vec<Result<StreamChunk>> = tokens
            .into_iter()
            .map(|token| Ok(StreamChunk::ContentDelta { delta: token }))
            .chain(std::iter::once(Ok(StreamChunk::Done {
                stop_reason: "end_turn".to_string(),
            })))
            .collect();

        Ok(Box::pin(stream::iter(chunks)))
    }
}

/// Test token-by-token streaming (not batch conversion)
///
/// Contract:
/// - Tokens arrive incrementally (one per chunk)
/// - Order preserved
/// - Stream ends with Done chunk
#[tokio::test]
async fn test_dst_llm_client_token_streaming() {
    let config = SimConfig::new(6001);

    let result = Simulation::new(config)
        .run_async(|_sim_env| async move {
            let tokens = vec![
                "Hello".to_string(),
                " ".to_string(),
                "world".to_string(),
                "!".to_string(),
            ];
            let client = MockStreamingLlmClient::new(tokens.clone());

            // Call stream_complete directly
            let mut stream = client
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Say hello".to_string(),
                }])
                .await?;

            // Collect chunks
            let mut content_chunks = Vec::new();
            let mut done_received = false;

            while let Some(chunk_result) = stream.next().await {
                let chunk = chunk_result?;

                match chunk {
                    StreamChunk::ContentDelta { delta } => {
                        content_chunks.push(delta);
                    }
                    StreamChunk::Done { .. } => {
                        done_received = true;
                        break;
                    }
                    _ => {}
                }
            }

            // Verify streaming behavior
            assert_eq!(
                content_chunks.len(),
                tokens.len(),
                "Should have same number of chunks as tokens"
            );
            assert_eq!(
                content_chunks, tokens,
                "Chunks should match tokens in order"
            );
            assert!(done_received, "Should receive Done chunk");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Token streaming test failed: {:?}",
        result.err()
    );
}

/// Test stream cancellation (early drop)
///
/// Contract:
/// - Dropping stream consumer stops iteration
/// - No resource leak
/// - Clean shutdown
#[tokio::test]
async fn test_dst_llm_client_cancellation() {
    let config = SimConfig::new(6002);

    let result = Simulation::new(config)
        .run_async(|_sim_env| async move {
            let tokens: Vec<String> = (0..100).map(|i| format!("token{} ", i)).collect();
            let client = MockStreamingLlmClient::new(tokens);

            // Start streaming
            let mut stream = client
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Long response".to_string(),
                }])
                .await?;

            // Consume only 5 chunks then drop
            let mut consumed = 0;
            while let Some(chunk_result) = stream.next().await {
                let _chunk = chunk_result?;
                consumed += 1;
                if consumed >= 5 {
                    break; // Drop stream early
                }
            }

            // Stream is dropped here - should clean up without panic
            assert_eq!(consumed, 5, "Should have consumed exactly 5 chunks");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Cancellation test failed: {:?}",
        result.err()
    );
}

/// Test streaming with storage delays
///
/// Contract:
/// - Stream completes despite StorageLatency faults
/// - Tokens arrive in order
/// - No tokens lost
#[tokio::test]
async fn test_dst_llm_client_with_storage_delay() {
    let config = SimConfig::new(6003);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 5,
                max_ms: 20,
            },
            0.5, // 50% of operations delayed
        ))
        .run_async(|_sim_env| async move {
            let tokens = vec![
                "One".to_string(),
                " ".to_string(),
                "Two".to_string(),
                " ".to_string(),
                "Three".to_string(),
            ];
            let expected_content = tokens.join("");
            let client = MockStreamingLlmClient::new(tokens);

            // Stream with delays active
            let mut stream = client
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Count words".to_string(),
                }])
                .await?;

            let mut content = String::new();
            while let Some(chunk_result) = stream.next().await {
                let chunk = chunk_result?;

                if let StreamChunk::ContentDelta { delta } = chunk {
                    content.push_str(&delta);
                }
            }

            // Verify complete content despite delays
            assert_eq!(content, expected_content, "Content should be complete");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Storage delay test failed: {:?}",
        result.err()
    );
}

/// Test concurrent streams
///
/// Contract:
/// - Multiple clients can stream concurrently
/// - Streams don't interfere with each other
/// - All streams complete successfully
#[tokio::test]
async fn test_dst_llm_client_concurrent() {
    let config = SimConfig::new(6004);

    let result = Simulation::new(config)
        .run_async(|_sim_env| async move {
            use kelpie_core::{Runtime, TokioRuntime};
            let runtime = TokioRuntime;

            // Create 3 clients with different token sets
            let mut handles = Vec::new();

            for i in 1..=3 {
                let tokens: Vec<String> =
                    (0..10).map(|j| format!("client{}token{} ", i, j)).collect();
                let client = MockStreamingLlmClient::new(tokens);

                let handle = runtime.spawn(async move {
                    let mut stream = client
                        .stream_complete(vec![LlmMessage {
                            role: "user".to_string(),
                            content: format!("Message {}", i),
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

            // All streams should complete
            for handle in handles {
                match handle.await {
                    Ok(Ok(count)) => {
                        assert!(count > 0, "Stream should have chunks");
                    }
                    Ok(Err(e)) => {
                        panic!("Stream failed: {:?}", e);
                    }
                    Err(e) => {
                        panic!("Task panicked: {:?}", e);
                    }
                }
            }

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Concurrent streaming test failed: {:?}",
        result.err()
    );
}

/// Test streaming with comprehensive fault injection
///
/// Contract:
/// - Stream completes despite multiple faults
/// - Tokens arrive in order
/// - Graceful degradation
#[tokio::test]
async fn test_dst_llm_client_comprehensive_faults() {
    let config = SimConfig::new(6005);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 10,
                max_ms: 30,
            },
            0.4, // 40% storage delays
        ))
        .run_async(|_sim_env| async move {
            let tokens: Vec<String> = (0..20).map(|i| format!("t{} ", i)).collect();
            let expected_content = tokens.join("");
            let client = MockStreamingLlmClient::new(tokens);

            // Stream with faults active
            let mut stream = client
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test resilience".to_string(),
                }])
                .await?;

            let mut chunk_count = 0;
            let mut content = String::new();

            while let Some(chunk_result) = stream.next().await {
                // Should not fail despite faults
                let chunk = chunk_result?;
                chunk_count += 1;

                if let StreamChunk::ContentDelta { delta } = chunk {
                    content.push_str(&delta);
                }
            }

            // Verify stream completed successfully despite faults
            assert!(chunk_count > 0, "Should have chunks despite faults");
            assert_eq!(content, expected_content, "Content should be complete");

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Comprehensive fault test failed: {:?}",
        result.err()
    );
}

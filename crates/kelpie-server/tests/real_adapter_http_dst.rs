//! TRUE DST tests for RealLlmAdapter with HTTP mocking (Phase 7.8 REDO)
//!
//! TigerStyle: DST-first with HTTP mocking and fault injection
//!
//! These tests use mockito to simulate Anthropic's SSE API.
//! Tests WILL FAIL until RealLlmAdapter.stream_complete() is implemented.

use futures::stream::StreamExt;
use kelpie_core::Result;
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_server::actor::{LlmClient, LlmMessage, RealLlmAdapter, StreamChunk};
use kelpie_server::llm::{LlmClient as RealLlmClient, LlmConfig};
use mockito::{Server, ServerGuard};

/// Build mock Anthropic SSE response
///
/// Simulates incremental token delivery via Server-Sent Events.
fn mock_anthropic_sse_response() -> String {
    // Anthropic SSE format with incremental tokens
    let events = vec![
        "event: message_start\n",
        "data: {\"type\":\"message_start\",\"message\":{\"id\":\"msg_test\",\"type\":\"message\",\"role\":\"assistant\",\"content\":[],\"model\":\"claude-test\"}}\n",
        "\n",
        "event: content_block_start\n",
        "data: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\n",
        "\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"Hello\"}}\n",
        "\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\" \"}}\n",
        "\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"world\"}}\n",
        "\n",
        "event: content_block_delta\n",
        "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"!\"}}\n",
        "\n",
        "event: content_block_stop\n",
        "data: {\"type\":\"content_block_stop\",\"index\":0}\n",
        "\n",
        "event: message_stop\n",
        "data: {\"type\":\"message_stop\"}\n",
        "\n",
    ];

    events.join("")
}

/// Test that RealLlmAdapter.stream_complete() produces incremental chunks
///
/// Contract:
/// - RealLlmAdapter calls llm.stream_complete_with_tools()
/// - Tokens arrive incrementally (4 separate ContentDelta chunks)
/// - Stream ends with Done chunk
/// - Total: 5 chunks (4 content + 1 done)
///
/// THIS TEST WILL FAIL until RealLlmAdapter overrides stream_complete().
/// Without override, it uses default (batch → stream) which produces only 2 chunks.
#[tokio::test]
async fn test_dst_real_adapter_uses_real_streaming() {
    let config = SimConfig::new(8001);

    let result = Simulation::new(config)
        .run_async(|_sim_env| async move {
            // Start mock HTTP server
            let mut server = Server::new_async().await;

            // Configure mock to return SSE stream
            let mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .match_header("x-api-key", "test-key")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_anthropic_sse_response())
                .create_async()
                .await;

            // Create LlmClient pointing to mock server
            // Add "anthropic.com" to path so is_anthropic() returns true
            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let llm_client = RealLlmClient::new(llm_config);

            // Create RealLlmAdapter
            let adapter = RealLlmAdapter::new(llm_client);

            // Call stream_complete
            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Say hello".to_string(),
                }])
                .await?;

            // Collect all chunks
            let mut chunks = Vec::new();
            while let Some(chunk_result) = stream.next().await {
                let chunk = chunk_result?;
                chunks.push(chunk);
            }

            // Verify incremental streaming (NOT batch)
            // Expected: 4 ContentDelta + 1 Done = 5 chunks
            // With default impl: 1 ContentDelta + 1 Done = 2 chunks
            assert!(
                chunks.len() >= 5,
                "Expected 5+ chunks (real streaming), got {} (batch mode?)",
                chunks.len()
            );

            // Verify content chunks
            let content_chunks: Vec<_> = chunks
                .iter()
                .filter_map(|c| match c {
                    StreamChunk::ContentDelta { delta } => Some(delta.clone()),
                    _ => None,
                })
                .collect();

            assert_eq!(
                content_chunks.len(),
                4,
                "Should have 4 content chunks (tokens)"
            );

            // Verify content matches expected tokens
            assert_eq!(content_chunks[0], "Hello");
            assert_eq!(content_chunks[1], " ");
            assert_eq!(content_chunks[2], "world");
            assert_eq!(content_chunks[3], "!");

            // Verify Done chunk
            let last_chunk = chunks.last().unwrap();
            match last_chunk {
                StreamChunk::Done { stop_reason } => {
                    assert_eq!(stop_reason, "end_turn");
                }
                _ => panic!("Last chunk should be Done"),
            }

            // Verify mock was called
            mock.assert_async().await;

            Ok(())
        })
        .await;

    assert!(
        result.is_ok(),
        "Real streaming test failed: {:?}",
        result.err()
    );
}

/// Test RealLlmAdapter streaming with storage faults
///
/// Contract:
/// - Stream completes despite StorageLatency faults (50%)
/// - All tokens arrive (no data loss)
/// - Incremental delivery still works
#[tokio::test]
async fn test_dst_real_adapter_streaming_with_faults() {
    let config = SimConfig::new(8002);

    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(
            FaultType::StorageLatency {
                min_ms: 10,
                max_ms: 50,
            },
            0.5, // 50% of operations delayed
        ))
        .run_async(|_sim_env| async move {
            // Start mock HTTP server
            let mut server = Server::new_async().await;

            // Configure mock
            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(200)
                .with_header("content-type", "text/event-stream")
                .with_body(mock_anthropic_sse_response())
                .create_async()
                .await;

            // Create adapter
            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            // Stream with faults active
            let mut stream = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test".to_string(),
                }])
                .await?;

            // Collect chunks
            let mut content = String::new();
            let mut chunk_count = 0;

            while let Some(chunk_result) = stream.next().await {
                let chunk = chunk_result?;
                chunk_count += 1;

                if let StreamChunk::ContentDelta { delta } = chunk {
                    content.push_str(&delta);
                }
            }

            // Verify completion despite faults
            assert!(chunk_count >= 5, "Should have all chunks despite faults");
            assert_eq!(content, "Hello world!", "Content should be complete");

            Ok(())
        })
        .await;

    assert!(result.is_ok(), "Fault tolerance test failed: {:?}", result.err());
}

/// Test RealLlmAdapter error handling
///
/// Contract:
/// - HTTP errors are wrapped correctly
/// - Error messages are preserved
/// - Stream terminates on error
#[tokio::test]
async fn test_dst_real_adapter_error_handling() {
    let config = SimConfig::new(8003);

    let result = Simulation::new(config)
        .run_async(|_sim_env| async move {
            // Start mock HTTP server
            let mut server = Server::new_async().await;

            // Configure mock to return error
            let _mock = server
                .mock("POST", "/test.anthropic.com/messages")
                .with_status(429)
                .with_header("content-type", "application/json")
                .with_body(r#"{"error":{"type":"rate_limit_error","message":"Rate limit exceeded"}}"#)
                .create_async()
                .await;

            // Create adapter
            let llm_config = LlmConfig {
                base_url: format!("{}/test.anthropic.com", server.url()),
                api_key: "test-key".to_string(),
                model: "claude-test".to_string(),
                max_tokens: 100,
            };
            let adapter = RealLlmAdapter::new(RealLlmClient::new(llm_config));

            // Call stream_complete (should error)
            let stream_result = adapter
                .stream_complete(vec![LlmMessage {
                    role: "user".to_string(),
                    content: "Test".to_string(),
                }])
                .await;

            // Verify error is returned
            assert!(stream_result.is_err(), "Should return error for HTTP 429");

            let error = stream_result.err().unwrap();
            match error {
                kelpie_core::Error::Internal { message } => {
                    assert!(
                        message.contains("LLM streaming failed") || message.contains("API error"),
                        "Error should mention LLM failure or API error, got: {}",
                        message
                    );
                }
                _ => panic!("Should be Internal error"),
            }

            Ok(())
        })
        .await;

    assert!(result.is_ok());
}

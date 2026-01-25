//! DST tests for production WAL code under simulated time
//!
//! This is a REFERENCE IMPLEMENTATION for Phase 1 of True DST Simulation Architecture.
//! It demonstrates the pattern of using production kelpie-storage code with simulated time.
//!
//! Key Pattern:
//! - Use production `MemoryWal` from kelpie-storage (not a mock)
//! - Inject `SimClock` from kelpie-dst as the TimeProvider
//! - Tests run deterministically under simulated time
//! - Same code runs in production with `WallClockTime`
//!
//! TigerStyle: DST-first testing with explicit time control, 2+ assertions per test.

use bytes::Bytes;
use kelpie_core::ActorId;
use kelpie_dst::SimClock;
use kelpie_storage::{MemoryWal, WalOperation, WalStatus, WriteAheadLog};
use std::sync::Arc;

// =============================================================================
// Reference DST Tests: Production WAL + Simulated Time
// =============================================================================

/// Test basic WAL append with simulated time.
///
/// Demonstrates:
/// - Production MemoryWal code running under SimClock
/// - Timestamps are controlled by the simulated clock
/// - Deterministic behavior (same seed = same result)
#[madsim::test]
async fn test_wal_append_with_sim_time() {
    // Create SimClock at a known starting time
    let clock = Arc::new(SimClock::from_millis(1000));

    // Create production MemoryWal with injected SimClock
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "wal-1").unwrap();

    // Append an entry
    let entry_id = wal
        .append(
            WalOperation::CreateAgent,
            &actor_id,
            Bytes::from("test-data"),
        )
        .await
        .unwrap();

    // Verify entry was created with SimClock timestamp
    let entry = wal
        .get(entry_id)
        .await
        .unwrap()
        .expect("entry should exist");

    // Precondition: entry timestamp should match SimClock's time
    assert_eq!(
        entry.created_at_ms, 1000,
        "timestamp should be from SimClock"
    );
    assert_eq!(entry.status, WalStatus::Pending);
    assert_eq!(entry.actor_id, actor_id.to_string());
    assert!(matches!(entry.operation, WalOperation::CreateAgent));

    // Postcondition: entry should exist in WAL
    assert!(
        wal.get(entry_id).await.unwrap().is_some(),
        "entry should be retrievable"
    );
}

/// Test WAL entries created at different simulated times.
///
/// Demonstrates:
/// - Advancing SimClock affects timestamps in production WAL code
/// - Time ordering is preserved
#[madsim::test]
async fn test_wal_time_ordering_with_sim_time() {
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "wal-2").unwrap();

    // Append first entry at t=0
    let entry1_id = wal
        .append(WalOperation::CreateAgent, &actor_id, Bytes::from("first"))
        .await
        .unwrap();

    // Advance simulated time by 100ms
    clock.advance_ms(100);

    // Append second entry at t=100
    let entry2_id = wal
        .append(WalOperation::UpdateAgent, &actor_id, Bytes::from("second"))
        .await
        .unwrap();

    // Advance simulated time by 50ms
    clock.advance_ms(50);

    // Append third entry at t=150
    let entry3_id = wal
        .append(WalOperation::DeleteAgent, &actor_id, Bytes::from("third"))
        .await
        .unwrap();

    // Verify timestamps reflect simulated time progression
    let entry1 = wal.get(entry1_id).await.unwrap().unwrap();
    let entry2 = wal.get(entry2_id).await.unwrap().unwrap();
    let entry3 = wal.get(entry3_id).await.unwrap().unwrap();

    // Preconditions: timestamps should match SimClock times
    assert_eq!(entry1.created_at_ms, 0, "first entry at t=0");
    assert_eq!(entry2.created_at_ms, 100, "second entry at t=100");
    assert_eq!(entry3.created_at_ms, 150, "third entry at t=150");

    // Postcondition: time ordering preserved
    assert!(
        entry1.created_at_ms < entry2.created_at_ms,
        "entry1 should be before entry2"
    );
    assert!(
        entry2.created_at_ms < entry3.created_at_ms,
        "entry2 should be before entry3"
    );
}

/// Test WAL pending entries retrieval with simulated time.
///
/// Demonstrates:
/// - Production WAL pending_entries works under simulated time
/// - Entries are sorted by ID (oldest first)
#[madsim::test]
async fn test_wal_pending_entries_with_sim_time() {
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "wal-3").unwrap();

    // Create entries at different times
    let entry1_id = wal
        .append(WalOperation::CreateAgent, &actor_id, Bytes::from("old"))
        .await
        .unwrap();

    clock.advance_ms(100);

    let entry2_id = wal
        .append(WalOperation::UpdateAgent, &actor_id, Bytes::from("mid"))
        .await
        .unwrap();

    clock.advance_ms(100);

    let entry3_id = wal
        .append(WalOperation::SendMessage, &actor_id, Bytes::from("new"))
        .await
        .unwrap();

    // Get all pending entries
    let pending = wal.pending_entries().await.unwrap();

    // Preconditions
    assert_eq!(pending.len(), 3, "should find 3 pending entries");

    // Verify entries are sorted by ID (oldest first)
    assert_eq!(pending[0].id, entry1_id, "first entry should be oldest");
    assert_eq!(pending[1].id, entry2_id, "second entry");
    assert_eq!(pending[2].id, entry3_id, "third entry should be newest");

    // Postcondition: all returned entries are pending
    for entry in &pending {
        assert!(
            matches!(entry.status, WalStatus::Pending),
            "all entries should be pending"
        );
    }
}

/// Test WAL complete/fail lifecycle with simulated time.
///
/// Demonstrates:
/// - Production WAL state transitions work correctly under DST
/// - SimClock doesn't affect state machine correctness
#[madsim::test]
async fn test_wal_lifecycle_with_sim_time() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "wal-4").unwrap();

    // Create entries
    let entry1_id = wal
        .append(
            WalOperation::CreateAgent,
            &actor_id,
            Bytes::from("to-complete"),
        )
        .await
        .unwrap();

    clock.advance_ms(10);

    let entry2_id = wal
        .append(WalOperation::UpdateAgent, &actor_id, Bytes::from("to-fail"))
        .await
        .unwrap();

    // Verify both start as Pending
    assert_eq!(
        wal.get(entry1_id).await.unwrap().unwrap().status,
        WalStatus::Pending
    );
    assert_eq!(
        wal.get(entry2_id).await.unwrap().unwrap().status,
        WalStatus::Pending
    );

    // Advance time and complete entry1
    clock.advance_ms(100);
    wal.complete(entry1_id).await.unwrap();
    assert_eq!(
        wal.get(entry1_id).await.unwrap().unwrap().status,
        WalStatus::Complete
    );

    // Advance time and fail entry2
    clock.advance_ms(50);
    wal.fail(entry2_id, "test failure").await.unwrap();
    let entry2 = wal.get(entry2_id).await.unwrap().unwrap();
    assert!(matches!(entry2.status, WalStatus::Failed { .. }));

    // Verify completed_at_ms timestamps
    let entry1_final = wal.get(entry1_id).await.unwrap().unwrap();
    let entry2_final = wal.get(entry2_id).await.unwrap().unwrap();

    // entry1: created at 1000, completed at 1110 (1000 + 10 + 100)
    assert_eq!(entry1_final.completed_at_ms, Some(1110));
    // entry2: created at 1010, failed at 1160 (1000 + 10 + 100 + 50)
    assert_eq!(entry2_final.completed_at_ms, Some(1160));

    // Postconditions: pending count should be 0
    assert_eq!(
        wal.pending_count().await.unwrap(),
        0,
        "no entries should be pending after completion/failure"
    );
}

/// Test deterministic reproducibility of WAL operations.
///
/// Demonstrates:
/// - Given the same SimClock starting time, WAL behavior is deterministic
/// - This is the foundation of DST: reproducible tests
#[madsim::test]
async fn test_wal_determinism() {
    // Run the same sequence twice with the same starting time
    let results_run1 = run_deterministic_sequence(1000).await;
    let results_run2 = run_deterministic_sequence(1000).await;

    // Precondition: sequences should be identical
    assert_eq!(
        results_run1.len(),
        results_run2.len(),
        "same number of entries"
    );

    for (i, (ts1, ts2)) in results_run1.iter().zip(results_run2.iter()).enumerate() {
        assert_eq!(ts1, ts2, "entry {} timestamps should match", i);
    }

    // Run with different starting time - results should differ
    let results_run3 = run_deterministic_sequence(5000).await;

    // Postcondition: different start time = different timestamps
    assert_ne!(
        results_run1[0], results_run3[0],
        "different starting time should produce different timestamps"
    );
}

/// Helper function for determinism test
async fn run_deterministic_sequence(start_ms: u64) -> Vec<u64> {
    let clock = Arc::new(SimClock::from_millis(start_ms));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "determinism").unwrap();

    let mut timestamps = Vec::new();

    // Fixed sequence of operations
    for i in 0..5 {
        let entry_id = wal
            .append(
                WalOperation::Custom(format!("op-{}", i)),
                &actor_id,
                Bytes::from(format!("entry-{}", i)),
            )
            .await
            .unwrap();

        let entry = wal.get(entry_id).await.unwrap().unwrap();
        timestamps.push(entry.created_at_ms);

        // Advance by fixed amount
        clock.advance_ms(10);
    }

    timestamps
}

/// Test concurrent WAL operations under simulated time.
///
/// Demonstrates:
/// - Production WAL handles concurrent operations correctly
/// - SimClock provides consistent time view across tasks
#[madsim::test]
async fn test_wal_concurrent_operations() {
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = Arc::new(MemoryWal::with_time_provider(clock.clone()));
    let actor_id = ActorId::new("dst-test", "concurrent").unwrap();

    // Spawn multiple concurrent append operations
    let mut handles = Vec::new();
    for i in 0..10 {
        let wal = wal.clone();
        let actor_id = actor_id.clone();
        let handle = madsim::task::spawn(async move {
            wal.append(
                WalOperation::SendMessage,
                &actor_id,
                Bytes::from(format!("data-{}", i)),
            )
            .await
            .unwrap()
        });
        handles.push(handle);
    }

    // Wait for all appends to complete
    let mut entry_ids = Vec::new();
    for handle in handles {
        entry_ids.push(handle.await.unwrap());
    }

    // Precondition: all entries were created
    assert_eq!(entry_ids.len(), 10, "all 10 entries should be created");

    // All entries should exist with valid timestamps
    for entry_id in &entry_ids {
        let entry = wal.get(*entry_id).await.unwrap();
        assert!(entry.is_some(), "entry {} should exist", entry_id);
        let entry = entry.unwrap();
        assert_eq!(
            entry.created_at_ms, 0,
            "all entries created at same simulated time"
        );
    }

    // Postcondition: unique entry IDs
    let unique_ids: std::collections::HashSet<_> = entry_ids.iter().collect();
    assert_eq!(unique_ids.len(), 10, "all entry IDs should be unique");
}

/// Test WAL cleanup with simulated time.
///
/// Demonstrates:
/// - Production WAL cleanup logic works under simulated time
/// - Time-based retention uses SimClock timestamps
#[madsim::test]
async fn test_wal_cleanup_with_sim_time() {
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "cleanup").unwrap();

    // Create and complete entries at different times
    let entry1_id = wal
        .append(WalOperation::CreateAgent, &actor_id, Bytes::from("old"))
        .await
        .unwrap();

    clock.advance_ms(100);
    wal.complete(entry1_id).await.unwrap();
    // entry1 completed at t=100

    clock.advance_ms(400);
    let entry2_id = wal
        .append(WalOperation::UpdateAgent, &actor_id, Bytes::from("mid"))
        .await
        .unwrap();

    clock.advance_ms(100);
    wal.complete(entry2_id).await.unwrap();
    // entry2 completed at t=600

    clock.advance_ms(400);
    let entry3_id = wal
        .append(WalOperation::SendMessage, &actor_id, Bytes::from("new"))
        .await
        .unwrap();
    // entry3 is still pending

    // Cleanup entries completed before t=500
    let removed = wal.cleanup(500).await.unwrap();

    // Preconditions
    assert_eq!(
        removed, 1,
        "should remove 1 entry (entry1 completed at 100)"
    );
    assert!(
        wal.get(entry1_id).await.unwrap().is_none(),
        "entry1 should be removed"
    );
    assert!(
        wal.get(entry2_id).await.unwrap().is_some(),
        "entry2 should remain (completed at 600)"
    );
    assert!(
        wal.get(entry3_id).await.unwrap().is_some(),
        "entry3 should remain (pending)"
    );

    // Postcondition: pending count unchanged (only entry3 was pending)
    assert_eq!(
        wal.pending_count().await.unwrap(),
        1,
        "entry3 still pending"
    );
}

/// Test idempotency with simulated time.
///
/// Demonstrates:
/// - Production WAL idempotency works under simulated time
/// - Duplicate requests don't create duplicate entries
#[madsim::test]
async fn test_wal_idempotency_with_sim_time() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor_id = ActorId::new("dst-test", "idempotency").unwrap();
    let idempotency_key = "msg-uuid-12345".to_string();

    // First append with idempotency key
    let (id1, is_new1) = wal
        .append_with_idempotency(
            WalOperation::SendMessage,
            &actor_id,
            Bytes::from("message payload"),
            idempotency_key.clone(),
        )
        .await
        .unwrap();

    assert!(is_new1, "First append should create new entry");
    let entry1 = wal.get(id1).await.unwrap().unwrap();
    assert_eq!(entry1.created_at_ms, 1000);

    // Advance time and try again with same key
    clock.advance_ms(500);
    let (id2, is_new2) = wal
        .append_with_idempotency(
            WalOperation::SendMessage,
            &actor_id,
            Bytes::from("different payload"),
            idempotency_key.clone(),
        )
        .await
        .unwrap();

    // Preconditions
    assert!(!is_new2, "Second append should return existing entry");
    assert_eq!(id2, id1, "Should return same entry ID");

    // Entry timestamp should be original (not updated)
    let entry2 = wal.get(id2).await.unwrap().unwrap();
    assert_eq!(
        entry2.created_at_ms, 1000,
        "Timestamp should be from first append"
    );

    // Postcondition: only one entry
    assert_eq!(wal.pending_count().await.unwrap(), 1);
}

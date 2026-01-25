//! Aggressive stress test to find real bugs in MemoryWal
//!
//! This tries edge cases that might expose latent bugs:
//! - Boundary timestamps (0, u64::MAX)
//! - Many concurrent operations at same timestamp
//! - Cleanup at exact completion time
//! - Rapid create/complete/cleanup cycles

use bytes::Bytes;
use kelpie_core::ActorId;
use kelpie_dst::SimClock;
use kelpie_storage::{MemoryWal, WalOperation, WriteAheadLog};
use std::sync::Arc;

#[madsim::test]
async fn stress_boundary_timestamps() {
    // Test with timestamp 0
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor = ActorId::new("stress", "1").unwrap();
    
    let id = wal.append(WalOperation::CreateAgent, &actor, Bytes::from("t0")).await.unwrap();
    let entry = wal.get(id).await.unwrap().unwrap();
    assert_eq!(entry.created_at_ms, 0, "timestamp 0 should work");
    
    // Test with very large timestamp
    clock.advance_ms(u64::MAX / 2);
    let id2 = wal.append(WalOperation::UpdateAgent, &actor, Bytes::from("big")).await.unwrap();
    let entry2 = wal.get(id2).await.unwrap().unwrap();
    assert!(entry2.created_at_ms > 0, "large timestamp should work");
}

#[madsim::test]
async fn stress_cleanup_at_exact_boundary() {
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor = ActorId::new("stress", "2").unwrap();
    
    // Create entry at t=0
    let id = wal.append(WalOperation::CreateAgent, &actor, Bytes::from("data")).await.unwrap();
    
    // Complete at exactly t=100
    clock.advance_ms(100);
    wal.complete(id).await.unwrap();
    
    // Cleanup with threshold = 100 (exact boundary)
    // Should this remove entries completed at exactly 100? 
    // The implementation uses `t < older_than_ms`, so 100 < 100 = false
    // Entry should NOT be removed
    let removed = wal.cleanup(100).await.unwrap();
    assert_eq!(removed, 0, "entry at exact boundary should NOT be removed (< not <=)");
    
    // Cleanup with threshold = 101 should remove it
    let removed2 = wal.cleanup(101).await.unwrap();
    assert_eq!(removed2, 1, "entry should be removed when threshold > completion time");
}

#[madsim::test]
async fn stress_many_same_timestamp() {
    let clock = Arc::new(SimClock::from_millis(1000));
    let wal = Arc::new(MemoryWal::with_time_provider(clock.clone()));
    let actor = ActorId::new("stress", "3").unwrap();
    
    // Create 100 entries at exactly the same timestamp
    let mut handles = Vec::new();
    for i in 0..100 {
        let wal = wal.clone();
        let actor = actor.clone();
        handles.push(madsim::task::spawn(async move {
            wal.append(
                WalOperation::SendMessage,
                &actor,
                Bytes::from(format!("msg-{}", i)),
            ).await.unwrap()
        }));
    }
    
    let mut ids = Vec::new();
    for h in handles {
        ids.push(h.await.unwrap());
    }
    
    // All should have same timestamp
    for id in &ids {
        let entry = wal.get(*id).await.unwrap().unwrap();
        assert_eq!(entry.created_at_ms, 1000);
    }
    
    // All IDs should be unique
    let unique: std::collections::HashSet<_> = ids.iter().collect();
    assert_eq!(unique.len(), 100, "all 100 entries should have unique IDs");
}

#[madsim::test] 
async fn stress_rapid_lifecycle() {
    let clock = Arc::new(SimClock::from_millis(0));
    let wal = MemoryWal::with_time_provider(clock.clone());
    let actor = ActorId::new("stress", "4").unwrap();
    
    // Rapid create -> complete -> cleanup cycles
    for i in 0..50 {
        let id = wal.append(
            WalOperation::Custom(format!("cycle-{}", i)),
            &actor,
            Bytes::from("data"),
        ).await.unwrap();
        
        clock.advance_ms(1);
        wal.complete(id).await.unwrap();
        
        clock.advance_ms(1);
        let removed = wal.cleanup(clock.now_ms()).await.unwrap();
        
        // Each cycle should clean up the previous entry
        if i > 0 {
            assert!(removed >= 1, "cycle {} should cleanup at least 1 entry", i);
        }
    }
    
    // Final state: 1 entry (from last cycle, just completed)
    assert_eq!(wal.pending_count().await.unwrap(), 0);
}

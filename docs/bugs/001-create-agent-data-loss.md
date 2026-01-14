# BUG-001: create_agent Data Loss on Deactivation Crash

**Status:** FOUND via aggressive fault injection
**Severity:** HIGH - Data loss, user-visible inconsistency
**Found By:** test_deactivate_during_create_crash with 50% CrashDuringTransaction rate
**Date:** 2026-01-14

## Summary

`AgentService.create_agent()` can return success (with agent ID) but the agent is not actually persisted if a crash occurs during actor deactivation between the `invoke("create")` and `get_agent()` calls.

## Reproduction

```rust
// Run with high crash rate during transaction commit
let config = SimConfig::new(3001);
Simulation::new(config)
    .with_fault(FaultConfig::new(FaultType::CrashDuringTransaction, 0.5))
    .run_async(|sim_env| async move {
        let service = create_service(&sim_env)?;

        // This succeeds
        let agent = service.create_agent(request).await?;

        // But this fails with "agent not found"
        let retrieved = service.get_agent(&agent.id).await?; // FAILS
    })
```

**Reproduction Rate:** ~5-10% with 50% CrashDuringTransaction fault

## Root Cause

**Code:** `crates/kelpie-server/src/service/mod.rs:40-56`

```rust
pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState> {
    let actor_id = ActorId::new("agents", uuid::Uuid::new_v4().to_string())?;
    let payload = serde_json::to_vec(&request)?;

    // Step 1: Invoke succeeds - actor has state IN MEMORY
    self.dispatcher
        .invoke(actor_id.clone(), "create".to_string(), Bytes::from(payload))
        .await?;

    // Step 2: Actor deactivates (memory pressure, idle timeout, etc.)
    //         on_deactivate() → kv_set() → CRASH DURING WRITE

    // Step 3: get_agent tries to read from storage
    //         Storage has no data or partial data → FAILS
    self.get_agent(actor_id.id()).await // ← This is where it fails
}
```

**Timing Window:**

```
Time →
──────────────────────────────────────────────────────────────────────
invoke("create") → Actor.on_deactivate() → kv_set(state) → get_agent()
      ✓                                        💥 CRASH       ✗ FAIL
```

If crash happens during `kv_set()` in `on_deactivate()`, the state is not persisted, but `invoke()` has already succeeded.

## Impact

**User Perspective:**
1. POST /v1/agents returns 200 OK with agent ID
2. GET /v1/agents/{id} immediately returns 404 Not Found
3. User thinks agent exists, but it doesn't

**Data Loss:**
- Agent creation request is lost
- User has an agent ID that points to nothing
- No indication that creation actually failed

**Consistency Violation:**
- Create operation reports success
- Resource doesn't exist
- Violates atomicity guarantee

## Fix Options

### Option 1: Return State Directly from Create (RECOMMENDED)

Don't call `get_agent()` after create. Return the state directly from the actor:

```rust
pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState> {
    let actor_id = ActorId::new("agents", uuid::Uuid::new_v4().to_string())?;
    let payload = serde_json::to_vec(&request)?;

    // Invoke create and get response
    let response = self.dispatcher
        .invoke(actor_id.clone(), "create".to_string(), Bytes::from(payload))
        .await?;

    // Deserialize AgentState from response
    serde_json::from_slice(&response).map_err(|e| Error::Internal {
        message: format!("Failed to deserialize AgentState: {}", e),
    })
}
```

**Change AgentActor.handle_create to return AgentState:**

```rust
async fn handle_create(
    &self,
    ctx: &mut ActorContext<AgentActorState>,
    request: CreateAgentRequest,
) -> Result<AgentState> {  // ← Return AgentState instead of ()
    assert!(ctx.state.agent.is_none(), "Agent already created");
    let mut agent_state = AgentState::from_request(request);
    agent_state.id = ctx.id.id().to_string();
    ctx.state.agent = Some(agent_state.clone());
    Ok(agent_state)  // ← Return the created state
}
```

**Pros:**
- Eliminates the timing window
- No extra round-trip to storage
- Simpler, more efficient

**Cons:**
- Still vulnerable if crash happens during on_deactivate after returning
- User gets agent state, but it might not be persisted

**Verdict:** Better, but not perfect. Still has a window where in-memory state differs from persisted state.

### Option 2: Force Synchronous Persistence

Add a "commit" operation that forces immediate persistence:

```rust
pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState> {
    let actor_id = ActorId::new("agents", uuid::Uuid::new_v4().to_string())?;

    // Create agent
    let payload = serde_json::to_vec(&request)?;
    let response = self.dispatcher
        .invoke(actor_id.clone(), "create".to_string(), Bytes::from(payload))
        .await?;

    // Force immediate persistence
    self.dispatcher.invoke(actor_id.clone(), "commit".to_string(), Bytes::new()).await?;

    // Now safe to return
    serde_json::from_slice(&response).map_err(...)
}
```

**Pros:**
- Guarantees persistence before returning
- Create is truly atomic

**Cons:**
- Requires new "commit" operation in AgentActor
- Extra round-trip
- Performance impact (sync I/O)

### Option 3: Retry get_agent on Failure

If get_agent fails, retry a few times before giving up:

```rust
pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState> {
    let actor_id = ActorId::new("agents", uuid::Uuid::new_v4().to_string())?;
    let payload = serde_json::to_vec(&request)?;

    self.dispatcher.invoke(actor_id.clone(), "create".to_string(), Bytes::from(payload)).await?;

    // Retry get_agent up to 3 times with backoff
    for i in 0..3 {
        match self.get_agent(actor_id.id()).await {
            Ok(agent) => return Ok(agent),
            Err(e) if i < 2 => {
                tokio::time::sleep(Duration::from_millis(10 * (i + 1))).await;
                continue;
            }
            Err(e) => return Err(e),
        }
    }

    unreachable!()
}
```

**Pros:**
- Handles transient failures
- No actor changes needed

**Cons:**
- Hides the real problem
- Still fails if persistence truly fails
- Adds latency

### Option 4: Two-Phase Create (BEST for Correctness)

Split create into prepare + commit phases:

```rust
// Phase 1: Reserve ID and prepare (in-memory only)
let actor_id = ActorId::new("agents", uuid::Uuid::new_v4().to_string())?;
self.dispatcher.invoke(actor_id, "prepare_create", payload).await?;

// Phase 2: Commit (force persistence + verification)
self.dispatcher.invoke(actor_id, "commit_create", Bytes::new()).await?;

// Phase 3: Return committed state
self.get_agent(actor_id.id()).await
```

**Pros:**
- True atomicity
- Can rollback on failure
- Consistent with database 2PC

**Cons:**
- Complex - requires 3 round-trips
- Significant refactoring
- Overkill for this use case?

## Recommendation

**Immediate Fix:** Option 1 (Return state directly from create)
- Eliminates the obvious bug
- Simple change, no extra round-trips
- Still vulnerable to deactivation crash, but smaller window

**Long-term Fix:** Option 2 (Force synchronous persistence)
- Add `commit` operation that forces on_deactivate
- Only use for create/update/delete operations
- Provide `create_async` variant for bulk operations

## Testing

Added test that catches this bug:

```bash
$ cargo test -p kelpie-server --test agent_deactivation_timing
test test_deactivate_during_create_crash ... FAILED
Found 1 consistency violations during deactivation crashes
```

**Before Fix:**
- Bug reproduction rate: ~5-10% with 50% crash rate

**After Fix:**
- Should be 0% with Option 1 or Option 2

## Related Issues

- Similar bug likely affects `update_agent()` and `delete_agent()`
- Any multi-step operation with deactivation window has this risk
- Need to audit all service methods for this pattern

## References

- Test: `crates/kelpie-server/tests/agent_deactivation_timing.rs`
- Code: `crates/kelpie-server/src/service/mod.rs:40-56`
- Actor: `crates/kelpie-server/src/actor/agent_actor.rs:33-52`

# Registry Actor Refactoring - Option 1 (Long-term Solution)

**Date**: 2026-01-21
**Status**: IN PROGRESS
**Plan Sequence**: 028

## Summary

Refactor the agent registry from a storage abstraction to a proper Actor, enabling message-based agent registration and solving the architectural limitation where actors cannot write to other namespaces.

## Context

**Current State**:
- Registry is managed through `AgentStorage` trait (storage abstraction)
- AgentActor cannot self-register due to ActorContext scoping
- Option 2 (TeleportService fix) is implemented but requires service layer to handle registration
- Three registration paths exist with inconsistent patterns

**Problem**:
- Violates actor model principles (direct storage access instead of messages)
- Cannot register from within actors (encapsulation violation required)
- Registry operations not traceable as actor invocations
- No clean way for actors to discover other actors

## Goals

1. **Create RegistryActor**: Proper actor that manages agent metadata
2. **Message-based API**: Register/unregister/list via actor invocations
3. **Self-registration**: AgentActor can register itself during activation
4. **Backward compatibility**: Keep AgentStorage trait during migration
5. **DST coverage**: Registry operations work under fault injection

## Non-Goals

- Removing AgentStorage trait (keep for backward compatibility)
- Distributed registry across multiple nodes (single-node for now)
- Advanced discovery features (health checks, etc.) - future work

## Options & Decisions

### Option A: Registry as Regular Actor
**Pros**:
- Simple implementation
- Uses existing actor runtime
- Natural message passing

**Cons**:
- Single point of failure
- Activation/deactivation overhead
- Storage scoped to "system/agent_registry"

### Option B: Registry as Special System Actor
**Pros**:
- Always active (never deactivated)
- Direct storage access (unscoped)
- Can bypass activation overhead

**Cons**:
- More complex implementation
- Special-case code in runtime
- Harder to test in DST

### Option C: Hybrid - Actor Interface + Storage Backend
**Pros**:
- Best of both worlds
- Actor API for message passing
- Storage backend for bulk operations
- Backward compatible

**Cons**:
- Two code paths to maintain
- Slight complexity increase

**DECISION: Option C - Hybrid Approach**
- RegistryActor provides message-based API
- Uses AgentStorage internally for actual persistence
- Allows gradual migration from direct storage to actor messages
- Maintains backward compatibility

**Trade-offs Accepted**:
- Temporary duplication (actor + storage trait) during migration
- Slight performance overhead for message passing vs direct storage

## Quick Decision Log

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 2026-01-21 14:00 | Use hybrid approach (Option C) | Allows gradual migration, maintains compatibility | Temporary code duplication |
| 2026-01-21 14:05 | Actor ID: "system/agent_registry" | Follows system namespace convention | Single registry per system |
| 2026-01-21 14:10 | Use AgentStorage internally | Reuse existing storage logic | Actor is a wrapper initially |

## Implementation Phases

### Phase 1: Create RegistryActor (Core Implementation)
**Goal**: Basic actor with register/unregister/list/get operations

**Tasks**:
1. Create `crates/kelpie-server/src/actor/registry_actor.rs`
2. Define RegistryActorState (cache + storage reference)
3. Implement Actor trait for RegistryActor
4. Add operations:
   - `register` - Register agent metadata
   - `unregister` - Remove agent from registry
   - `list` - List all agents (with optional filters)
   - `get` - Get specific agent metadata
5. Add unit tests

**Acceptance Criteria**:
- RegistryActor compiles and passes tests
- Can register/unregister/list agents via invoke()
- State persists via on_deactivate()

### Phase 2: Integration - Self-Registration
**Goal**: AgentActor can register itself during activation

**Tasks**:
1. Add DispatcherHandle to AgentActor (for sending messages)
2. Update AgentActor::on_activate() to send register message
3. Update AgentActor::on_deactivate() to send unregister message (optional)
4. Add integration test

**Acceptance Criteria**:
- AgentActor successfully registers on activation
- Registered agents appear in registry list
- No direct storage access from AgentActor

### Phase 3: Migrate TeleportService
**Goal**: Use RegistryActor instead of direct storage access

**Tasks**:
1. Add DispatcherHandle to TeleportService
2. Replace `agent_storage.save_agent()` with dispatcher.invoke(registry)
3. Update tests
4. Verify teleported agents appear in registry

**Acceptance Criteria**:
- TeleportService uses actor messages for registration
- Teleported agents appear in list_agents()
- Tests pass

### Phase 4: Migrate API Layer
**Goal**: Use RegistryActor for list/get operations

**Tasks**:
1. Update API handlers to invoke RegistryActor
2. Deprecate direct AgentStorage calls for registry ops
3. Add API integration tests

**Acceptance Criteria**:
- GET /agents uses RegistryActor
- GET /agents/{id} uses RegistryActor
- API tests pass

### Phase 5: DST Coverage
**Goal**: Registry operations work under fault injection

**Tasks**:
1. Create DST test for registry operations
2. Test registration under faults (storage failures, crashes)
3. Verify registry consistency after recovery

**Acceptance Criteria**:
- Registry DST test passes
- Registry state consistent under faults

## What to Try (Updated After Each Phase)

### Phase 1: Core RegistryActor ✅
**Works Now**:
- RegistryActor with 4 operations (register, unregister, list, get)
- Message-based API via actor invocations
- State persistence with metrics tracking
- 5 unit tests all passing

### Phase 2: AgentActor Self-Registration ✅
**Works Now**:
- AgentActor.with_dispatcher() builder method
- Self-registration on activation
- Non-fatal registration (doesn't block activation)
- Backward compatible (dispatcher optional)

### Phase 3: TeleportService Migration ✅
**Works Now**:
- TeleportService uses DispatcherHandle instead of AgentStorage
- with_dispatcher() builder method
- Registration via RegistryActor message passing
- Backward compatible (dispatcher optional)
- All tests still passing (166/166)

**Doesn't Work Yet**:
- API layer integration (Phase 4)

**Known Limitations**:
- Single-node only (no distributed registry yet)
- No caching (reads hit storage every time)

## Architecture Design

### RegistryActor Structure

```rust
/// Registry actor - manages global agent metadata
pub struct RegistryActor {
    /// Storage backend for persistence
    storage: Arc<dyn AgentStorage>,
    /// Optional in-memory cache (future optimization)
    cache: Option<HashMap<String, AgentMetadata>>,
}

/// Registry actor state
#[derive(Serialize, Deserialize, Default)]
pub struct RegistryActorState {
    /// Agent count (for metrics)
    agent_count: u64,
    /// Last updated timestamp
    last_updated_ms: u64,
}
```

### Message Protocol

**Register Agent**:
```json
{
  "operation": "register",
  "metadata": { /* AgentMetadata */ }
}
```

**Response**: `{"status": "ok", "agent_id": "..."}`

**List Agents**:
```json
{
  "operation": "list",
  "filter": {  // optional
    "tags": ["production"],
    "agent_type": "MemgptAgent"
  }
}
```

**Response**: `{"agents": [...]}`

### Integration Pattern

```rust
// Before (direct storage):
storage.save_agent(&metadata).await?;

// After (actor message):
let request = serde_json::json!({
    "operation": "register",
    "metadata": metadata
});
let response = dispatcher.invoke(
    ActorId::new("system", "agent_registry")?,
    "register".to_string(),
    serde_json::to_vec(&request)?
).await?;
```

## Testing Strategy

### Unit Tests
- RegistryActor operations (register/unregister/list/get)
- State serialization/deserialization
- Error handling (duplicate registration, not found, etc.)

### Integration Tests
- AgentActor self-registration on activation
- TeleportService registration after teleport
- API layer using RegistryActor

### DST Tests
- Registry consistency under storage faults
- Registration during concurrent actor activations
- Recovery after registry actor crash

## Migration Path

### Step 1: Add RegistryActor (non-breaking)
- Create actor, add to runtime
- Keep existing AgentStorage calls working

### Step 2: Migrate Call Sites (gradual)
- Update one component at a time
- Run tests after each migration
- Keep both paths working temporarily

### Step 3: Deprecate Direct Access (future)
- Mark AgentStorage registry methods as deprecated
- Add warnings for direct access
- Plan removal timeline

## Risks & Mitigations

**Risk**: Performance regression (message passing overhead)
**Mitigation**: Add in-memory cache, benchmark before/after

**Risk**: Breaking existing tests/integrations
**Mitigation**: Gradual migration, keep backward compatibility

**Risk**: Single point of failure
**Mitigation**: Document as known limitation, plan distributed registry for future

## Success Criteria

- ✅ RegistryActor implemented and tested
- ✅ AgentActor can self-register via messages
- ✅ TeleportService uses RegistryActor
- ✅ API layer uses RegistryActor
- ✅ DST tests pass
- ✅ All existing tests still pass
- ✅ Zero direct AgentStorage calls for registry operations

## Files to Modify

### New Files
- `crates/kelpie-server/src/actor/registry_actor.rs` - RegistryActor implementation
- `crates/kelpie-server/tests/registry_actor_dst.rs` - DST tests

### Modified Files
- `crates/kelpie-server/src/actor/mod.rs` - Export RegistryActor
- `crates/kelpie-server/src/actor/agent_actor.rs` - Add self-registration
- `crates/kelpie-server/src/service/teleport_service.rs` - Use RegistryActor
- `crates/kelpie-server/src/api/*.rs` - Update API handlers
- `crates/kelpie-server/src/state.rs` - Initialize RegistryActor

## Progress Tracking

- [x] Phase 1: Core RegistryActor implementation
- [x] Phase 2: AgentActor self-registration
- [x] Phase 3: TeleportService migration
- [ ] Phase 4: API layer migration
- [ ] Phase 5: DST coverage

## Notes

- This is a foundational architectural improvement
- Enables future features (agent discovery, health checks, etc.)
- Aligns with actor model principles (message passing, not shared state)
- Option 2 (TeleportService fix) remains as fallback if needed

## References

- Original analysis: agent_actor.rs lines 671-727
- Option 2 implementation: teleport_service.rs lines 235-278
- Actor model: kelpie-core/src/actor.rs
- Storage trait: kelpie-server/src/storage/traits.rs

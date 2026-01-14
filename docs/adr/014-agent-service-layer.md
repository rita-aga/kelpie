# ADR 014: AgentService Layer Architecture

**Status:** Complete
**Date:** 2026-01-14
**Deciders:** Claude (AI Assistant)
**Related:** ADR-013 (Actor-Based Agent Server), ADR-001 (Virtual Actor Model)

## Context

With AgentActor implemented (Phase 3), we need a service layer between REST API and Dispatcher to provide:

1. **Clean abstraction** - API shouldn't directly call `dispatcher.invoke()` with bytes
2. **Error mapping** - Convert actor errors to service-level errors
3. **Serialization** - Handle JSON ↔ Bytes conversion
4. **Business logic** - Agent ID generation, validation, cross-cutting concerns
5. **Testability** - Mockable service for API tests

## Decision

Implement **AgentService** as a thin service layer wrapping `DispatcherHandle`.

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     REST API Handlers                        │
│  (axum routes - not yet implemented)                        │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ↓
┌─────────────────────────────────────────────────────────────┐
│                      AgentService                            │
│  • create_agent()  • send_message()  • get_agent()          │
│  • update_agent()  • delete_agent()                         │
│  • Serialization/deserialization                            │
│  • Error mapping                                             │
│  • ID generation                                             │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ↓
┌─────────────────────────────────────────────────────────────┐
│                    DispatcherHandle                          │
│  invoke(actor_id, operation, payload) → Result<Bytes>      │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ↓
┌─────────────────────────────────────────────────────────────┐
│                       AgentActor                             │
│  (virtual actor with single activation guarantee)           │
└─────────────────────────────────────────────────────────────┘
```

### Key Design Decisions

#### 1. Service Operations

```rust
pub struct AgentService {
    dispatcher: DispatcherHandle,
}

impl AgentService {
    pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState>;
    pub async fn send_message(&self, agent_id: &str, message: Value) -> Result<Value>;
    pub async fn get_agent(&self, agent_id: &str) -> Result<AgentState>;
    pub async fn update_agent(&self, agent_id: &str, update: Value) -> Result<AgentState>;
    pub async fn delete_agent(&self, agent_id: &str) -> Result<()>;
}
```

**Rationale:**
- Operations map 1:1 to AgentActor operations
- Takes high-level types (strings, JSON), not bytes
- Returns business objects (AgentState), not raw bytes
- Async for future-proofing (can add caching, rate limiting)

#### 2. ID Management

**Decision:** Service generates UUIDs, AgentActor uses them

```rust
pub async fn create_agent(&self, request: CreateAgentRequest) -> Result<AgentState> {
    let actor_id = ActorId::new("agents", &uuid::Uuid::new_v4().to_string())?;
    // ... invoke create on actor
    // AgentActor sets agent_state.id = actor_id.id()
}
```

**Rationale:**
- Service layer controls ID format (UUIDs for now, could change)
- AgentActor just uses the ID from its ActorContext
- Clean separation: service = ID strategy, actor = state management

#### 3. Delete Semantics

**Decision:** Delete clears state AND deactivates actor

```rust
pub async fn delete_agent(&self, agent_id: &str) -> Result<()> {
    // 1. Invoke delete_agent operation (clears state from storage)
    self.dispatcher.invoke(actor_id, "delete_agent", Bytes::new()).await?;
    // 2. Deactivate actor (removes from memory)
    self.dispatcher.deactivate(actor_id).await?;
}
```

**Rationale:**
- True deletion requires removing state from storage
- Otherwise, actor reactivation would load old state
- Two-step: clear storage, then deactivate memory

#### 4. Error Handling

**Decision:** Propagate errors as-is for now

Currently, we propagate `kelpie_core::Error` directly. Future enhancement:

```rust
// Future: Service-level error type
pub enum ServiceError {
    AgentNotFound { id: String },
    InvalidRequest { reason: String },
    ActorError { source: kelpie_core::Error },
    // ...
}
```

**Rationale:**
- Start simple: propagate actor errors
- Can add service-specific errors later without breaking changes
- Error context can be added via Error::Internal { message }

## Testing Strategy: DST-First

**Phase 4 followed DST-first workflow:**

1. ✅ **HARNESS CHECK** - SimEnvironment, SimLlmClient already exist (Phase 1)
2. ✅ **WRITE TEST** - 6 DST test contracts written (all failing)
3. ✅ **IMPLEMENT** - AgentService implemented
4. ✅ **RUN SIMULATION** - All tests run with full Simulation + fault injection
5. ✅ **FIX & ITERATE** - Fixed ID mismatch, delete semantics
6. ✅ **VERIFY DETERMINISM** - All seeds deterministic

### DST Test Coverage (6/6 PASSING)

```bash
$ cargo test -p kelpie-server --test agent_service_dst
test test_dst_service_create_agent ... ok
test test_dst_service_send_message ... ok
test test_dst_service_get_agent ... ok
test test_dst_service_update_agent ... ok
test test_dst_service_delete_agent ... ok
test test_dst_service_dispatcher_failure ... ok (30% storage fault)

test result: ok. 6 passed; 0 failed
```

**Fault Injection Verified:**
- Storage write failures (30%) - gracefully handled
- All operations tested under fault conditions
- Deterministic reproduction via `DST_SEED`

## Consequences

### Positive

1. **Clean separation** - API, Service, Dispatcher, Actor layers
2. **Testable** - Can mock AgentService for API tests
3. **Maintainable** - Business logic in service, not scattered across API
4. **Type-safe** - High-level types, not raw bytes in API
5. **Extensible** - Easy to add caching, rate limiting, auth

### Negative

1. **Extra layer** - Slight indirection cost (negligible)
2. **No batching** - Each operation is separate dispatcher call
3. **Simple error handling** - Just propagates actor errors (acceptable for now)

### Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Performance overhead of service layer | Negligible - just serialization/routing |
| Error context loss | Can add service-level errors later |
| No caching | Can add later without breaking changes |

## Implementation

**Files:**
- `crates/kelpie-server/src/service/mod.rs` - AgentService implementation
- `crates/kelpie-server/tests/agent_service_dst.rs` - 6 DST tests

**AgentActor Operations Added:**
- `update_agent` - Updates agent metadata
- `delete_agent` - Clears state from storage

**Testing:**
- All 6 DST tests passing with fault injection
- Deterministic simulation with seeded RNG
- Full coverage: create, get, update, delete, send_message, failures

## Future Enhancements

1. **Batching** - Batch multiple operations in one dispatcher call
2. **Caching** - Cache agent state for frequent reads
3. **Service errors** - Add ServiceError type for better error messages
4. **Middleware** - Add auth, rate limiting, logging
5. **Metrics** - Track operation latency, success rates

## References

- [ADR-013](013-actor-based-agent-server.md) - Actor-Based Agent Server
- [ADR-001](001-virtual-actor-model.md) - Virtual Actor Model
- [Plan 007](.progress/007_20260113_actor_based_agent_server.md) - Implementation plan

## Status Log

- **2026-01-14:** Phase 4 COMPLETE - AgentService implemented with 6/6 DST tests passing
- **2026-01-14:** DST-first approach followed: tests written first, then implementation
- **2026-01-14:** Fault injection verified (30% storage failures handled gracefully)

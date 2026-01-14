# ADR-012: Session Storage Architecture

**Date:** 2026-01-13
**Status:** Accepted
**Author:** Claude

## Context

Kelpie needs persistent storage for:
1. Agent metadata and configuration
2. Core memory blocks (persona, human)
3. Session state for crash recovery
4. Conversation messages

Currently all state is in-memory HashMaps, lost on restart.

## Decision

### Storage Split: FDB + Umi

| Data | Storage | Rationale |
|------|---------|-----------|
| Agent metadata | FDB | Configuration, rarely changes, fast lookup |
| Core blocks (persona, human) | FDB | Small, needed every request, direct editing |
| Session state | FDB | Checkpoints, crash recovery, transactional |
| Messages | FDB | Ordered log, fast sequential access |
| Archival memory | Umi | Large scale, vector search |
| Promoted blocks (facts, goals, scratch) | Umi | Auto-promotion from archival |
| Message semantic index | Umi | conversation_search tool |

### Why This Split?

**FDB for hot path:**
- Core blocks needed on EVERY request (~1ms read)
- Messages needed for context window (~1ms sequential)
- Session state for checkpoint/recovery (~1ms)

**Umi for search:**
- Archival memory is unbounded, needs vector search
- Promotion logic lives in Umi
- conversation_search needs semantic matching

### Session Checkpointing

**Iteration-level checkpoints** for robust crash recovery:

```
Agent Loop Iteration N:
1. Load session state from FDB
2. Build context (FDB + Umi)
3. Call LLM
4. Execute tool
5. CHECKPOINT to FDB  ← After each iteration
6. Check stop condition
7. Loop or exit
```

On crash, resume from last checkpoint (not restart).

### Data Structures

```rust
/// Agent metadata (FDB)
struct AgentMetadata {
    id: String,
    name: String,
    agent_type: AgentType,
    model: Option<String>,
    system: Option<String>,
    tool_ids: Vec<String>,
    tags: Vec<String>,
    metadata: Value,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

/// Session state for crash recovery (FDB)
struct SessionState {
    session_id: String,
    agent_id: String,
    iteration: u32,
    pause_until_ms: Option<u64>,
    pending_tool_calls: Vec<PendingToolCall>,
    last_tool_result: Option<String>,
    stop_reason: Option<String>,
    started_at: DateTime<Utc>,
    checkpointed_at: DateTime<Utc>,
}

/// Pending tool call (for crash recovery)
struct PendingToolCall {
    id: String,
    tool_name: String,
    tool_input: Value,
    started_at: DateTime<Utc>,
}
```

### FDB Key Schema

```
agents/{agent_id}/metadata     → AgentMetadata (JSON)
agents/{agent_id}/blocks       → Vec<Block> (JSON)
sessions/{agent_id}/{session}  → SessionState (JSON)
messages/{agent_id}/{ts_ms}    → Message (JSON)
```

### Storage Trait (DST-Compatible)

```rust
#[async_trait]
trait AgentStorage: Send + Sync {
    // Agent CRUD
    async fn save_agent(&self, agent: &AgentMetadata) -> Result<(), StorageError>;
    async fn load_agent(&self, id: &str) -> Result<Option<AgentMetadata>, StorageError>;
    async fn delete_agent(&self, id: &str) -> Result<(), StorageError>;
    async fn list_agents(&self) -> Result<Vec<AgentMetadata>, StorageError>;

    // Core blocks
    async fn save_blocks(&self, agent_id: &str, blocks: &[Block]) -> Result<(), StorageError>;
    async fn load_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StorageError>;

    // Session checkpoints
    async fn save_session(&self, state: &SessionState) -> Result<(), StorageError>;
    async fn load_session(&self, agent_id: &str, session_id: &str) -> Result<Option<SessionState>, StorageError>;
    async fn delete_session(&self, agent_id: &str, session_id: &str) -> Result<(), StorageError>;

    // Messages
    async fn append_message(&self, agent_id: &str, msg: &Message) -> Result<(), StorageError>;
    async fn load_messages(&self, agent_id: &str, limit: usize) -> Result<Vec<Message>, StorageError>;
    async fn load_messages_since(&self, agent_id: &str, since_ms: u64) -> Result<Vec<Message>, StorageError>;
}
```

## Alternatives Considered

### 1. All in Umi
- **Pro:** Single system
- **Con:** Slower for hot path (vector overhead), complex for checkpoints

### 2. All in FDB
- **Pro:** Single system, fast
- **Con:** No vector search, would need separate search system

### 3. Message-level checkpoints only
- **Pro:** Simpler
- **Con:** Lose in-flight work on crash

## Consequences

### Positive
- Fast hot path (FDB reads ~1ms)
- Robust crash recovery (iteration-level)
- Clean session handoff
- Semantic search via Umi
- DST-compatible via trait abstraction

### Negative
- Two storage systems to maintain
- Async Umi indexing adds complexity
- More checkpoint writes (after each iteration)

### Risks
- FDB/Umi consistency during failures
- Checkpoint overhead under high load

## DST Test Requirements

| Test | Faults | Assertion |
|------|--------|-----------|
| Agent CRUD | StorageWriteFail (20%) | Agents persist after retry |
| Checkpoint survives crash | CrashAfterWrite | Resume at correct iteration |
| Checkpoint lost | CrashBeforeWrite | Restart at last checkpoint |
| Session handoff | None | New instance resumes exactly |
| Pause survives crash | CrashAfterWrite | Pause state restored |
| Message ordering | StorageLatency | Messages in correct order |
| High load | Mixed faults (10%) | No data corruption |
| Determinism | All faults | Same seed = same behavior |

## References

- ADR-002: FoundationDB Integration
- ADR-010: Heartbeat/Pause Mechanism
- ADR-011: Agent Types Abstraction
- Letta agent state persistence

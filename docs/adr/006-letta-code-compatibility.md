# ADR-006: Letta-Code Compatibility

## Status

Accepted

## Date

2026-01-11

## Context

Kelpie aims to be a drop-in replacement for the Letta server, enabling users to leverage Kelpie's stateful actor runtime while maintaining compatibility with existing Letta tooling. [letta-code](https://github.com/letta-ai/letta-code) is a CLI coding agent (similar to Claude Code) that uses the Letta API for persistent agent memory.

Initial testing revealed several API compatibility gaps:

1. **Trailing slash handling**: letta-code sends requests with trailing slashes (e.g., `/v1/agents/?limit=1`) which returned 404
2. **Standalone blocks**: letta-code creates blocks independently via `/v1/blocks` before associating them with agents
3. **Core memory access by label**: letta-code accesses blocks via `/v1/agents/{id}/core-memory/blocks/{label}` using labels, not IDs
4. **Flexible message format**: letta-code sends messages with content as arrays of content blocks, not simple strings

## Decision

Implement the following compatibility features:

### 1. Trailing Slash Normalization

Wrap the Axum router with `tower_http::normalize_path::NormalizePath` to strip trailing slashes before routing:

```rust
let app = NormalizePath::trim_trailing_slash(app);
axum::serve(listener, ServiceExt::<Request>::into_make_service(app)).await?;
```

### 2. Standalone Blocks API (`/v1/blocks`)

Add a new `standalone_blocks` module with full CRUD operations:

- `POST /v1/blocks` - Create standalone block
- `GET /v1/blocks` - List blocks with pagination and label filtering
- `GET /v1/blocks/{id}` - Get block by ID
- `PATCH /v1/blocks/{id}` - Update block
- `DELETE /v1/blocks/{id}` - Delete block

Storage uses a separate `HashMap<String, Block>` in `AppState`.

### 3. Core Memory Routes by Label

Add routes that access agent blocks by label instead of ID:

- `GET /v1/agents/{id}/core-memory/blocks/{label}` - Get block by label
- `PATCH /v1/agents/{id}/core-memory/blocks/{label}` - Update block by label

State methods `get_block_by_label` and `update_block_by_label` search the agent's blocks vector by label.

### 4. Flexible Message Parsing

Update `CreateMessageRequest` to handle multiple input formats:

```rust
pub struct CreateMessageRequest {
    #[serde(default = "default_role")]
    pub role: MessageRole,
    #[serde(alias = "text", default)]
    pub content: String,
    pub messages: Option<Vec<LettaMessage>>,
    #[serde(alias = "message")]
    pub msg: Option<String>,
}
```

`LettaMessage.content` uses a custom deserializer that handles both string and array-of-content-blocks formats:

```rust
fn deserialize_content<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
```

## Consequences

### Positive

- letta-code can create agents and send messages through Kelpie
- Existing Letta Python/TypeScript SDKs gain compatibility
- Flexible message parsing supports both simple and complex formats
- No breaking changes to existing Kelpie API consumers

### Negative

- Standalone blocks are not automatically associated with agents (conceptual mismatch)
- Response format still differs from Letta's exact schema
- Additional code paths to maintain for compatibility

### Neutral

- Core-memory routes duplicate functionality with existing block routes (different access patterns)
- Standalone blocks storage is separate from agent blocks (intentional separation)

## Alternatives Considered

### Alternative 1: Proxy Layer

Run a separate proxy that transforms requests/responses between letta-code and Kelpie. Rejected because it adds deployment complexity and latency.

### Alternative 2: Fork letta-code

Modify letta-code to use Kelpie's native API. Rejected because it would require maintaining a fork and wouldn't benefit other Letta SDK users.

### Alternative 3: Strict Letta Schema Matching

Implement exact Letta response schemas with all fields. Deferred to future work - the current implementation handles the critical path (message processing).

## References

- [letta-code GitHub](https://github.com/letta-ai/letta-code)
- [Letta API Documentation](https://docs.letta.com/api-reference)
- [tower-http NormalizePath](https://docs.rs/tower-http/latest/tower_http/normalize_path/index.html)

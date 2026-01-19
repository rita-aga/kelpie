# Architecture Map

A curated guide to the Kelpie codebase for agents and developers.

## 🗺️ High-Level Map

### Core Logic (`crates/kelpie-core`)
- **Types**: `src/types.rs` - `ActorId`, `Message`, `Envelope`
- **Errors**: `src/error.rs` - Global `Error` enum and `Result` type
- **Consts**: `src/lib.rs` - `TIMEOUT_MS_MAX`, `MEMORY_LIMIT_BYTES`

### Runtime & Execution (`crates/kelpie-runtime`, `crates/kelpie-server`)
- **Server Entry**: `crates/kelpie-server/src/main.rs` - CLI, config, FDB wiring
- **API Routes**: `crates/kelpie-server/src/api/` - Axum handlers (`agents.rs`, `tools.rs`)
- **Global State**: `crates/kelpie-server/src/state.rs` - `AppState` (holds storage, tool registry)
- **Dispatcher**: `crates/kelpie-runtime/src/dispatcher.rs` - Routes messages to actors
- **Actor Loop**: `crates/kelpie-runtime/src/actor.rs` - The `process_message` loop

### Memory & Storage (`crates/kelpie-memory`, `crates/kelpie-storage`)
- **Memory System**: `crates/kelpie-memory/src/lib.rs` - `CoreMemory`, `WorkingMemory`, `ArchivalMemory`
- **FDB Backend**: `crates/kelpie-storage/src/fdb.rs` - FoundationDB implementation
- **In-Memory**: `crates/kelpie-storage/src/memory.rs` - `HashMap` implementation

### Sandboxing (`crates/kelpie-sandbox`, `crates/kelpie-vm`)
- **Interface**: `crates/kelpie-sandbox/src/lib.rs` - `Sandbox` trait
- **Process**: `crates/kelpie-sandbox/src/process.rs` - `ProcessSandbox` (std::process)
- **Firecracker**: `crates/kelpie-vm/src/firecracker.rs` - MicroVM management

---

## 🔄 Critical Data Flows

### 1. HTTP Request to Agent
1. **Request**: `POST /v1/agents/{id}/messages` hits `kelpie-server::api::agents::send_message`
2. **Lookup**: `AppState` looks up actor placement (Cluster logic)
3. **Dispatch**: Message sent to `Dispatcher` -> `ActorMailbox`
4. **Processing**: `Actor` wakes up -> loads state (Storage) -> calls `handle_message`
5. **Persist**: `Actor` saves state changes (Storage)
6. **Response**: HTTP 200 OK with `Message` response

### 2. Agent Tool Call
1. **Decision**: LLM outputs tool call JSON (e.g., `run_python`)
2. **Registry**: `Agent` calls `ToolRegistry::get("run_python")`
3. **Execution**:
   - IF builtin: Executed in-process (`kelpie-server::tools`)
   - IF sandboxed: `Sandbox::exec(...)` inside VM/Process
   - IF MCP: `McpClient::call_tool(...)` over stdio/HTTP
4. **Result**: Output returned to Agent context -> Memory updated

### 3. State Persistence (FDB)
1. **Write**: `Actor` calls `save_state()`
2. **Transaction**: `FdbKV` opens transaction
3. **Conflict Check**: FDB ensures linearizability
4. **Commit**: Data written to `(namespace, id, key)`

---

## 🧩 Key Interfaces

### `AgentActor` (Trait)
Defines how an agent behaves.
- `on_activate(&self, ctx)`: Load memory
- `handle_message(&self, ctx, msg)`: Main logic
- `on_deactivate(&self, ctx)`: Checkpoint

### `Sandbox` (Trait)
Defines isolation boundary.
- `start()`, `stop()`
- `exec(cmd, args)`
- `snapshot()`, `restore()`

### `Tool` (Trait)
Defines executable capabilities.
- `name()`, `description()`, `schema()`
- `call(args)`

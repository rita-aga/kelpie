# DST Integration & Storage Remediation Plan

## Status
- **Date Started**: 2026-01-21
- **Goal**: Fix the disconnect between Actor persistence and API storage, sanitize kelpie-cluster, and verify full system determinism.
- **Current State**: Planning.

## The Problems

1.  **Storage Gap (Critical)**:
    -   **Actors** (`AgentActor`) persist state as a single BLOB (`agent_state`).
    -   **API** (`AgentStorage`) reads granular keys (`message:N`, `blocks`).
    -   **Consequence**: API endpoints like `GET /messages` return empty results even if the Actor has history, because the Actor isn't writing the keys the API reads.

2.  **Registry Gap**:
    -   Actors do not self-register in the global agent list.
    -   **Consequence**: Agents created via Teleport or internal mechanisms may be "invisible" to `list_agents`.

3.  **Cluster Leaks**:
    -   `kelpie-cluster` uses raw `tokio::spawn` and `tokio::time::sleep`.
    -   **Consequence**: Distributed tests cannot be run deterministically under `madsim`.

## Plan

### Phase 1: Cluster Sanitization (Immediate)
Make `kelpie-cluster` deterministic.
- [ ] Refactor `kelpie-cluster` to use `kelpie_core::Runtime` trait.
- [ ] Replace `tokio::spawn` with `runtime.spawn()`.
- [ ] Replace `tokio::time::sleep` with `runtime.sleep()`.
- [ ] Add `clippy` ban for raw tokio types in `kelpie-cluster`.

### Phase 2: Storage Unification (The "Write-Through" Fix)
Update `AgentActor` to write data in a format the API can read.
- [ ] **Define Storage Layout**: Standardize on the granular layout defined in `FdbAgentRegistry` as the contract.
- [ ] **Update AgentActor**:
    -   Modify `on_deactivate` (and periodic checkpoints) to write granular keys:
        -   `message:{N}` for new messages.
        -   `message_count` for sequence tracking.
        -   `blocks` for memory blocks.
    -   *TigerStyle*: Keep the `agent_state` BLOB for fast Actor recovery, but treat granular keys as "Index/View" data for the API.
- [ ] **Self-Registration**:
    -   Modify `AgentActor::on_activate` to check if `system/agent_registry` contains its metadata.
    -   If missing, write self to registry (ensures Teleported agents appear in API).

### Phase 3: Full Lifecycle DST Test
Verify the loop is closed.
- [ ] Create `tests/full_lifecycle_dst.rs`.
- [ ] **Scenario**:
    1.  Create Agent via API (verifies Registry).
    2.  Send Message via Actor/Service (verifies Actor logic).
    3.  List Messages via API (verifies Storage Gap fix).
    4.  Simulate Crash/Restart.
    5.  List Messages via API again (verifies Persistence).

### Phase 4: Cleanup
- [ ] Remove any legacy `SimStorage` code that might still be lurking (checked: mostly gone).
- [ ] Verify `kelpie-server` tests pass with `--features dst,madsim`.

## Execution Order
1. Phase 1 (Cluster) - Independent, easy win.
2. Phase 2 (Storage) - Core architectural fix.
3. Phase 3 (Test) - Verification.

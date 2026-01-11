# ADR-003: WASM Actor Runtime

## Status

Proposed

## Date

2025-01-10

## Implementation Status

| Component | Status | Location |
|-----------|--------|----------|
| Wasmtime integration | 🚧 Scaffolded | `kelpie-wasm/src/lib.rs` |
| waPC protocol | ⏳ Not Started | P3 priority |
| Module registry | ⏳ Not Started | P3 priority |
| Host functions | ⏳ Not Started | P3 priority |
| Rust WASM actors | ⏳ Not Started | Future |
| TinyGo actors | ⏳ Not Started | Future |

**Note**: WASM actor support is a P3 (nice-to-have) feature. Basic scaffolding exists but runtime integration is not implemented. Focus is on native Rust actors first.

## Context

Kelpie aims to support polyglot actors - allowing developers to write actors in languages other than Rust. This is particularly important for:
- AI agent development where Python is dominant
- Existing codebases in Go, TypeScript, etc.
- Sandboxed execution for untrusted actor code
- Hot code deployment without cluster restart

## Decision

We support **WebAssembly (WASM)** actors using the **wasmtime** runtime and **waPC** protocol.

### Architecture

```
┌─────────────────────────────────────────────────────┐
│                   Kelpie Node                        │
│  ┌─────────────────────────────────────────────┐   │
│  │              Actor Runtime                   │   │
│  │  ┌─────────────┐    ┌─────────────────────┐ │   │
│  │  │ Native Rust │    │    WASM Actors      │ │   │
│  │  │   Actors    │    │  ┌───────────────┐  │ │   │
│  │  │             │    │  │   wasmtime    │  │ │   │
│  │  │             │    │  │   runtime     │  │ │   │
│  │  │             │    │  │  ┌─────────┐  │  │ │   │
│  │  │             │    │  │  │  waPC   │  │  │ │   │
│  │  │             │    │  │  │ protocol│  │  │ │   │
│  │  └─────────────┘    │  │  └─────────┘  │  │ │   │
│  │                     │  └───────────────┘  │ │   │
│  │                     └─────────────────────┘ │   │
│  └─────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────┘
```

### waPC Protocol

waPC (WebAssembly Procedure Calls) provides a standard host-guest communication protocol:

**Guest (WASM actor) exports:**
- `__guest_call(operation_size: i32, payload_size: i32) -> i32`

**Host (Kelpie runtime) exports:**
- `__host_call(namespace: string, operation: string, payload: bytes) -> bytes`
- `__console_log(msg: string)`

### WASM Actor Interface

```rust
// Host-side representation
pub struct WasmActor {
    module: Arc<wasmtime::Module>,
    instance: wasmtime::Instance,
    store: wasmtime::Store<WasmActorState>,
}

impl WasmActor {
    pub async fn invoke(
        &mut self,
        operation: &str,
        payload: &[u8],
    ) -> Result<Vec<u8>> {
        // Call __guest_call via waPC protocol
    }
}
```

### Module Loading

```rust
pub struct WasmModuleRegistry {
    // Module cache by content hash
    modules: HashMap<[u8; 32], Arc<wasmtime::Module>>,
    engine: wasmtime::Engine,
}

impl WasmModuleRegistry {
    pub async fn load(&self, wasm_bytes: &[u8]) -> Result<Arc<wasmtime::Module>> {
        let hash = sha256(wasm_bytes);
        if let Some(module) = self.modules.get(&hash) {
            return Ok(module.clone());
        }
        // Compile and cache
    }
}
```

### Supported Languages

| Language | Toolchain | Status |
|----------|-----------|--------|
| Rust | cargo + wasm32-unknown-unknown | Planned |
| Go | TinyGo | Planned |
| Python | Pyodide / MicroPython | Future |
| TypeScript | AssemblyScript | Future |

## Consequences

### Positive

- **Polyglot Support**: Write actors in multiple languages
- **Sandboxing**: WASM provides memory isolation
- **Hot Deployment**: Swap modules without restart
- **Portable**: WASM runs anywhere
- **Security**: Untrusted code runs safely

### Negative

- **Performance Overhead**: WASM is slower than native Rust
- **Limited Async**: WASM async support is still evolving
- **Memory Constraints**: WASM has 4GB memory limit
- **Toolchain Complexity**: Each language needs its own toolchain
- **Debugging Difficulty**: Harder to debug WASM than native code

### Neutral

- Need to maintain waPC bindings for each language
- Module loading adds startup latency

## Alternatives Considered

### gRPC Services per Language

- Each language runs as separate process
- Communicate via gRPC

**Rejected because**: Higher latency, more operational complexity, loses actor benefits.

### Embedded Language Runtimes

- Embed V8 for JavaScript
- Embed Python interpreter

**Rejected because**: Heavy runtimes, security concerns, maintenance burden.

### Native Plugins via FFI

- Dynamic libraries (.so/.dll) for each language

**Rejected because**: Memory safety concerns, platform-specific, no sandboxing.

## References

- [wasmtime](https://github.com/bytecodealliance/wasmtime)
- [waPC Protocol](https://wapc.io/)
- [WASM Component Model](https://component-model.bytecodealliance.org/)

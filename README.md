# Kelpie

[![CI](https://github.com/nerdsane/kelpie/actions/workflows/ci.yml/badge.svg)](https://github.com/nerdsane/kelpie/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A distributed virtual actor system with linearizability guarantees, designed for AI agent orchestration and general stateful distributed systems.

## Overview

Kelpie is a Rust implementation of the virtual actor model (Orleans/NOLA pattern) with:

- **Linearizable Operations**: Single activation guarantee ensures at most one instance of an actor exists at any time
- **DST-First**: Deterministic Simulation Testing from day one, inspired by FoundationDB and TigerBeetle
- **FoundationDB Backend**: Per-actor KV storage with ACID transactions
- **WASM Actors**: Write actors in Rust, Go, or other languages compiled to WebAssembly
- **AI Agent Ready**: First-class support for stateful agent orchestration

## Quick Start

```rust
use kelpie_core::{Actor, ActorContext, ActorId, Result};
use async_trait::async_trait;
use bytes::Bytes;
use serde::{Deserialize, Serialize};

#[derive(Default, Serialize, Deserialize)]
struct CounterState {
    count: u64,
}

struct CounterActor;

#[async_trait]
impl Actor for CounterActor {
    type State = CounterState;

    async fn invoke(
        &self,
        ctx: &mut ActorContext<Self::State>,
        operation: &str,
        _payload: Bytes,
    ) -> Result<Bytes> {
        match operation {
            "increment" => {
                ctx.state.count += 1;
                Ok(Bytes::from(ctx.state.count.to_string()))
            }
            "get" => Ok(Bytes::from(ctx.state.count.to_string())),
            _ => Err(kelpie_core::Error::InvalidOperation {
                operation: operation.to_string(),
            }),
        }
    }
}
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         Kelpie Cluster                           │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐ │
│  │   Node 1    │  │   Node 2    │  │        Node N           │ │
│  │  ┌───────┐  │  │  ┌───────┐  │  │  ┌───────┐  ┌───────┐  │ │
│  │  │Actor A│  │  │  │Actor C│  │  │  │Actor E│  │Actor F│  │ │
│  │  │Actor B│  │  │  │Actor D│  │  │  │ (WASM)│  │ (Rust)│  │ │
│  │  └───────┘  │  │  └───────┘  │  │  └───────┘  └───────┘  │ │
│  └──────┬──────┘  └──────┬──────┘  └───────────┬─────────────┘ │
│         │                │                      │               │
│  ┌──────┴────────────────┴──────────────────────┴─────────────┐│
│  │                    Actor Runtime                            ││
│  └─────────────────────────────┬──────────────────────────────┘│
│                                │                                │
│  ┌─────────────────────────────┴──────────────────────────────┐│
│  │                      Registry                               ││
│  └─────────────────────────────┬──────────────────────────────┘│
└────────────────────────────────┼────────────────────────────────┘
                                 │
┌────────────────────────────────┴────────────────────────────────┐
│                        FoundationDB                              │
└──────────────────────────────────────────────────────────────────┘
```

## Crates

| Crate | Description |
|-------|-------------|
| `kelpie-core` | Core types, errors, and constants |
| `kelpie-runtime` | Actor runtime and dispatcher |
| `kelpie-registry` | Actor placement and discovery |
| `kelpie-storage` | Per-actor KV storage |
| `kelpie-wasm` | WASM actor runtime |
| `kelpie-cluster` | Cluster coordination |
| `kelpie-agent` | AI agent abstractions |
| `kelpie-dst` | Deterministic Simulation Testing |
| `kelpie-server` | Standalone server binary |
| `kelpie-cli` | CLI tools |

## DST (Deterministic Simulation Testing)

All critical paths are tested under simulation with fault injection:

```bash
# Run with random seed (logged for reproduction)
cargo test -p kelpie-dst

# Reproduce specific run
DST_SEED=12345 cargo test -p kelpie-dst

# Stress test
cargo test -p kelpie-dst stress --release -- --ignored
```

### Fault Types

- **Storage**: Write fail, read fail, corruption, latency, disk full
- **Crash**: Before write, after write, during transaction
- **Network**: Partition, delay, packet loss, reordering
- **Time**: Clock skew, clock jump
- **Resource**: Out of memory, CPU starvation

## Development

### Prerequisites

- Rust 1.75+
- FoundationDB (optional, for production)

### Building

```bash
cargo build
```

### Testing

```bash
cargo test
```

### Documentation

```bash
cargo doc --open
```

## Engineering Principles

Kelpie follows **TigerStyle** (Safety > Performance > DX):

- **Explicit Constants**: All limits are named with units (`TIMEOUT_MS_MAX`)
- **Big-Endian Naming**: From big to small concept (`actor_id_length_bytes_max`)
- **2+ Assertions per Function**: Preconditions and postconditions
- **No Silent Truncation**: Explicit conversions only
- **DST Coverage**: Every critical path

See [CLAUDE.md](./CLAUDE.md) for detailed development guidelines.

## Architecture Decision Records

- [ADR-001: Virtual Actor Model](./docs/adr/001-virtual-actor-model.md)
- [ADR-002: FoundationDB Integration](./docs/adr/002-foundationdb-integration.md)
- [ADR-003: WASM Actor Runtime](./docs/adr/003-wasm-actor-runtime.md)
- [ADR-004: Linearizability Guarantees](./docs/adr/004-linearizability-guarantees.md)
- [ADR-005: DST Framework](./docs/adr/005-dst-framework.md)

## Performance Targets

| Metric | Target |
|--------|--------|
| Single-actor throughput | >500K ops/sec |
| Cross-actor throughput | >100K ops/sec |
| Actor activation rate | >10K/sec |
| DST coverage | 100% of critical paths |

## Inspiration

- [NOLA](https://github.com/richardartoul/nola) - Go virtual actors
- [Orleans](https://github.com/dotnet/orleans) - .NET virtual actors
- [FoundationDB](https://www.foundationdb.org/) - Simulation testing pioneer
- [TigerBeetle](https://github.com/tigerbeetle/tigerbeetle) - TigerStyle engineering

## License

Apache-2.0

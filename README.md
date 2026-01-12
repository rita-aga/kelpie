# Kelpie

[![CI](https://github.com/nerdsane/kelpie/actions/workflows/ci.yml/badge.svg)](https://github.com/nerdsane/kelpie/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

An open-source agent runtime with stateful memory, sandboxed execution, and MCP tool integration.

## Overview

Kelpie provides infrastructure for building AI agents that:

- **Persist state** across invocations with a three-tier memory hierarchy
- **Execute tools safely** via MCP protocol with process or VM isolation
- **Scale horizontally** with virtual actor model and cluster coordination
- **Test deterministically** with simulation testing and fault injection

## Quick Start

```bash
# Start the server
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server

# Create an agent
curl -X POST http://localhost:8283/v1/agents \
  -H "Content-Type: application/json" \
  -d '{
    "name": "my-agent",
    "memory_blocks": [
      {"label": "persona", "value": "You are a helpful assistant."}
    ]
  }'

# Send a message
curl -X POST http://localhost:8283/v1/agents/{id}/messages \
  -H "Content-Type: application/json" \
  -d '{"role": "user", "content": "Hello!"}'
```

## Features

### Memory Hierarchy

| Tier | Purpose | Size | Persistence |
|------|---------|------|-------------|
| **Core** | Always in LLM context | ~32KB | Per-agent |
| **Working** | Session KV store | Unbounded | Per-agent |
| **Archival** | Semantic search | Unbounded | Per-agent |

### Sandbox Isolation

| Level | Implementation | Boot Time |
|-------|----------------|-----------|
| Process | OS process isolation | <10ms |
| VM | Firecracker microVM | ~125ms |

### Tool Integration (MCP)

```rust
// Connect to any MCP server
let client = McpClient::new(McpTransportType::Stdio {
    command: "npx".to_string(),
    args: vec!["-y", "@modelcontextprotocol/server-filesystem", "/tmp"],
});
client.connect().await?;

// Discover and execute tools
let tools = client.discover_tools().await?;
let result = client.execute_tool("read_file", json!({"path": "/tmp/test.txt"})).await?;
```

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Kelpie Server                        │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐ │
│  │  REST API   │  │  LLM Client │  │  MCP Tools      │ │
│  └──────┬──────┘  └──────┬──────┘  └────────┬────────┘ │
│         └────────────────┼──────────────────┘          │
│                    ┌─────┴─────┐                       │
│                    │  Runtime  │                       │
│                    └─────┬─────┘                       │
│  ┌───────────────────────┼───────────────────────────┐ │
│  │              Memory System                        │ │
│  │  [Core 32KB] [Working KV] [Archival Vectors]     │ │
│  └───────────────────────┼───────────────────────────┘ │
│                    ┌─────┴─────┐                       │
│                    │  Storage  │                       │
│                    └───────────┘                       │
└─────────────────────────────────────────────────────────┘
```

## Crates

| Crate | Description | Status |
|-------|-------------|--------|
| `kelpie-core` | Types, errors, constants | Complete |
| `kelpie-runtime` | Actor dispatcher | Complete |
| `kelpie-memory` | Memory hierarchy | Complete |
| `kelpie-storage` | KV storage | Complete |
| `kelpie-sandbox` | Process/VM isolation | Complete |
| `kelpie-tools` | MCP client, tool registry | Complete |
| `kelpie-cluster` | Node coordination | Complete |
| `kelpie-server` | REST API server | Complete |
| `kelpie-dst` | Simulation testing | Complete |
| `kelpie-agent` | Agent abstractions | Planned |
| `kelpie-wasm` | WASM actors | Planned |

## API Compatibility

Kelpie implements Letta-compatible REST endpoints with SSE streaming support:

```
GET  /health
GET  /v1/agents
POST /v1/agents
GET  /v1/agents/{id}
PATCH /v1/agents/{id}
DELETE /v1/agents/{id}
GET  /v1/agents/{id}/blocks
PATCH /v1/agents/{id}/blocks/{bid}
GET  /v1/agents/{id}/messages
POST /v1/agents/{id}/messages              # JSON or SSE (stream_steps=true)
POST /v1/agents/{id}/messages/stream       # SSE streaming
GET  /v1/blocks                            # Standalone blocks
POST /v1/blocks
GET  /v1/agents/{id}/core-memory/blocks/{label}  # Access by label
```

### letta-code CLI

Use Kelpie as a drop-in replacement for Letta server with [letta-code](https://github.com/letta-ai/letta-code):

```bash
# Start Kelpie server
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server

# Run letta-code pointing to Kelpie
LETTA_BASE_URL=http://localhost:8283 letta -p "help me write a function"
```

### Python SDK

Use with existing Letta clients:

```python
from letta_client import Letta

client = Letta(base_url="http://localhost:8283")
agent = client.agents.create(name="my-agent")
```

## Testing

Kelpie uses Deterministic Simulation Testing (DST) for reliability:

```bash
# Run all tests
cargo test

# Run with specific seed for reproduction
DST_SEED=12345 cargo test -p kelpie-dst

# Run with fault injection
cargo test -p kelpie-dst -- --ignored
```

### Fault Types

- **Storage**: Write fail, read fail, corruption, latency
- **Network**: Partition, delay, packet loss, reordering
- **Crash**: Before write, after write, during transaction
- **Time**: Clock skew, clock jump

## Configuration

Environment variables:

| Variable | Description | Default |
|----------|-------------|---------|
| `ANTHROPIC_API_KEY` | Anthropic API key | Required for Claude |
| `OPENAI_API_KEY` | OpenAI API key | Required for GPT |
| `KELPIE_HOST` | Server bind address | `0.0.0.0` |
| `KELPIE_PORT` | Server port | `8283` |
| `OTEL_EXPORTER_OTLP_ENDPOINT` | OpenTelemetry endpoint | None |
| `RUST_LOG` | Log level | `info` |

## Roadmap

See [VISION.md](./VISION.md) for detailed roadmap.

**Next priorities:**
1. ~~FoundationDB integration~~ ✅ Backend implemented, needs production testing
2. Agent framework abstraction
3. Local embeddings (fastembed)
4. Authentication

## Engineering Principles

Kelpie follows **TigerStyle** (Safety > Performance > DX):

- Explicit constants with units: `TIMEOUT_MS_MAX`, `MEMORY_BYTES_LIMIT`
- Big-endian naming: `actor_state_size_bytes_max`
- 2+ assertions per function
- No silent truncation
- DST coverage for critical paths

See [CLAUDE.md](./CLAUDE.md) for development guidelines.

## Inspiration

- [NOLA](https://github.com/richardartoul/nola) - Go virtual actors
- [Letta](https://github.com/letta-ai/letta) - Stateful AI agents
- [FoundationDB](https://www.foundationdb.org/) - Simulation testing
- [TigerBeetle](https://github.com/tigerbeetle/tigerbeetle) - TigerStyle

## License

Apache-2.0

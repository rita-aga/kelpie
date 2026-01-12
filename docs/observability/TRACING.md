# Kelpie Tracing Reference

This document describes the distributed tracing instrumentation in Kelpie.

## Overview

Kelpie uses OpenTelemetry for distributed tracing, providing visibility into:
- Request flow through the system
- Actor lifecycle (activation, invocation, deactivation)
- Storage operations
- Performance bottlenecks

## Quick Start

### Basic Logging

```bash
# See INFO-level spans (critical paths only)
RUST_LOG=info cargo run -p kelpie-server

# See all spans including DEBUG-level internals
RUST_LOG=debug cargo run -p kelpie-server
```

### Export to OTLP Collector

```bash
# Export traces to Jaeger, Zipkin, or any OTLP-compatible backend
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 \
RUST_LOG=info \
cargo run -p kelpie-server --features otel
```

### Run Jaeger Locally

```bash
# Start Jaeger all-in-one (includes collector + UI)
docker run -d --name jaeger \
  -p 4317:4317 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest

# View traces at http://localhost:16686
```

---

## Span Hierarchy

Kelpie's spans follow a hierarchical structure:

```
HTTP Request (INFO)
├─ API Handler (INFO) - e.g., create_agent, send_message
│  ├─ Dispatcher::handle_invoke (DEBUG)
│  │  ├─ ActiveActor::activate (INFO)
│  │  │  └─ Storage::get (INFO/DEBUG)
│  │  └─ ActiveActor::process_invocation (INFO)
│  │     ├─ Actor::invoke (user code)
│  │     └─ Storage::set (INFO/DEBUG)
│  └─ ActiveActor::deactivate (INFO)
│     └─ Storage::set (INFO/DEBUG)
```

---

## Span Levels

### INFO Level (Critical Paths)

**When to use INFO:**
- User-facing operations that affect latency
- Actor lifecycle events
- API request handlers

**Examples:**
- `Runtime::start`
- `send_message` (API handler)
- `ActiveActor::activate`
- `Dispatcher::handle_invoke` (activation path only)

**Fields captured:**
- `agent_id` - Actor identifier
- `operation` - Operation name
- `request_id` - HTTP request ID (from headers)

### DEBUG Level (Internal Operations)

**When to use DEBUG:**
- Internal operations not on critical path
- Helper functions
- Frequent operations that would spam logs

**Examples:**
- `Dispatcher::handle_invoke` (message processing)
- `generate_sse_events` (streaming internals)
- `execute_tool_async` (tool execution)

**Fields captured:**
- Same as INFO, plus operation-specific details

---

## Instrumented Components

### 1. Runtime Layer

**File:** `crates/kelpie-runtime/src/runtime.rs`

| Span | Level | Fields | Description |
|------|-------|--------|-------------|
| `Runtime::start` | INFO | - | Runtime initialization |
| `Runtime::stop` | INFO | - | Runtime shutdown |

### 2. Dispatcher Layer

**File:** `crates/kelpie-runtime/src/dispatcher.rs`

| Span | Level | Fields | Description |
|------|-------|--------|-------------|
| `Dispatcher::run` | INFO | - | Main dispatcher loop |
| `Dispatcher::handle_invoke` | DEBUG | `actor_id`, `operation` | Message routing |

### 3. Activation Layer

**File:** `crates/kelpie-runtime/src/activation.rs`

| Span | Level | Fields | Description |
|------|-------|--------|-------------|
| `ActiveActor::activate` | INFO | `actor_id` | Actor activation and state load |
| `ActiveActor::process_invocation` | INFO | `actor_id`, `operation` | Message processing |
| `ActiveActor::deactivate` | INFO | `actor_id` | Actor deactivation and state save |

### 4. API Handlers (Server)

**File:** `crates/kelpie-server/src/api/*.rs`

All HTTP API handlers are instrumented at INFO level:

| Endpoint | Span | Fields |
|----------|------|--------|
| `POST /v1/agents` | `create_agent` | `agent_name` |
| `GET /v1/agents/:id` | `get_agent` | `agent_id` |
| `GET /v1/agents` | `list_agents` | `limit`, `cursor` |
| `PATCH /v1/agents/:id` | `update_agent` | `agent_id` |
| `DELETE /v1/agents/:id` | `delete_agent` | `agent_id` |
| `POST /v1/agents/:id/messages` | `send_message` | `agent_id`, `stream` |
| `GET /v1/agents/:id/messages` | `list_messages` | `agent_id`, `limit` |
| `GET /v1/agents/:id/blocks` | `list_blocks` | `agent_id` |
| `PATCH /v1/agents/:id/blocks/:block_id` | `update_block` | `agent_id`, `block_id` |
| `POST /v1/agents/:id/archival` | `add_archival` | `agent_id` |
| `GET /v1/agents/:id/archival` | `search_archival` | `agent_id`, `query`, `limit` |
| `POST /v1/tools` | `register_tool` | `name` |
| `POST /v1/tools/:name/execute` | `execute_tool` | `name` |

### 5. Storage Layer

**File:** `crates/kelpie-storage/src/{fdb.rs,memory.rs}`

Both FDB and in-memory storage implementations have matching spans:

| Span | Level | Fields | Description |
|------|-------|--------|-------------|
| `ActorKV::get` | DEBUG | `actor_id`, `key_len` | Read operation |
| `ActorKV::set` | DEBUG | `actor_id`, `key_len`, `value_len` | Write operation |
| `ActorKV::delete` | DEBUG | `actor_id`, `key_len` | Delete operation |
| `ActorKV::list_keys` | DEBUG | `actor_id`, `prefix_len` | List operation |
| `ActorKV::begin_transaction` | INFO | `actor_id` | Transaction start |

---

## Span Fields Reference

### Common Fields

| Field | Type | Example | Description |
|-------|------|---------|-------------|
| `agent_id` | String | `"test/counter-1"` | Qualified actor ID (namespace/id) |
| `operation` | String | `"increment"` | Actor operation name |
| `key_len` | usize | `42` | Storage key length in bytes |
| `value_len` | usize | `1024` | Storage value length in bytes |
| `limit` | usize | `50` | Pagination limit |
| `cursor` | Option<String> | `"abc123"` | Pagination cursor |

### Field Naming Conventions

Following TigerStyle:
- Use full words, not abbreviations (`agent_id`, not `aid`)
- Include units in name when applicable (`key_len`, `duration_seconds`)
- Use snake_case for consistency with Rust

---

## Example Traces

### Actor Activation Flow

```
[INFO ] Runtime::start
[INFO ] Dispatcher::run
[INFO ] create_agent agent_name="my-agent"
[DEBUG] Dispatcher::handle_invoke actor_id="default/my-agent" operation="increment"
[INFO ] ActiveActor::activate actor_id="default/my-agent"
[DEBUG]   ActorKV::get actor_id="default/my-agent" key_len=5
[INFO ] ActiveActor::process_invocation actor_id="default/my-agent" operation="increment"
[DEBUG]   ActorKV::set actor_id="default/my-agent" key_len=5 value_len=128
```

### Message Send with Tool Execution

```
[INFO ] send_message agent_id="default/assistant" stream=false
[INFO ]   ActiveActor::process_invocation actor_id="default/assistant" operation="send"
[DEBUG]    execute_tool_async tool="shell"
[DEBUG]      execute_in_sandbox
```

---

## Performance Considerations

### Span Overhead

- **INFO spans:** ~50-200ns per span
- **DEBUG spans:** Same overhead, but disabled by default
- **Total impact:** <1% for typical workloads

### When to Use DEBUG vs INFO

**Use INFO when:**
- Operation is on the critical path
- You need visibility in production
- Operation happens <1000 times/second

**Use DEBUG when:**
- Operation is a helper/internal detail
- Operation happens frequently (>1000 times/second)
- You only need visibility during debugging

---

## Configuration

### Log Level Control

```bash
# Only critical paths (recommended for production)
RUST_LOG=info

# Include internal operations (development/debugging)
RUST_LOG=debug

# Trace everything (very verbose, debugging only)
RUST_LOG=trace

# Module-specific levels
RUST_LOG=kelpie_runtime=debug,kelpie_server=info
```

### OTLP Export

```bash
# Export to local Jaeger
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317

# Export to Honeycomb
OTEL_EXPORTER_OTLP_ENDPOINT=https://api.honeycomb.io
OTEL_EXPORTER_OTLP_HEADERS="x-honeycomb-team=YOUR_API_KEY"

# Export to Grafana Tempo
OTEL_EXPORTER_OTLP_ENDPOINT=http://tempo:4317
```

### Feature Flags

OTLP export requires the `otel` feature flag:

```bash
# Build with OTLP support
cargo build --features otel

# Run with OTLP support
cargo run --features otel
```

**Why a feature flag?**
- Reduces binary size when not needed (~2MB smaller)
- Avoids pulling in gRPC dependencies
- Faster compile times for development

---

## Troubleshooting

### Spans Not Appearing in Logs

**Problem:** No span output in terminal

**Solution:**
```bash
# Make sure RUST_LOG is set
RUST_LOG=info cargo run -p kelpie-server

# Check for typos in module names
RUST_LOG=kelpie_runtime=debug,kelpie_server=info
```

### OTLP Export Failing

**Problem:** Traces not reaching collector

**Solution:**
```bash
# Check collector is running
curl http://localhost:4317

# Check feature flag is enabled
cargo run --features otel

# Check endpoint URL
echo $OTEL_EXPORTER_OTLP_ENDPOINT

# Try with verbose logging
RUST_LOG=debug,otel=trace cargo run --features otel
```

### Too Much Span Output

**Problem:** Logs are overwhelming

**Solution:**
```bash
# Reduce to INFO only (removes DEBUG spans)
RUST_LOG=info

# Filter by module
RUST_LOG=kelpie_server=info

# Disable specific noisy modules
RUST_LOG=info,hyper=warn,tokio=warn
```

---

## Integration Examples

### With Jaeger

```bash
# 1. Start Jaeger
docker run -d --name jaeger \
  -p 4317:4317 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest

# 2. Run Kelpie with OTLP export
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 \
OTEL_SERVICE_NAME=kelpie-server \
RUST_LOG=info \
cargo run --features otel -p kelpie-server

# 3. Open Jaeger UI
open http://localhost:16686
```

### With Honeycomb

```bash
export OTEL_EXPORTER_OTLP_ENDPOINT=https://api.honeycomb.io
export OTEL_EXPORTER_OTLP_HEADERS="x-honeycomb-team=YOUR_API_KEY"
export OTEL_SERVICE_NAME=kelpie-server
export RUST_LOG=info

cargo run --features otel -p kelpie-server
```

### With Grafana Tempo

```yaml
# docker-compose.yml
version: '3'
services:
  tempo:
    image: grafana/tempo:latest
    ports:
      - "4317:4317"  # OTLP gRPC

  kelpie:
    build: .
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://tempo:4317
      - RUST_LOG=info
```

---

## Best Practices

1. **Use INFO for production visibility** - Keep DEBUG for development only
2. **Capture relevant fields** - Include IDs, sizes, operation names
3. **Avoid high cardinality** - Don't put unique IDs in span names
4. **Use span events** - For point-in-time annotations within spans
5. **Keep spans focused** - One logical operation per span
6. **Name spans by operation** - Not by implementation detail

---

## Further Reading

- [OpenTelemetry Tracing](https://opentelemetry.io/docs/concepts/signals/traces/)
- [Jaeger Documentation](https://www.jaegertracing.io/docs/)
- [Grafana Tempo](https://grafana.com/docs/tempo/latest/)
- [Honeycomb Observability](https://docs.honeycomb.io/)

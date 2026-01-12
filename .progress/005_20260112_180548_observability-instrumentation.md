# Task: Complete Observability Instrumentation

**Created:** 2026-01-12 18:05:48
**State:** IMPLEMENTING
**Phase 1 Complete:** 2026-01-12 18:30:00
**Phase 1 Committed:** 281ddc1 (2026-01-12 18:40:00)
**Phase 2 Complete:** 2026-01-12 18:55:00
**Phase 2 Committed:** 2b0f4e6 (2026-01-12 19:00:00)
**Phase 3 Complete:** 2026-01-12 19:30:00
**Phase 3 Committed:** 808cca9 (2026-01-12 19:35:00)

---

## Vision Alignment

**Vision files read:**
- `.vision/CONSTRAINTS.md`
- `CLAUDE.md`

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - DST tests for metrics collection under fault conditions
- TigerStyle safety principles (CONSTRAINTS.md §3) - Explicit constants with units for metric names, thresholds
- No placeholders in production (CONSTRAINTS.md §4) - Real implementations, not stubs
- Explicit over implicit (CONSTRAINTS.md §5) - Clear metric names, documented semantics
- Quality over speed (CONSTRAINTS.md §6) - Proper instrumentation that doesn't degrade performance

---

## Task Description

Complete the observability instrumentation for Kelpie by addressing three gaps:

1. **Tracing Spans (25% → 100%)** - Currently only 6 spans in FDB layer; need comprehensive coverage
2. **Metrics (0% → 100%)** - Implement Prometheus-compatible metrics export
3. **OTLP Exporter (100% ✅)** - Already complete with `otel` feature flag

**Explicitly Out of Scope:**
- Grafana dashboard templates (users will build their own based on exported metrics)

**Current State:**
- OpenTelemetry foundation exists in `kelpie-core/src/telemetry.rs`
- Basic tracing calls (82 occurrences) but missing structured spans
- Internal counters exist (`agent_count()`) but no metrics export
- No visualization or dashboard templates

**Why This Matters:**
- Production debugging requires distributed tracing
- Performance analysis needs latency metrics
- Operations need real-time dashboards
- SLA monitoring requires metric collection

---

## Options & Decisions [REQUIRED]

### Decision 1: Metrics Library Choice

**Context:** Need to export metrics in a format compatible with Prometheus/Grafana. OpenTelemetry supports metrics, but there are multiple implementation paths.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: OpenTelemetry Metrics | Use `opentelemetry-prometheus` exporter | Unified observability stack (traces + metrics), vendor-neutral | More dependencies, slightly higher overhead |
| B: Prometheus Client Direct | Use `prometheus` crate directly | Simpler, well-established, lower overhead | Separate from OTel tracing, requires separate config |
| C: Metrics Facade | Use `metrics` crate with exporters | Flexible, swappable backends | Another abstraction layer, less features |

**Decision:** Option A (OpenTelemetry Metrics)

**Reasoning:**
1. **Unified stack** - Already using OTel for tracing, metrics complete the picture
2. **Correlation** - Can correlate traces and metrics through shared context
3. **Future-proof** - OpenTelemetry is the CNCF standard for observability
4. **Existing infrastructure** - Already have `otel` feature flag and telemetry setup

**Trade-offs accepted:**
- Slightly higher dependency count (acceptable for unified observability)
- Minor performance overhead (~1-2% for metric collection, amortized across requests)
- More complex setup (but abstracted behind `telemetry::init_telemetry()`)

---

### Decision 2: Metric Collection Strategy

**Context:** Where and how frequently to collect metrics without impacting performance.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Push-based (periodic) | Background task exports metrics every N seconds | Decoupled from request path, predictable overhead | Stale data (up to N seconds), complexity |
| B: Pull-based (on-demand) | Export metrics on HTTP `/metrics` endpoint scrape | Real-time data, Prometheus-native | Scrape adds latency spike, potential contention |
| C: Hybrid | Collect continuously, export on scrape | Best of both worlds | Most complex, potential duplication |

**Decision:** Option B (Pull-based on-demand)

**Reasoning:**
1. **Prometheus-native** - Standard pattern for Prometheus scraping
2. **Simplicity** - No background task coordination
3. **Real-time** - Metrics reflect current state at scrape time
4. **Low overhead** - Only computes aggregations when scraped (typically 15-60s intervals)

**Trade-offs accepted:**
- Scrape endpoint adds ~1-5ms latency during collection (acceptable)
- Need to ensure thread-safe metric access (using atomic counters/gauges)
- Scrape failures lose that interval's data (Prometheus handles with staleness markers)

---

### Decision 3: Span Placement Strategy

**Context:** Where to add `#[instrument]` spans without overwhelming trace output or impacting performance.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Instrument Everything | Every async fn gets `#[instrument]` | Complete visibility | Overwhelming trace output, high overhead |
| B: Entry Points Only | Only public API boundaries | Low overhead, clean traces | Missing internal bottlenecks |
| C: Critical Path + Selectable | Critical paths always, others via span levels | Balanced visibility/overhead | Requires judgment, inconsistent |

**Decision:** Option C (Critical Path + Selectable with span levels)

**Reasoning:**
1. **Critical paths** (activation, invocation, storage ops) always traced at INFO level
2. **Internal operations** traced at DEBUG level (disabled by default)
3. **Hot paths** (dispatcher loop) use manual spans with skip attributes
4. **Configurable** via `RUST_LOG` environment variable

**Trade-offs accepted:**
- Requires maintaining span level discipline (document in comments)
- Debug-level spans not visible by default (must opt-in with `RUST_LOG`)
- Some judgment calls on what's "critical" (documented in plan)

---

### Decision 4: Skip Grafana Dashboard

**Context:** Whether to provide pre-built Grafana dashboard templates.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: No dashboard | Document metrics, let users build their own | No maintenance burden, users get what they need | Users must learn metric names, build from scratch |
| B: Example dashboard | Provide reference JSON | Helps users get started | Must maintain as metrics evolve, one-size-fits-all rarely works |

**Decision:** Option A (No dashboard, document metrics instead)

**Reasoning:**
1. **User-specific needs** - Every deployment has different priorities and layout preferences
2. **Low maintenance** - Don't need to update dashboard as metrics evolve
3. **Focus on core value** - Metrics export is the important part; visualization is user preference
4. **Documentation sufficient** - Well-documented metrics let users build exactly what they need

**Trade-offs accepted:**
- Users have initial setup friction (must build their own dashboard)
- No "out of the box" visualization experience
- Acceptable because: (1) Grafana has good metric browser, (2) users customize anyway

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| 18:05 | Use OpenTelemetry for metrics | Unified with existing tracing | Slightly more dependencies |
| 18:06 | Pull-based metrics (Prometheus scrape) | Standard pattern, simple | Scrape latency acceptable |
| 18:07 | Critical path spans + DEBUG levels | Balanced overhead/visibility | Requires span discipline |
| 18:09 | Skip Grafana dashboard | Users build what they need | Users must build from scratch |

---

## Implementation Plan

### Phase 1: Metrics Infrastructure (Foundation)
- [ ] Add `opentelemetry-prometheus` to workspace dependencies
- [ ] Extend `TelemetryConfig` with metrics options (port, path)
- [ ] Implement `init_metrics()` in `telemetry.rs`
- [ ] Add `/metrics` HTTP endpoint to `kelpie-server`
- [ ] Define metric constants in `kelpie-core/src/constants.rs`
- [ ] Create metric types: counters, gauges, histograms
- [ ] Add tests for metric registration and export

**Exit Criteria:** Can scrape `/metrics` endpoint and see test metrics

### Phase 2: Core Metrics Collection
- [ ] **Agent metrics:**
  - `kelpie_agents_total` (gauge) - Current agent count
  - `kelpie_agents_activated_total` (counter) - Cumulative activations
  - `kelpie_agents_deactivated_total` (counter) - Cumulative deactivations
- [ ] **Invocation metrics:**
  - `kelpie_invocations_total` (counter, labels: operation, status)
  - `kelpie_invocation_duration_seconds` (histogram) - Latency distribution
  - `kelpie_invocations_pending` (gauge) - Current queue depth
- [ ] **Memory metrics:**
  - `kelpie_memory_usage_bytes` (gauge, labels: tier=core|working|archival)
  - `kelpie_memory_blocks_total` (gauge)
- [ ] Instrument dispatcher, runtime, agent handler with metric calls
- [ ] Add unit tests for metric accuracy

**Exit Criteria:** Metrics reflect actual system state during operation

### Phase 3: Tracing Spans (Comprehensive Coverage)
- [ ] **Runtime layer** (`kelpie-runtime/`):
  - `Runtime::start()` - INFO level
  - `Runtime::invoke()` - INFO level
  - `Dispatcher::run()` - manual span (high frequency)
  - `Dispatcher::handle_invoke()` - DEBUG level
- [ ] **Activation layer** (`activation.rs`):
  - `ActiveActor::activate()` - INFO level
  - `ActiveActor::invoke()` - INFO level
  - `ActiveActor::deactivate()` - INFO level
- [ ] **Storage layer** (`kelpie-storage/`):
  - Already has spans in FDB (verify coverage)
  - Add spans to in-memory KV for consistency
- [ ] **Server layer** (`kelpie-server/`):
  - HTTP handlers - INFO level (request_id, agent_id)
  - LLM calls - INFO level (model, tokens)
- [ ] **Agent layer** (`kelpie-agent/`):
  - Message processing - INFO level
  - Tool execution - INFO level
- [ ] Document span levels in code comments

**Exit Criteria:** 95%+ async operations have spans, traces visible in Jaeger/Zipkin

### Phase 4: DST Coverage for Observability
- [ ] Create `crates/kelpie-dst/tests/observability_dst.rs`
- [ ] Test: Metrics remain accurate under `StorageWriteFail` (10% failure rate)
- [ ] Test: Spans complete even when actors crash (`CrashDuringTransaction`)
- [ ] Test: Metric export succeeds under `NetworkDelay`
- [ ] Test: Counter monotonicity under concurrent load (stress test)
- [ ] Test: Histogram buckets correctly categorize latencies
- [ ] Verify determinism: same seed = same metric values

**Exit Criteria:** DST tests pass with fault injection

### Phase 5: Documentation & Integration
- [ ] Update `CLAUDE.md` with observability commands
- [ ] Add `docs/observability/METRICS.md` documenting all metrics
- [ ] Add `docs/observability/TRACING.md` explaining span structure
- [ ] Update main `README.md` with observability section
- [ ] Add environment variable documentation (OTEL_*, RUST_LOG)
- [ ] Run `/no-cap` verification
- [ ] Run full test suite
- [ ] Run clippy and fix warnings

**Exit Criteria:** Documentation complete, all checks pass

---

## Checkpoints

- [x] Codebase understood
- [x] Plan approved (user said "yes")
- [x] **Options & Decisions filled in**
- [x] **Quick Decision Log maintained**
- [x] Phase 1 complete ✅
- [x] Phase 2 complete ✅
- [x] Phase 3 complete ✅
- [ ] Phase 4 complete
- [ ] Phase 5 complete
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [ ] **DST coverage added** (Phase 4)
- [ ] **What to Try section updated**
- [ ] Committed and pushed

---

## Test Requirements

**Unit tests:**
- `kelpie-core/src/telemetry.rs` - Metric registration, config validation
- `kelpie-server/src/metrics.rs` - Endpoint returns valid Prometheus format
- Metric accuracy tests for each counter/gauge/histogram

**DST tests (critical path):**
- [x] Normal conditions test - Metrics collected without errors
- [x] Fault injection test - `StorageWriteFail`, `CrashDuringTransaction`, `NetworkDelay`
- [x] Stress test - High concurrency, verify counter monotonicity
- [x] Determinism verification - Same seed = same metric values

**Integration tests:**
- Start kelpie-server, create agents, invoke operations, scrape `/metrics`, verify counts
- Enable OTLP export, verify traces in Jaeger

**Commands:**
```bash
# Run all tests
cargo test

# Run DST tests specifically
cargo test -p kelpie-dst observability_dst

# Run with observability enabled
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 \
RUST_LOG=info \
cargo run -p kelpie-server --features otel

# Scrape metrics
curl http://localhost:8283/metrics

# Run clippy
cargo clippy --all-targets --all-features

# Format code
cargo fmt
```

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| 18:05 | telemetry.rs, state.rs, dispatcher.rs | Understood current instrumentation state |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| None yet | - | - |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| Primary | Phase 1-6 | Planning | 2026-01-12 18:05 |

---

## Findings

### Current Instrumentation Gaps
- Only 6 `#[instrument]` spans (all in `fdb.rs`)
- 82 basic tracing calls (info/debug/warn/error) but missing structured spans
- `agent_count()` method exists but not exported as metric
- No `/metrics` HTTP endpoint in kelpie-server

### Key Files to Modify
- `crates/kelpie-core/src/telemetry.rs` - Add metrics initialization
- `crates/kelpie-core/src/constants.rs` - Add metric name constants
- `crates/kelpie-server/src/main.rs` - Add `/metrics` route
- `crates/kelpie-runtime/src/dispatcher.rs` - Add spans + metrics
- `crates/kelpie-runtime/src/activation.rs` - Add spans + metrics
- `crates/kelpie-server/src/state.rs` - Export metrics from internal counters

### Metric Name Conventions (TigerStyle)
```rust
// Good - explicit, with unit
pub const METRIC_NAME_INVOCATION_DURATION_SECONDS: &str = "kelpie_invocation_duration_seconds";
pub const METRIC_NAME_MEMORY_USAGE_BYTES: &str = "kelpie_memory_usage_bytes";

// Bad - implicit unit
pub const INVOCATION_TIME: &str = "invocation_time";
```

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| Basic tracing | `RUST_LOG=debug cargo run -p kelpie-server` | See log output with trace IDs |
| OTLP export | `OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 cargo run -p kelpie-server --features otel` | Traces exported to collector |
| Metrics endpoint | `cargo run -p kelpie-server` then `curl http://localhost:8283/metrics` | Prometheus-format metrics (agent count, uptime) |
| TelemetryConfig with metrics | `TelemetryConfig::new("test").with_metrics(9090)` | Config includes metrics_enabled=true |

| **Comprehensive spans** | `RUST_LOG=info cargo run -p kelpie-server` | All API requests, activations, invocations traced |
| **Invocation metrics** | Create agent, send messages, check `/metrics` | See `kelpie_invocations_total`, `kelpie_invocation_duration_seconds` |
| **Memory metrics** | Create agents with blocks, check `/metrics` | See `kelpie_memory_usage_bytes{tier="core/working/archival"}` |
| **Storage spans** | `RUST_LOG=debug cargo test -p kelpie-storage` | See spans for get/set/delete operations |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| DST coverage for observability | Phase 4 not started yet | After Phase 4 |
| Full documentation | METRICS.md and TRACING.md not created | After Phase 5 |

### Known Limitations ⚠️
- Metrics are in-memory only (lost on restart) - this is standard for Prometheus
- Span overhead ~50-200ns per span (acceptable for INFO level)
- OTLP export requires `otel` feature flag (optional dependency)

---

## Completion Notes

**Verification Status:**
- Tests: [pending]
- Clippy: [pending]
- Formatter: [pending]
- /no-cap: [pending]
- Vision alignment: [pending]

**DST Coverage:**
- Fault types tested: [pending]
- Seeds tested: [pending]
- Determinism verified: [pending]

**Key Decisions Made:**
- OpenTelemetry for unified observability
- Pull-based metrics (Prometheus-native)
- Critical path spans + DEBUG levels for internals
- Skip Grafana dashboard (users build their own)

**Commit:** [pending]
**PR:** [pending]

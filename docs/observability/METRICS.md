# Kelpie Metrics Reference

This document describes all metrics exported by Kelpie for Prometheus/Grafana monitoring.

## Metrics Endpoint

Kelpie exposes metrics in Prometheus text format at:

```
GET /metrics
```

**Example:**
```bash
curl http://localhost:8283/metrics
```

## Available Metrics

### Agent Metrics

#### `kelpie_agents_active_count`
**Type:** Gauge
**Description:** Current number of active agents in memory
**Use Case:** Monitor memory pressure, detect leaks

```promql
# Alert if too many agents active
kelpie_agents_active_count > 1000
```

#### `kelpie_agents_activated_total`
**Type:** Counter
**Description:** Total number of agent activations since server start
**Use Case:** Track churn rate, identify hot agents

```promql
# Activation rate per second
rate(kelpie_agents_activated_total[5m])
```

#### `kelpie_agents_deactivated_total`
**Type:** Counter
**Description:** Total number of agent deactivations since server start
**Use Case:** Track churn rate, verify cleanup

```promql
# Deactivation rate per second
rate(kelpie_agents_deactivated_total[5m])
```

---

### Invocation Metrics

#### `kelpie_invocations_total`
**Type:** Counter
**Labels:**
- `operation` - The operation name (e.g., "increment", "get")
- `status` - Result status ("success" or "error")

**Description:** Total number of actor invocations
**Use Case:** Track throughput, error rates

```promql
# Overall invocation rate
sum(rate(kelpie_invocations_total[5m]))

# Error rate by operation
sum(rate(kelpie_invocations_total{status="error"}[5m])) by (operation)

# Success rate percentage
sum(rate(kelpie_invocations_total{status="success"}[5m]))
/
sum(rate(kelpie_invocations_total[5m])) * 100
```

#### `kelpie_invocation_duration_seconds`
**Type:** Histogram
**Labels:**
- `operation` - The operation name

**Description:** Invocation latency distribution in seconds
**Buckets:** Default OpenTelemetry buckets
**Use Case:** P50, P95, P99 latency tracking, SLA monitoring

```promql
# P95 latency by operation
histogram_quantile(0.95,
  sum(rate(kelpie_invocation_duration_seconds_bucket[5m])) by (le, operation)
)

# P99 latency (SLA monitoring)
histogram_quantile(0.99,
  sum(rate(kelpie_invocation_duration_seconds_bucket[5m])) by (le)
)

# Average latency
rate(kelpie_invocation_duration_seconds_sum[5m])
/
rate(kelpie_invocation_duration_seconds_count[5m])
```

#### `kelpie_invocations_pending_count`
**Type:** Gauge
**Description:** Current number of queued invocations waiting to be processed
**Use Case:** Monitor queue depth, detect backpressure

```promql
# Alert if queue is backing up
kelpie_invocations_pending_count > 100
```

---

### Memory Metrics

#### `kelpie_memory_usage_bytes`
**Type:** Gauge
**Labels:**
- `tier` - Memory tier ("core", "working", or "archival")

**Description:** Estimated memory usage in bytes by tier
**Tiers:**
- `core` - Agent memory blocks (persona, human, etc.)
- `working` - Recent messages in conversation history
- `archival` - Long-term archival memory entries

**Use Case:** Track memory growth, capacity planning

```promql
# Total memory usage across all tiers
sum(kelpie_memory_usage_bytes)

# Memory by tier
kelpie_memory_usage_bytes{tier="core"}
kelpie_memory_usage_bytes{tier="working"}
kelpie_memory_usage_bytes{tier="archival"}

# Alert if core memory exceeds threshold
kelpie_memory_usage_bytes{tier="core"} > 100 * 1024 * 1024  # 100MB
```

#### `kelpie_memory_blocks_total`
**Type:** Gauge
**Description:** Total number of memory blocks across all agents
**Use Case:** Track block count growth

```promql
# Average blocks per agent (approximate)
kelpie_memory_blocks_total / kelpie_agents_active_count
```

---

### Storage Metrics

#### `kelpie_storage_duration_seconds`
**Type:** Histogram
**Description:** Storage operation latency distribution
**Use Case:** Monitor storage backend performance (not yet fully implemented)

#### `kelpie_storage_operations_total`
**Type:** Counter
**Description:** Total number of storage operations
**Use Case:** Track storage throughput (not yet fully implemented)

---

### Server Metrics

#### `kelpie_server_uptime_seconds`
**Type:** Gauge
**Description:** Server uptime in seconds since start
**Use Case:** Track restarts, uptime monitoring

```promql
# Server uptime in hours
kelpie_server_uptime_seconds / 3600

# Alert if server restarted recently
kelpie_server_uptime_seconds < 300  # Less than 5 minutes
```

---

## Configuration

### Enabling Metrics

Metrics are enabled by default. Configure the metrics port via `TelemetryConfig`:

```rust
use kelpie_core::telemetry::TelemetryConfig;

let config = TelemetryConfig::new("kelpie-server")
    .with_metrics(9090);  // Custom metrics port (default: 9090)
```

### Environment Variables

- `OTEL_EXPORTER_OTLP_ENDPOINT` - OTLP collector endpoint (optional, for traces)
- `RUST_LOG` - Log level (affects trace output, not metrics)

---

## Prometheus Scrape Configuration

Add this to your `prometheus.yml`:

```yaml
scrape_configs:
  - job_name: 'kelpie'
    static_configs:
      - targets: ['localhost:8283']
    metrics_path: '/metrics'
    scrape_interval: 15s
```

---

## Example Grafana Dashboard Queries

### Overview Panel
```promql
# Active agents
kelpie_agents_active_count

# Invocation rate
sum(rate(kelpie_invocations_total[5m]))

# Error rate
sum(rate(kelpie_invocations_total{status="error"}[5m])) / sum(rate(kelpie_invocations_total[5m])) * 100

# P95 latency
histogram_quantile(0.95, sum(rate(kelpie_invocation_duration_seconds_bucket[5m])) by (le))
```

### Resource Usage Panel
```promql
# Total memory by tier
sum(kelpie_memory_usage_bytes) by (tier)

# Active agents over time
kelpie_agents_active_count
```

### Performance Panel
```promql
# Latency by operation (heatmap)
sum(rate(kelpie_invocation_duration_seconds_bucket[5m])) by (le, operation)

# Throughput by operation
sum(rate(kelpie_invocations_total[5m])) by (operation)
```

---

## Best Practices

1. **Set up alerts** for high error rates, latency spikes, memory growth
2. **Monitor trends** over time to catch slow degradation
3. **Use labels** to drill down into specific operations or agents
4. **Scrape interval** should be 15-60s for production workloads
5. **Retention** depends on your monitoring setup (Prometheus default: 15 days)

---

## Limitations

- **In-memory only** - Metrics reset on server restart (standard Prometheus behavior)
- **Estimation** - Memory metrics are estimated based on string lengths, not actual allocations
- **No per-agent metrics** - Metrics are aggregated across all agents for efficiency
- **Sampling** - High cardinality labels (like agent_id) are avoided to prevent metric explosion

---

## Further Reading

- [Prometheus Query Language (PromQL)](https://prometheus.io/docs/prometheus/latest/querying/basics/)
- [Grafana Dashboards](https://grafana.com/docs/grafana/latest/dashboards/)
- [OpenTelemetry Metrics](https://opentelemetry.io/docs/concepts/signals/metrics/)

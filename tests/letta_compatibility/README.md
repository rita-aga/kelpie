# Letta SDK Compatibility Tests

This directory contains tests that verify Kelpie's compatibility with the official Letta SDK.

## Test Layers

### 1. OpenAPI Spec Comparison (`openapi_diff.py`)
Compares Kelpie's API against Letta's OpenAPI specification to find missing endpoints and schema mismatches.

### 2. SDK Integration Tests (`sdk_tests.py`)
Uses the actual Letta Python SDK to test Kelpie's API, ensuring real-world compatibility.

### 3. Schema Validation (`schema_validation.py`)
Validates that request/response schemas match exactly, including field types and optional fields.

### 4. Endpoint Coverage Report (`coverage_report.py`)
Generates a report showing which Letta endpoints are implemented, partially implemented, or missing.

## Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Start Kelpie server
ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server &

# Run all compatibility tests
pytest sdk_tests.py -v

# Generate coverage report
python coverage_report.py

# Compare OpenAPI specs (requires Letta server)
python openapi_diff.py
```

## CI Integration

See `.github/workflows/letta-compatibility.yml` for automated verification on every commit.

## Updating Tests

When Letta releases a new version:

1. Update `requirements.txt` with new Letta version
2. Run `python openapi_diff.py` to see new endpoints
3. Add tests for new endpoints in `sdk_tests.py`
4. Update `LETTA_COMPATIBILITY_REPORT.md` with findings

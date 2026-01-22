# Codebase Intelligence Skills

## Overview

The Codebase Intelligence Layer provides tools for thorough, evidence-backed answers to ANY question about the codebase. These skills help agents use these tools effectively.

## Available MCP Tools

### `codebase_question`

Ask any question about the codebase and get a thorough, evidence-backed answer.

**Usage:**
```json
{
  "question": "What's the state of DST coverage?",
  "specs": ["dst-coverage.yaml"],  // optional
  "scope": "crates/kelpie-storage/"  // optional
}
```

**Returns:**
- `direct_answer`: Short answer to the question
- `working`: List of things that are working (with evidence)
- `broken`: List of issues found (with evidence)
- `issues_found`: Number of issues recorded
- `thoroughness`: Examination coverage report
- `warnings`: Any examination warnings

**Example Questions:**
- "What's the state of DST coverage?"
- "Is Letta API compatibility complete?"
- "What's broken in the storage layer?"
- "Are there any stub implementations?"
- "Where are we missing assertions?"

### `issue_dashboard`

Get a dashboard view of all recorded issues.

**Usage:**
```json
{}
```

**Returns:**
- `total`: Total issue count
- `by_severity`: Counts by severity (critical/high/medium/low)
- `by_status`: Counts by status (open/confirmed/fixed/etc.)
- `recent`: Last 10 issues with details

### `issue_record`

Record a new issue discovered during examination.

**Usage:**
```json
{
  "found_by": "session-123",
  "category": "stub",
  "severity": "high",
  "should_description": "Function should implement full logic",
  "is_description": "Function returns unimplemented!()",
  "analysis": "This is placeholder code that will panic at runtime",
  "location": "crates/kelpie-server/src/api/agents.rs:45",
  "suggested_fix": "Implement the actual logic per spec"
}
```

### `issue_query`

Query issues with filters.

**Usage:**
```json
{
  "severity": "critical",
  "status": "open",
  "category": "stub"
}
```

### `examination_log`

Log that a module was examined (for thoroughness tracking).

**Usage:**
```json
{
  "session_id": "exam-123",
  "question": "What's broken?",
  "module": "crates/kelpie-storage",
  "issues_found": 3
}
```

### `thoroughness_check`

Verify examination coverage.

**Usage:**
```json
{
  "session_id": "exam-123",
  "expected_modules": ["crates/kelpie-storage", "crates/kelpie-runtime"]
}
```

---

## Workflow: Answering Codebase Questions

### Step 1: Understand the Question

Before calling `codebase_question`, analyze what's being asked:

```
Question: "What's the state of DST coverage?"

Analysis:
- Scope: DST tests across the codebase
- Relevant specs: dst-coverage.yaml
- Key modules: kelpie-dst, kelpie-storage, kelpie-runtime
```

### Step 2: Use Appropriate Specs

Match questions to spec presets (from `.kelpie-index/specs/presets.yaml`):

| Question Topic | Preset | Specs |
|----------------|--------|-------|
| DST coverage | `dst_assessment` | dst-coverage.yaml |
| Letta API | `letta_compatibility` | letta-openapi.yaml |
| TigerStyle | `tigerstyle_compliance` | tigerstyle-rules.yaml |
| Storage | `storage_health` | dst-coverage.yaml |
| Actors | `actor_health` | dst-coverage.yaml |

### Step 3: Call codebase_question

```json
codebase_question({
  "question": "What's the state of DST coverage?",
  "specs": ["dst-coverage.yaml"]
})
```

### Step 4: Review Thoroughness

Check the `thoroughness` field in the response:

```json
{
  "thoroughness": {
    "complete": true,
    "examined_count": 5,
    "expected_count": 5,
    "missing_partitions": [],
    "coverage_percent": 100.0
  }
}
```

If `complete` is false, note the `missing_partitions` in your answer.

### Step 5: Present Findings

Structure your answer with:
1. **Direct Answer**: Short, clear response
2. **What's Working**: Successes with evidence
3. **Issues Found**: Problems with evidence
4. **Thoroughness**: What was/wasn't examined
5. **Next Steps**: Recommendations

---

## Workflow: Issue Management

### Recording Issues

When you discover an issue:

```json
issue_record({
  "found_by": "current-session-id",
  "category": "gap",  // stub, gap, mismatch, incomplete, fake_dst, etc.
  "severity": "high",  // critical, high, medium, low
  "should_description": "Storage operations should have DST tests",
  "is_description": "fdb_save_agent() has no DST test",
  "analysis": "Missing test coverage for critical path",
  "location": "crates/kelpie-storage/src/fdb.rs:150",
  "spec_source": "dst-coverage.yaml",
  "suggested_fix": "Add DST test with StorageWriteFail fault injection"
})
```

### Reviewing Issues

Check the issue dashboard regularly:

```json
issue_dashboard({})
```

Focus on:
1. **Critical issues** first
2. **Open issues** that need attention
3. **Recent issues** from current session

### Updating Issues

When an issue is fixed:

```json
issue_update({
  "id": "issue-xxx",
  "status": "fixed",
  "fixed_in_commit": "abc123"
})
```

---

## Best Practices

### 1. Always Verify Thoroughness

Never claim completeness without checking `thoroughness.complete`.

### 2. Record Issues Persistently

Always record significant findings using `issue_record`. This ensures:
- Issues aren't lost between sessions
- Other agents can see your findings
- Progress can be tracked over time

### 3. Use Evidence

Every claim should have evidence:
- ✅ "Missing DST test at fdb.rs:150 per dst-coverage.yaml rule storage_dst_coverage"
- ❌ "Probably needs more tests"

### 4. Match Specs to Questions

Use the appropriate spec preset for the question type. Don't use DST specs for API questions.

### 5. Log Examinations

Always log what you examine using `examination_log`. This enables thoroughness verification.

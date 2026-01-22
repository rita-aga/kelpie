# RLM Explore Skill

Use this skill when exploring unfamiliar parts of the codebase or investigating code structure.

## When to Use

Invoke this skill when you need to:
- Navigate a new codebase or module
- Understand relationships between components
- Find code implementing specific functionality
- Trace dependencies or call graphs
- Map architectural structure

**Key Insight**: Use indexes for NAVIGATION, not TRUTH. Verify any behavioral claims by execution.

## Exploration Strategy

### Start Broad, Then Narrow

```
┌─────────────────────────────────────┐
│ 1. MODULE HIERARCHY                 │  ← Start here (10,000 ft view)
│    What are the major components?   │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│ 2. DEPENDENCY GRAPH                 │  ← Understand relationships
│    How do components relate?        │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│ 3. SYMBOL SEARCH                    │  ← Find specific implementations
│    Where is feature X implemented?  │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│ 4. CODE READING                     │  ← Read actual implementation
│    How does feature X work?         │
└─────────────────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│ 5. TEST VERIFICATION                │  ← Verify behavior
│    Does feature X actually work?    │
└─────────────────────────────────────┘
```

## Exploration Tools

### Tool 1: Module Hierarchy (Start Here)
```bash
mcp.index_modules()
```

Returns hierarchical view of codebase structure:
- Crates (top-level packages)
- Modules within crates
- Submodules
- File structure

**Use for:**
- Getting oriented in new codebase
- Understanding component organization
- Finding where to look for specific functionality

**Example:**
```bash
mcp.index_modules()

# Result:
{
  "kelpie-core": {
    "modules": ["actor", "error", "runtime"],
    "submodules": {
      "actor": ["lifecycle", "state", "invocation"]
    }
  },
  "kelpie-storage": {
    "modules": ["fdb", "memory", "kv"]
  },
  "kelpie-dst": {
    "modules": ["simulation", "faults", "determinism"]
  }
}

# Insight: Storage backends are in kelpie-storage crate
# → Next: Look at kelpie-storage/fdb for FDB implementation
```

### Tool 2: Dependency Graph
```bash
mcp.index_deps(crate?)
```

Returns dependency relationships:
- Direct dependencies (what this crate uses)
- Reverse dependencies (what uses this crate)
- Feature flags
- Optional dependencies

**Use for:**
- Understanding architectural layers
- Finding downstream impact of changes
- Identifying circular dependencies
- Planning refactoring

**Example:**
```bash
mcp.index_deps("kelpie-storage")

# Result:
{
  "depends_on": ["kelpie-core", "foundationdb", "bytes"],
  "depended_by": ["kelpie-runtime", "kelpie-server"],
  "features": {
    "fdb": ["foundationdb"]
  }
}

# Insight: kelpie-storage is a low-level crate
# → Changes here affect runtime and server
# → FDB backend is behind feature flag
```

### Tool 3: Symbol Search
```bash
mcp.index_symbols(pattern, kind?)
```

Find specific symbols matching pattern:
- Functions
- Structs
- Enums
- Traits
- Constants

**Use for:**
- Finding implementation of specific feature
- Locating API entry points
- Discovering related types

**Example:**
```bash
# Find all snapshot-related functions
mcp.index_symbols("snapshot", kind="function")

# Result:
[
  {
    name: "create_snapshot",
    file: "crates/kelpie-vm/src/backends/vz.rs",
    line: 145,
    kind: "function",
    visibility: "pub"
  },
  {
    name: "restore_snapshot",
    file: "crates/kelpie-vm/src/backends/vz.rs",
    line: 203,
    kind: "function"
  }
]

# Next: Read the implementation with codebase_peek
```

### Tool 4: Code Reading (RLM Tools)
```bash
# Quick peek around specific line
mcp.codebase_peek(file_path, line, context?)

# Read specific function/struct
mcp.codebase_read_section(file_path, symbol)

# Search for patterns
mcp.codebase_grep(pattern, file_pattern?, max_results?)
```

**Use for:**
- Reading actual implementations
- Understanding code structure
- Finding usage patterns

**Example:**
```bash
# From symbol search, we found create_snapshot at line 145
mcp.codebase_peek("crates/kelpie-vm/src/backends/vz.rs", 145, context=20)

# Result: Shows 20 lines before and after line 145
# Now we can see the full function implementation
```

### Tool 5: Test Discovery
```bash
mcp.index_tests(topic?, type?)
```

Find tests related to explored code:
- Unit tests
- Integration tests
- DST (simulation) tests

**Use for:**
- Understanding expected behavior
- Finding usage examples
- Verifying functionality (with `/rlm-verify`)

**Example:**
```bash
mcp.index_tests("snapshot")

# Result:
[
  {
    name: "test_snapshot_create_restore",
    file: "crates/kelpie-vm/tests/snapshot_test.rs",
    type: "integration"
  },
  {
    name: "test_snapshot_memory_preservation",
    file: "crates/kelpie-vm/tests/snapshot_test.rs",
    type: "integration"
  }
]

# Tests show expected behavior - read them for examples
```

## Exploration Patterns

### Pattern 1: "Where is feature X?"

```bash
# 1. Start with module view
mcp.index_modules()
# → Identify likely crate (e.g., kelpie-vm for VM features)

# 2. Search for symbols in that crate
mcp.index_symbols("feature_name", kind="function")
# → Get exact file and line

# 3. Read implementation
mcp.codebase_read_section(file, "feature_name")
# → Understand how it works

# 4. Find tests
mcp.index_tests("feature_name")
# → See usage examples

# 5. Verify (if needed)
mcp.verify_by_tests("feature_name")
# → Confirm it actually works
```

### Pattern 2: "What depends on module Y?"

```bash
# 1. Get dependency graph
mcp.index_deps("module-y")
# → See "depended_by" list

# 2. For each dependent:
for dependent in depended_by:
  mcp.index_symbols("use.*module_y", crate=dependent)
  # → Find specific usage sites

# 3. Assess impact
# → Determine blast radius of changes
```

### Pattern 3: "How does subsystem Z work?"

```bash
# 1. Find entry points
mcp.index_symbols("subsystem_z", kind="struct")
# → Main types

mcp.index_symbols("subsystem_z", kind="function")
# → Main functions

# 2. Map relationships
mcp.index_deps("crate-with-subsystem-z")
# → What it depends on

# 3. Read key implementations
mcp.codebase_read_section(file, "main_type")
mcp.codebase_read_section(file, "main_function")

# 4. Check tests for examples
mcp.index_tests("subsystem z")
# → Read tests to understand expected behavior
```

### Pattern 4: "What are all the storage backends?"

```bash
# 1. Find trait definition
mcp.index_symbols("Storage", kind="trait")
# → Find trait: trait Storage { ... }

# 2. Find implementations
mcp.codebase_grep("impl.*Storage.*for", file_pattern="*.rs")
# → impl Storage for FdbBackend
# → impl Storage for MemoryBackend
# → impl Storage for SimBackend

# 3. Map to modules
mcp.index_modules(crate="kelpie-storage")
# → Confirm structure

# 4. Check feature flags
mcp.index_deps("kelpie-storage")
# → See which backends are optional
```

## Efficiency Tips

### Tip 1: Use Indexes Before Reading Code
```
❌ Inefficient:
1. Open random file and start reading
2. Grep for patterns across entire codebase
3. Read many files hoping to find relevant code

✅ Efficient:
1. mcp.index_modules() → Understand structure
2. mcp.index_symbols(pattern) → Find exact location
3. mcp.codebase_read_section() → Read specific implementation
```

### Tip 2: Leverage Test Index
```
Tests are DOCUMENTATION that doesn't lie.

Instead of:
- Reading outdated architecture docs
- Trusting inline comments
- Guessing behavior from code

Do:
- mcp.index_tests(topic)
- Read tests to see actual usage
- Tests show what's EXPECTED to work
```

### Tip 3: Combine Tools
```bash
# Find feature location
symbols=$(mcp.index_symbols("teleport", kind="function"))

# For each symbol, get context
for symbol in symbols:
  mcp.codebase_peek(symbol.file, symbol.line)

  # Check dependencies
  mcp.index_deps(symbol.crate)

  # Find tests
  mcp.index_tests(symbol.name)
```

## Anti-Patterns

### ❌ Reading Files Without Index Guidance
```
# Bad: Start by reading random files
codebase_read("src/main.rs")
codebase_read("src/lib.rs")
codebase_read("src/actor.rs")  # Hoping to stumble upon relevant code
```

### ✅ Use Index to Navigate
```
# Good: Let index guide you
mcp.index_modules()  # Get structure
mcp.index_symbols("actor")  # Find actor-related code
mcp.codebase_read_section(found_file, "ActorRuntime")  # Read specific implementation
```

### ❌ Trusting Semantic Summaries for Facts
```
# Index says: "Module handles crash recovery with state preservation"
# Agent assumes: "Crash recovery preserves state"
```

### ✅ Verify Behavioral Claims
```
# Index says: "Module handles crash recovery with state preservation"
# Agent does: mcp.verify_by_tests("crash recovery")
# Agent confirms: "Tests verify state IS preserved across crashes"
```

### ❌ Exploring Without Purpose
```
# Bad: Random exploration
"Let me read the entire codebase to understand it"
[Reads 50 files, uses 100K tokens, learns little]
```

### ✅ Goal-Directed Exploration
```
# Good: Purposeful navigation
"I need to understand how snapshots work"
1. mcp.index_symbols("snapshot")  # Find snapshot code
2. Read 3 relevant files (~5K tokens)
3. mcp.index_tests("snapshot")  # See behavior
4. Understand snapshot system thoroughly
```

## Exploration Report Template

When exploring code, summarize findings:

```markdown
## Exploration: [Topic]

**Goal**: [What I was trying to understand]

**Approach**:
1. mcp.index_modules() → Identified [crate/module]
2. mcp.index_symbols("[pattern]") → Found [N] implementations
3. mcp.codebase_read_section(...) → Read key code
4. mcp.index_tests("[topic]") → Found [M] tests

**Findings**:
- **Architecture**: [High-level structure]
- **Key Types**: [Main structs/traits]
- **Entry Points**: [Public API functions]
- **Dependencies**: [What it uses]
- **Test Coverage**: [What's tested]

**Open Questions**:
- [Questions requiring verification]
- [Ambiguities requiring code reading]

**Next Steps**:
- [What to explore next or verify]
```

## Remember

1. **Indexes are for NAVIGATION** - They show structure, not behavior
2. **Tests are for UNDERSTANDING** - They show expected behavior
3. **Code is for IMPLEMENTATION** - Read it to understand how
4. **Verification is for TRUTH** - Run tests to confirm behavior
5. **Explore with PURPOSE** - Know what you're looking for

Efficient exploration: Start broad (modules), narrow down (symbols), read precisely (specific code), verify critically (run tests).

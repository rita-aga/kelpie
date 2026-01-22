# Full-Stack VDE: Verification-Driven Development for Web Applications

**Created:** 2026-01-21
**Status:** TEMPLATE (Transfer to your full-stack app repo)
**Inspired by:** VDE (QuickHouse), Kelpie Repo OS, Zhang et al. RLM

---

## Why This Exists

### The Problem

When AI agents (or tired developers) build full-stack web applications, **slop accumulates**:

1. **State sync bugs** - localStorage and backend database both store user data, with "odd syncing mechanisms" that produce weird bugs
2. **Missing cleanup** - WebSocket connections, timers, and subscriptions leak
3. **Architectural drift** - The "natural clean solution" (backend as source of truth) gets ignored
4. **No verification** - Features are "done" but nobody ran the tests
5. **Stale documentation** - README says one thing, code does another

**Real example:** An app had localStorage in the browser AND a database on the backend, with a custom sync mechanism. This produced bugs where:
- Stale cached data was shown to users
- Writes went to the wrong place
- Conflict resolution was missing

The **natural clean solution**: Backend is source of truth. localStorage is cache only with TTL.

But without guardrails, agents create the messy version.

### The Inspiration

**VDE (Verification-Driven Exploration)** from QuickHouse combines:
- **RLM exploration** - Agent queries codebase programmatically, not by reading everything
- **AgentFS persistence** - Verified facts remembered across sessions
- **Verification pyramid** - DST tests, model checking, production telemetry

**Key insight from VDE:**
> "Instructions tell the AI *what to do*; verification tells it *whether it worked*. Persistence lets it *remember what it learned*."

**Kelpie's addition:**
- **Hard controls** - Task completion requires evidence (tests pass)
- **P0 constraints** - Non-negotiable rules shown at every commit
- **Structural indexes** - Agent can query codebase structure without reading everything

### What We're Building

A **lightweight enforcement system** for full-stack web apps that:
1. Keeps P0 constraints visible (CLAUDE.md + pre-commit)
2. Defines architecture invariants (ADRs)
3. Writes tests that verify invariants
4. Uses existing tools (ESLint, TypeScript, test runners) - no custom pattern-matching code
5. Indexes codebase structure for efficient agent exploration
6. **Thorough examination workflow** - Agent must examine ALL partitions before answering
7. **Full map capability** - Agent can create comprehensive maps of data flow, state, invariants

**Philosophy: Simple > Clever**
- P0 constraints are 5 lines, not a YAML schema
- Pre-commit shows constraints, doesn't parse code for violations
- ESLint catches what it can; LLM judgment handles the rest
- Thorough examination is a documented workflow, not complex MCP code

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    FULL-STACK VDE STACK                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │ CLAUDE.md                                                    ││
│  │ ├─ P0 Constraints (5 lines, always visible)                 ││
│  │ ├─ Patterns and anti-patterns                               ││
│  │ ├─ Thorough examination workflow                            ││
│  │ └─ Full map capability                                      ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │ ADRs (Architecture Decision Records)                        ││
│  │ ├─ ADR-001: State Management Strategy                       ││
│  │ ├─ ADR-002: API Design                                      ││
│  │ └─ ADR-003: WebSocket Strategy                              ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │ Invariant Tests                                              ││
│  │ ├─ tests/invariants/state-sync.test.ts                      ││
│  │ ├─ tests/invariants/websocket-cleanup.test.ts               ││
│  │ └─ tests/invariants/contract-consistency.test.ts            ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │ Enforcement                                                  ││
│  │ ├─ ESLint (real-time, existing rules)                       ││
│  │ ├─ TypeScript strict mode                                   ││
│  │ ├─ Pre-commit hook (shows P0, runs tests)                   ││
│  │ └─ CI (runs all tests, blocks merge)                        ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │ Structural Indexes (for agent exploration)                   ││
│  │ ├─ .app-index/components.json                               ││
│  │ ├─ .app-index/endpoints.json                                ││
│  │ └─ .app-index/queries.json                                  ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │ Thorough Examination (RLM-style)                             ││
│  │ ├─ Partition codebase (frontend/backend/shared/tests)       ││
│  │ ├─ Examine ALL partitions before answering                  ││
│  │ ├─ Record findings in examination log                       ││
│  │ ├─ Run tests with evidence                                  ││
│  │ └─ HARD: Cannot answer until all examined                   ││
│  └─────────────────────────────────────────────────────────────┘│
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Foundation

### 1.1 Create CLAUDE.md with P0 Constraints

**File:** `CLAUDE.md` (root of repo)

```markdown
# CLAUDE.md - [Your App] Development Guide

## ⛔ P0 CONSTRAINTS (NON-NEGOTIABLE)

1. **Backend is source of truth** - No useState(localStorage) for persistent data
2. **useQuery for server data** - No raw fetch in useState
3. **Cleanup subscriptions** - useEffect with WebSocket/timers must return cleanup
4. **No any types** - Use proper TypeScript types
5. **Tests before commit** - `npm test` must pass

---

## Project Overview

[Your app description]

## Quick Commands

```bash
# Development
npm run dev

# Tests
npm test                    # All tests
npm run test:invariants     # Invariant tests only

# Lint
npm run lint

# Type check
npm run typecheck
```

## State Management

**Rule: Backend is source of truth.**

```typescript
// ✅ CORRECT: React Query for server data
const { data: user } = useQuery(['user', userId], () => api.getUser(userId))

// ❌ WRONG: localStorage as source of truth
const [user, setUser] = useState(JSON.parse(localStorage.getItem('user')))
```

**Rule: Local state is for UI only.**

```typescript
// ✅ CORRECT: UI-only state
const [isModalOpen, setIsModalOpen] = useState(false)
const [selectedTab, setSelectedTab] = useState('overview')

// ❌ WRONG: Server data in local state
const [posts, setPosts] = useState([])
useEffect(() => { fetch('/api/posts').then(setPosts) }, [])
```

## WebSocket Cleanup

**Rule: Always return cleanup function.**

```typescript
// ✅ CORRECT
useEffect(() => {
  const socket = new WebSocket(url)
  socket.onmessage = handleMessage
  
  return () => {
    socket.close()  // CLEANUP
  }
}, [url])

// ❌ WRONG: No cleanup
useEffect(() => {
  const socket = new WebSocket(url)
  socket.onmessage = handleMessage
  // Missing cleanup!
}, [url])
```

## Before Committing

1. Run `npm test` - all tests must pass
2. Run `npm run lint` - no errors
3. Run `npm run typecheck` - no type errors
4. Review P0 constraints above
```

### 1.2 Create Pre-commit Hook

**File:** `tools/hooks/pre-commit`

```bash
#!/bin/bash
set -e

echo "🔍 Running pre-commit checks..."

# Type checking
echo "→ Type checking..."
npm run typecheck || { echo "❌ Type errors found"; exit 1; }

# Linting
echo "→ Linting..."
npm run lint || { echo "❌ Lint errors found"; exit 1; }

# Tests
echo "→ Running tests..."
npm test || { echo "❌ Tests failed"; exit 1; }

# Show P0 constraints
echo ""
echo "══════════════════════════════════════════════════════════"
echo "⛔ P0 CONSTRAINTS - Confirm before commit:"
echo "══════════════════════════════════════════════════════════"
echo "1. Backend is source of truth - No useState(localStorage)"
echo "2. useQuery for server data - No raw fetch in useState"
echo "3. Cleanup subscriptions - useEffect returns cleanup"
echo "4. No any types - Proper TypeScript types"
echo "5. Tests passed ✓"
echo "══════════════════════════════════════════════════════════"
echo ""
echo "✅ All checks passed. Commit proceeding."
```

**File:** `tools/hooks/install.sh`

```bash
#!/bin/bash
cp tools/hooks/pre-commit .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit
echo "✅ Pre-commit hook installed"
```

### 1.3 Directory Structure

```
your-app/
├── CLAUDE.md                    # P0 constraints + development guide
├── docs/
│   └── adr/                     # Architecture Decision Records
│       ├── 001-state-management.md
│       ├── 002-api-design.md
│       └── 003-websocket-strategy.md
├── tools/
│   └── hooks/
│       ├── pre-commit           # Shows P0, runs tests
│       └── install.sh           # Installs hooks
├── tests/
│   └── invariants/              # Tests for architecture invariants
│       ├── state-sync.test.ts
│       └── cleanup.test.ts
└── .app-index/                  # Structural indexes (Phase 4)
    ├── components.json
    └── endpoints.json
```

**Checkpoint:**
- [ ] CLAUDE.md created with P0 constraints at top
- [ ] Pre-commit hook created and executable
- [ ] Hook installation script created
- [ ] Run `tools/hooks/install.sh` to activate

---

## Phase 2: Architecture Decision Records

### 2.1 ADR-001: State Management Strategy

**File:** `docs/adr/001-state-management.md`

```markdown
# ADR-001: State Management Strategy

## Status
Accepted

## Context
We need a consistent approach to state management that:
- Prevents state sync bugs (the localStorage + backend problem)
- Makes data flow predictable
- Works well with React's rendering model

## Decision

### Server State: React Query
All data that exists on the server uses React Query (TanStack Query).

```typescript
// Server state - managed by React Query
const { data, isLoading, error } = useQuery(['users', userId], fetchUser)
```

### Client State: useState/Zustand
UI-only state (modals, form inputs, selected tabs) uses useState or Zustand.

```typescript
// Client state - UI only
const [isOpen, setIsOpen] = useState(false)
```

### No localStorage for Persistent Data
localStorage is forbidden for persistent data. React Query handles caching.

If localStorage is needed for preferences (theme, sidebar state), it must:
- Be clearly marked as non-authoritative
- Have explicit TTL or be invalidated on mount

## Invariants

1. **INV-001**: Data that exists in database MUST be fetched via useQuery
2. **INV-002**: useState CANNOT be initialized with localStorage for persistent data
3. **INV-003**: Mutations MUST use useMutation with cache invalidation

## Consequences

### Positive
- Single source of truth (backend)
- No sync bugs
- Built-in caching, refetching, error handling

### Negative
- Learning curve for React Query
- More boilerplate for simple fetches
```

### 2.2 ADR-002: WebSocket Strategy

**File:** `docs/adr/002-websocket-strategy.md`

```markdown
# ADR-002: WebSocket Strategy

## Status
Accepted

## Context
Real-time features require WebSocket connections. Common bugs:
- Connections not cleaned up on unmount (memory leaks)
- No reconnection logic
- Stale handlers after re-renders

## Decision

### Use Custom Hook with Cleanup
All WebSocket connections go through a custom hook that handles cleanup.

```typescript
// hooks/useWebSocket.ts
export function useWebSocket(url: string, onMessage: (data: any) => void) {
  useEffect(() => {
    const socket = new WebSocket(url)
    
    socket.onmessage = (event) => {
      onMessage(JSON.parse(event.data))
    }
    
    socket.onerror = (error) => {
      console.error('WebSocket error:', error)
    }
    
    // REQUIRED: Cleanup on unmount
    return () => {
      socket.close()
    }
  }, [url, onMessage])
}
```

### Reconnection with Exponential Backoff
Production connections must implement reconnection.

## Invariants

1. **INV-004**: Every WebSocket connection MUST have cleanup in useEffect return
2. **INV-005**: Direct `new WebSocket()` in components is forbidden - use the hook

## Consequences

### Positive
- No leaked connections
- Consistent reconnection behavior
- Centralized error handling

### Negative
- Must use hook, can't inline WebSocket
```

**Checkpoint:**
- [ ] ADR-001: State Management created
- [ ] ADR-002: WebSocket Strategy created
- [ ] Additional ADRs for your specific concerns

---

## Phase 3: Invariant Tests

### 3.1 State Sync Invariant Tests

**File:** `tests/invariants/state-sync.test.ts`

```typescript
import { renderHook, waitFor } from '@testing-library/react'
import { QueryClient, QueryClientProvider } from '@tanstack/react-query'
import { rest } from 'msw'
import { setupServer } from 'msw/node'

// Mock server
const server = setupServer(
  rest.get('/api/user', (req, res, ctx) => {
    return res(ctx.json({ id: 1, name: 'Test User' }))
  })
)

beforeAll(() => server.listen())
afterEach(() => server.resetHandlers())
afterAll(() => server.close())

describe('INV-001: Backend is source of truth', () => {
  it('client state matches server after fetch', async () => {
    const queryClient = new QueryClient()
    const wrapper = ({ children }) => (
      <QueryClientProvider client={queryClient}>{children}</QueryClientProvider>
    )
    
    const { result } = renderHook(() => useUser(1), { wrapper })
    
    await waitFor(() => {
      expect(result.current.data).toEqual({ id: 1, name: 'Test User' })
    })
  })
  
  it('mutation updates server and invalidates cache', async () => {
    const queryClient = new QueryClient()
    const wrapper = ({ children }) => (
      <QueryClientProvider client={queryClient}>{children}</QueryClientProvider>
    )
    
    // Setup: User exists
    const { result: userResult } = renderHook(() => useUser(1), { wrapper })
    await waitFor(() => expect(userResult.current.data).toBeDefined())
    
    // Update server response
    server.use(
      rest.get('/api/user', (req, res, ctx) => {
        return res(ctx.json({ id: 1, name: 'Updated Name' }))
      })
    )
    
    // Mutate
    const { result: mutationResult } = renderHook(
      () => useUpdateUser(),
      { wrapper }
    )
    
    await mutationResult.current.mutateAsync({ id: 1, name: 'Updated Name' })
    
    // Cache should be invalidated, refetch should show new data
    await waitFor(() => {
      expect(userResult.current.data.name).toBe('Updated Name')
    })
  })
  
  it('stale localStorage does not override fresh server data', async () => {
    // Seed stale localStorage
    localStorage.setItem('user-1', JSON.stringify({ 
      id: 1, 
      name: 'Stale Cached Name',
      _cachedAt: Date.now() - 86400000 // 1 day old
    }))
    
    const queryClient = new QueryClient()
    const wrapper = ({ children }) => (
      <QueryClientProvider client={queryClient}>{children}</QueryClientProvider>
    )
    
    const { result } = renderHook(() => useUser(1), { wrapper })
    
    // Should fetch fresh data, not use stale localStorage
    await waitFor(() => {
      expect(result.current.data.name).toBe('Test User')
      expect(result.current.data.name).not.toBe('Stale Cached Name')
    })
    
    // Cleanup
    localStorage.removeItem('user-1')
  })
})
```

### 3.2 WebSocket Cleanup Tests

**File:** `tests/invariants/websocket-cleanup.test.ts`

```typescript
import { renderHook, act } from '@testing-library/react'
import { useWebSocket } from '@/hooks/useWebSocket'

// Mock WebSocket
class MockWebSocket {
  static instances: MockWebSocket[] = []
  
  url: string
  onmessage: ((event: any) => void) | null = null
  closed = false
  
  constructor(url: string) {
    this.url = url
    MockWebSocket.instances.push(this)
  }
  
  close() {
    this.closed = true
  }
  
  static reset() {
    MockWebSocket.instances = []
  }
}

beforeEach(() => {
  MockWebSocket.reset()
  ;(global as any).WebSocket = MockWebSocket
})

describe('INV-004: WebSocket cleanup required', () => {
  it('closes socket on unmount', () => {
    const onMessage = jest.fn()
    
    const { unmount } = renderHook(() => 
      useWebSocket('ws://localhost/test', onMessage)
    )
    
    // Socket should be created
    expect(MockWebSocket.instances.length).toBe(1)
    const socket = MockWebSocket.instances[0]
    expect(socket.closed).toBe(false)
    
    // Unmount
    unmount()
    
    // Socket should be closed
    expect(socket.closed).toBe(true)
  })
  
  it('closes old socket when URL changes', () => {
    const onMessage = jest.fn()
    
    const { rerender } = renderHook(
      ({ url }) => useWebSocket(url, onMessage),
      { initialProps: { url: 'ws://localhost/test1' } }
    )
    
    const firstSocket = MockWebSocket.instances[0]
    expect(firstSocket.closed).toBe(false)
    
    // Change URL
    rerender({ url: 'ws://localhost/test2' })
    
    // First socket should be closed
    expect(firstSocket.closed).toBe(true)
    
    // New socket should be open
    const secondSocket = MockWebSocket.instances[1]
    expect(secondSocket.closed).toBe(false)
  })
})
```

### 3.3 Package.json Scripts

```json
{
  "scripts": {
    "test": "vitest run",
    "test:watch": "vitest",
    "test:invariants": "vitest run tests/invariants/",
    "lint": "eslint src/",
    "typecheck": "tsc --noEmit"
  }
}
```

**Checkpoint:**
- [ ] tests/invariants/state-sync.test.ts created
- [ ] tests/invariants/websocket-cleanup.test.ts created
- [ ] `npm run test:invariants` passes
- [ ] Tests actually verify the invariants from ADRs

---

## Phase 4: Structural Indexes (Optional)

For larger codebases, create indexes for efficient agent exploration.

### 4.1 Simple Indexer Script

**File:** `tools/indexer/index.ts`

```typescript
import * as fs from 'fs'
import * as path from 'path'
import * as glob from 'glob'

interface ComponentInfo {
  name: string
  file: string
  hooks: string[]
  queries: string[]
}

interface EndpointInfo {
  method: string
  path: string
  file: string
  handler: string
}

function indexComponents(): ComponentInfo[] {
  const files = glob.sync('src/**/*.tsx')
  const components: ComponentInfo[] = []
  
  for (const file of files) {
    const content = fs.readFileSync(file, 'utf-8')
    
    // Find component exports
    const componentMatch = content.match(/export (?:default )?function (\w+)/)
    if (!componentMatch) continue
    
    // Find hooks used
    const hooks = [...content.matchAll(/use\w+/g)].map(m => m[0])
    
    // Find React Query queries
    const queries = [...content.matchAll(/useQuery\(\[['"](\w+)['"]/g)]
      .map(m => m[1])
    
    components.push({
      name: componentMatch[1],
      file,
      hooks: [...new Set(hooks)],
      queries: [...new Set(queries)],
    })
  }
  
  return components
}

function indexEndpoints(): EndpointInfo[] {
  // Adjust for your backend structure (Express, Fastify, etc.)
  const files = glob.sync('src/api/**/*.ts')
  const endpoints: EndpointInfo[] = []
  
  for (const file of files) {
    const content = fs.readFileSync(file, 'utf-8')
    
    // Find route definitions (Express style)
    const routes = content.matchAll(/router\.(get|post|put|delete)\(['"]([^'"]+)['"]/g)
    
    for (const match of routes) {
      endpoints.push({
        method: match[1].toUpperCase(),
        path: match[2],
        file,
        handler: path.basename(file, '.ts'),
      })
    }
  }
  
  return endpoints
}

// Generate indexes
const components = indexComponents()
const endpoints = indexEndpoints()

fs.mkdirSync('.app-index', { recursive: true })
fs.writeFileSync('.app-index/components.json', JSON.stringify(components, null, 2))
fs.writeFileSync('.app-index/endpoints.json', JSON.stringify(endpoints, null, 2))

console.log(`✅ Indexed ${components.length} components, ${endpoints.length} endpoints`)
```

### 4.2 Usage

```bash
# Generate indexes
npx ts-node tools/indexer/index.ts

# Agent can then query:
cat .app-index/components.json | jq '.[] | select(.queries | length > 0)'
```

**Checkpoint:**
- [ ] Indexer script created (if needed for your codebase size)
- [ ] .app-index/ in .gitignore (regenerated, not committed)
- [ ] Document how to regenerate indexes

---

## Phase 5: CI Integration

### 5.1 GitHub Actions

**File:** `.github/workflows/ci.yml`

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v4
      
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'
      
      - run: npm ci
      
      - name: Type Check
        run: npm run typecheck
      
      - name: Lint
        run: npm run lint
      
      - name: Tests
        run: npm test
      
      - name: Invariant Tests
        run: npm run test:invariants
```

**Checkpoint:**
- [ ] CI workflow created
- [ ] CI runs on all PRs
- [ ] CI blocks merge if tests fail

---

## Phase 6: Thorough Examination & Full Map

This phase enables agents to **thoroughly answer questions** about the codebase and create a **full map of what's happening**. This is the RLM exploration capability from Kelpie.

### 6.1 The Problem

When asked "Is the user profile feature working correctly?" or "What's happening with state management?", agents often:
- Read a few files and guess
- Miss entire areas of the codebase
- Claim "it's working" without evidence

**We need:**
- Systematic examination of all relevant parts
- Hard control that blocks completion until all partitions examined
- Evidence-based answers, not guesses

### 6.2 Partitioning the Codebase

For a full-stack app, partitions are:

```
┌─────────────────────────────────────────────────────────────────┐
│  CODEBASE PARTITIONS                                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  FRONTEND                                                        │
│  ├─ src/components/       # React components                    │
│  ├─ src/hooks/            # Custom hooks (useQuery, etc.)       │
│  ├─ src/stores/           # Zustand/Redux stores                │
│  ├─ src/pages/            # Page components / routes            │
│  └─ src/utils/            # Utility functions                   │
│                                                                  │
│  BACKEND                                                         │
│  ├─ src/api/              # API route handlers                  │
│  ├─ src/services/         # Business logic                      │
│  ├─ src/models/           # Database models                     │
│  └─ src/middleware/       # Auth, validation, etc.              │
│                                                                  │
│  SHARED                                                          │
│  ├─ src/types/            # Shared TypeScript types             │
│  └─ src/contracts/        # API contracts (request/response)    │
│                                                                  │
│  TESTS                                                           │
│  ├─ tests/unit/           # Unit tests                          │
│  ├─ tests/integration/    # Integration tests                   │
│  └─ tests/invariants/     # Invariant tests                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 6.3 Thorough Examination Workflow

**Add to CLAUDE.md:**

```markdown
## Thorough Examination Workflow

When asked to examine a feature or answer a question about the codebase:

### Step 1: Identify Scope

```bash
# Use indexes to find relevant files
cat .app-index/components.json | jq '.[] | select(.name | contains("User"))'
cat .app-index/endpoints.json | jq '.[] | select(.path | contains("user"))'
```

### Step 2: List Required Partitions

For the feature being examined, identify ALL partitions that must be checked:

```
Required partitions for "user profile":
- [ ] Frontend: UserProfile.tsx, UserSettings.tsx
- [ ] Hooks: useUser.ts, useUpdateUser.ts
- [ ] Backend: /api/users/:id (GET, PUT)
- [ ] Services: UserService.ts
- [ ] Models: User.model.ts
- [ ] Types: UserDTO.ts
- [ ] Tests: user.test.ts, user-api.test.ts
```

### Step 3: Examine Each Partition

For EACH partition, record:
1. **What it does** (brief summary)
2. **Invariant compliance** (does it follow ADR rules?)
3. **Issues found** (if any)

```markdown
## Examination Log

### UserProfile.tsx
- Uses useQuery(['user', id]) ✅ (INV-001: backend source of truth)
- No localStorage usage ✅
- No issues found

### useUser.ts
- Returns useQuery result ✅
- Proper error handling ✅
- No issues found

### /api/users/:id (backend)
- Validates input ✅
- Returns proper types ✅
- Issue: Missing rate limiting ⚠️
```

### Step 4: Run Tests

```bash
# Run tests related to the feature
npm test -- --grep "user"
npm run test:invariants
```

### Step 5: Synthesize Answer

Only after ALL partitions examined AND tests run:

```markdown
## Answer

**Question:** Is the user profile feature working correctly?

**Partitions Examined:** 7/7 ✅
- Frontend: UserProfile.tsx, UserSettings.tsx
- Hooks: useUser.ts, useUpdateUser.ts
- Backend: /api/users/:id
- Services: UserService.ts
- Tests: user.test.ts

**Invariant Compliance:**
- INV-001 (backend source of truth): ✅ All components use useQuery
- INV-002 (no localStorage for persistent): ✅ No violations
- INV-004 (WebSocket cleanup): N/A (no WebSocket in this feature)

**Tests:** 12 passed, 0 failed

**Issues Found:**
1. ⚠️ Missing rate limiting on /api/users/:id (low priority)

**Conclusion:** User profile feature is working correctly. One minor issue noted.
```

### HARD CONTROL: Cannot Answer Until All Examined

**You CANNOT provide a final answer until:**
1. ALL identified partitions have been examined
2. Examination log shows each partition checked
3. Tests have been run with results recorded

If you find yourself wanting to answer before examining all partitions, STOP and examine the rest first.
```

### 6.4 Full Map Capability

**Add to CLAUDE.md:**

```markdown
## Creating a Full Map

When asked "How does X work?" or "Give me a map of the codebase":

### Step 1: Generate/Update Indexes

```bash
npx ts-node tools/indexer/index.ts
```

### Step 2: Map Data Flow

For the feature/area being mapped:

```
┌─────────────────────────────────────────────────────────────────┐
│  DATA FLOW: User Profile                                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  User clicks "Profile"                                           │
│       │                                                          │
│       ▼                                                          │
│  ProfilePage.tsx                                                 │
│       │                                                          │
│       ▼                                                          │
│  useUser(userId) hook                                            │
│       │                                                          │
│       ▼                                                          │
│  useQuery(['user', userId], fetchUser)                           │
│       │                                                          │
│       ▼                                                          │
│  GET /api/users/:id                                              │
│       │                                                          │
│       ▼                                                          │
│  UserService.getById(id)                                         │
│       │                                                          │
│       ▼                                                          │
│  User.findById(id) [database]                                    │
│       │                                                          │
│       ▼                                                          │
│  Response → React Query cache → Component renders                │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Step 3: Map State Management

```
┌─────────────────────────────────────────────────────────────────┐
│  STATE MANAGEMENT MAP                                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  SERVER STATE (React Query)                                      │
│  ├─ ['user', id]         → User profile data                    │
│  ├─ ['users']            → User list                            │
│  ├─ ['posts', userId]    → User's posts                         │
│  └─ ['notifications']    → User notifications                   │
│                                                                  │
│  CLIENT STATE (Zustand)                                          │
│  ├─ uiStore.sidebarOpen  → Sidebar visibility                   │
│  ├─ uiStore.theme        → Light/dark theme                     │
│  └─ uiStore.selectedTab  → Current tab selection                │
│                                                                  │
│  ❌ NO localStorage for persistent data                          │
│  ✅ localStorage only for: theme preference (with TTL)           │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Step 4: Map Invariant Coverage

```
┌─────────────────────────────────────────────────────────────────┐
│  INVARIANT COVERAGE MAP                                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  INV-001: Backend is source of truth                             │
│  ├─ UserProfile.tsx      ✅ uses useQuery                       │
│  ├─ PostList.tsx         ✅ uses useQuery                       │
│  ├─ Settings.tsx         ✅ uses useQuery                       │
│  └─ Dashboard.tsx        ⚠️ NEEDS REVIEW (complex state)        │
│                                                                  │
│  INV-002: No localStorage for persistent data                    │
│  ├─ Searched all .tsx files                                     │
│  ├─ Found 0 violations                                          │
│  └─ Theme preference uses TTL ✅                                │
│                                                                  │
│  INV-004: WebSocket cleanup                                      │
│  ├─ ChatPanel.tsx        ✅ returns cleanup                     │
│  ├─ Notifications.tsx    ✅ uses useWebSocket hook              │
│  └─ LiveUpdates.tsx      ⚠️ NEEDS REVIEW                        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Step 5: Surface Issues

From the map, identify:
1. **Violations** - Code that breaks invariants
2. **Gaps** - Missing tests, undocumented flows
3. **Risks** - Complex areas that need attention

```markdown
## Issues Surfaced

### Violations
- None found

### Gaps
1. Dashboard.tsx has complex state management - needs review
2. LiveUpdates.tsx WebSocket cleanup not verified
3. No integration test for user update flow

### Risks
1. Real-time features (Chat, Notifications) have more moving parts
2. State sync between tabs not handled
```
```

### 6.5 Examination Log Template

**File:** `.progress/templates/examination.md`

```markdown
# Examination: [Question/Feature]

**Date:** YYYY-MM-DD
**Question:** [What are we examining?]

## Required Partitions

- [ ] [Partition 1]
- [ ] [Partition 2]
- [ ] ...

## Examination Log

### [Partition 1]
- **Summary:** 
- **Invariant compliance:** 
- **Issues:** 

### [Partition 2]
- **Summary:** 
- **Invariant compliance:** 
- **Issues:** 

## Test Results

```bash
# Command run:
npm test -- --grep "[feature]"

# Results:
X passed, Y failed
```

## Answer

**Partitions Examined:** X/Y

**Invariant Compliance:**
- INV-001: 
- INV-002: 
- ...

**Issues Found:**
1. 
2. 

**Conclusion:**
```

### 6.6 Hard Control Implementation

If using MCP tools, add this enforcement:

```typescript
// tools/mcp-app/src/examine.ts

interface ExaminationState {
  question: string
  requiredPartitions: string[]
  examinedPartitions: string[]
  findings: Record<string, string>
  testsRun: boolean
}

const examinations = new Map<string, ExaminationState>()

server.setRequestHandler("examination_start", async (request) => {
  const { question, partitions } = request.params
  const examId = crypto.randomUUID()
  
  examinations.set(examId, {
    question,
    requiredPartitions: partitions,
    examinedPartitions: [],
    findings: {},
    testsRun: false,
  })
  
  return { examId, partitions }
})

server.setRequestHandler("examination_record", async (request) => {
  const { examId, partition, findings } = request.params
  const exam = examinations.get(examId)
  
  if (!exam) throw new Error("Examination not found")
  
  exam.examinedPartitions.push(partition)
  exam.findings[partition] = findings
  
  const remaining = exam.requiredPartitions.filter(
    p => !exam.examinedPartitions.includes(p)
  )
  
  return { 
    recorded: true, 
    remaining,
    complete: remaining.length === 0 
  }
})

server.setRequestHandler("examination_answer", async (request) => {
  const { examId, answer } = request.params
  const exam = examinations.get(examId)
  
  if (!exam) throw new Error("Examination not found")
  
  // HARD CONTROL: Block if not all partitions examined
  const missing = exam.requiredPartitions.filter(
    p => !exam.examinedPartitions.includes(p)
  )
  
  if (missing.length > 0) {
    return {
      allowed: false,
      error: `Cannot answer: ${missing.length} partitions not examined`,
      missing,
    }
  }
  
  // HARD CONTROL: Block if tests not run
  if (!exam.testsRun) {
    return {
      allowed: false,
      error: "Cannot answer: Tests have not been run",
    }
  }
  
  return { allowed: true, answer }
})
```

**Without MCP (simpler approach):**

Just document in CLAUDE.md that the agent must:
1. List all partitions before starting
2. Check off each partition as examined
3. Run tests before answering
4. Include examination log in the answer

The "hard control" is the instruction + the format that makes it obvious if steps were skipped.

**Checkpoint:**
- [ ] Thorough examination workflow added to CLAUDE.md
- [ ] Full map capability documented
- [ ] Examination log template created
- [ ] Agent understands: cannot answer until all partitions examined

---

## Quick Reference

### P0 Constraints (Memorize These)

1. **Backend is source of truth** - No useState(localStorage) for persistent data
2. **useQuery for server data** - No raw fetch in useState
3. **Cleanup subscriptions** - useEffect returns cleanup function
4. **No any types** - Proper TypeScript types
5. **Tests before commit** - All tests must pass

### File Checklist

| File | Purpose | Created |
|------|---------|---------|
| `CLAUDE.md` | P0 constraints + dev guide + examination workflow | [ ] |
| `tools/hooks/pre-commit` | Shows P0, runs tests | [ ] |
| `docs/adr/001-state-management.md` | State management decisions | [ ] |
| `docs/adr/002-websocket-strategy.md` | WebSocket decisions | [ ] |
| `tests/invariants/state-sync.test.ts` | State sync tests | [ ] |
| `tests/invariants/websocket-cleanup.test.ts` | Cleanup tests | [ ] |
| `.github/workflows/ci.yml` | CI pipeline | [ ] |
| `.progress/templates/examination.md` | Examination log template | [ ] |
| `tools/indexer/index.ts` | Structural indexer (Phase 4) | [ ] |

### Commands

```bash
# Install hooks
./tools/hooks/install.sh

# Run all tests
npm test

# Run invariant tests only
npm run test:invariants

# Check types
npm run typecheck

# Lint
npm run lint
```

---

## What This Achieves

1. **P0 constraints always visible** - Top of CLAUDE.md, shown at every commit
2. **Architecture documented** - ADRs explain WHY decisions were made
3. **Invariants tested** - Not just claimed, but verified by tests
4. **Enforcement at multiple layers** - ESLint, TypeScript, pre-commit, CI
5. **Simple, not over-engineered** - 5 lines of P0, not a YAML schema
6. **Thorough examination guaranteed** - Agent cannot answer until all partitions examined
7. **Full map capability** - Agent can create data flow, state management, and invariant coverage maps
8. **Evidence-based answers** - Answers include examination log, test results, specific findings

The agent (or developer) sees constraints, follows them, examines thoroughly before answering, and can't commit without tests passing. That's the whole system.

---

## Adapting This Plan

### For Your Specific App

1. **Update P0 constraints** - What are YOUR non-negotiable rules?
2. **Write ADRs for your decisions** - State management, API design, auth, etc.
3. **Create invariant tests** - What bugs have bitten you? Test against those.
4. **Customize pre-commit** - Add your specific checks

### For Different Tech Stacks

| Stack | State Management | Testing |
|-------|------------------|---------|
| React + React Query | This plan as-is | Vitest + React Testing Library |
| React + Redux | Replace useQuery rules with Redux patterns | Same |
| Vue + Pinia | Adapt state patterns for Vue | Vitest + Vue Test Utils |
| Svelte | Adapt for Svelte stores | Vitest + Svelte Testing Library |

The principles transfer. The specific patterns change.

---

## References

- [VDE Paper](internal) - Verification-Driven Exploration for QuickHouse
- [Kelpie Repo OS](.progress/026_20260120_repo_os_rlm_infrastructure.md) - Kelpie's implementation
- [Zhang et al. RLM](https://alexzhang13.github.io/blog/2025/rlm/) - Recursive Language Models
- [TanStack Query](https://tanstack.com/query) - React Query documentation
- [Vitest](https://vitest.dev/) - Testing framework

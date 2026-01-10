# Architecture Decision Records

This directory contains Architecture Decision Records (ADRs) for the Kelpie project.

## What is an ADR?

An ADR is a document that captures an important architectural decision made along with its context and consequences.

## ADR Index

| ADR | Title | Status | Date |
|-----|-------|--------|------|
| [000](./000-template.md) | ADR Template | - | - |
| [001](./001-virtual-actor-model.md) | Virtual Actor Model | Accepted | 2025-01-10 |
| [002](./002-foundationdb-integration.md) | FoundationDB Integration | Accepted | 2025-01-10 |
| [003](./003-wasm-actor-runtime.md) | WASM Actor Runtime | Proposed | 2025-01-10 |
| [004](./004-linearizability-guarantees.md) | Linearizability Guarantees | Accepted | 2025-01-10 |
| [005](./005-dst-framework.md) | DST Framework | Accepted | 2025-01-10 |

## Creating a New ADR

1. Copy `000-template.md` to a new file with the next number
2. Fill in the sections
3. Update this README's index
4. Submit for review

## ADR Status

- **Proposed**: Under discussion
- **Accepted**: Approved and implemented
- **Deprecated**: No longer recommended
- **Superseded**: Replaced by another ADR

## References

- [ADR GitHub Organization](https://adr.github.io/)
- [Michael Nygard's ADR Article](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions)

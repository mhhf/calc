---
title: Development Index
created: 2026-02-10
modified: 2026-02-11
summary: Index of active development documents
tags: [index, development]
---

# Development Documents

Active implementation plans and design documents for in-progress work.

## Active Documents

| Document | Description | Tags |
|----------|-------------|------|
| [[architecture-pipelines]] | v2 architecture implementation tracker | `architecture` `v2` `implementation` |
| [[CORE_SPLIT]] | Design for generic vs focused prover separation | `architecture` `prover` `design` |
| [[dsl_refactor]] | DSL migration from ll.json to .calc/.rules | `dsl` `celf` `tree-sitter` `migration` |
| [[family-design]] | Calculus family abstraction (@mode, @role) | `family` `lnl` `architecture` |
| [[authorization-implementation]] | Ownership/authorization modalities | `authorization` `ownership` `modalities` |
| [[todo]] | Outstanding development tasks | `planning` `tasks` |

## Research (Active)

| Document | Description | Tags |
|----------|-------------|------|
| [[../research/execution-trees-metaproofs]] | Execution trees, metaproofs, coinduction | `research` `execution` `metaproofs` |

## Completed

| Document | Description | Completed |
|----------|-------------|-----------|
| [[primitives-implementation]] | binlit/strlit/charlit storage, type policies | 2026-02-11 |

## Document Lifecycle

1. **dev/** - Active implementation plans, deliberation
2. **doc/research/** - Theoretical research, design decisions, analysis
3. **doc/documentation/** - How the system works NOW
4. **delete** - Completed implementation plans, obsolete docs

## Cleanup Summary (Feb 2026)

**Merged into research/prover-optimization.md:**
- arena-allocation, optimization_analysis, optimization_strategies

**Merged into dev/primitives-implementation.md:**
- import-mechanism, lazy-primitive-storage, syntactic-sugar

**Deleted (obsolete/completed):**
- focusing_refactoring (decision made, v2 uses inferred polarity)
- v2-migration-history (redundant with CHANGELOG)
- claude-meta, content_addressed_hash_bug, display_implementation
- FFI-IMPLEMENTATION-PLAN, frontend-refactor, IMPLEMENTATION-PLAN-MDE
- proof_view, README, DONE

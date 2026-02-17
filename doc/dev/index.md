---
title: Development Index
created: 2026-02-10
modified: 2026-02-15
summary: Index of active development documents
tags: [index, development]
---

# Development Documents

Active implementation plans and design documents for in-progress work.

## Active Documents

| Document | Description | Tags |
|----------|-------------|------|
| [[architecture-pipelines]] | v2 architecture implementation tracker | `architecture` `v2` `implementation` |
| [[dsl_refactor]] | DSL migration from ll.json to .calc/.rules | `dsl` `celf` `tree-sitter` `migration` |
| [[authorization-implementation]] | Ownership/authorization modalities | `authorization` `ownership` `modalities` |
| [[prooverlasagne]] | Layered prover architecture (L1 kernel → L2 generic → L3 focused → L4 strategy → L5 UI) | `architecture` `prover` `refactor` |
| [[evm-modeling-approaches]] | EVM symbolic execution design space | `symbolic-execution` `EVM` `design` |
| [[todo]] | Outstanding development tasks | `planning` `tasks` |

## Optimization Plans

| Document | Status | Summary |
|----------|--------|---------|
| [[forward-optimization-roadmap]] | ACTIVE | Forward chaining: Stages 1-4 done, 5a/6/7 next |
| [[constructor-indexing]] | DEFERRED | O(1) identity via tag index (sequent prover) |

**Forward optimization next steps:** Stage 6 (de Bruijn theta) → Stage 7 (delta + compiled sub) → Stage 5a (dirty tracking at 100+ rules).

See also: [[../research/prover-optimization]] for the full optimization catalog.

## Research (Active)

| Document | Description | Tags |
|----------|-------------|------|
| [[../research/execution-trees-metaproofs]] | Execution trees, metaproofs, coinduction | `research` `execution` `metaproofs` |
| [[../research/de-bruijn-indexed-matching]] | De Bruijn indexed pattern matching | `optimization` `de-Bruijn` `Stage-6` |
| [[../research/term-indexing]] | Discrimination trees, fingerprints, code trees | `optimization` `indexing` `Stage-9` |
| [[../research/forward-chaining-networks]] | Rete, TREAT, LEAPS, CHR for linear logic | `optimization` `TREAT` `CHR` |
| [[../research/compiled-pattern-matching]] | Maranget decision trees, compiled match | `optimization` `compilation` |
| [[../research/incremental-matching]] | Semi-naive evaluation, relational e-matching | `optimization` `incremental` `Datalog` |
| [[../research/equational-completion]] | Equational completion for arithmetic catch-alls | `equational-completion` `confluence` |

## Completed

| Document | Description | Completed |
|----------|-------------|-----------|
| [[primitives-implementation]] | binlit/strlit/charlit storage, type policies | 2026-02-11 |
| ~~CORE_SPLIT~~ | Superseded by [[prooverlasagne]] §3.2-3.3 | 2026-02-13 |
| ~~manual-proof-architecture~~ | Superseded by [[prooverlasagne]] §3.5, §3.7 | 2026-02-13 |
| ~~manual-prover-refactor~~ | All bugs fixed, tests pass (67/67) | 2026-02-13 |
| [[../documentation/family-design]] | Calculus family abstraction (moved to docs) | 2026-02-13 |

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
- explicit-substitutions (premise addressed by content-addressing: `copy = h => h`, `applySimultaneous`)
- persistent-data-structures (premise invalidated: contexts are `{hash: count}`, no deep copy)
- focusing_refactoring (decision made, uses inferred polarity)
- v2-migration-history (redundant with CHANGELOG)
- claude-meta, content_addressed_hash_bug, display_implementation
- FFI-IMPLEMENTATION-PLAN, frontend-refactor, IMPLEMENTATION-PLAN-MDE
- proof_view, README, DONE

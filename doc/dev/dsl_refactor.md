---
title: DSL Refactor Status
created: 2026-02-10
modified: 2026-02-11
summary: Tracking migration from ll.json to .calc/.rules format
tags: [dsl, celf, tree-sitter, migration]
status: active
---

# DSL Refactor: Extended Celf

Status tracker for ll.json to .calc/.rules migration.

## Completed Phases

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Tree-sitter parser for pure Celf | ✓ |
| 2 | Extended Celf (@annotations) | ✓ |
| 3 | ll.json generator | ✓ |
| 3.5 | Family abstraction | ✓ |
| v2 Prover | Focused proof search | ✓ |

## Current Files

```
lib/tree-sitter-mde/   # Tree-sitter grammar
lib/celf/
├── ts-parser.js       # Tree-sitter parser
└── generator.js       # ll.json generator
calculus/
├── linear-logic.calc  # Connectives
└── linear-logic.rules # Rules
families/
└── display_calculus.family
```

## Remaining Work

### Phase 4: Complete Migration

**Goal:** Remove ll.json, use only .calc/.rules

| Consumer | Status |
|----------|--------|
| lib/calc.js | ✓ deprecated |
| lib/parser.js | ✓ deprecated |
| libexec/calc-*-v2 | ✓ created |
| src/ui/ | Pending |

**Blockers:**
- [ ] Migrate UI to v2 prover
- [ ] Delete ll.json
- [ ] Remove v1 code

### Phase 5: FFI Support

Add `@ffi` and `@mode` for computational predicates:

```celf
plus : bin -> bin -> bin -> type
  @ffi "arithmetic.plus"
  @mode + + -.
```

### Phase 6: Stdlib

Create reusable library:
- Port lib/bin.mde from optimism-mde
- Create full Celf-compatible stdlib

## References

- [[architecture-pipelines]] - v2 architecture
- [[FFI-IMPLEMENTATION-PLAN]] - FFI details
- Research: [[clf-celf-ceptre]], [[DSL-approaches]]

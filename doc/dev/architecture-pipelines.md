---
title: v2 Architecture Implementation
created: 2026-02-10
modified: 2026-02-11
summary: Implementation tracker for v2 parallel architecture
tags: [architecture, v2, implementation]
status: active
---

# v2 Architecture Implementation

Parallel implementation of clean architecture alongside legacy v1.

## Design Principles

1. **No globals**: Pass calculus/store explicitly
2. **Trusted kernel**: Minimal core that applies rules
3. **Pluggable strategies**: Proof search algorithms separate
4. **Test against old**: Cross-check v2 vs v1

## Current Structure

```
lib/v2/
├── kernel/           # ✓ Implemented
│   ├── store.js      # Content-addressed store
│   ├── ast.js        # Pure AST
│   ├── ast-hash.js   # Hash computation
│   ├── sequent.js    # Sequent representation
│   ├── substitute.js # Substitution
│   └── unify.js      # MGU
├── calculus/         # ✓ Implemented
│   └── index.js      # Calculus loader
├── parser/           # ✓ Implemented
│   └── sequent-parser.js
├── prover/           # ✓ Implemented
│   ├── focused/      # Focused prover
│   ├── forward.js    # Forward chaining
│   ├── pt.js         # Proof trees
│   └── index.js
├── meta/             # ✓ Implemented
│   └── focusing.js   # Polarity inference
└── index.js          # Main API
```

## Implementation Status

| Phase | Description | Status |
|-------|-------------|--------|
| 1. Parser | Tree-sitter formula parser | ✓ |
| 2. Renderer | Pure render function | ✓ |
| 3. Sequent | Clean sequent representation | ✓ |
| 4. Kernel | Rule application | ✓ |
| 5. Focused Prover | Andreoli focusing | ✓ |
| 6. Generic Prover | Exhaustive search | Pending |
| 7. Integration | CLI --v2 flags | Partial |
| 8. Cleanup | Remove legacy | Pending |

## CLI Integration

```bash
# v2 tools exist:
./libexec/calc-parse-v2 "A -o A"
./libexec/calc-proof-v2 "A -o A"
```

## Remaining Work

1. **Generic Prover**: Implement exhaustive search for verification
2. **Full CLI Integration**: Unified interface with version selection
3. **Cross-check Tests**: Automated comparison v1 vs v2
4. **Legacy Removal**: Once all tests pass on v2

## References

- [[CORE_SPLIT]] - Core/calculus separation design
- [[focusing_refactoring]] - Focusing implementation details
- Research: [[prover-architecture]], [[content-addressed-formulas]]

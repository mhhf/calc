---
title: Calculus Family Abstraction
created: 2026-02-10
modified: 2026-02-11
summary: Family system for shared calculus infrastructure
tags: [family, lnl, architecture]
status: implemented
---

# Calculus Family Abstraction

## Current Files

```
calculus/
├── lnl.family    # LNL infrastructure (@mode linear/cartesian)
├── ill.calc      # ILL connectives (@extends lnl)
└── ill.rules     # ILL inference rules
```

## Key Concepts

### Modes
- `@mode linear` - No contraction/weakening
- `@mode cartesian` - Contraction + weakening

### Role Annotations

| Role | Purpose |
|------|---------|
| `sequent` | Sequent structure |
| `context_concat` | Context join |
| `formula_lift` | Formula → structure |
| `unit` | Empty context |
| `labeled_formula` | Named proof term |

### Metavariables

```celf
@metavar formula prefix="F?" examples="A B C".
@metavar structure prefix="?" examples="X Y D".
```

## Generator Flow

```
.family + .calc + .rules → generator.js → ll.json
```

## References

- [[dsl_refactor]] - Migration status
- Research: [[multi-type-display-calculus]]

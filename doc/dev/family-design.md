---
title: Calculus Family Abstraction
created: 2026-02-10
modified: 2026-02-10
summary: Design for family abstraction allowing multiple calculi to share infrastructure through role annotations and modes
tags: [family, abstraction, lnl, multi-type, calculus]
---

# Calculus Family Abstraction Design

## Current Implementation

All files in `calculus/` directory:
```
calculus/
├── lnl.family       # LNL (Linear/Non-Linear) family infrastructure
├── ill.calc         # Intuitionistic Linear Logic connectives
└── ill.rules        # ILL inference rules
```

### Family File (lnl.family)

LNL is a multi-type display calculus with two modes:
- **Linear** (`@mode linear`): No contraction/weakening
- **Cartesian** (`@mode cartesian`): Contraction + weakening allowed

Key declarations:
```celf
@family lnl.

structure: type @layer structure @mode linear.
cart_structure: type @layer structure @mode cartesian @structural "contraction weakening".

seq: cart_structure -> structure -> formula -> sequent
  @ascii "_ ; _ |- -- : _"
  @role sequent.
```

### Calc File (ill.calc)

Logic-specific connectives with `@extends` directive:
```celf
@extends lnl.

formula: type.

tensor: formula -> formula -> formula
  @ascii "_ * _"
  @polarity positive
  @category multiplicative.
```

### Role Annotations

| Role | Purpose | Example |
|------|---------|---------|
| `judgment` | Unwrap in patterns | `deriv: sequent -> type @role judgment.` |
| `sequent` | Sequent structure | `seq: ... @role sequent.` |
| `context_concat` | Context join | `comma: ... @role context_concat.` |
| `formula_lift` | Formula → structure | `struct: ... @role formula_lift.` |
| `unit` | Empty context | `empty: structure @role unit.` |
| `labeled_formula` | Named proof term | `labeled: term -> formula -> structure @role labeled_formula.` |

## Metavariables

Defined via `@metavar` directive:
```celf
@metavar formula prefix="F?" examples="A B C".
@metavar structure prefix="?" examples="X Y D".
@metavar cart_structure prefix="G?" examples="G H".
```

## Generator Flow

```
.family + .calc + .rules → generator.js → ll.json → parser
```

The generator:
1. Parses all files with tree-sitter
2. Extracts family infrastructure and @role registry
3. Extracts logic connectives
4. Extracts inference rules
5. Generates ll.json with patterns derived from @ascii annotations

## Future: Direct to Parser

Goal: Remove ll.json indirection, generate parser directly from .family+.calc+.rules files.

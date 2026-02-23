---
title: "State Property DSL"
created: 2026-02-18
modified: 2026-02-23
summary: "Design language to express invariants over CALC program states — predicate combinators over multiset states"
tags: [metaproofs, DSL, invariants, design]
type: design
cluster: Verification
status: planning
priority: 8
depends_on: []
required_by: [TODO_0030, TODO_0031, TODO_0032]
---

# State Property DSL

Extracted from TODO_0008. A language to express properties over execution states. Foundation for all metaproof tools.

See [TODO_0008 §4](0008_metaproofs.md#4-state-property-dsl-task_1) for full design with options analysis.

## Design Decision

**Hybrid approach:** JS predicate combinators as the core, with optional declarative DSL syntax as future sugar.

## Core Combinators (~60 LOC in `lib/engine/property.js`)

```javascript
count(pred)            // count facts matching predicate name
sum(pred, argIndex)    // sum argument values of matching facts
has(pred, args?)       // exists a fact matching pred with optional args
forall(pred, check)    // all facts matching pred satisfy check
exists(pred, check)    // some fact matching pred satisfies check
absent(pred, args?)    // no fact matches pred with args
```

## Property Types

| Type | Quantification | Example |
|------|---------------|---------|
| Point property | One state | `count('pc')(state) === 1` |
| Universal | All leaves | `forall leaves. count('pc') === 1` |
| Existential | Some leaf | `exists leaf. has('token', {addr: bob})` |

## Tasks

- [ ] Implement `count`, `sum`, `has`, `forall`, `exists`, `absent` combinators
- [ ] Implement `matchPredicate(hash, predName)` helper using Store API
- [ ] Implement `extractArg(hash, argIndex)` for parameterized queries
- [ ] Integration with `getAllLeaves(tree)` for tree-wide checking
- [ ] Tests: property evaluation over known states

## References

- Martens (2015) — Ceptre consumptive/generative invariants (thesis Ch. 6)
- Das et al. (2021) — Nomos resource weight annotations
- RES_0050 — Metaproof verification landscape

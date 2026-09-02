---
title: Calculus Family Abstraction
created: 2026-02-10
modified: 2026-09-02
summary: Family system for shared calculus infrastructure
tags: [family, lnl, architecture]
status: implemented
---

# Calculus Family Abstraction

A **family** is a reusable structural-discipline bundle: declarative source + executable engine bindings. Calculi opt in via `@extends lnl` in their `.calc` file.

## Directory layout

```
family/lnl/
├── lnl.family        # Declarative: base types, sequent constructor, structural rules
├── family-config.js  # Executable: cc.family = { name, engine: { ... } }
└── lib/
    ├── persistent.js    # Persistent goal proving (proveNaive)
    ├── loli.js          # Dynamic rule matching (matchLoli)
    ├── loli-drain.js    # Persistent-trigger loli drain (drainLolis)
    └── existential.js   # ∃-variable resolution (resolveEx)
```

## lnl.family — declarative source

Defines base types (`term`, `structure`, `sequent`, `deriv`), the sequent constructor:

```
seq: structure -> structure -> structure -> sequent
  @position_modes "cartesian linear linear"
```

and structural rules tagged `@structural exchange/contraction/weakening` with `@position 1` (cartesian) or `@position 2` (linear).

`buildCalculus` **derives** `contextStructure` (`{ zones, properties, consumableZone, copySource, copyTarget }`) from these declarations. Declared-but-underivable structure (no unique consumable zone) is a loud load error. `DEFAULT_CONTEXT_STRUCTURE` in `lib/kernel/sequent.js` covers bare calculi that omit `@position_modes`.

## family-config.js — executable bindings

```js
const lnlFamily = { name: 'lnl', engine: { proveNaive, matchDynamicRule: matchLoli,
                                            drainDynamicRules: drainLolis, resolveEx } };
```

The generic engine receives these four hooks as data on `cc.family.engine` (composed by reference, M2 pattern). Absent `cc.family` → state-lookup-only persistent proving, null dynamic-rule slots.

## Layer DAG

`lib/` ↛ `family/` ↛ `calculus/`. `family/` may import `lib/`, never `calculus/`. Enforced by `tests/engine/layer-dag.test.js`.

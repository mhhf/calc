---
term: "absorption — Absorption (!L)"
summary: "Absorption: moves `!A` from the linear zone into the cartesian (persistent) zone."
tags: [ill, inference-rule, structural-rule, bridge]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `absorption` — Absorption (!L)

Absorption: moves `!A` from the linear zone into the cartesian (persistent) zone.

## Shape

```
G, A ; D |- C
────────────────  !L
G ; D, !A |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `absorption` |
| Pretty | `!L` |
| Connective | — |
| Side | — |
| Premises | 1 |
| Invertible | true |
| Structural | false |
| Bridge | linear_to_cartesian |
| Binding | — |

## In CALC

Emitted by the focused prover as `absorption`. Proof-tree/v1 nodes serialize with `"rule": "absorption"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

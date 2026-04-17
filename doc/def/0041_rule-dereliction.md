---
term: "dereliction — Dereliction (!D)"
summary: "Dereliction: uses a `!A` resource once, as if it were `A` in the linear zone."
tags: [ill, inference-rule, structural-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `dereliction` — Dereliction (!D)

Dereliction: uses a `!A` resource once, as if it were `A` in the linear zone.

## Shape

```
G ; D, A |- C
────────────────  !D
G ; D, !A |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `dereliction` |
| Pretty | `!D` |
| Connective | — |
| Side | — |
| Premises | 1 |
| Invertible | true |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `dereliction`. Proof-tree/v1 nodes serialize with `"rule": "dereliction"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

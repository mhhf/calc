---
term: "promotion — Promotion (!R)"
summary: "Promotion: introduces `!A` when `A` is provable under an empty linear context (exponential right-introduction)."
tags: [ill, inference-rule, structural-rule, bridge]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `promotion` — Promotion (!R)

Promotion: introduces `!A` when `A` is provable under an empty linear context (exponential right-introduction).

## Shape

```
G ; |- A
───────────  !R
G ; |- !A
```

## Properties

| Property | Value |
|---|---|
| Name | `promotion` |
| Pretty | `!R` |
| Connective | — |
| Side | — |
| Premises | 1 |
| Invertible | false |
| Structural | false |
| Bridge | linear_to_cartesian |
| Binding | — |

## In CALC

Emitted by the focused prover as `promotion`. Proof-tree/v1 nodes serialize with `"rule": "promotion"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

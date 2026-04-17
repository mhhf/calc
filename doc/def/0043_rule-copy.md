---
term: "copy — Contraction (Cartesian Copy)"
summary: "Contraction on cartesian context: duplicates a reusable (`!`-wrapped) assumption into the linear zone."
tags: [ill, inference-rule, structural-rule, structural]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `copy` — Contraction (Cartesian Copy)

Contraction on cartesian context: duplicates a reusable (`!`-wrapped) assumption into the linear zone.

## Shape

```
G, A ; D, A |- C
──────────────────  Copy
G, A ; D |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `copy` |
| Pretty | `Copy` |
| Connective | — |
| Side | — |
| Premises | 1 |
| Invertible | unspecified |
| Structural | true |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `copy`. Proof-tree/v1 nodes serialize with `"rule": "copy"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

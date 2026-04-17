---
term: "id — Identity Axiom"
summary: "Identity axiom: `A ⊢ A`. Closes a branch when the succedent matches a linear assumption."
tags: [ill, inference-rule, structural-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `id` — Identity Axiom

Identity axiom: `A ⊢ A`. Closes a branch when the succedent matches a linear assumption.

## Shape

```
  (no premises)
─────────────────  Id
; A |- A
```

## Properties

| Property | Value |
|---|---|
| Name | `id` |
| Pretty | `Id` |
| Connective | — |
| Side | — |
| Premises | 0 |
| Invertible | true |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `id`. Proof-tree/v1 nodes serialize with `"rule": "id"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

---
term: "exists_r — Exists Right (∃R)"
summary: "Introduces the `exists` (∃) connective on the right of the sequent."
tags: [ill, inference-rule, exists, positive-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `exists_r` — Exists Right (∃R)

Introduces the `exists` (∃) connective on the right of the sequent.

## Shape

```
G ; D |- A
───────────────────  ∃R
G ; D |- exists A
```

## Properties

| Property | Value |
|---|---|
| Name | `exists_r` |
| Pretty | `∃R` |
| Connective | exists |
| Side | right |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | metavar |

## In CALC

Emitted by the focused prover as `exists_r`. Proof-tree/v1 nodes serialize with `"rule": "exists_r"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `exists` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

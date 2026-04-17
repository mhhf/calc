---
term: "tensor_r — Tensor Right (⊗R)"
summary: "Introduces the `tensor` (⊗) connective on the right of the sequent."
tags: [ill, inference-rule, tensor, positive-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `tensor_r` — Tensor Right (⊗R)

Introduces the `tensor` (⊗) connective on the right of the sequent.

## Shape

```
G ; D |- A      G ; D' |- B
─────────────────────────────  ⊗R
G ; D, D' |- A * B
```

## Properties

| Property | Value |
|---|---|
| Name | `tensor_r` |
| Pretty | `⊗R` |
| Connective | tensor |
| Side | right |
| Premises | 2 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `tensor_r`. Proof-tree/v1 nodes serialize with `"rule": "tensor_r"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `tensor` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

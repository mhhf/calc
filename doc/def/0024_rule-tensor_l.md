---
term: "tensor_l — Tensor Left (⊗L)"
summary: "Eliminates the `tensor` (⊗) connective on the left of the sequent."
tags: [ill, inference-rule, tensor, positive-connective, left-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `tensor_l` — Tensor Left (⊗L)

Eliminates the `tensor` (⊗) connective on the left of the sequent.

## Shape

```
G ; D, A, B |- C
───────────────────  ⊗L
G ; D, A * B |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `tensor_l` |
| Pretty | `⊗L` |
| Connective | tensor |
| Side | left |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `tensor_l`. Proof-tree/v1 nodes serialize with `"rule": "tensor_l"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `tensor` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

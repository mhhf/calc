---
term: "forall_r — Forall Right (∀R)"
summary: "Introduces the `forall` (∀) connective on the right of the sequent."
tags: [ill, inference-rule, forall, negative-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `forall_r` — Forall Right (∀R)

Introduces the `forall` (∀) connective on the right of the sequent.

## Shape

```
G ; D |- A
───────────────────  ∀R
G ; D |- forall A
```

## Properties

| Property | Value |
|---|---|
| Name | `forall_r` |
| Pretty | `∀R` |
| Connective | forall |
| Side | right |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | eigenvariable |

## In CALC

Emitted by the focused prover as `forall_r`. Proof-tree/v1 nodes serialize with `"rule": "forall_r"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `forall` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

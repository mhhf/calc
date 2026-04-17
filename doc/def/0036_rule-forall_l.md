---
term: "forall_l — Forall Left (∀L)"
summary: "Eliminates the `forall` (∀) connective on the left of the sequent."
tags: [ill, inference-rule, forall, negative-connective, left-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `forall_l` — Forall Left (∀L)

Eliminates the `forall` (∀) connective on the left of the sequent.

## Shape

```
G ; D, A |- C
──────────────────────  ∀L
G ; D, forall A |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `forall_l` |
| Pretty | `∀L` |
| Connective | forall |
| Side | left |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | metavar |

## In CALC

Emitted by the focused prover as `forall_l`. Proof-tree/v1 nodes serialize with `"rule": "forall_l"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `forall` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

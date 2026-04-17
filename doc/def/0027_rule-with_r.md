---
term: "with_r — With Right (&R)"
summary: "Introduces the `with` (&) connective on the right of the sequent."
tags: [ill, inference-rule, with, negative-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `with_r` — With Right (&R)

Introduces the `with` (&) connective on the right of the sequent.

## Shape

```
G ; D |- A      G ; D |- B
────────────────────────────  &R
G ; D |- A & B
```

## Properties

| Property | Value |
|---|---|
| Name | `with_r` |
| Pretty | `&R` |
| Connective | with |
| Side | right |
| Premises | 2 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `with_r`. Proof-tree/v1 nodes serialize with `"rule": "with_r"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `with` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

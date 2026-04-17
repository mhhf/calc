---
term: "with_l1 — With Left (&L₁)"
summary: "Eliminates the `with` (&) connective on the left of the sequent."
tags: [ill, inference-rule, with, negative-connective, left-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `with_l1` — With Left (&L₁)

Eliminates the `with` (&) connective on the left of the sequent.

## Shape

```
G ; D, A |- C
───────────────────  &L₁
G ; D, A & B |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `with_l1` |
| Pretty | `&L₁` |
| Connective | with |
| Side | left |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `with_l1`. Proof-tree/v1 nodes serialize with `"rule": "with_l1"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `with` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

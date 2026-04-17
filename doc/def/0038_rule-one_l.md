---
term: "one_l — One Left (1L)"
summary: "Eliminates the `one` (1) connective on the left of the sequent."
tags: [ill, inference-rule, one, positive-connective, left-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `one_l` — One Left (1L)

Eliminates the `one` (1) connective on the left of the sequent.

## Shape

```
G ; D |- C
───────────────  1L
G ; D, I |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `one_l` |
| Pretty | `1L` |
| Connective | one |
| Side | left |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `one_l`. Proof-tree/v1 nodes serialize with `"rule": "one_l"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `one` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

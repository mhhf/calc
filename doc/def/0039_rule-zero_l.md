---
term: "zero_l — Zero Left (0L)"
summary: "Eliminates the `zero` (0) connective on the left of the sequent."
tags: [ill, inference-rule, zero, positive-connective, left-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `zero_l` — Zero Left (0L)

Eliminates the `zero` (0) connective on the left of the sequent.

## Shape

```
  (no premises)
──────────────────  0L
G ; D, zero |- C
```

## Properties

| Property | Value |
|---|---|
| Name | `zero_l` |
| Pretty | `0L` |
| Connective | zero |
| Side | left |
| Premises | 0 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `zero_l`. Proof-tree/v1 nodes serialize with `"rule": "zero_l"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `zero` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

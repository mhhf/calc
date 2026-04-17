---
term: "one_r — One Right (1R)"
summary: "Introduces the `one` (1) connective on the right of the sequent."
tags: [ill, inference-rule, one, positive-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `one_r` — One Right (1R)

Introduces the `one` (1) connective on the right of the sequent.

## Shape

```
  (no premises)
─────────────────  1R
G ; |- I
```

## Properties

| Property | Value |
|---|---|
| Name | `one_r` |
| Pretty | `1R` |
| Connective | one |
| Side | right |
| Premises | 0 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `one_r`. Proof-tree/v1 nodes serialize with `"rule": "one_r"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `one` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

---
term: "loli_r — Linear Implication Right (⊸R)"
summary: "Introduces the `loli` (⊸) connective on the right of the sequent."
tags: [ill, inference-rule, loli, negative-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `loli_r` — Linear Implication Right (⊸R)

Introduces the `loli` (⊸) connective on the right of the sequent.

## Shape

```
G ; D, A |- B
─────────────────  ⊸R
G ; D |- A -o B
```

## Properties

| Property | Value |
|---|---|
| Name | `loli_r` |
| Pretty | `⊸R` |
| Connective | loli |
| Side | right |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `loli_r`. Proof-tree/v1 nodes serialize with `"rule": "loli_r"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `loli` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

---
term: "oplus_r2 — Plus Right (+R₂)"
summary: "Introduces the `oplus` (⊕) connective on the right of the sequent."
tags: [ill, inference-rule, oplus, positive-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `oplus_r2` — Plus Right (+R₂)

Introduces the `oplus` (⊕) connective on the right of the sequent.

## Shape

```
G ; D |- B
────────────────  +R₂
G ; D |- A + B
```

## Properties

| Property | Value |
|---|---|
| Name | `oplus_r2` |
| Pretty | `+R₂` |
| Connective | oplus |
| Side | right |
| Premises | 1 |
| Invertible | unspecified |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `oplus_r2`. Proof-tree/v1 nodes serialize with `"rule": "oplus_r2"`. The rule is loaded from [`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `oplus` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

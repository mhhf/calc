---
term: "monad_l — Monad Left ({_}L)"
summary: "Eliminates the `monad` ({·}) connective on the left of the sequent."
tags: [ill, inference-rule, monad, negative-connective, left-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `monad_l` — Monad Left ({_}L)

Eliminates the `monad` ({·}) connective on the left of the sequent.

## Shape

```
G ; D, A |- { C }
───────────────────────  {_}L
G ; D, { A } |- { C }
```

## Properties

| Property | Value |
|---|---|
| Name | `monad_l` |
| Pretty | `{_}L` |
| Connective | monad |
| Side | left |
| Premises | 1 |
| Invertible | false |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `monad_l`. Proof-tree/v1 nodes serialize with `"rule": "monad_l"`. This rule is **synthesized** by the calculus loader from the connective declaration in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc) — it is not written out explicitly in `ill.rules`. Dispatch is handled by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `monad` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

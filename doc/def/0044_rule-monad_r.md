---
term: "monad_r — Monad Right ({_}R)"
summary: "Introduces the `monad` ({·}) connective on the right of the sequent."
tags: [ill, inference-rule, monad, negative-connective, right-rule]
autogen: true
autogen_source: calculus/ill/ill.rules
see_also: []
---

# `monad_r` — Monad Right ({_}R)

Introduces the `monad` ({·}) connective on the right of the sequent.

## Shape

```
G ; D |- A
────────────────  {_}R
G ; D |- { A }
```

## Properties

| Property | Value |
|---|---|
| Name | `monad_r` |
| Pretty | `{_}R` |
| Connective | monad |
| Side | right |
| Premises | 1 |
| Invertible | true |
| Structural | false |
| Bridge | — |
| Binding | — |

## In CALC

Emitted by the focused prover as `monad_r`. Proof-tree/v1 nodes serialize with `"rule": "monad_r"`. This rule is **synthesized** by the calculus loader from the connective declaration in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc) — it is not written out explicitly in `ill.rules`. Dispatch is handled by the rule interpreter (`lib/prover/rule-interpreter.js`).

See also the connective definition in [`calculus/ill/ill.calc`](../../calculus/ill/ill.calc), which assigns `monad` its arity and polarity.

---

> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._

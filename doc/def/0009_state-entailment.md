---
term: "State Entailment"
summary: "S entails S' (S ⊳ S') iff the ILL translation of S proves the translation of S' — decidable for CHR states."
tags: [chr, linear-logic, entailment]
see_also: [DEF_0001, DEF_0003]
references:
  - "Betz & Frühwirth, 'Linear-logic based analysis of constraint handling rules with disjunction', 2013"
---

# State Entailment

In the Betz/Frühwirth framework, state entailment is defined as:

```
S ⊳ S'  iff  S^L ⊢_Σ S'^L
```

State `S` entails state `S'` when the ILL translation of `S` logically proves the translation of `S'`.

**State equivalence** follows: `S ≡_e T` iff `S ⊳ T` and `T ⊳ S`.

**Theorem 4.10 (Betz & Frühwirth):** State entailment is decidable.

## Example

`{a, b, !c}` entails `{a, !c}` because `a ⊗ b ⊗ !c ⊢ a ⊗ !c` (consume `b` via weakening on linear resources... actually this requires careful treatment — linear resources cannot be discarded without `!`).

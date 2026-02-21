---
term: "CHR Soundness (Theorem 4.8)"
summary: "Every operational CHR derivation corresponds to a valid ILL deduction — operational reachability implies logical entailment."
tags: [chr, linear-logic, soundness, theorem]
see_also: [DEF_0001, DEF_0010]
references:
  - "Betz & Frühwirth, 'Linear-logic based analysis of constraint handling rules with disjunction', 2013"
---

# CHR Soundness (Theorem 4.8)

**Theorem (Betz & Frühwirth 2013):** `S ↦* T ⟹ S^L ⊢_Σ T^L`

Every operational CHR derivation (a sequence of rule applications transforming state `S` to state `T`) corresponds to a valid deduction in Intuitionistic Linear Logic. Operational reachability implies logical entailment.

## Example

If a CHR program transforms `{gcd(6), gcd(4)}` into `{gcd(2)}` via repeated simpagation, then `gcd(6) ⊗ gcd(4) ⊢ gcd(2)` is a valid ILL sequent.

## In CALC

This result transfers directly: every execution trace of CALC's forward engine is a valid ILL proof. The forward engine is sound by construction — no separate proof needed.

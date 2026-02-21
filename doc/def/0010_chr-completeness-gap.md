---
term: "CHR Completeness Gap"
summary: "Full completeness (every ILL derivation = operational CHR derivation) fails in general, unlike soundness which always holds."
tags: [chr, linear-logic, completeness, soundness]
see_also: [DEF_0003, DEF_0007]
references:
  - "Betz & Frühwirth, 'Linear-logic based analysis of constraint handling rules with disjunction', 2013"
---

# CHR Completeness Gap

While soundness (operational derivation ⟹ ILL proof) always holds, full **completeness** (every ILL derivation corresponds to an operational derivation) fails because:

1. **ILL allows arbitrary resource shuffling** not corresponding to any rule application
2. **Propagation history** restricts operational derivations beyond what the logic captures

Completeness holds only for specific program classes (e.g., programs without propagation rules, or with restricted resource patterns).

## Example

An ILL proof might shuffle linear resources in ways that don't correspond to any CHR rule firing — the proof is valid in logic but has no operational counterpart.

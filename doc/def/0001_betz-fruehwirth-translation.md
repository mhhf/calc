---
term: "Betz/Frühwirth Translation (-)^L"
summary: "A mapping from CHR constraints and rules into Intuitionistic Linear Logic formulas."
tags: [chr, linear-logic, translation, soundness]
see_also: [DEF_0002, DEF_0004]
references:
  - "Betz & Frühwirth, 'A linear-logic semantics for Constraint Handling Rules', 2005"
  - "Betz & Frühwirth, 'Linear-logic based analysis of constraint handling rules with disjunction', 2013"
---

# Betz/Frühwirth Translation (-)^L

The translation `(-)^L` maps CHR constructs into ILL (Intuitionistic Linear Logic):

| CHR construct | ILL translation |
|---|---|
| User-defined constraint `c(t̄)` | Linear atom `c(t̄)` |
| Built-in constraint `b(t̄)` | `!b(t̄)` (banged/persistent) |
| Conjunction | Tensor (`⊗`) |
| True | `1` (unit) |

## Example

CHR simpagation rule `r @ H₁ \ H₂ ⟺ G | B` translates to:

```
H₁^L ⊗ H₂^L ⊗ G^L ⊢ H₁^L ⊗ ∃ȳ.(B^L ⊗ G^L)
```

- `H₁` = kept head (appears both sides)
- `H₂` = removed head (consumed, left side only)
- `G` = guard (banged, both sides)

## In CALC

Linear facts = user-defined constraints (no bang). Persistent facts (`!A`) = built-in/kept heads. Forward rules = simpagation rules. FFI/backward proving = guard evaluation.

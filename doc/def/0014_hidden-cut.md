---
term: "Hidden Cut (⊗_L as Cut)"
summary: "In Stéphan's ω_l, the ⊗_L rule splits resources between a 'lemma' and its 'use', acting as a hidden instance of Cut."
tags: [proof-theory, cut, linear-logic, sequent-calculus]
see_also: [DEF_0013]
references:
  - "Stéphan, 'Sequent calculus for CHR', ICLP, 2018"
---

# Hidden Cut (⊗_L as Cut)

In Stéphan's ω_l system, the left-elimination of tensor (`⊗_L`) is a **hidden use of Cut** in linear logic. It splits resources between:

- A **lemma** (left subproof — solve one constraint)
- Its **use** (right subproof — solve the remaining constraints)

Both ω_l and ω_l^⊗ eliminate these Cut instances to linearize derivations.

## Example

Goal `a ⊗ b` with resources `{r₁, r₂, r₃}`:

```
⊗_L splits into:
  Left:  {r₁, r₂} ⊢ a    (lemma: solve a)
  Right: {r₃} ⊢ b         (use: solve b with remaining)
```

The resource split is the "cut" — it's a choice point that determines which resources go where.

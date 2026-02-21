---
term: "Stéphan's ω_l System"
summary: "A sequent calculus where CHR derivations ARE proof trees — each CHR step is an inference rule application."
tags: [chr, linear-logic, proof-theory, sequent-calculus]
see_also: [DEF_0001, DEF_0003, DEF_0014, DEF_0015]
references:
  - "Stéphan, 'Sequent calculus for CHR', ICLP, 2018"
---

# Stéphan's ω_l System

Unlike Betz/Frühwirth (who show derivations *imply* entailment via translation), Stéphan constructs a sequent calculus where CHR derivations **are** proof trees. Each CHR operational step corresponds directly to an inference rule application.

Key difference: Betz encodes the program as `!r₁ ⊗ !r₂` (banged rules). Stéphan uses `r₁ & r₂` (additive conjunction = committed choice).

Two sequent forms:

| Form | Sequent | Meaning |
|---|---|---|
| Non-focused | `(Γ ▸ Ω_# ◁ S_↑ ⊢ S_↓)` | Process goal `Ω_#` using program `Γ` |
| Focused | `(Γ ! Δ ▷ a ◁ S_↑ ⊢ S_↓)` | Focused on constraint `a`, trying rules `Δ` |

**Theorem 7:** ω_l is sound AND complete w.r.t. ω_t. A CHR goal is solved by program `Γ` iff there exists an ω_l proof.

## Key Inference Rules

- **true**: axiom (goal solved)
- **⊗_L**: split goal, allocate resources (hidden Cut)
- **W**: Weakening (skip rule)
- **F**: Focusing (select constraint)
- **↑**: Inactivate (store constraint unchanged)
- **\\⟺**: Apply (fire simpagation rule)

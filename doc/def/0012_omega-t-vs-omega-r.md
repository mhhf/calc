---
term: "ω_t vs ω_r (CHR Operational Semantics)"
summary: "ω_t is the abstract nondeterministic CHR semantics; ω_r is the refined deterministic semantics used in implementations."
tags: [chr, operational-semantics]
see_also: [DEF_0002, DEF_0013]
references:
  - "Duck, Stuckey, Garcia de la Banda, Holzbaur, 'The refined operational semantics of CHR', ICLP, 2004"
---

# ω_t vs ω_r (CHR Operational Semantics)

**ω_t (theoretical):** The abstract operational semantics — highly nondeterministic. Does not fix rule order, constraint order, or matching order. Any applicable rule may fire at any time.

**ω_r (refined):** The implemented semantics — deterministic. Uses textual rule order, active-constraint driven evaluation. Fixes all three sources of nondeterminism.

**Correctness:** ω_r is correct w.r.t. ω_t — every ω_r derivation is a valid ω_t derivation.

## Example

Given rules `r₁` and `r₂` both applicable:
- ω_t: either may fire (nondeterministic)
- ω_r: `r₁` fires first (textual order)

## In CALC

CALC's forward engine uses a committed-choice semantics closer to ω_r (first match wins in `run()`), but symexec explores all matches (closer to ω_t).

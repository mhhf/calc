---
term: "Four CHR Nondeterminism Sources"
summary: "CHR has four sources of nondeterminism: rule selection, disjunction, store ordering, and multi-headed matching."
tags: [chr, nondeterminism]
see_also: [DEF_0012, DEF_0004]
references:
  - "Stéphan, 'Sequent calculus for CHR', ICLP, 2018"
---

# Four CHR Nondeterminism Sources

1. **Don't-care rule selection** (committed choice) — when multiple rules apply, which one fires. By design.
2. **Don't-know disjunction** (CHR∨) — disjunctive rule bodies create genuine choice points. Deliberate.
3. **Constraint store ordering** — the store is a multiset, so wake-up order is unspecified.
4. **Multi-headed matching** — when multiple constraints match a head, which ones are chosen.

Stéphan's ω_l^⊗ (which uses a sequence store instead of multiset) eliminates sources 3 and 4, making it deterministic but incomplete.

## In CALC

CALC's `run()` (committed-choice) resolves source 1 by first-match. Symexec explores all matches (source 1 = branching). Source 2 = `⊕` branching. Sources 3+4 are resolved by the strategy stack's deterministic iteration order.

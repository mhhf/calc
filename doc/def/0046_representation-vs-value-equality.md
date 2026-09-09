---
term: "Representation equality vs. value equality (state canonicity)"
summary: "Hash identity (===) is representation equality; value equality is theory-relative. The engine keeps them interchangeable INSIDE live states via the state-canonicity invariant; certifiers compare modulo the theories instead of trusting it."
tags: [content-addressed-store, hash-consing, soundness, engine-metatheory, equational-theory]
see_also: []
---

# Representation equality vs. value equality

Two ground terms can denote one value in different representations:
`binlit 3` and `i(i(e))` are theory-equal (binlit theory) but
hash-distinct. In a content-addressed store, `===` on hashes is
**representation** equality; **value** equality is a judgment relative
to the registered equational theories (`unify` on ground terms decides
it). The two cannot be identified store-globally: theories are calculus
data while the Store is calculus-agnostic, so a canonical form is not
well-defined at the store level — hashes must stay theory-independent
(serialization stability, cross-calculus reuse).

## The state-canonicity invariant

Every fact hash in a **live engine state** is a fixpoint of the
composed theory canonicalizer (`buildCanonicalizer(cc.theories)`).
Under this invariant, hash identity inside the engine — FactSet rows,
dedup sets, memo keys, PRF value-derived keys, cohort grouping — IS
value identity. Enforced at every fact-entry boundary:

- **Forward/timed production** — compile-time `canonPatterns` gate
  (`compile.js conseqCanonPatterns`): a consequent applying a theory
  class-constructor over a variable (`tok (i X)`) is flagged; the
  produce funnel (`state-ops.js`, timed `fire`) canonicalizes only
  flagged patterns — unflagged rules pay nothing.
- **Plain-object state entry** (`canonObject` in exec/explore/
  normalizeTimedState) — Store-level API callers may hand any
  representation; counts merge on collision.
- **Dynamic-rule materialization** (`family/lnl/lib/loli.js`) — one
  canonicalize pass over the instantiated body.
- **Clause-resolution outputs** (pre-existing) — resolve-all,
  compiled-clause tiers, compose tabling, backward cache.

Pinned by `tests/engine/state-canonicity.test.js` (all six pins fail
against a production path without the gate).

## Who may rely on what

- **Engine internals** rely on the invariant (hash-keyed structures).
- **Certifiers/checkers do NOT trust it** — they receive rules and
  states from outside and compare modulo the theories
  (certify-confluence `_thEq`; the fire/draw checkers prove stamp and
  theory goals clause-only). Defense-in-depth, not redundancy.
- **strlit has no canonical form** (its `canonicalize` is identity):
  string-valued facts may split rows by representation
  (`strlit "ab"` vs `cons`-spine). Matching stays correct (theory
  rewriting); only row-merging is unavailable. Known, deliberate:
  folding cons-spines eagerly would fight partial string patterns.

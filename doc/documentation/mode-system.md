---
title: The Mode System (Well-Modedness Checker)
modified: 2026-09-10
summary: How lib/engine/well-moded.js checks well-modedness at load time, discharging THY_0039 Theorem 3.
tags: [symexec, forward-chaining, modes, architecture, engine-theory]
---

# The Mode System

`lib/engine/well-moded.js` is a load-time fence (task #81 / P7) that checks a
program is **well-moded** with **certified-functional** forced steps — the
hypothesis of THY_0039 Theorem 3 (parametric adequacy). Its metatheory is
THY_0039 §6; this file is how the check works now.

It runs in `_buildCalc` after `materializeLoadTimeClauses` and before `checkAll`,
whenever there are clauses or forward rules. It attaches:

- `calc.functionalPreds : Set<"pred#outPos">` — the certified-functional forced
  modes (consumed by the forcing-goal check and task #84);
- `calc.wellModedLint : { warnings, errors } | null` — the findings.

**Warn-first.** Every finding is a warning. A calculus flips them to a hard
load error by setting `cc.wellModed = 'strict'` (the `cc.typeCheck: 'strict'`
pattern). ILL stays warn-first: its corpus has three residual findings (below).

## The three analyses

**§6.1 Functionality certification** (`certifyFunctional`). A predicate is
certified functional at output position `i` when either

- *clausal*: its clause heads are input-disjoint on the complement of `i`
  (`nonUnifiable` pairwise — ≤ 1 clause per ground input), AND each clause's
  body functionally determines the head's output from its inputs through
  currently-certified premises (`bodyDetermines`, a greatest fixpoint that
  admits self/mutual recursion but rejects a body grounding its output through a
  relational or EDB predicate); or
- *FFI*: a non-`multiModal` FFI predicate's declared `-` positions
  (`cc.ffi.parsedModes`) — the spec-functional carve-out, sound because the
  FFI≡clause invariant makes the clause resolution the same unique function.

`checkForcingGoals` then requires every FORCED slot — found by a dataflow
saturation over the rule's existential goals (`existentialGoals`), mirroring the
runtime resolver: a goal determines a slot at position `i` once its other
positions are ground — to name a certified mode. A non-certified force is a G1
warning.

**§6.2 Parameter-flow + V1** (`buildTaint`, `checkStructuralMatch`). An abstract
interpretation over parameter-freeness of predicate-argument **leaf paths**.
`taint(pred)` is the set of leaf paths that may hold a parameter; sources are
the existential slots, and the conduit transfers taint through consume→produce
edges. Only value leaves are tainted, never the constructor spine.

Unbounded recursion (a stack of parameters, values at `0.1ᵏ.0`) uses a **regular
star-path** abstraction (`canonPath`): a run of a repeated child index longer
than any pattern inspects collapses to a star `c*` (0+ repeats), keeping
value-vs-spine exact where a depth truncation would fold a value path into a
spine one. **V1** (`structuralAtStar`) DFS-matches the NFA of a starred taint
path against a finite pattern; a non-variable at the parameter leaf decomposes
it (flag); a spine traversal or an ancestor variable is opaque.

**§6.3 Guard-coverage + V2** (`checkGuardCoverage`). When a parameter is the
scrutinee of a ⊕ (its value decides the branch via eq/neq guards), the
alternatives must COVER the value space and be mutually EXCLUSIVE. Region
enumeration — each distinct guard constant, plus the generic value distinct from
all of them — evaluates each alternative's guards on the scrutinee by ground
evaluation (exact for eq/neq over one scrutinee). Zero feasible alternatives in
a region is a coverage failure; more than one is an exclusion failure. A guard
comparing the scrutinee to a non-constant is undecidable in the `{eq,neq}`
fragment (task #84).

## Soundness direction

The analysis over-approximates: it may reject a well-moded program, never accept
an ill-moded one (THY_0039 §6.4, Theorem 4). Certification is sound (certified ⇒
functional); non-certified predicates are permanently deferred. Rejecting-more
and deferring-more both cost completeness, never correctness.

## The EVM corpus

The corpus certifies its forced arithmetic (`plus#2`, `to256#1`, `mul#2`,
`eq_bool#2`, …), has zero V1 (every stack/memory match binds values as variables
and walks only the spine), and certifies jumpi's `!neq C 0 ⊕ !eq C 0` (V2). The
three residual warnings are `cd_copy`/`code_copy`: clause-defined copy loops
whose determinism rests on mutually-exclusive `le`/`lt` **body guards** — beyond
the eq/neq decidable fragment, which is exactly task #84 (certified-total
predicates). ILL therefore stays warn-first until #84 lands.

Pins: `tests/engine/well-moded.test.js`.

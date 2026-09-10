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

**Warn-first, then strict.** Every finding is a warning; a calculus flips them
to a hard load error by setting `cc.wellModed = 'strict'` (the
`cc.typeCheck: 'strict'` pattern). **ILL is now strict** (task #85): its corpus
is confirmed inside the accepted set. Strict enforcement targets a *fresh,
unspecialized SOURCE load* — a bytecode/fused artifact and a compose-cache
snapshot restore (`skipCompose`) stay warn-first, because the source-level taint
analysis reads their inlined rules imprecisely (an inlined `arr_get` matching a
ground `pc`'s structure trips V1) and the source's well-modedness was already
enforced at its own load. `opts.wellModed: 'warn'` opts out per load (used by
the deliberately ill-moded unit fixtures).

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
  FFI≡clause invariant makes the clause resolution the same unique function; or
- *guard-exclusive* (task #85, `clausesSeparated`/`orderUnsat`): heads that
  unify on their inputs are still ≤ 1-firing when their bodies are pairwise
  mutually exclusive — the union of their region constraints (head-literal
  equalities + order/eq/neq body guards, lifted onto shared head-input symbols)
  is UNSAT in the order+eq theory. A body var fixed by a certified determiner is
  canonicalised to a shared symbol; a declared unbounded sum
  (`cc.domain.sumPreds`, `plus A B C ⊢ C = A+B`) injects `C > A`, `C > B`. The
  non-strict `C ≥ summand` facts are sound only for non-negative summands, so
  `sumPreds` may be declared only over a domain with a non-negative floor
  (`cc.domain.orderDomain.min ≥ 0`, enforced warn-first by `checkSumPreds`).
  This certifies the `cd_copy`/`code_copy`/`code_read32` copy loops (determinism
  = `le End Offset` vs `lt Offset End`, `Size = 0` vs `neq Size 0`).

`checkForcingGoals` then requires every FORCED slot — found by a dataflow
saturation over the rule's existential goals (`existentialGoals`), mirroring the
runtime resolver: a goal determines a slot at position `i` once its other
positions are ground — to name a certified mode. A non-certified force is a G1
warning.

**§6.1′ Decision-procedure certification** (`certifyDecidable`). The
decision-procedure twin of functionality. A predicate is a certified **total
decision procedure** — every ground argument tuple decided true/false,
terminating — when it is a non-`multiModal` FFI predicate whose *every* position
is an input (`+`): a boolean judgment with no output slot (`lt : '+ +'`). The
result is `calc.decidablePreds : Set<predName>`. This is a different axis from
`functionalPreds`, which certifies a unique output at a `-` position; an order
guard has no output position, so it is (correctly) never functional. The set is
consumed by the runtime G2 order-tell prune (task #84, THY_0039 §4): a ground
tell of a false order atom (`lt 7 5`) is pruned. `checkConstraintDecls` warns
(warn-first) on any predicate the calculus declares an order guard
(`cc.domain.constraintPreds.order`) that is not so certified — a mis-declaration
whose ground prune would rest on an unbacked comparator; explore refuses it by
intersecting the declared order guards with `decidablePreds`.

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
scrutinee of a ⊕ (its value decides the branch), the alternatives must COVER the
value space and be mutually EXCLUSIVE. The fragment is eq/neq **plus the
certified-total order guards** (`constraintPreds.order` ∩ `decidablePreds`, task
#86). Decision is representative-point enumeration over the declared value
domain (`cc.domain.orderDomain`: a well-founded floor `min` and a `discrete`
flag; `guardCoverageVerdict`): the guards compare the scrutinee to constants
`{cᵢ}`, whose arrangement partitions the domain into the points `{cᵢ}` and the
gaps between them; each guard is constant on a cell, so testing one integer per
non-empty cell — the floor and each `cᵢ, cᵢ ± 1` (clamped ≥ floor) — is exact
and complete (`guardHolds` evaluates `=`/`≠`/`<`/`≤`) **on a discrete order**.
Discreteness is the soundness gate (on a dense domain `≤ 3 ⊕ ≥ 4` is not
covering but has no integer witness of the gap), so an order guard over a
non-`discrete` domain is refused; eq/neq are density-agnostic. Zero feasible
alternatives in a cell is a coverage failure; more than one is an exclusion
failure. A guard comparing the scrutinee to a non-constant, via an uncertified
predicate, or over a non-discrete domain, stays undecidable and is flagged. The
`orderUnsat` and `guardCoverageVerdict` decision procedures are fuzzed against
brute force (`tools/fuzz-well-moded.js`).

## Soundness direction

The analysis over-approximates: it may reject a well-moded program, never accept
an ill-moded one (THY_0039 §6.4, Theorem 4). Certification is sound (certified ⇒
functional); non-certified predicates are permanently deferred. Rejecting-more
and deferring-more both cost completeness, never correctness.

## The EVM corpus

The corpus certifies its forced arithmetic (`plus#2`, `to256#1`, `mul#2`,
`eq_bool#2`, …), has zero V1 (every stack/memory match binds values as variables
and walks only the spine), and certifies jumpi's `!neq C 0 ⊕ !eq C 0` (V2). The
`cd_copy`/`code_copy` copy loops — clause-defined loops whose determinism rests
on mutually-exclusive `le`/`lt` **body guards** — are certified by the §6.1
guard-exclusive route (task #85, via `code_read32` and `plus`'s declared
monotonicity), so the corpus is **fully clean** and **ILL is `wellModed:
'strict'`**. (A bytecode-specialized/fused load can still surface a V1
false-positive on an inlined rule; those loads stay warn-first — see the
strict-scope note above.)

Pins: `tests/engine/well-moded.test.js` (incl. the guard-exclusivity block +
`orderUnsat` unit + the strict-enforcement throw).

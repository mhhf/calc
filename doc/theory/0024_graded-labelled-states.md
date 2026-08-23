---
title: "Graded Labelled States: Annotation as Context Label, `at` as its Internalization"
created: 2026-08-23
modified: 2026-08-23
summary: "The engine state of a graded timed calculus is a LABELLED multiset — rows (formula, label, count) with the formula content-addressed and the label drawn from a calculus-declared graded algebra — while the calculus keeps `at` as a formula connective internalizing the label (hybrid-logic style). An adequacy lemma makes the two views interchangeable; every label observation passes through a reification boundary (the coalescer's exclusion set enumerates exactly the observers). Consequences: term addresses are time-stable (the Store stops growing with elapsed time), rebase is an O(live) table rebuild-swap with zero term allocation, and the multiplicity column of run-length states is recognized as the ℕ-instance of the same construction."
tags: [till, timed, labels, labelled-deduction, hybrid-logic, subexponentials, coeffects, graded-monad, content-addressing, fact-set, representation]
category: "Engine Theory"
unique_contribution: "Three results: (1) the two-level split — `at` as internalizing connective in the sequent calculus, labels on multiset rows in the operational state — with an adequacy lemma showing match/fire commute with the encoding, so the labelled representation is a semantics-preserving change of state representation, not a new logic; (2) the OBSERVER-BOUNDARY principle: a label needs term-level existence only where a rule binds or computes with it, and the coalescer's derived exclusion set already computes exactly that observer set — reification is lazy and rare by the same argument that makes coalescing effective; (3) address stability as the operational payoff of labelled deduction: content-addressed term identity must be time-independent or the arena degenerates into the temporal-Datalog holds(P,T) pattern — the count column of run-length states and the stamp column are the SAME construction over different grade algebras (ℕ vs ℚ≥0), giving one generic mechanism for future annotation logics (provenance semirings, spatial regions, epistemic indices)."
references:
  - "Chaudhuri & Despeyroux (2013). A Hybrid Linear Logic for Constrained Transition Systems. TYPES/LIPIcs 26 — worlds as a monoid; `at` internalizes hybrid satisfaction."
  - "Olarte, Pimentel & de Paiva (2017/2019). Hybrid and Subexponential Linear Logics; Hybrid linear logic, revisited. ENTCS/MSCS — formula-level `at` is proof-theoretically redundant over context labels (SELL encoding)."
  - "Nigam, Olarte & Pimentel (2009–2017). Subexponentials in linear logic — modalities as context zones indexed by a preordered signature."
  - "Gabbay (1996) LDS; Negri (2005) labelled sequent calculi; Simpson (1994) — the labelled-deduction methodology: semantic parameters as labels with a separate label theory."
  - "Atkey (2018) QTT; Orchard et al. (2019) Granule; Petricek, Orchard & Mycroft (2013/14) coeffects — grades on CONTEXT ENTRIES (x :ρ A) over a preordered semiring."
  - "Kanovich, Kirigin, Nigam, Scedrov & Talcott (2016). Timed Multiset Rewriting. FORMATS — configurations as external (fact, timestamp) pairs; the direct MSR precedent."
  - "McSherry et al. — differential dataflow's (data, time, diff) triples; consolidation ≈ coalescing."
  - "Bengtsson & Yi (2004); Behrmann et al. (2004) — timed-automata zones: state = (location, DBM); LU-extrapolation ≈ coalesce/rebase."
  - "Green, Karvounarakis & Tannen (2007). Provenance Semirings. PODS — the annotation column over a commutative semiring."
  - "doc/theory/0018 (delay-graded lax monad), 0019 (timed matching/settle), 0022 (fenced grade algebras); TODO_0278 (the scale ladder this lands in)."
---

# Graded Labelled States

## The principle

A graded timed calculus needs its annotations in two places, and they are
not the same place:

- **In the logic**, `at : formula -> delay -> formula` is a genuine
  connective — `A@t` is a proposition, the retiming axiom
  `at_l : A@T1 ⊢ A@T2 ← !le T1 T2` gives its proof theory, and the
  backward prover and adequacy theorems (THY_0018/0019) reason with it.
  This is hybrid logic's satisfaction operator, internalized.
- **In the engine state**, the label lives OUTSIDE the term: the state is
  a multiset of rows `(A, ℓ, n)` — formula hash `A` (content-addressed),
  label `ℓ` from the calculus-declared grade algebra, multiplicity `n`.
  No `at`-node exists at runtime; `at` appears only in static rule
  patterns (compile-time) and at interchange boundaries (serialization,
  plain-object states, event records).

The literature converges on this split from five directions: labelled
deduction (Gabbay/Negri/Simpson) makes semantic parameters labels with a
separate label theory; SELL shows modalities are context-zone indices;
HyLL has both mechanisms and Olarte–Pimentel–de Paiva proved the
formula-level `at` adds no proof-theoretic expressiveness over the
labels; QTT/Granule put grades on context entries `x :ρ A`; and timed MSR
(Kanovich et al. 2016) writes configurations as external `(fact, t)`
pairs — having migrated away from time-as-predicate-argument. On the
systems side the same shape is universal: differential dataflow's
`(data, time, diff)`, timed automata's `(location, zone)`, provenance
semirings' annotation column. The only precedent for time INSIDE interned
fact identity is temporal Datalog's `holds(P, T)` — the state-explosion
pattern zone abstraction was invented to escape.

## The label algebra

A calculus declares, per label kind (till declares one: the stamp):

    parse  : term → value        -- ground stamp term → algebra value
    reify  : value → term        -- lazy internalization (memoized)
    cmp    : value × value → ord -- the availability order (scheduling)
    add    : value × value → value -- the effect monoid ⊗ (delay composition)
    unit   : value               -- ⊗-unit; the default label (D11)
    float  : value → ℝ ∪ {NaN}   -- monotone order fast path (sound comparator)
    mix    : value → int32       -- Zobrist contribution (value-derived)

till instantiates: values are exact rationals `(n, d)`, `cmp`/`add` from
`lib/rat.js`, `parse`/`reify` = `ratParts`/`putRat`, the float is the
correctly-rounded double (monotone, hence a sound order prefilter —
TODO_0277). The MULTIPLICITY column of run-length states is this same
construction at the semiring ℕ: count is a label the engine already
stores beside the address, not inside it. Future annotation logics
(provenance semirings, spatial regions, epistemic indices) plug in as
new algebras, not new engine code — exactly the modularity labelled
deduction promises.

Values are interned per-State in a **stamp table** (value ↔ small id,
with cached float, mix, and reified term). The table is session-local
and compactable — unlike the append-only Store arena, dead labels die.

## The graded firing law

Firing is the graded structure, stated on labels:

    activation a(m) = ⊔ { ℓ(x) | x consumed or read by m } ⊔ after-bounds
    output label    = a(m) ⊗ d          -- d the rule's monad grade (delay)

`⊔` is the join in the availability order (max for time), `⊗` the effect
monoid (+ for time). This is THY_0018's delay-graded lax monad read off
the state representation: the labelled multiset is the Kleisli context
of the graded monad, and the retiming axiom `at_l` is precisely the
semantic license for `⊔` (delaying availability is free; never early).

The COUNT column gets its own firing law by the same construction at ℕ:
cohort firing (TODO_0278 B1) fires a match once at multiplicity k —
consume k·take, produce k·count at one label — exactly when the k
sequential fires are forced (unique candidate, no same-instant
enablement), so the batched step is the k-fold action of the rule on
the ℕ-label, state-identical to the unrolled prefix by induction.

## Adequacy

**Lemma (representation adequacy).** Let `⌈·⌉` encode a labelled state as
a formula multiset by `⌈(A, ℓ, n)⌉ = at(A, reify ℓ)^n` (unit labels may
drop the wrapper, D11). Then `⌈·⌉` is a bijection onto stamped multisets,
and for every rule r and conflict resolution: match(r, S) ≅ match(r, ⌈S⌉)
(same assignments, same activations) and ⌈fire(m, S)⌉ = fire(m, ⌈S⌉).
Hence settle, settleExplore, and every derived observable (stamped
multiset, event multiset, quiescence, next) are representation-invariant.

*Proof sketch.* Both directions of each step are label-local. (⇒) A
pattern observes a row through exactly two channels: the inner formula
(matched on the content address — identical in both representations) and
the label, which enters only through binding sites (`A@Q`, `!_k A@T`) and
guard/goal computation (windows, delays, persistent-goal arguments) — all
of which pass through `parse`/`reify`, which are mutually inverse on
ground stamp terms (canonStamp normalizes the term side first). Output
labels are produced only by the firing law, which is computed in the
algebra on both sides (`putRat ∘ add ∘ ratParts` = `add` under the
bijection). (⇐) `at` cannot occur in consequents (stamps come only from
the scheduler — convert.js rejects it), cannot nest (grammar), and the
persistent zone is unlabelled (timeless), so the encoding is total and
the bijection preserves zones. ∎

Two observables are NOT preserved, and are contractually excluded: the
32-bit state hash (the labelled Zobrist mixes (inner, mix ℓ, n) instead
of (at-hash, n)) and the equal-label enumeration tiebreak (inner-address
order instead of pair-address order). Both are representation-internal
names; programs whose outcomes depend on them are exactly the
draw-sensitive ones, and for those ANY draw is a valid world
(settleExplore's contract — the same class in which coalesce and rebase
already live). The change renames which world a seed picks, once.

## The covariant-draw corollary (TODO_0278 A3a)

Labels-beside-terms makes draw covariance definable: a tie whose rules
bind no stamp position has a draw identity that is a function of
signature-visible content only (counts, `!_W` totals, clause outputs are
forced equal by recurrence; only stamp-binding patterns can smuggle an
absolute time into θ). Give such draws a PRF input built from the tied
set's canonical FRONTIER-RELATIVE identities — with coalesce-eligible
cohorts encoded at their normal form and takes aggregated per (inner,
stamp), so neither coalesce cadence nor cohort split/merge is visible —
and the recurrence induction extends through draws: `state(t+p) =
shift_p(state(t))` INCLUDING the choices. Tie-poisoned periodic systems
(multi-consumer economies) then certify exactly, and acceleration stays
state-identical to the coalesced run on drawing programs.

## The observer boundary

A label needs term-level existence only where the logic can SEE it. The
observer set — stamp-binding patterns, windowed rules, counted stamped
parcels, possessed lolis — is precisely what the coalescer already
derives as its exclusion set (TODO_0277). Reification is therefore lazy
and rare by the same argument that makes coalescing effective: a program
whose rules observed most stamps would neither coalesce nor certify, and
already sits outside the fast fragment. The millions of unobserved
timestamps a long run mints never touch the Store.

## Address stability (the operational payoff)

With labels inside the term (`at(inner, stamp)` as a Store node), term
identity is time-dependent: every (inner × stamp) combination interns an
immortal arena node, every firing pays a hash-cons insert, and shifting
the time origin re-interns the live state. Measured on PP2 shell+kiln:
~0.4M dead nodes per simulated day, ~15% of settle CPU in interning.
With labels beside the term: addresses are time-stable (the Store stops
growing with elapsed time), firing writes a row, and rebase REBUILD-SWAPS
the live rows into a fresh table — O(live), zero term allocation, with
compaction built in. (A uniform in-place table shift was rejected: a
shifted value can collide with the unit label, breaking the value
injectivity that value-derived hashing and row dedup require.)
Coalescing becomes a label-column rewrite (dead labels → unit), the
analog of DBM LU-extrapolation. Measured on PP2 shell+kiln: 4 simulated
days grow the Store by 161 nodes (was ~1.9M) and the live label table
holds 4–5 entries after each rebase.

## What stays internal

The connective `at` remains: in the calculus (prover rules, adequacy
theorems), in rule PATTERNS (static formulas, compiled once), in the
surface syntax, and in interchange encodings (plain-object states,
store-binary, event records) where materialization is O(live) and
bounded. The labelled representation is invisible outside the engine —
the same doctrine as run-length counts: the index is optimization, the
multiset is semantics.

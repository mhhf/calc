---
title: "The Destination-Discipline Confluence Certificate"
created: 2026-09-08
modified: 2026-09-08
summary: "A checkable discipline (D1-D6) under which ALL interleavings of committed forward steps in linear multiset rewriting converge — the write-once destination-passing fragment of SAX (FSCD 2020 Thm. 10), generalized to a calculus-agnostic certificate over compiled rules + an initial state. Soundness-only: `confluent: true` is backed by a strong-diamond argument (no termination needed); refusals carry witnesses and never assert non-confluence. A valid certificate lets explore() commit to ONE interleaving (digest-pinned to the exact rule set and state), collapsing interleaving branching wholesale. Shipped as calc.certifyConfluence (lib/engine/certify-confluence.js) with the SAX machine as the certified instance and the observable write-race as the pinned refusal."
tags: [linear-logic, forward-chaining, confluence, sax, destination-passing, certificates, multiset-rewriting]
category: "Engine metatheory"
unique_contribution: "The generalization of SAX's confluence theorem from a property of ONE fixed machine to a checkable per-(ruleset, state) certificate over an arbitrary calculus's compiled forward rules: (1) the six-condition discipline D1-D6 — keyed consumption, dispatch exclusion, determined instances, slot reuse, no engine-level branching, initial-state invariants — with the strong-diamond proof factored so each condition discharges exactly one commutation obligation; (2) the observation that SAX's case-pair determinism is NOT dispatch-pattern exclusion but single-writer cell contradiction (case_in1/case_in2 have IDENTICAL dispatch patterns; their same-destination coexistence is excluded by the write-once cell holding one value) — so the certificate's pairwise check must disjoin syntactic non-unifiability with ground-value contradiction on declared single-writer predicates, which is the precise formal content of 'write-once implies confluence'; (3) produce-only predicates (pure output sinks) are exempt from keying and slot reuse because multiset accumulation commutes and no exclusion obligation mentions them — separating the discipline's load-bearing conditions from decorative ones."
references:
  - "DeYoung-Pfenning-Pruiksma, Semi-Axiomatic Sequent Calculus (FSCD 2020) — Thm. 10 (machine confluence); Fig. 6 (the machine this discipline abstracts)"
  - "TODO_0309 P2 (this deliverable); P1 (family/sax + machine.sax, the certified instance); TODO_0261 avenue C (subsumed)"
  - "lib/timed/certify.js certifyContention (the certifier mold: static pairwise + state-dependent halves, soundness-only)"
  - "lib/measure/ci.js certifyCI / THY_0031 (the refusal-with-witness pattern)"
  - "TODO_0042 (explore soundness/completeness — the certificate is the complementary WHOLESALE prune; note explore's per-rule match enumeration under-approximates interleavings, so the certificate claims MORE than explore samples)"
  - "Newman 1942 / Church-Rosser: strong diamond gives confluence without termination — why D1-D6 avoid any termination obligation"
---

# The Destination-Discipline Confluence Certificate

## 1. The claim and its scope

`calc.certifyConfluence(initialState, discipline)` certifies, for the
loaded RUNTIME rule set and the given initial state:

> Every maximal interleaving of committed forward steps reaches the
> same final state (literal state equality — no α-renaming needed).

Soundness-only, in the house certificate style (certifyContention,
certifyCI): `confluent: true` is backed by the argument in §3; a
refusal returns `{ confluent: false, witness: { reason, … } }` naming
the first violated condition and asserts nothing about actual
non-confluence. The discipline names (which predicate is `proc`-like,
which is the write-once cell) are CALLER DATA — the certifier holds no
calculus vocabulary.

## 2. The discipline D1–D6

- **D1 keyed consumption.** Every linear pattern's predicate has a
  declared destination argument, and all of a rule's linear patterns
  share one destination term — a rule works at one address.
- **D2 dispatch exclusion.** Each rule has exactly one pattern on the
  declared dispatch predicate. For any two rules, same-destination
  coexistence is impossible: their dispatch patterns fail to unify, OR
  the unifier forces two declared single-writer cells to hold distinct
  ground values at the same key — distinct MODULO the registered
  equational theories (hash-level inequality would mistake two
  representations of ONE value, binlit 3 vs i(i e), for a
  contradiction and grant a false certificate).
- **D3 determined instances.** A rule's variables are fixed by its
  linear patterns plus single-writer goals whose keys are already
  determined (a closure computation). No witness-choice
  nondeterminism survives.
- **D4 slot reuse.** Produced linear facts of consumed predicates
  reuse a consumed (predicate, destination) slot; produce-only
  predicates (never in any antecedent) are exempt — sinks accumulate
  commutatively. Single-writer persistents are produced only by
  consuming their declared linear guard at the same key; guards are
  never produced.
- **D5 no engine-level branching.** No ⊕ alternatives, no existential
  consequents (fresh-name nondeterminism — detected on the COMPILED
  marker, existentialSlots, since compilation strips ∃ from the
  consequent; the tag-level scan remains as defense for uncompiled
  rule data), no dynamic-rule (implication) production or state, no
  timed features.
- **D6 initial-state invariants.** Per (consumed predicate,
  destination) at most one fact; per single-writer key at most one
  cell; no unwritten guard coexisting with its written cell. Equality
  is MODULO the registered theories: hash-keyed uniqueness would admit
  two theory-equal representations of one destination — one
  destination to the matcher, two to the map — and either a write
  conflict or θ-nondeterminism follows.

## 3. The diamond argument

Take two distinct enabled steps in any reachable state (D6 is
inductive under D4, so the invariants hold everywhere).

*Different destinations:* consumed multisets are disjoint outright —
every consumed fact carries its destination in an argument position
(D1), and facts at different destinations are different content
addresses.

*Same destination:* both rules' dispatch patterns must match THE
unique dispatch fact there (D6 + D4 preservation). For distinct rules
D2 makes that impossible — either the patterns cannot both match one
fact, or their single-writer demands contradict (the cell has one
value, ever: guards are never produced, so a written cell is final).
For the same rule, D3 forces the identical instance: the unique facts
per (predicate, destination) determine every linear variable, and the
closure through single-writer goals determines the rest.

*Commutation of disjoint steps:* linear effects are multiset
arithmetic on disjoint supports; persistent growth is monotone and
positive goals stay provable (theories/FFI are pure); every witness is
interleaving-independent (D3 + write-once: a single-writer cell's
value is the same whenever it exists at all). Both orders produce the
same state; D5 removed every source of non-literal equality. Strong
diamond gives Church–Rosser directly — no termination obligation
(Newman's lemma is not needed).

*Preconditions (documented in the certifier, not checked):* backward
proving of persistent goals is MONOTONE — proved against the
persistent component only, with no linear side effects (holds for
every shipped family by construction; a family whose hooks consume
linear resources during backward proofs is outside the discipline).
And theory-awareness is evaluated against the theories registered at
certification time; the digests pin rules and state, not the kernel's
theory table — certify and explore under the same loaded calculus.

## 4. What the SAX instance teaches

The machine's write rules exclude each other syntactically (`wpr` vs
`win1` heads). But `case_in1`/`case_in2` have IDENTICAL dispatch
patterns `proc D (pcase S P1 P2)` — their determinism is the
write-once cell: `!cell S vin1` and `!cell S vin2` cannot coexist.
The certificate's D2 disjunction is exactly this: **"write-once
implies confluence" formally means the pairwise exclusion may be
discharged by single-writer value contradiction where syntax fails.**
Dropping the single-writer declaration makes the machine refusable —
the cell is load-bearing (pinned in tests).

The observable race (`proc d win1 * proc d win2`) is refused at D6
with a `duplicate-destination` witness: the same demo that shows
non-confluence empirically is the certificate's canonical refusal.

## 5. Explore integration

A valid certificate collapses explore's interleaving branching to one
committed path (`opts.confluence`): the certificate carries digests of
the exact rule set and initial state, and any mismatch throws — a
stale certificate must never prune a genuinely branching exploration.
On the certified swap configuration the leaf count drops from all
interleavings to 1, with the surviving leaf equal to the common final
state. Note the asymmetry with TODO_0042: explore's per-rule match
enumeration under-approximates the true interleaving set, while the
certificate is a statement about ALL interleavings — stronger than
what explore samples.

## 6. Refusal taxonomy (pinned)

Twenty reasons, each with an adversarial test asserting exactly its
witness (tests/engine/certify-confluence.test.js):

- *Preconditions:* `no-connective-info` (D5 must never silently no-op
  for want of rc), `no-dispatch-declared`.
- *Per-rule (D1/D4/D5):* `timed-feature`, `internal-choice`,
  `existential-consequent`, `dynamic-rule-production`,
  `unkeyed-pattern`, `multi-destination`, `dispatch-arity`,
  `guard-production`, `unkeyed-production`,
  `non-slot-reuse-production`, `unguarded-cell-production`,
  `underdetermined-instance`.
- *Pairwise (D2):* `overlapping-dispatch`.
- *Initial state (D6):* `dynamic-rule-in-state`, `unkeyed-state-fact`,
  `duplicate-destination`, `duplicate-persistent-value`,
  `guard-cell-coexistence` — the D6 duplicates additionally pinned
  MODULO THEORY (hash-distinct binlit/i-o-e representations of one
  destination refuse), at the Store level, since program text
  canonicalizes before the certifier ever sees it.

Beyond the per-reason pins, tools/fuzz-confluence.js fuzzes the
certificate itself (seeded random keyed programs, terminating by a
marker-measure): certified ⇒ exhaustive explore converges AND
committed exec is invariant under rule-order permutation AND the
certificate-pruned explore reaches the common state; every refusal
reason must come from this taxonomy; injected duplicate destinations
must flip certified trials to refusal. A 25-trial slice runs in the
fast suite, 200 trials in test:heavy; the harness is
mutation-verified (a neutered D6 fails 34/60 trials).

## 7. Honest limits (the completeness frontier)

The discipline is sufficient, far from necessary: multi-destination
rules (joins), allocation of fresh destinations (SNAX's `p1 D` at
runtime — refused because freshness is a state property the static
check cannot see), functional persistent relations beyond declared
single-writers, and confluent-modulo-⊕ readings are all refusals
today. Each is a widening with its own proof obligation; the
certificate structure (per-condition witnesses) is built to absorb
them one at a time.

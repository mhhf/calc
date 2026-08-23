---
title: "Forced-Prefix Cohort Firing: Why Confluence Is the Wrong Theorem for Batching"
created: 2026-08-23
modified: 2026-08-23
summary: "Firing one match at multiplicity k (consume k·take, produce k·count — TODO_0278 B1) is NOT justified by the confluence of the k single fires: under a committed-choice scheduler with a draw-based conflict chooser, confluence proves order-independence of fires the scheduler may never perform. The correct criterion is the FORCED PREFIX: the batch is exact iff the sequential scheduler would provably fire this exact match k times consecutively. A per-firing decidable sufficient condition — unique candidate at the instant, no same-instant enablement, no persistent production at any delay, no per-fire draws — makes the batch equal the sequential k-prefix by induction, state-identical including the state hash and every later PRF draw. The multiplicity witness k = min over consumed rows of floor((count − reserved)/take) subsumes the structural guards: whole-pool and spread takes floor to 1, and preserved machines batch #machines-parallel with serialization emerging from resource counting rather than a special case."
tags: [till, timed, batching, cohort-firing, committed-choice, confluence, petri-nets, partial-order-reduction, run-length, scheduling]
category: "Engine Theory"
paper: "FULLY compiled into doc/paper/till (calc c712242b, 2026-08-23) — the negative result (confluence is the wrong theorem) and the forced-prefix theorem = paper Thm 8.2 with the multiplicity witness and Zeno preservation in §8."
unique_contribution: "Four claims. (1) A NEGATIVE result: the natural proof obligation 'batched fire = k single fires, by strict confluence' (stated as such in TODO_0278's invariant zero) is insufficient — a tied competitor on a shared cohort gives a counterexample where the batched world is unreachable by any sequential run (the PRF chooser interleaves). Exactness needs the scheduler to FORCE the k fires, not merely tolerate their reordering. (2) The forced-prefix theorem: three invariants — resource removal only raises per-rule minimal activations (a min over a shrinking candidate set), outputs land strictly after the instant or feed no antecedent, the persistent zone is untouched — imply the unique candidate recomputes identically and untied after each intermediate fire, so batch ≡ sequential k-prefix bit-exactly (Zobrist, draws, schedule). (3) The uniform multiplicity witness min floor((count − reserved)/take), under which serialization is EMERGENT: a consumed-and-reproduced machine bounds k by the machine count and re-produced copies land at a⊗d, so k same-stamp machines batch k-parallel and stagger the next round with no machine-specific rule. (4) Placement in the design space: Petri-net step semantics and GAMMA/P-systems maximal parallelism fire multisets of transitions but preserve only reachability (any-world); forced-prefix batching realizes a k-uniform step INSIDE an interleaving committed-choice semantics while preserving replay-exactness per seed — the ample-set/POR condition repurposed from 'may commute' to 'must repeat'."
references:
  - "TODO_0278 B1 (design riders + shipped record; calc ff750723); doc/documentation/timed-performance.md §Cohort firing (operational guards, measurements)"
  - "THY_0024 Graded Labelled States (the count column as the ℕ-label; batching = the rule's k-fold action on it)"
  - "THY_0019 timed matching/settle (D12 committed-choice minimal-activation order; P5 PRF chooser)"
  - "Petri nets, step semantics (e.g. Best & Devillers 1987, Sequential and concurrent behaviour in Petri net theory) — a step = a multiset of transition firings enabled by summed resources; reachability-level equivalence only"
  - "Banâtre & Le Métayer (1990). The GAMMA model. Sci. Comput. Program. — chemical multiset rewriting with parallel reaction steps"
  - "Păun (2000). Computing with Membranes. JCSS — P systems fire rules at multiplicities under maximal parallelism (any-world semantics)"
  - "Peled (1993). All from one, one for all: ample sets in partial-order reduction. CAV — the commutation condition our same-instant-enablement test inverts"
  - "Newman (1942); Huet (1980) — confluence/commutation lemmas: what the naive argument proves, and why it is not enough here"
  - "McSherry et al. — differential dataflow: aggregates-as-diffs, the systems sibling of firing on counts"
---

# Forced-Prefix Cohort Firing

## The wrong theorem

The natural justification for firing a match once at multiplicity k —
"the k single fires use disjoint resources under one substitution, so
they are pairwise confluent, and any interleaving reaches the batched
state" — proves the wrong thing. Confluence is a statement about the
fires the scheduler performs; it says nothing about WHETHER the
scheduler performs them. Counterexample: `spoil: wood -o {I}` and
`saw: wood -o {plank}@2` tied at one instant over a 10⁶-wood cohort.
Batching spoil consumes the whole cohort; the sequential run interleaves
spoil and saw by PRF draws. The batched state is not merely a reordering
— it is a world no sequential execution reaches. Under invariant zero
(exact replay per seed), that is a wrong answer, not an optimization.

## The forced-prefix theorem

**Theorem.** Let m be the unique candidate at instant a (no tie), with
per-fire consumption C and reservation R over the state's rows. Suppose
firing m (i) produces no linear output that lands at a — every delay is
strictly positive, or its zero-delay outputs feed no rule or possessed-
loli antecedent and no wildcard pattern is in scope — (ii) produces no
persistent fact, (iii) draws nothing per fire (no weighted consequent,
no existential resolution), and (iv) is not itself a possessed loli.
Then for every k ≤ min over consumed rows of floor((count − R)/C), the
batched step (consume k·C, produce k·outputs, one event) equals the
sequential k-prefix of the run — state-identical including the Zobrist
hash, the pending schedule, and every subsequent PRF draw.

*Proof (induction on the k−1 intermediate states).* After each fire:
removals only raise other rules' minimal activations (each activation is
a min over a shrunken candidate set), so no candidate joins the instant
from below; by (i) no produced fact creates a candidate AT the instant
(outputs land at a⊗d > a, or feed nothing); by (ii) the persistent zone
— which is timeless, hence instantly visible at ANY delay — is
untouched; and the resource bound guarantees the same rows still cover
C + R, so the deterministic matcher (FIFO enumeration over stable rows)
recomputes the SAME match, still unique, still activation-minimal.
Hence the scheduler is forced to fire m again, k times. State-identity
is then exact because FactSet mutations hash final counts and the draw
stream consumed no randomness inside the batch. ∎

Condition (ii) is not implied by a delay check: a persistent fact
produced under a DELAYED monad is still visible at the instant (the
persistent zone carries no labels — THY_0024), so it can enable a
competitor no delay test sees. Working this condition out exposed a
live defect: the engine's instant-feeding test returned "not feeding"
for any positive delay BEFORE examining persistent consequents, so
settleExplore's ample-set commit could miss reachable worlds (repro: a
delayed `!k` producer tied with a consumer of the cohort a `!k`-guarded
rule also wants — the d-world vanished). Fixed by checking persistent
consequents first; pinned by till-settle's persistent-arcs containment
arm. A theorem's premises are a checklist for the implementation.

Condition (i)'s loli clause had the same fate (audit 2026-08-23): the
implementation keyed "feeds a rule antecedent" off the STATIC rule list,
but possessed lolis are candidate sources too — a zero-delay output only
a state loli consumes slipped the guard, so a batch ran past the loli
competitor and the grow/loli tie draw vanished from the PRF stream
(trace order diverged from the sequential prefix; a `!_W`-binding loli
would diverge in state, though v1 fences those). Fixed by extending the
antecedent tables with state-loli antecedents at each check site
(settle's tie/batch guards and settleExplore's ample set); pinned by
till-batch's loli fence arm. Twice now: the premises are the checklist.

## The multiplicity witness

k = min over consumed rows of floor((count − reserved)/C) is not merely
a bound — it subsumes the structural guards one would otherwise state:
`!_W` binds and takes the whole pool (floor 1); an age-agnostic spread
take fully exhausts every cohort but its last (floor 1 there); and a
preserved machine (`$saw`, consumed and re-produced) has count =
#machines, so k same-stamp machines batch k-parallel while their
re-produced copies land at a⊗d and serialize the next round — the
serial behaviour of one machine and the parallel behaviour of a machine
park both EMERGE from resource counting. Reads subtract because each
fire of the prefix re-reads the pool (k·C + R ≤ count).

## Zeno preservation, for free

A zero-progress loop must feed its own instant — its output IS its
antecedent — so condition (i) excludes it from batching. The instant
guard therefore keeps its meaning under batching (it now counts RULE
progress rather than tokens), and no divergent program can batch its
way past it.

## Placement

Petri-net step semantics, GAMMA, and P systems all fire multisets of
rule instances in one step, but their parallel step is an any-world
device: it preserves reachability, not the identity of a scheduled run.
Forced-prefix batching is the interleaving-semantics counterpart — a
k-uniform step performed inside committed choice, exact per seed. The
enabling condition is the ample-set/POR commutation test inverted:
partial-order reduction asks when reorderings MAY be collapsed because
they commute; the forced prefix asks when the scheduler MUST repeat
itself, so the collapse is not a choice among worlds but the world.
The observable encoding follows: one event record with per-fire facts
and a multiplicity — the event list is a run-length encoding of the
sequential one, the same construction the state already uses for its
count column (THY_0024's ℕ-label, now with its firing law).

# Big Next — Theoretical Branches

Synthesis of the open todo corpus (2026-09-08, 66 open todos read in full), filtered to
theory: expressivity, metatheory, generalization, foundational cleanup. Excluded by
design: publishing, mechanization, applications, performance, tooling. Baseline: the
till/gill/will/sill metatheory (THY_0023–0034) is closed and papered — these branches
extend the frontier, they do not re-tread it.

Todos live in hq (`hq todo show <id>`); THY_NNNN = `doc/theory/NNNN_*.md`.

## 1. Fixed points: μMALL + ○ — the biggest expressivity gap

**TODO_0009, TODO_0203, TODO_0064 (Axis 3)**

CALC cannot state or prove anything about unbounded behavior — no induction, no
coinduction, no liveness, no bisimulation. The ladder is scoped: tabling (~80 LOC on
content-addressed hashing) → cyclic proofs with back-edges (~200 LOC; the store gives
O(1) cycle detection) → native μ/ν connectives (~400 LOC). Metatheory prizes:

- μMALL strictly subsumes the exponentials (Baelde 2012: `!A = νX. A & X`) — bang
  becomes a derived connective.
- With arithmetic, cyclic proofs ≡ explicit induction (Berardi–Tatsuta 2017) — the
  automation-friendly cyclic route loses nothing.
- TODO_0203's target calculus: intuitionistic μMALL + ○ with the lax monad as the ○
  tick — signals = `νX. A & ○X`, streams = `μX. A ⊕ ○X`; Krishnaswami's bounded-space
  theorem gives leak-freedom by construction.

Prerequisite for inductive invariants in the verification track (TODO_0008/0030).

## 2. Adjoint logic: one mechanism for all the modalities

**TODO_0064 (Axis 2), TODO_0012, TODO_0013, TODO_0032, TODO_0276 (theory core)**

The modal machinery accumulated piecewise — `!`, graded `{A}`, counted bang, sill's
located zone, will's drawn tokens. Adjoint logic (Pruiksma–Pfenning; Licata–Shulman)
reconstructs all of them as mode shifts `↑/↓` over a mode preorder, with the monad
literally `↑↓`. Groundwork exists: THY_0032 shows the derived contextStructure IS a
two-mode preorder instance and maps the seven prover sites that hardcode two zones
(its "negative ROI now" disposition is exactly what this branch would revisit).
Companion metatheory: TODO_0012's proper multi-type display calculus — make
`lnl.family` type-uniform and residuated so Belnap's metatheorem yields cut
elimination FOR FREE per future calculus, replacing the hand-proved three-cut
induction per instance. Fresh theorem parked in TODO_0276: cut admissibility for
principal-graded modalities combined with weight grades (`[K](!_w A)`, principal ×
weight orthogonality) under a partial, non-collapsing ⊕ — a real stress test of the
fenced-grade-algebra framework independent of the governance application.

## 3. Metatheory of the forward engine itself

**TODO_0309 (subsumes 0045, 0261), TODO_0042, TODO_0307 (P7 — DONE), TODO_0007, TODO_0005**

Consolidated 2026-09-08 into TODO_0309: sax.family as the second structural family
(first milestone), certifyConfluence for the destination-passing fragment, the ⊢_fwd
judgment restated PARAMETRICALLY over family axioms (discharged for lnl AND sax —
the LNL-shaped statement below is superseded), and the store-as-SNAX theorem.
P0+P1 LANDED (2026-09-08): family/sax + calculus/sax ship with the snip-searching
prover and the sax-native machine; five generic engine/loader completeness findings
fixed; the interface-extension list (P3's raw material) is recorded in the todo and
doc/documentation/sax-family.md. P2 LANDED (2026-09-08): calc.certifyConfluence —
the destination-discipline confluence certificate (THY_0036), with explore's
single-interleaving commit. P3 LANDED (2026-09-08): THY_0035 — ⊢_fwd parametric
over the family record (CS, P, D, X), axioms A1-A4 + match-completeness C1-C3,
discharged for lnl AND sax; the four-hooks-are-the-LNL-part finding is now a
specialization theorem. P4 LANDED (2026-09-08): THY_0037 — the store-as-SNAX
conjecture PARTIALLY FALSIFIED against the MFPS 2022 laws (L2 projection-
distinctness fails on equal subtrees; the temporal no-go: content addresses
cannot name futures) with the factorization theorem as the repair: machine.sax's
destination terms are the legal SNAX address algebra, the store concretizes
storables, !cell is the graph between them. P5 LANDED (2026-09-08): THY_0038 —
the adjoint-bridge ROI re-evaluated (supersedes THY_0032 §4): negative →
STAGED-POSITIVE; frontier = three gaps (G1 affine zone policy, G2 multi-
cartesian, G3 succedent modes) with executable pins; will's drawn_l2 ghost
identified as a hand-rolled affine mode (Stage A's deletion payoff); the
adjoint-sax instance specified. TODO_0309 is COMPLETE (P0-P5); branch 2's
Stage A/B now start from designs. TODO_0307 is now DONE (2026-09-10), and its
P7 follow-on — the THY_0039 §6 mode system (well-modedness + functionality/
decidability certification, tasks #80–#86 + audit remediation) — is COMPLETE,
with ILL `wellModed: 'strict'`. The branch's headline open-research item is
closed; what remains is the execution-tree checker (below).

The backward prover is kernel-checked; the forward engine's search semantics is still
folklore. Queued theorems:

- Execution-tree judgment `Σ; Δ ⊢_fwd T : A` with typed constructors (leaf, step,
  fork, branch, cycle, bound, memo, dead) — TODO_0045 — **DONE**. Judgment + term
  language: THY_0035 (parametric over the family record 𝔉). Checker: THY_0041 +
  `lib/prover/forward-check.js` (`checkForwardTree`) — the forward twin of
  `lib/prover/kernel.js`, generalizing the timed face's `elaborate-trace.js`/
  `certifyRun` (settle runs → kernel-checked @fire trees) to the whole `explore()`
  tree with all eight constructors, untimed. explore(evidence:true) emits a per-edge
  step witness (θ only); `api.certifyExplore` runs explore + check end-to-end. Whole-
  tree SOUNDNESS is machine-checked (θ the sole trusted witness); the three
  COMPLETENESS claims (leaf quiescence, dead-node prune, branch all-rules-present)
  are the stated oracle residue → TODO_0042.
- Soundness/completeness of `explore()` against it, via the QCHR ω^{∃∀} game-tree
  correspondence (Barichard–Stéphan, TOCL 2025) — TODO_0042; the hypersequent reading
  (TODO_0007) is the coarser dual view.
- THY_0035 (the parametric ⊢_fwd judgment, LANDED) + THY_0039 (eigenvariable
  semantics of existentials, from the TODO_0307 bug): forced elimination as an
  admissible rule under a groundness × functionality mode discipline, "witness
  capture" as a named violation class. The mode system (P7) that discharges it is now
  COMPLETE (`well-moded.js`: §6.1 functionality + §6.1′ decidability + §6.2 taint/V1
  + §6.3 guard-coverage/V2; tasks #80–#86 + audit); ILL is strict.
- TODO_0261 SAX/SNAX: CALC = "SAX without addresses" (same logic, proof SEARCH
  instead of proof reduction); the destination-passing fragment inherits SAX
  confluence (prunable explore branches); the content-addressed store as a
  non-standard SNAX concretization is a plausible standalone theorem.
- Constraint-propagation completeness (TODO_0005): infeasible symbolic branches are
  currently not pruned — sound but incomplete.

This branch turns "the engine works" into "the engine is a proof system."

## 4. Certified representations: "FFI is optimization" as a theorem

**TODO_0221, TODO_0184, TODO_0223, TODO_0191, TODO_0163**

The FFI principle is a discipline; this branch makes it metatheory. Every native
representation is a Hoare abstraction function (TODO_0221), with the genuinely novel
questions: linearity-aware data refinement (classical Hoare/He/Sanders theory is
persistent-only — the linear/persistent split is unaddressed in the literature),
partial isomorphisms (ground-only representations), and `symbolicInterpretation` as
Nelson–Oppen theory extension (the sha3 class). TODO_0184 is the constructive half:
synthesize the catamorphism from the clauses and VERIFY it is an injective
homomorphism — representation by recognition, not by hand. TODO_0163 makes the same
move for the supercompiler: replace `maxDepth`/`controlHash` with a homeomorphic-
embedding whistle and MSG generalization over linear multisets, where the open theory
is that linear consumption breaks the monotonicity classical HET relies on.
TODO_0191 (bisimulation-certified rule compilation) is the pipeline's far end.

## 5. Graded-frontier residue: open problems the papers left behind

**TODO_0304(a), TODO_0264, TODO_0269 (items 8, 10, 14–15), TODO_0266, TODO_0293
(theory item)**

Sharply-posed questions with machinery already in place:

- General-path genericity converse for the CI criterion — upgrade THY_0031 §6's
  trichotomy to a dichotomy: extend zero-concentration witnesses through observed
  colliders, existence hops, drops, allocation forks; infinite-class limit.
- Dimensioned/group-graded LL (TODO_0264): does Kennedy's units-parametricity free
  theorem transport to linear grades — conservation as a free theorem? Plus
  decidability of combined semiring × abelian-group grade unification.
- Expectation-semiring `{A}_w` (TODO_0269 item 8): the analysis dual of sampling —
  the monad grade carries exact odds; woplus deliberately has no sequent rules until
  this exists.
- Partial-order time (item 10): lattice-join stamps / vector clocks — the next
  generalization of the scheduling dioid THY_0033/0034 just fenced.
- Non-idempotent ⊔ scheduling (TODO_0293): when ⊔ = + the monotone-completion
  argument (L1) fails — replacement condition or impossibility proof unknown
  (THY_0034 factored the USE CASES away; the algebraic question stands).
- Differential invariants for the nonlinear dynamics fragment (TODO_0266): Platzer-
  style dL invariants for E6 feedback loops — distinct from Ehrhard's differential LL.

## 6. Foundational cleanup with theoretical weight

**TODO_0268, TODO_0271, TODO_0275, TODO_0012 (again)**

Three cleanups are abstraction theorems in disguise:

- Syntax ≡ declarations (TODO_0268): grammar fully derivable from `.calc` templates,
  nonterminals BEING the checker's sorts — anything that parses is well-sorted by
  construction. Half shipped; the sort-nonterminal unification is the remaining theory.
- Store identity audit (TODO_0271): separate arena-layout churn from tag semantics;
  design a stable external reference key — the prerequisite for derivations-as-data
  and any metadata sidecar.
- Rulevar vs metavar as distinct kinds (TODO_0275): the syntactic honesty a
  formalized metatheory will demand.

## Also real, smaller: verification metatheory

**TODO_0008, TODO_0030, TODO_0031** — one clean result worth landing: CALC states
form a well-structured transition system under multiset inclusion, so coverability is
decidable (Rackoff EXPSPACE); P-invariants fall out of the incidence matrix. The
Petri-net inheritance, made precise.

## Ranking

Highest theory-per-effort: **branch 3** (engine metatheory — now the most-advanced
branch: TODO_0309 complete, the mode system (P7)/THY_0039 complete, TODO_0307 done,
the ⊢_fwd execution-tree CHECKER (TODO_0045/THY_0041) done; what remains is explore()
adequacy — the completeness residue, TODO_0042. It is the soundness story everything
else stands on),
**branch 1** (fixed points — largest expressivity jump, cheap on-ramp via
tabling/cyclic proofs), **branch 5** (graded residue — questions already sharply
posed). **Branch 2** (adjoint logic) is the biggest unification payoff and the
biggest surgery — THY_0032's seven-site map is the honest cost estimate; it is the
branch that turns four hand-proved calculi into instances of one metatheorem.

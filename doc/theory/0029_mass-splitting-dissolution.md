---
title: "The Mass-Splitting Box Dissolves: Splitting Laws as Structural Facts of the Token Zone"
created: 2026-09-02
modified: 2026-09-02
summary: "T4-d(ii) discharged by dissolution: the conjectured weight-graded contraction □_{r+s}A ⊢ □_rA ⊗ □_sA adds no derivable content to will. Its count face is the counted bang's derivable splitting law (!_{k+m}A ⊣⊢ !_kA ⊗ !_mA, with exact conservation — leak and mint both refuted); its mass face is tensor context splitting itself (the token multiset partitions across ⊗-premises, so run mass factorizes multiplicatively in EVERY derivation, no side condition — and the sketch's additive grade composition was the budget semiring, not the likelihood monoid); its sum face is the forking connectives (∃_ρ/⊕ sum collapse-child masses). Any primitive box is either token-backed (then definable as ⟨Θ⟩ ⊗ A and its laws derivable) or a weight-conservation leak; the contraction shape specifically would clone a draw, which THY_0027 §4's no-cloning forbids and the prover refutes (one token cannot serve two ⊗-channels). Proving the mass leg flushed a general completeness gap in the focused prover — synthetic atoms could not close by id with leftovers — repaired at the root."
tags: [linear-logic, probabilistic, will, graded-types, provenance, proof-theory, focusing]
category: "Probabilistic Generation"
unique_contribution: "The dissolution theorem for the mass-splitting graded contraction: in a calculus where weight lives in the endsequent (draw tokens in the linear zone, THY_0027), every sound instance of □_{r+s}A ⊢ □_rA ⊗ □_sA is already derivable or structural — counts split by the counted bang, masses factorize by ⊗-context splitting of the token zone (multiplicatively, correcting the sketch's semiring), sums live at the forking connectives — and no primitive weight box can say more: token-backed boxes are definable, unbacked boxes violate exact weight conservation, and the contraction shape would clone a draw (no-cloning, refuted executably). 'Independent channels' is thereby fully reduced to the disjoint-provenance property (THY_0028), completing the pattern of THY_0027 §3g: what looked like missing connectives (the two-semiring judgment, the weight box) are projections of one design — grades on formulas, draws in the zone, mass a function of the derivation."
references:
  - "THY_0026 §6 T4-d / §9 item 1(ii) — the conjecture discharged here"
  - "THY_0027 — weight conservation through cut, no-cloning at ∃_ρ (§4), the §3g dissolution precedent, the §3f′ leak-audit shape reused in the dichotomy"
  - "THY_0028 — single-counting + certificate visibility; §6 recorded the dissolution probe this document resolves; Theorem 1 is the semantic content of 'independent channels'"
  - "TODO_0300 task 1(ii) — the phase-plan slot"
  - "Girard (1987). Linear Logic (the counted-bang reading !_kA ≅ A⊗…⊗A; SELL/BLL lineage)"
  - "Atkey (2018). Syntax and Semantics of QTT; Hoffmann et al. RAML — the additive budget semiring the sketch's r+s actually belongs to (credits, not likelihoods)"
  - "Barthe, Hsu & Liao (2020). PSL; Li, Ahmed & Holtzen (2023). Lilac (⊗/∗ = independence — the reading the mass leg operationalizes)"
  - "Kschischang, Frey & Loeliger (2001). Factor graphs and the sum-product algorithm (message splitting — the reading dissolved into provenance partition)"
---

# The Mass-Splitting Box Dissolves

**Status.** Proved and pinned (2026-09-02). Discharges THY_0026 §9 item
1(ii) by DISSOLUTION, resolving the probe of THY_0028 §6 in the
affirmative. Executable pins: `tests/will-prover.test.js` ("splitting
laws are structural"). Side result: a general completeness repair to the
focused prover (synthetic-atom identity with leftovers, §5).

## 1. The question, and the type mismatch it contains

T4-d's sketch (THY_0026 §6) posited a weight-graded box with the
contraction-shaped splitting law

```
□_{r+s} A  ⊢  □_r A ⊗ □_s A        "mass splits over independent channels"
```

read as factor-graph message splitting. The question 1(ii) asked:
soundness of this law — which presupposes answering what □_r *is* in
will. But will's standing lesson (THY_0027 §3g) is that weight does not
live on formulas: mass is a function of the DERIVATION,

```
mass(D)  =  Π { ρ(c)  |  drawn c s ∈ ⟨Θ⟩ }        (⟨Θ⟩ the endsequent's token zone)
```

A weight-graded box would put mass back on a formula — re-introducing
exactly the two-semiring judgment whose dissolution ("grades on
formulas, draws in the zone") was THY_0027's structural result. So the
box must be re-read: WHICH object in will carries an r that splits over
⊗? The answer is: three different objects, in three different semirings,
all already present. The sketch's single law conflates them.

## 2. Theorem: the splitting laws are structural

**(i) Counts split additively — the counted bang, derivable.** For all
k, m:

```
!_{k+m} A  ⊢  !_k A ⊗ !_m A        and conversely        !_k A ⊗ !_m A  ⊢  !_{k+m} A
```

are derivable (bang_l3 peels k+m linear parcels, tensor_r splits the
context, bang_r2/bang_r3 rebuild), and conservation is exact: neither
`!_5 a ⊢ !_2 a ⊗ !_2 a` (leak) nor `!_4 a ⊢ !_2 a ⊗ !_3 a` (mint) is
derivable. *Proof sketch:* each `!_K A` stands for K linear parcels of
A (D4/SELL reading); every bang rule preserves the total parcel count
of A (bang_l3/bang_r2 transfer one parcel across `!qsub K 1 J`;
bang_l4/bang_r3 act only at K=0 with nothing in transit, bang_r3's
empty-zone repair from the THY_0027 §3f′ audit closing the affine
leak), and the calculus has no weakening or contraction at the parcel
level. Pinned all four directions. If the box's grade is read as a
BUDGET of uses, □ already exists: it is `!_k`, and its r+s is honest —
counts compose additively because multiplicity is a cost, not a
likelihood.

**(ii) Masses split multiplicatively — ⊗-context splitting, structural.**
Let D be any derivation of `Γ; Δ, ⟨Θ⟩ ⊢ A ⊗ B` ending in tensor_r with
premise derivations D_A, D_B. The linear context splits, and drawn
tokens are ordinary linear hypotheses (THY_0027: tokens follow their
contexts through every context-splitting rule), so

```
Θ = Θ_A ⊎ Θ_B        hence        mass(D) = mass(D_A) · mass(D_B)
```

— the splitting law holds in EVERY derivation, with no side condition
and no annotation: it is a corollary of linearity. Conversely, mass is
never minted by contraction: the token class admits ghost (@affine
weakening) but no contraction, and promotion through a draw is fenced
(THY_0027 §3e), so a token reaches at most one ⊗-premise. Pinned both
ways: `p c, p d, drawn c s, drawn d s ⊢ (∃_ρX:s. p X) ⊗ (∃_ρX:s. p X)`
derivable (each channel consumes its own token — kernel-checked with
witness substitution), while `p c, p c, drawn c s ⊬ (∃_ρX. p X) ⊗
(∃_ρX. p X)` — one token cannot serve two channels. Note the semiring
correction: mass composes over ⊗ by ·, not +. The sketch's additive
r+s was the budget semiring — leg (i)'s discipline, not this one.

**(iii) Masses SUM where derivations fork — the connectives, not a
contraction.** Additive mass composition exists in will, at exactly the
places alternatives exist: the collapse tree's children sum
(`Σ_c ρ(c)·…` at ∃_ρ, THY_0026 §8 T1) and ⊕/woplus alternatives carry
branch weights. Summation is a property of forking, and the forking
connectives already carry it; no contraction internalizes it.

## 3. Definability: the box is the endsequent in disguise

Define, for a ground token multiset Θ with Π ρ(Θ) = r:

```
□_r A  ≜  ⟨Θ⟩ ⊗ A        (the tokens, tensored onto A)
```

Then the box's laws are derivable from Theorem (ii) plus reassociation
(token multisets reassociate freely over ⊗ — pinned:
`drawn c s ⊗ (drawn d s ⊗ a) ⊢ (drawn c s ⊗ drawn d s) ⊗ a`):
□_1 A = A (empty Θ), □_r □_s A ⊢ □_{r·s} A, and the splitting law with
· for +. The would-be introduction rule is @draw itself — minting a
token IS minting mass, and it is checker-bound (draw-check re-derives
the prior); the elimination is ghost — mass may be discarded (affine),
never duplicated. The judgment `Γ; Δ, ⟨Θ⟩ ⊢ C` already IS "C at mass
Π ρ(Θ)": the box was never missing, it is the sequent's own token zone
read as a formula.

## 4. The conservation dichotomy: no primitive box can say more

Suppose will added a primitive □_r with an introduction that asserts
mass r. Either:

- **(a) token-backed** — the introduction consumes tokens with
  Π ρ = r. Then it is §3's definable box: redundant.
- **(b) unbacked** — the introduction mints r without draws. Then the
  principal cut of intro against elim creates (or its dual erases) run
  mass not witnessed by any token — violating THY_0027's exact weight
  conservation through cut. This is precisely the shape of the
  bang_r3 affine leak the §3f′ audit caught and repaired: a rule whose
  zone is not backed by its premises is a conservation leak, and the
  audit discipline rejects it.
- **(c) contraction-shaped specifically** (the sketch's □_{r+s}A ⊢
  □_rA ⊗ □_sA, one A becoming two): duplicating a weight-carrying
  hypothesis is cloning a draw. THY_0027 §4 shows identity is
  primitive at ∃_ρ — a committed draw can be passed along whole but
  not deconstructed and re-derived — and the executable face is
  Theorem (ii)'s refutation: one token refuses two channels.

The residual reading — an r NOT tied to run mass, spendable across
branches ("budgeted evidence", THY_0028 §6's refutation candidate) —
is not a counterexample but a different modality with a different
semiring: it is the credits discipline of the amortized-cost
literature, and will already has its additive core as the counted bang
(leg (i): budget = multiplicity). Conflating a spendable budget with
posterior mass would let programs manufacture probability; the
dichotomy above is why will refuses the conflation structurally.

**Corollary (T4-d(ii) closed).** The mass-splitting graded contraction
adds no derivable content to will. "Independent channels" is the
disjoint-provenance property (THY_0028 Theorem 1); the certificate of a
split is not a grade annotation but the endsequent's token partition
(this document, leg (ii)) together with the fire chain's provenance
partition (THY_0028 Theorem 2b). Factor-graph message splitting is what
⊗-context splitting looks like from the semantics; the calculus needs
no new connective to say it. The dissolution completes THY_0027 §3g's
pattern: the two-semiring judgment and the weight box were both
projections of the one design decision — grades on formulas, draws in
the zone.

## 5. The search-level completion the theorem forced

Leg (ii) is a derivability claim, and testing it flushed a genuine
completeness gap in the focused prover (`lib/prover/focused.js`),
unrelated to tokens: SYNTHETIC ATOMS — predicate-headed formulas with
no rule on the focused side (`drawn`, `superpose`, ordinary predicates
`p c`) — could close by identity only via the pre-focus id, which
requires consuming the WHOLE remaining context. Under focus, the id
path was gated on `isAtomic` (atom/freevar/metavar), so a synthetic
atom in a non-final ⊗-premise was unprovable and provability was
ORDER-DEPENDENT: `a, p c ⊢ a ⊗ p c` proved while `p c, a ⊬ p c ⊗ a`.
Tokens inherited the gap (they could never partition through ⊗), which
is how the theorem found it. Repair at the root: the focused phase now
tries the general identity (with leftovers, like the atomic id) exactly
when no rule exists for the focused formula's tag on that side; the
kernel checks the resulting id leaves as before. All suites pass
unchanged — no pin anywhere relied on the gap. The pattern repeats
THY_0028's engine-bug find: theory pins are adversarial tests of the
implementation.

## 6. Residual

T4-d(iii) — the quantitative good-labelling / conditional-independence
theorem for dynamic derivation forests — is DISCHARGED AT DRAFT GRAIN
by THY_0031 (2026-09-02; Denis's read pending). This document supplied
its unconditional base case one step beyond THY_0028: not only do
disjoint provenances multiply (Theorem 1 there), but the ⊗-structure
of the endsequent already exhibits the partition (leg (ii) here) —
which is exactly THY_0031's exhibition corollary (Cor. 3): under
separation, the token zone splits Θ = Θ_A ⊎ Θ_B along the criterion's
sides in every class derivation.

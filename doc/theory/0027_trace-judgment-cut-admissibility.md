---
title: "Trace-Judgment Cut Admissibility: ∃_ρ by Draw-Token Internalization"
created: 2026-09-01
modified: 2026-09-01
summary: "will's weighted existential gets exact cut admissibility by internalizing the trace as linear draw-token hypotheses: Δ ⊢ A [Θ] is DEFINABLE as gill's judgment with Θ a multiset of ground linear atoms drawn(c,s) in Δ; ∃_ρ-R consumes a token, ghost-draw is weakening restricted to tokens, and trace conservation under cut reduction becomes definitional (cut elimination preserves the endsequent, and the trace now lives in the endsequent). Cut admissibility is gill/till's three-cut induction plus three new cases; the duplication and erasure danger audits pass because promotion already requires an empty linear zone. Identity expansion fails at ∃_ρ (id stays primitive: a draw cannot be re-derived — no-cloning), promotion through a draw is impossible (probabilistic conclusions are not bangable knowledge), and the mass bridge is the evaluation homomorphism out of the proof-counting provenance polynomial, counted over ghost-free focused derivations."
tags: [linear-logic, proof-theory, cut-elimination, existential, exists, probabilistic, graded-types, will, provenance]
category: "Probabilistic Generation"
unique_contribution: "First cut-admissibility result for a measure-weighted existential quantifier (constructor priors ρ : s → ℚ≥0) in a linear sequent calculus, with EXACT weight conservation — no relaxation order, no expectation, no threshold. The mechanism is new: the run trace is not a judgment annotation but a definable zone of linear draw-token hypotheses, making weight a function of the endsequent and turning grade preservation into endsequent preservation. Three structural consequences not in the literature: (1) ghost-draw = weakening restricted to the token class, forced by cut reduction (tape-linear systems are not closed under cut reduction) and excluded from canonical counting exactly like ordinary weakening under focusing; (2) no promotion through a draw — !R's empty-linear-zone condition, applied to tokens, is precisely what makes contraction-driven duplication and weakening-driven erasure trace-safe; (3) identity expansion fails at ∃_ρ — a proof-theoretic no-cloning: a committed draw can be passed along whole but not deconstructed and re-derived."
references:
  - "THY_0026 — the probability-graded existential (§2's graded-⟨w⟩ judgment sketch is superseded by this document; §5 collapse-as-principal-cut survives token-refined; §8 T1–T3 supply the measure side of the bridge)"
  - "THY_0023 — till metatheory (the three-cut lexicographic induction this proof extends; identity expansion, which ∃_ρ now exceptions)"
  - "THY_0021 — weighted additive disjunction (woplus as the derived Boolean instance)"
  - "RES_0140 (hq) — the tutorial chronicle: the crash, the repairs, the 2026-09 research round (four sweeps) behind the design"
  - "TODO_0298 — practical plan (obligation list this document discharges; will.rules implementation next)"
  - "Green, Karvounarakis & Tannen (2007). Provenance Semirings. PODS (ℕ[X] initiality; monomials = proof trees — the universality behind §6)"
  - "Grädel & Tannen (2017/2024). Semiring Provenance for First-Order Logic (∃ as semiring sum; positive semirings recover classical truth)"
  - "Vaux (2009). The algebraic lambda calculus. MSCS (positive scalars: confluent/conservative; negatives collapse — why the sum face is not made syntactic)"
  - "Lucas & Mio (2022). Proof Theory of Riesz Spaces. LMCS (the only syntactic cut elimination for a sum-valued judgment; the deferred stretch face's template)"
  - "Antonelli, Dal Lago & Pistone (2022). Curry and Howard Meet Borel. LICS (mass judgment without syntactic cut elimination — the wall, hit independently)"
  - "Lew, Cusumano-Towner, Sherman, Carbin & Mansinghka (2020). Trace types. POPL (trace faithfulness; the objection that forced the ghost discipline)"
  - "Sato (1995). Distribution semantics (run = deterministic derivation conditional on the random record)"
  - "Chi & Geman (1998/99). Subcriticality (bridge convergence for recursive sorts)"
  - "Staton (2017). Commutative Semantics for Probabilistic Programming. ESOP (unnormalized composes; normalization at the boundary)"
---

# Trace-Judgment Cut Admissibility

**Status.** Proved (hand derivation, 2026-09-01): internalization (§1), cut
admissibility with exact trace conservation (§3), identity-expansion exception
(§4), stripping/ghost discipline (§5). Assembled on top of THY_0026 §8: the
universality bridge (§6). Residual for the paper: the focused system spelled
out (§8). Implementation target: `will.rules` (TODO_0298 item 1).

## 1. The internalization theorem

The trace judgment of RES_0140 Ch. 7 — `Γ ; Δ ⊢ A [Θ]` with Θ a multiset of
draw records `(c:s)` and weight `w(Θ) = Π ρ(c)` — needs no fourth zone.
Introduce one kernel-reserved atom family

```
drawn : (c : s) -> (s : sort) -> type      % linear, ground, no right rule
```

and define:

> **Γ ; Δ ⊢ A [Θ]  :=  Γ ; Δ, ⟨Θ⟩ ⊢ A**, where ⟨Θ⟩ is the multiset of
> linear hypotheses `drawn c s` for each record `(c:s) ∈ Θ`.

Every piece of trace bookkeeping is then ordinary context bookkeeping:

| trace-zone behavior (RES_0140 Ch. 7) | context behavior it reduces to |
|---|---|
| cut concatenates traces | cut merges linear contexts |
| additive lockstep (&R shares Θ) | with_r shares Δ (verbatim, gill.rules) |
| promotion is trace-empty | bang_r requires an empty linear zone (verbatim) |
| ghost-draw pads Θ | weakening, restricted to `drawn` atoms |
| weight multiplies along cut | w(Θ₁⊎Θ₂) = w(Θ₁)·w(Θ₂), from multiset union |

The presentation as a separate zone `[Θ]` and the implementation as `drawn`
facts in Δ are isomorphic; everything below is stated in the internalized form.

**Fences.** (i) `drawn` is kernel-reserved: no program rule may produce it in a
consequent, no right rule exists, the fire checker never concludes it. Tokens
enter judgments only at the boundary — the @draw checker mints one `drawn c s`
per collapse event, checking `ρ(c)` against the declared prior. (ii) Tokens are
ground: a draw records a constructor head, so substitution never touches them
(rung-2 lazy draws record the head constructor only, matching priors being
per-constructor).

## 2. The rules

will.rules = gill.rules (unchanged, by reference until now — this adds the
first will-own rules) plus:

```
∃_ρ-R(c):   Γ ; Δ ⊢ A[c/x]                      ∃-L:  Γ ; Δ, A[a/x] ⊢ C   (a fresh)
            ─────────────────────────────             ─────────────────────────
            Γ ; Δ, drawn c s ⊢ ∃_ρ x:s. A             Γ ; Δ, ∃_ρ x:s. A ⊢ C

ghost:      Γ ; Δ ⊢ C
            ───────────────────────
            Γ ; Δ, drawn c s ⊢ C
```

∃_ρ-R **consumes** a token: "given that a draw of c occurred, assert the
weighted existential via c." ∃-L is the standard eigenvariable rule,
token-neutral. `ghost` is weakening restricted to the token class (Δ proper
stays linear; the token sub-zone is affine — mixed-discipline zones are
standard). No rule contracts a token; no rule proves one.

The graded-⟨w⟩ rules of THY_0026 §2 are superseded: there the weight was a
judgment grade multiplied in at ∃_ρ-R, and the principal cut reduction —
which substitutes the witness and deletes the ∃_ρ-R node — loses the ρ(c)
factor (⟨2⟩ → ⟨1⟩ on a two-constructor example; RES_0140 Ch. 5 has the
frame-by-frame). Weight is not a grade; it is a *function of the endsequent*:
w = Π ρ(c) over the `drawn` hypotheses present.

## 3. Cut admissibility (main theorem)

**Theorem.** The three cuts of THY_0023 (linear, lax, persistent) remain
admissible in gill + §2's rules, and every reduction step preserves the
endsequent — hence the trace and its weight are conserved *exactly*, with raw
ℚ≥0 priors.

**Proof.** By the same lexicographic induction (cut-formula weight with
first-order convention — witness substitution does not increase formula
weight; cut kind; premise heights). Cut elimination preserves the endsequent
by construction in every case; since the trace is part of the endsequent,
conservation is definitional. The burden is that the required reductions
*exist*. New or newly-audited cases:

**(a) Principal ∃_ρ-R / ∃-L.** The crash site, resolved:

```
π′: Γ; Δ₁ ⊢ A[c/x]                    σ′: Γ; Δ₂, A[a/x] ⊢ C   (a fresh)
π:  Γ; Δ₁, drawn c s ⊢ ∃_ρ x:s.A      σ:  Γ; Δ₂, ∃_ρ x:s.A ⊢ C
cut(π,σ): Γ; Δ₁, drawn c s, Δ₂ ⊢ C
```

Reduct: substitute (σ′[c/a] — legal: a fresh, c ground, tokens in Δ₂
untouched), cut on the smaller formula, restore the token by one `ghost`:

```
cut(π′, σ′[c/a]): Γ; Δ₁, Δ₂ ⊢ C
ghost:            Γ; Δ₁, Δ₂, drawn c s ⊢ C     — the same endsequent.  ∎(a)
```

The reduction *needs* `ghost`: it converts a used draw into an unused one. A
system whose tokens must be exactly consumed is not closed under cut
reduction — that is THY_0026's crash restated as a general law, and why
`ghost` is a rule, not a leak.

**(b) `ghost` commutation.** `ghost` as the last rule of either cut premise
commutes below the cut (standard weakening commutation; height decreases).
`ghost` never introduces the cut formula (tokens are never cut formulas by
(d)), so no principal case arises.

**(c) Identity cuts.** id exists at all formulas (gill's id is general), in
particular at ∃_ρ and at `drawn`; cut against id reduces by deletion, both
sides, as always.

**(d) Cuts on `drawn`.** The only derivations of `Γ; Δ ⊢ drawn c s` end in id
(no right rule, no checker conclusion — §1 fences). Case (c) covers them; no
other principal case on tokens exists.

**(e) Duplication audit.** The one duplication mechanism is the persistent
cut: cut^! substitutes a promoted derivation π at each `copy`. Promotion
(`bang_r: Γ; ⊢ !A ⇐ Γ; ⊢ A`) requires the linear zone empty — which now
includes tokens. So the duplicated derivation contains no draws: **no draw is
ever duplicated.** (The counted bang `!_K` peels by *splitting* context —
bang_r2 — never by duplicating; harmless.) Consequence, worth naming:
**no promotion through a draw** — a derivation that draws is not promotable.
This matches the engine exactly (draws are linear/event-world phenomena; the
persistent world is deterministic re-derivable knowledge) and the
Term/Resource/Proposition discipline: you may bang the *consequences of an
outcome*, never the luck itself.

**(f) Erasure audit.** Reductions that delete a subderivation: (i) principal
& — cut(with_r(π₁,π₂), with_l_i(σ)) keeps πᵢ, erases the other; with_r's
premises share one Δ (tokens included), so the endsequent loses nothing.
(ii) persistent weakening — an unused persistent hypothesis erases its
promotion π; π's linear zone is empty (e), so no token is lost. The current
gill fragment has no ⊕/0 left rules; when added, ⊕L shares Δ like with_r
(lockstep inherited) and 0L erases into an arbitrary endsequent (vacuously
safe). **No draw is ever erased.**

**(g) Lax and haul cuts.** monad_l/monad_r and haul_l/haul_r are
single-premise rules with persistent theory premises (!qsub/!le/!eq). Theory
premises are persistent-zone derivations — clause resolution, no linear zone,
hence no tokens. Grades compose exactly as in THY_0023's cut_lax (d+e via the
⊖ residual); tokens ride the linear contexts orthogonally. Delay grades and
weight tokens never share a slot — THY_0026 §2's "product of two semirings on
one judgment" dissolves: **grades on formulas, draws in the zone.** ∎

**(h) Additive lockstep, derived.** with_r gives both premises the same Δ,
hence the same tokens; a branch that draws less discharges the surplus by
`ghost`. The lockstep discipline of RES_0140 Ch. 10 is not a stipulation but
a consequence of sharing. ∎

## 4. Identity expansion fails at ∃_ρ — no-cloning

THY_0023 proves identity expansion (id derivable at compound formulas from id
at atoms). At ∃_ρ it fails: expanding `∃_ρx:s.B ⊢ ∃_ρx:s.B` by ∃-L opens a
fresh `a`, and re-introduction needs ∃_ρ-R — which consumes a token the
sequent does not have. There is no token-free eta-expansion; id stays
*primitive* at ∃_ρ (as it already is in gill.rules — id is general).

This is a feature with a physical reading: **a committed draw can be passed
along whole, but not deconstructed and re-derived** — re-derivation would be a
second draw (a different endsequent, one more token). A no-cloning-flavored
theorem appearing at exactly the connective that carries randomness, in a
classical calculus, for free.

## 5. Ghost discipline: stripping, padding, and the counting class

`ghost`-free derivations are those where every token is consumed by ∃_ρ-R.

- **Stripping.** Every derivation of Γ; Δ, ⟨Θ⟩ ⊢ A contains a ghost-free
  derivation of Γ; Δ, ⟨Θ₀⟩ ⊢ A for some Θ₀ ⊆ Θ (induction: remove `ghost`
  instances top-down).
- **Padding.** Γ; Δ, ⟨Θ₀⟩ ⊢ A implies Γ; Δ, ⟨Θ⟩ ⊢ A for every Θ ⊇ Θ₀
  (apply `ghost`).
- So **provable traces = the upward closure of ghost-free traces**;
  ⊆-minimal provable traces are ghost-free. The converse fails — ghost-free
  is *strictly* larger than minimal (e.g. A = (∃_ρx.P) ⊕ Q: the empty trace
  proves A via Q, the singleton trace proves it via P, both ghost-free) — and
  ghost-free, not minimal, is the correct counting class (both proofs above
  carry mass).
- **Divergence audit.** Counting all derivations would attach the factor
  Σ_k (Σ_c ρ(c))^k = ∞ to each proof via its padded variants (the Lew et al.
  objection). Counting ghost-free derivations excludes every padded variant.
  Ghost marks live on *rule occurrences*, not in the trace — necessarily so,
  since §3 conserves the endsequent on the nose while (a)'s reduct gains a
  `ghost` occurrence. Exactly weakening's profile: present in derivations,
  absent from canonical forms.
- **Conservativity.** Erasing tokens and mapping ∃_ρ-R/∃-L to ill.rules'
  exists_r/exists_l sends will-derivations to standard ILL derivations;
  conversely any such derivation lifts with Θ = the multiset of ∃-R witnesses
  at the ∃_ρ positions (with_r branches balanced by `ghost`). Hence
  `Γ; Δ ⊢ A [Θ]` for some Θ iff the plain judgment is derivable: the trace
  judgment is a conservative extension.

## 6. The bridge is universality

For a boundary judgment (Δ, A token-free), define the **proof-counting
provenance polynomial** and the mass:

```
N(A,Θ) := #{ focused, cut-free, ghost-free derivations of Γ; Δ, ⟨Θ⟩ ⊢ A }
P_A(X) := Σ_Θ N(A,Θ) · X^Θ   ∈ ℕ[X]          (X^Θ: a trace IS a monomial)
μ_K(A) := eval_K(P_A)  at  X_c ↦ ρ(c),  for any commutative semiring K
```

By ℕ[X] initiality (Green–Karvounarakis–Tannen) every semiring-valued reading
factors through P_A. Instances: K = (ℚ≥0,+,·) is will's mass — THY_0026 §8's
T1 identifies it with the denoted measure computed by exact mode, and T2/T3
supply convergence (Chi–Geman subcriticality; least fixpoints for recursive
sorts) and sampler unbiasedness. K = (min,+) is gill's optimum — idempotence
collapses the sum onto the single best derivation, which is why gill needs no
trace and a per-proof grade suffices. K = (ℂ,+,·) is reserved: evaluation is
still a homomorphism, but interference (cancellation) is forgetting that no
trace-level statement can undo — the trace level is the initial object, each
quantitative face a quotient of it. Cut admissibility is proved once (§3);
each face inherits invariance through its homomorphism.

## 7. Corrections this proof forces upstream

1. **THY_0026 §2**: the graded-⟨w⟩ judgment sketch fails its own §9
   obligation and is replaced by §2 above (weight = endsequent function of
   tokens). §5's "collapse is a principal cut" *survives* — refined: collapse
   is exactly reduction (a), and the token the checker mints is the record
   the reduct keeps.
2. **The two-semiring product judgment dissolves** (§3g): delay stays a
   formula grade (THY_0018), weight becomes tokens. No shared grade slot, no
   product-encoding question.
3. **Ghost-free ⊋ minimal** (§5) — TODO_0298's earlier phrasing "ghost-free
   traces = ⊆-minimal provable traces" holds only left-to-right.
4. **Marks on rules, not traces** (§5) — RES_0140 Ch. 10.5's `(c:s)^g`
   notation is superseded: marked trace entries would break §3's
   endsequent-on-the-nose conservation.

## 8. Residual for the paper (not blocking)

The focused system spelled out: ∃_ρ positive (right rule fires in the
positive phase, consuming a token; `drawn` a positive left-passive atom), so
that N(A,Θ) counts one derivation per genuinely-distinct run — the decimation
driver is operationally this focused prover already (each collapse-tree path
= one focused ghost-free derivation), which is THY_0026 §8 T1's enumeration
in proof-theoretic clothing. Plus THY_0026 §9's untouched items (T4-d,
inside-mass conditioning, policy independence).

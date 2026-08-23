---
title: "till Metatheory: Cut Admissibility, Identity Expansion, and Work Adequacy for the Graded Fragment"
created: 2026-08-21
modified: 2026-08-21
summary: "Full on-paper proofs discharging THY_0018 §8's sketch: cut admissibility (three cuts — linear, lax, persistent) for the delay-graded lax fragment via the judgmental presentation T2 and a cut-free-preserving equivalence with the implemented single-level system T1; identity expansion (id admissible at compound types from atomic axioms); counted-bang completeness (!_k A ≡ A^⊗k, full induction); and the non-circular WORK ADEQUACY theorem — the pure backward calculus with rules-as-hypotheses derives {⊗R}@W exactly when W bounds the TOTAL SEQUENTIAL WORK of an execution, so the graded monad alone is a cost logic and the max-plus makespan is contributed exclusively by the stamp coeffect (@fire/bridge): a provable separation, not a slogan."
tags: [till, linear-logic, lax-monad, proof-theory, cut-elimination, graded-types, time, adequacy, forward-chaining]
category: "Timed Rewriting"
paper: "FULLY compiled into doc/paper/till (calc c712242b, 2026-08-23) — two-presentation equivalence = paper Thm 3.1; identity expansion, counted-bang completeness, cut admissibility + corollaries = §4 (Thms 4.1–4.3, Cor 4.4); work adequacy + work/makespan separation = §6 (Thms 6.3–6.4)."
unique_contribution: "Three results beyond THY_0018's sketches: (1) the first full cut-admissibility proof for a GRADED lax/possibility modality (all published graded sequent calculi with cut elim grade the necessity side; Iemhoff 2024 proves cut elim for UNGRADED lax logic — this is its graded extension), including the observation that the count fence V = ℕ is exactly what makes the induction measure well-founded for counted bangs while dense delay grades never enter the measure; (2) mismatched principal cut cases are VACUOUS by theory-premise partiality (contradictory !qsub/!eq premises), so the partial residual ⊖ removes case-analysis obligations rather than adding them; (3) the work/makespan separation theorem: pure-backward derivability with rules-as-linear-hypotheses computes Σ-of-delays (total work), settle computes max-plus (makespan), the two provably coincide exactly on chain executions — a non-circular adequacy witness (kernel-verified, no bridge) that shows the stamp coeffect is a genuine extension, not conservative decoration."
references:
  - "THY_0018 — The Delay-Graded Lax Monad (the calculus; §8 is the sketch this document discharges)"
  - "THY_0019 — Timed Matching and the Settle Scheduler (operational side; settle, work vs makespan)"
  - "THY_0022 — Fenced Grade Algebras (the partial residual ⊖; Grade Preservation)"
  - "TODO_0270 — the till paper (proof obligations 1–4 land here)"
  - "TODO_0273 — theory premises replace @grade (the rule format the proofs cover)"
  - "Fairtlough & Mendler (1997). Propositional Lax Logic. Information and Computation."
  - "Pfenning & Davies (2001). A Judgmental Reconstruction of Modal Logic. MSCS (the judgmental method; structural cut admissibility)"
  - "Iemhoff (2024). Proof Theory for Lax Logic. Springer (cut elimination for UNGRADED lax logic — the ungraded base of Theorem 4)"
  - "Watkins, Cervesato, Pfenning & Walker (2002). A Concurrent Logical Framework I. CMU-CS-02-101 (CLF adequacy; the rules-as-hypotheses method of §7)"
  - "Negri & von Plato (1998). Cut Elimination in the Presence of Axioms. BSL (geometric-rule template for the theory premises)"
  - "Vollmer, Marshall, Eades III & Orchard (2025). A Mixed Linear and Graded Logic. CSL (closest graded sequent calculus — necessity side)"
  - "Girard, Scedrov & Scott (1992). Bounded Linear Logic. TCS (counted exponentials)"
---

# till Metatheory: Cut Admissibility, Identity Expansion, and Work Adequacy

Discharges TODO_0270 proof obligations 1–4 (THY_0018 §8's cases (i)–(vii),
the counted-bang lemma, η-expansion, non-circular adequacy). Everything here
is an on-paper proof over the implemented rule set `calculus/till/till.rules`;
none of it is machine-checked (mechanisation deliberately deferred — TODO_0270).
The executable witnesses are `tests/till-prover.test.js` (grid),
`tests/till-pure-adequacy.test.js` (§7), and `tools/fuzz-till.js` §4
(kernel-verified random towers).

## 1. Two presentations of one calculus

**T1 (implemented, single-level).** The rules of `till.rules`: one judgment
`Γ; Δ ⊢ C`, monads as formulas, grade side conditions as THEORY PREMISES
(`<- !qsub F E H`, `<- !le A B`, `<- !eq K 0`) discharged over the numeric
theory `prelude/rat.ill` (TODO_0273). The bridge rule `monad_r2` is
extra-logical and excluded throughout (§6 scoping).

**T2 (judgmental, two-level).** The presentation of THY_0018 §3–4: judgments
`Γ; Δ ⊢ A true` and `Γ; Δ ⊢ S lax@d` (`d` a ground grade in the fenced delay
algebra, so `d ≥ 0` — THY_0022), with rules

```
Γ; Δ ⊢ S true                Γ; Δ ⊢ S lax@d   d ≤ d'         Γ; Δ ⊢ S lax@d
─────────────── lax          ────────────────────── sub      ──────────────── {}R
Γ; Δ ⊢ S lax@0               Γ; Δ ⊢ S lax@d'                 Γ; Δ ⊢ {S}@d true

Γ; Δ, S ⊢ C lax@e
──────────────────────────── {}L        (sticky: conclusion must be lax)
Γ; Δ, {S}@d ⊢ C lax@(d + e)
```

plus, shared with T1: `id` (any formula), the multiplicative/additive rules
(⊗, ⊸, &, 1), the ω-bang triple (`!R` promotion with empty linear context,
`!D` dereliction, `!L` absorption) and `copy`, the counted-bang quadruple
(`!Rpeel`/`!R0`/`!Lpeel`/`!L0` with side conditions `K = J + 1` over ℕ resp.
`K = 0`), and the retiming axiom `at_l : Γ; A@t ⊢ A@t' true` (`t ≤ t'`). Left
rules are generic in the conclusion judgment (they apply under `true` and
`lax@e` conclusions alike); right rules of `true` never apply at `lax`.

**Lemma 1 (theory-premise adequacy).** For ground rational arguments:
`!qsub F E H` is derivable iff `H = F ⊖ E` (defined, i.e. `F ≥ E` and `H` in
the fence); `!le A B` iff `A ≤ B`; `!eq K 0` iff `K = 0`. On non-ground
arguments no theory premise is derivable. *Proof.* The clauses of
`prelude/rat.ill` compute exact rational arithmetic in the stated modes; the
three faces (clause, FFI, algebra) agree on definedness and value —
generatively pinned by `tools/fuzz-till.js` §§1–2 and argued in THY_0022 §4.
Non-ground arguments fail structurally (no clause head matches a metavariable
tower). ∎

Lemma 1 is used silently below: every T1 side condition is read as the
corresponding arithmetic fact and vice versa. In Negri–von Plato terms the
theory premises are GEOMETRIC rules over the ordered monoid — they carry no
sequent-level principal formula, which is why they never interfere with the
permutations in §6.

**Lemma 2 ({}-inversion, T2).** If `Γ; Δ ⊢ {S}@d true` then
`Γ; Δ ⊢ S lax@d`, cut-free preserving. *Proof.* Induction on the derivation.
`{}R`: its premise is the goal. `id` (`Γ; {S}@d ⊢ {S}@d`): derive
`Γ; S ⊢ S lax@0` by `lax` from `id`, then `{}L` gives
`Γ; {S}@d ⊢ S lax@(d+0)`. Left rules and `copy`: the same rule is generic in
the lax conclusion; apply IH to the premise(s) and re-apply. No other rule
concludes `{S}@d true`. ∎

**Lemma 3 (grade weakening, T1).** If `Γ; Δ ⊢ {S}@d` in T1 and `d ≤ d'`
(ground), then `Γ; Δ ⊢ {S}@d'`, cut-free preserving. *Proof.* Induction on
the derivation. `monad_r` (premise `Γ; Δ ⊢ S`, `!le 0 d`): re-apply with
`!le 0 d'` (transitivity). `monad_l` (principal `{A}@E ∈ Δ`, premise
`Γ; Δ₀, A ⊢ {S}@H`, `!qsub d E H`): by IH raise the premise to
`H' = H + (d' − d)` — defined since `d' ≥ d` — and re-apply `monad_l` with
`!qsub d' E H'`, derivable because `E + H' = (E + H) + (d' − d) = d'`
(associativity/commutativity). `id`: replace by the two-step
`monad_l` (`!qsub d' d (d' − d)`) over `monad_r` (`!le 0 (d'−d)`) as in §3.
`at_l` cannot conclude a monad (stamps attach to atoms only). Left rules and
`copy`: succedent passive, apply IH and re-apply. ∎

Lemma 3 is exactly T2's `sub`, admissible in T1 — which is why T1 has no sub
rule and no signed arithmetic: subeffecting lives in `monad_r`'s slack
(`!le 0 E`) and `monad_l`'s residual freedom.

**Theorem 4 (presentation equivalence).** `Γ; Δ ⊢ C` is T1-derivable iff
`Γ; Δ ⊢ C true` is T2-derivable; cut-free derivations map to cut-free
derivations in both directions, and the maps are size-linear.

*Proof.* (T2 → T1) By induction, representing `Γ; Δ ⊢ S lax@d` as
`Γ; Δ ⊢ {S}@d`: `lax` ↦ `monad_r` (`!le 0 0`); `sub` ↦ Lemma 3;
`{}R` ↦ the identity map on representations; `{}L` with grades `d, e` ↦
`monad_l` with `!qsub (d+e) d e` (derivable: `e ≥ 0` by the fence);
shared rules map to themselves (side conditions transfer by Lemma 1).
(T1 → T2) By induction: `monad_r` (premise `Γ; Δ ⊢ S`, `!le 0 E`) ↦
`lax; sub(0 ≤ E); {}R`; `monad_l` (premise `Γ; Δ₀, A ⊢ {C}@H`,
`!qsub F E H`) ↦ apply IH to the premise, then Lemma 2 to read it as
`Γ; Δ₀, A ⊢ C lax@H`, then `{}L` (grades `E, H`, conclusion
`lax@(E+H) = lax@F` by Lemma 1), then `{}R`; shared rules to themselves. Both
maps introduce no cut. ∎

Everything below is proved in T2 and transferred to T1 by Theorem 4; the
statements are quoted in T1 form where the implementation is concerned.

## 2. Measure

Formula weight `w`: atoms, stamped atoms, `1` have weight 1; binary
connectives `w(A□B) = w(A) + w(B) + 1`; `w(!A) = w({S}@d) = w(body) + 1`;
counted bang **`w(!_K A) = (K+1)·(w(A)+1)`** for ground `K ∈ ℕ`, and
`w(A) + 1` for non-ground `K`.

Two deliberate asymmetries, both fence-enabled (THY_0022):

- The count grade enters the measure, and is well-founded **because** its
  fence is ℕ. A ℚ-counted bang would break the induction; the fence is not
  bureaucracy but the termination argument.
- The delay grade never enters the measure: every `{·}@d`-cut descends to the
  BODY (§6 case {}R/{}L), so the density of ℚ delays is harmless. Cut
  elimination is measure-blind to exactly the grade that is dense.

Non-ground counts need no peel cases: by Lemma 1 the peel/zero side
conditions are underivable at non-ground grades, so a non-ground `!_W A` is
only ever introduced by `id` and eliminated by nothing — its principal cut
case is `id` vs `id`.

## 3. Identity expansion (η)

**Theorem 5.** For every formula `A` with ground grades, `Γ; A ⊢ A` is
derivable using axioms only at atoms: `id` at unstamped atoms and `at_l`
(with the reflexive `!le t t`) at stamped atoms.

*Proof.* Outer induction on `w(A)`, inner induction on the count grade.

- `a`: `id`. `a@t`: `at_l` with `t ≤ t`.
- `1`: `1L; 1R`.
- `A ⊗ B`: `⊗L`, then `⊗R` splitting into IH(A), IH(B).
- `A ⊸ B`: `⊸R` (goal `A⊸B, A ⊢ B`), then `⊸L` with IH(A), IH(B).
- `A & B`: `&R`; left branch `&L₁` + IH(A), right branch `&L₂` + IH(B).
- `!A`: `!L` (absorb A into Γ), then `!R` (linear context now empty), whose
  premise `Γ, A; · ⊢ A` is `copy` + IH(A).
- `!_K A`, `K ∈ ℕ` ground: inner induction on K. `K = 0`: `!L0` (weaken; both
  `!eq 0 0`) then `!R0` from the empty context. `K = J+1`: `!Lpeel`
  (`!qsub K 1 J`) exposing `A, !_J A`, then `!Rpeel` (`!qsub K 1 J`)
  splitting into IH(A) (outer) and IH(!_J A) (inner).
- `{S}@d`, `d` ground: `monad_l` with `!qsub d d 0` (residual 0), then
  `monad_r` with `!le 0 0`, premise IH(S). (In T2: `{}L; lax; {}R` with
  `d + 0 = d`.)

For NON-ground grades (`!_W A` under a metavariable grade, as pattern
formulas) the primitive general `id` remains necessary — Lemma 1 makes every
graded introduction rule inapplicable there. This is why T1 keeps `id` at all
formulas rather than restricting it to atoms: symbolic-grade identity is
axiomatic, ground-grade identity is admissible. ∎

## 4. Counted-bang completeness

Define the expansion `⌜!_k A⌝ = A ⊗ ⋯ ⊗ A` (k copies, right-nested;
`⌜!_0 A⌝ = 1`), homomorphic elsewhere.

**Theorem 6.** For every ground `k ∈ ℕ`: `!_k A ⊣⊢ ⌜!_k A⌝`, by derivations
using only the counted-bang quadruple, `⊗R/⊗L`, `1R/1L`, and `id`/η at `A`.
Consequently (with §6's cut admissibility) a sequent is provable in the
counted reading iff its expansion is provable in the bang-free fragment: the
four rules are complete for the `A^⊗k` semantics.

*Proof.* Both directions by induction on k.

(⊢, peel) `!_k A ⊢ ⌜!_k A⌝`. `k = 0`: `!L0` (`!eq 0 0`) then `1R`.
`k = n+1`: `!Lpeel` (`!qsub k 1 n`) exposes `A, !_n A`; `⊗R` splits the goal
`A ⊗ ⌜!_n A⌝` into `A ⊢ A` (η) and `!_n A ⊢ ⌜!_n A⌝` (IH).

(⊣, rebuild) `⌜!_k A⌝ ⊢ !_k A`. `k = 0`: `1L` then `!R0` (`!eq 0 0`).
`k = n+1`: `⊗L` exposes `A, ⌜!_n A⌝`; `!Rpeel` (`!qsub k 1 n`) splits into
`A ⊢ A` (η) and `⌜!_n A⌝ ⊢ !_n A` (IH).

Completeness: given a provable sequent in the expanded reading, cut each
hypothesis `!_k A` against (⊢) and the succedent against (⊣) — cuts are
admissible by Theorem 8, so the counted reading is provable; conversely with
the directions swapped. The split/merge isomorphism
`!_{a+b} A ⊣⊢ !_a A ⊗ !_b A` follows by composing both directions through
the expansion (associativity of ⊗ up to provability). Note `!R0` requires no
empty-context restriction — it closes a branch that received no resources,
which is what lets rebuilds thread mid-derivation (witnessed by the grid's
merge cases). ∎

## 5. Structural properties

**Lemma 7.** (a) Persistent weakening: `Γ; Δ ⊢ J` implies `Γ, A; Δ ⊢ J`,
height-preserving. (b) Persistent contraction is built in (`copy` reads Γ
non-destructively). (c) Exchange is trivial (contexts are multisets). (d)
LINEAR weakening and contraction are underivable (the kernel's leftover
discipline; `!_2 a ⊬ !_3 a`, `!_3 a ⊬ !_2 a` in the grid). *Proof.* (a)
routine induction; no rule inspects Γ beyond membership. ∎

## 6. Cut admissibility

Three cuts, stated in T2 (via Theorem 4 they are admissible in T1 with
`lax@d` read as `{·}@d`):

```
Γ; Δ ⊢ A true    Γ; Δ', A ⊢ J            Γ; Δ ⊢ S lax@d    Γ; Δ', S ⊢ C lax@e
────────────────────────────── cut       ───────────────────────────────────── cut_lax
Γ; Δ, Δ' ⊢ J                             Γ; Δ, Δ' ⊢ C lax@(d + e)

Γ; · ⊢ A true    Γ, A; Δ ⊢ J
────────────────────────────── cut!
Γ; Δ ⊢ J
```

(`J` ranges over both judgments.) The bridge `monad_r2` is not a rule of
either system: cut elimination is a theorem about the pure syntactic calculus;
the bridge is an admissible ORACLE whose soundness is THY_0018 §5 and whose
conclusions are therefore already derivable in the pure system it extends.

**Theorem 8 (cut admissibility).** All three cuts are admissible in the
cut-free system: from cut-free derivations 𝒟 of the left premise and ℰ of the
right premise, a cut-free derivation of the conclusion is constructible.

*Proof.* Lexicographic induction on
`(w(cut formula), kind, 𝒟, ℰ)` with kind ordered `cut! ≻ cut_lax ≻ cut` and
𝒟/ℰ compared structurally (an appeal is legitimate if the formula weight
drops; or it is equal and the kind drops; or both are equal and one premise
derivation is a sub-derivation of the current one, the other unchanged or
replaced by any derivation).

**I. cut (cut formula A true).**

*Axioms.* 𝒟 = `id`: conclusion is ℰ. ℰ = `id` on A: conclusion is 𝒟.
𝒟 = `at_l` (`A = a@t`, from `a@t₀`, `t₀ ≤ t`): if ℰ ends in `at_l` with the
cut formula principal (`a@t ⊢ a@t'`, `t ≤ t'`), conclude by `at_l` with
`t₀ ≤ t'` (transitivity — the only fact used; stacked retimings compose, so
this case terminates immediately). If ℰ = `id` on `a@t`, conclusion is 𝒟.
Otherwise `a@t` is passive in ℰ's last rule — case III.

*II. Principal cases* (A introduced by the last rule of 𝒟 on the right and
consumed by the last rule of ℰ on the left).

- `A = A₁ ⊗ A₂` (`⊗R` vs `⊗L`), `A = A₁ ⊸ A₂` (`⊸R` vs `⊸L`),
  `A = A₁ & A₂` (`&R` vs `&L₁/&L₂`), `A = 1` (`1R` vs `1L`): the standard
  ILL reductions; each replaces the cut by one or two cuts on proper
  subformulas (weight drops).
- `A = !B`: `!R` vs `!D` (dereliction): cut B (𝒟's premise `Γ; · ⊢ B`
  against ℰ's premise `Γ; Δ'₀, B ⊢ J`) — weight drops. `!R` vs `!L`
  (absorption): cut! B (𝒟's premise against ℰ's premise `Γ, B; Δ'₀ ⊢ J`) —
  weight drops (kind rises, which the lexicographic order permits under a
  weight drop).
- `A = !_K B`, ground `K`:
  - `!Rpeel` vs `!Lpeel`: 𝒟 gives `Γ; Δ₁ ⊢ B`, `Γ; Δ₂ ⊢ !_J B` with
    `!qsub K 1 J`; ℰ gives `Γ; Δ'₀, B, !_J' B ⊢ J` with `!qsub K 1 J'`. By
    Lemma 1 the residual is FUNCTIONAL: `J = J' = K−1`. Cut B, then cut
    `!_J B`: weights `w(B) < w(!_K B)` and
    `(K)(w(B)+1) < (K+1)(w(B)+1)`. This is where the measure's count clause
    earns its keep.
  - `!Rpeel` vs `!L0`, and `!R0` vs `!Lpeel`: **vacuous.** The side
    conditions demand `K ≥ 1` and `K = 0` simultaneously (Lemma 1:
    `!qsub K 1 J` derivable only when `K ≥ 1`) — no such pair of derivations
    exists. The partial residual does not merely guard soundness; it DELETES
    principal cut cases.
  - `!R0` vs `!L0`: 𝒟 is the axiom `Γ; · ⊢ !_0 B`; ℰ's premise `Γ; Δ'₀ ⊢ J`
    is already the conclusion.
  - non-ground `K`: only `id` introduces or eliminates — covered by the
    axiom cases.
- `A = {S}@d`: `{}R` vs `{}L`. 𝒟's premise: `Γ; Δ ⊢ S lax@d`. ℰ's premise:
  `Γ; Δ'₀, S ⊢ C lax@e`, conclusion `lax@(d+e)`. Apply **cut_lax** on S:
  `Γ; Δ, Δ'₀ ⊢ C lax@(d + e)` — exactly the required conclusion, weight
  drops. No grade arithmetic beyond the composition `{}L` already performs
  appears; this is THY_0018 §8 case (i), now an instance of the measure.

*III. Right-commutative* (A passive in ℰ's last rule R). Push the cut into
the premise of R containing A and re-apply R. Side conditions of R (theory
premises in T1; `≤`/ℕ-arithmetic in T2) mention only R's own principal
grades, which the permutation does not touch — Lemma 1 needs no
re-derivation, merely re-use (the Negri–von Plato geometric-rule discipline:
no principal formula in the sequent, nothing to permute). Two sub-cases of
note: R = `!R` (promotion) is vacuous — its linear context is empty, so the
cut formula cannot sit in it; R = `{}L` on some OTHER `{S'}@d'` permutes with
the composition `d' + e` untouched. ℰ ending in `lax`/`sub` likewise permutes
(the cut formula stays in Δ').

*IV. Left-commutative* (A passive in 𝒟's last rule — necessarily a LEFT rule
or `copy`, since A true is 𝒟's succedent and the lax-only rules
`lax`/`sub`/`{}L` cannot conclude `true`). Push the cut into the premise
whose succedent is A and re-apply. Same side-condition argument as III.

**V. cut_lax (cut formula S, grades d, e).** Case on 𝒟's last rule — the lax
judgment is generated by `lax`, `sub`, `{}L`, generic left rules, and `copy`,
and by nothing else:

- `lax` (d = 0, premise `Γ; Δ ⊢ S true`): apply **cut** (kind drops, same
  formula) with ℰ: `Γ; Δ, Δ' ⊢ C lax@e`, and `0 + e = e` (unit law) is the
  required grade.
- `sub` (premise `lax@d₀`, `d₀ ≤ d`): IH (same formula, same kind, smaller
  𝒟) gives `C lax@(d₀ + e)`; conclude by `sub` with
  `d₀ + e ≤ d + e` (monotonicity of + in ≤).
- `{}L` (principal `{S'}@d' ∈ Δ`, premise `Γ; Δ₀, S' ⊢ S lax@d₀`,
  `d = d' + d₀`): IH on the premise gives
  `Γ; Δ₀, S', Δ' ⊢ C lax@(d₀ + e)`; re-apply `{}L`:
  `lax@(d' + (d₀ + e)) = lax@((d' + d₀) + e) = lax@(d + e)` — associativity.
- generic left rule / `copy`: permute (side conditions untouched as in III).

The three grade facts used — unit, monotonicity, associativity (with
commutativity implicit in the algebra) — are the ordered-commutative-monoid
laws of THY_0018 §2 and nothing else; the proof is parametric in the grade
algebra exactly as the calculus is.

**VI. cut!.** Case on ℰ's last rule. `copy` on the cut formula A: ℰ's premise
is `Γ, A; Δ, A ⊢ J`; IH (cut!, smaller ℰ) gives `Γ; Δ, A ⊢ J`; then **cut**
(kind drops) with 𝒟 gives `Γ; Δ ⊢ J`. Every other rule (including `!R`,
whose premise retains Γ, and `copy` on a different persistent formula)
permutes: Γ threads unchanged through all rules, and 𝒟's linear context is
empty so no splitting is disturbed. Persistent weakening (Lemma 7a) closes
the leaves that no longer mention A. ∎

**Corollary 9.** (a) The graded-μ compositions used by THY_0018 Theorem 1
(chaining one `@fire`-step derivations) and the fusion argument of Theorem 3
(cut on the fresh intermediate J) are admissible: they never leave the
cut-free calculus. (b) Consistency: `·; · ⊢ a` is underivable for atomic a
(no cut-free rule concludes it). (c) The cut-free subformula property holds
up to grade recomputation: every formula in a cut-free derivation is a
subformula of the end-sequent with grades produced by ⊕/⊖ from end-sequent
grades — the analytic reading of "the theory premises are the only
arithmetic".

**Mapping to THY_0018 §8.** Sketch case (i) = II's `{S}@d` case; (ii)/(iii) =
V's `sub`/`{}L` cases + III/IV; (iv) is DISCHARGED — no erasure lift is
needed, the graded system is proved directly (the erased proof re-emerges as
the shadow of V under grade deletion); (v) = I's `at_l` case; (vi) = the
scoping paragraph above Theorem 8; (vii) = Theorem 4 + Lemma 3 (the
implementation encoding carries the theorem verbatim). The sketch's
"believed routine" is now "checked"; what remains non-mechanised is exactly
everything (TODO_0270's deferral), and the honest boundary statement in
THY_0018 §8 stands.

## 7. Work adequacy (the non-circular direction)

THY_0018's adequacy suite witnesses soundness THROUGH the bridge (each settle
step replayed as an @fire instance — round-15 TG-5). This section gives the
adequacy statement the PURE calculus supports, with no bridge, no engine, no
oracle: programs as hypotheses, CLF-style — and in doing so isolates exactly
what the pure graded monad measures.

**Setting.** A program `P = {Rᵢ = Inᵢ ⊸ {Outᵢ}@dᵢ}` with `Inᵢ, Outᵢ`
tensors of unstamped atoms and ground `dᵢ ≥ 0`; an unstamped initial
multiset Δ₀; MSR executions ε (fire any enabled rule, untimed reading) with
firing multiset `n : P → ℕ`, residual multiset R, and **work**
`work(ε) = Σᵢ n(Rᵢ)·dᵢ`. Encode ε's resources as the linear context

```
Δ_ε  =  Δ₀ ⊎ { !_{n(Rᵢ)} (Inᵢ ⊸ {Outᵢ}@dᵢ)  :  n(Rᵢ) ≥ 1 }
```

(rule multiplicity as a counted bang; `n = 1` may drop the bang).

**Theorem 10 (work adequacy).** For ground `W ≥ 0`:
`·; Δ_ε ⊢ {⊗R}@W` is derivable in pure T1 **iff** there is an execution
from Δ₀ with firing multiset n and residual R and `W ≥ Σᵢ n(Rᵢ)·dᵢ`.

*Proof.* (⇐, execution → derivation) Induction on ε. Empty: `R = Δ₀`;
`monad_r` (`!le 0 W`), then `⊗R`/`id` decompose `⊗Δ₀`. Step: let the first
firing be Rⱼ, consuming `Inⱼ ⊆ Δ₀`, producing Outⱼ; the tail ε′ runs from
`Δ₁ = Δ₀ ∖ Inⱼ ⊎ Outⱼ` with `n′(Rⱼ) = n(Rⱼ) − 1`. Peel one copy of Rⱼ
(`!Lpeel`; or use it directly if linear), apply `⊸L`: its In-premise is
`⊗R`/`id` over `Inⱼ`; its out-premise gains `{Outⱼ}@dⱼ`. Apply `monad_l`
charging dⱼ: the residual `W′ = W ⊖ dⱼ` is DEFINED because
`W ≥ work(ε) ≥ dⱼ`, and `W′ ≥ work(ε′)`. `⊗L` opens Outⱼ; the context is now
`Δ_{ε′}` and the goal `{⊗R}@W′` — IH. Every step is a pure rule; the
resulting tree passes full kernel verification with no unverified entries
(pinned in `tests/till-pure-adequacy.test.js`).

(⇒, derivation → execution) Let 𝒟 be a cut-free derivation of
`·; Δ_ε ⊢ {⊗R}@W`. Since the goal and all hypothesis subformulas outside
monads are atoms/tensors/lolis and R contains atoms only: (a) each
counted-bang hypothesis must be fully peeled (R contains no bang; no linear
weakening — Lemma 7d), yielding `n(Rᵢ)` loli copies; (b) each loli copy must
be consumed by `⊸L` (lolis cannot reach `id` against an atom goal, and
cannot be claimed in `⊗R` since R has none — if R is allowed to claim
residual FORMULAS, unfired copies may instead be returned in the goal, which
the theorem's atom-only R excludes by fiat); (c) each `⊸L` introduces
`{Outᵢ}@dᵢ`, which only `monad_l` can eliminate — charging dᵢ to the goal
grade exactly once. The `!qsub` chain telescopes:
`W = Σ (charged dᵢ) + E_final` with `E_final ≥ 0` from the terminal
`monad_r`'s `!le 0 E_final`, so `W ≥ Σᵢ n(Rᵢ)·dᵢ`. The `⊸L` steps ordered by
the derivation's dependency structure (a premise's resources must be
available in its split) linearise to an execution from Δ₀ with firing
multiset n reaching R: the linear splitting discipline is exactly multiset
rewriting reachability. (This direction is the standard CLF adequacy
permutation argument specialised to the atom-tensor fragment; the counted
peels add only Theorem 6.) ∎

**Theorem 11 (work/makespan separation).** The grade W of Theorem 10
measures TOTAL SEQUENTIAL WORK, not makespan. For the join program
`{a ⊸ {x}@2, b ⊸ {y}@3, x ⊗ y ⊸ {c}@1}` from `Δ₀ = {a, b}`:

- the least W with `Δ_ε ⊢ {c}@W` pure-derivable is `6 = 2 + 3 + 1`
  (Theorem 10; `{c}@5` and `{c}@4` are refuted),
- settle from the same state produces `c@4` (`max(2,3) + 1` — THY_0019), so
  the bridge judgment `Δ₀ ⊢ {c}@4` holds at horizon 4.

The two readings agree exactly when the firing DAG is a chain (then
Σ = critical path). Moreover the pure encoding cannot even mention stamped
inputs: no rule derives `a` from `a@t` (stamps are born at the boundary,
THY_0018 §5), so `a@1 ⊬ {b}@W` for every W under the encoding.
*Consequently:* the delay-graded lax monad alone is a COST logic — `{}L`'s
`d + e` is sequential composition; the tropical coeffect (max-plus
synchronisation, availability stamps) is contributed exclusively by the
`@fire` promotion rule, i.e. by the bridge. The stamp layer is a genuine
extension of the graded-monad fragment, not a conservative decoration — and
the bridge-soundness theorem (THY_0018 §5) is precisely the statement that
this extension is consistent with the pure fragment. ∎ (witnessed:
`tests/till-pure-adequacy.test.js` pins both columns.)

**Remark (why linear/counted hypotheses, not persistent).** CLF states
adequacy with rules in Γ. Bounded multiplicities in Δ give a sharper
statement (the sequent records exactly how often each rule fires — resource
accounting all the way up) and a cleaner ⇒ direction (no copy-permutation
cases). It also matches the implementation: the focused prover's `copy`
heuristic only copies persistent formulas that unify with the goal
(`lib/prover/focused.js`), so compound rule hypotheses in Γ are outside the
search fragment — a search-strategy scope, not a calculus limitation
(Theorem 8 holds regardless; the copy cut case VI is fully covered).

## 8. Status

| obligation (TODO_0270) | discharged by |
|---|---|
| 1. full cut elimination | Theorem 8 (+ Theorem 4, Lemmas 1–3, measure §2) |
| 2. counted-bang completeness | Theorem 6 |
| 3. η-expansion | Theorem 5 |
| 4. non-circular adequacy | Theorems 10–11 |

On-paper only; mechanisation is deferred (TODO_0270). The generative
executable witnesses remain: the provability grid, the pure-adequacy pins,
and `tools/fuzz-till.js` §4's kernel-verified random monad towers.

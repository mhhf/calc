---
title: "Principal-Graded Possession: Cut Admissibility for the Combined Modality [K](!_w A)"
created: 2026-09-14
modified: 2026-09-14
summary: "The governance layer's ownership object is 'principal K possesses weight-w of A', written [K](!_w A): an outer principal-indexed modality over an inner weight-graded bang. This document proves cut admissibility for that combined modality. Two fresh ingredients over the inherited graded-cut proof (THY_0023 Theorem 8, which is already parametric in the grade algebra): (1) the principal set is a PARTIAL-⊕ fenced grade algebra — the fourth instance after delay/count/weight — where ⊕ is undefined for distinct principals (a strict generalization of THY_0022's total-⊕ fence), and this partiality is exactly no-cross-principal-collapse: nested distinct-principal modalities cannot fuse, so the mismatched-principal cut cases are VACUOUS (the THY_0023 counted-bang vacuity trick, generalized from ⊖ to ⊕); (2) principal and weight occupy disjoint grade positions, so by the orthogonal-composition result (THY_0015 §3, {A}_{q·a}) the combined principal cut case factors into an outer SELL-style peel and an inner weight descent with NO interaction term. Both grades are dense/idempotent, hence measure-blind like delay: THY_0023's well-founded measure (carried solely by the ℕ count fence) is unchanged, and the whole proof reduces to the parametric core plus these two deltas. Discharges TODO_0276 'PROVE FRESH (a)'."
tags: [linear-logic, proof-theory, graded-types, graded-modality, cut-elimination, authorization, ownership, principals, lax-monad, SELL, residuated-monoids, soundness, governance]
category: "Proof theory"
unique_contribution: "The first cut-admissibility proof for a modality that composes a PRINCIPAL index with a QUANTITATIVE grade — [K](!_w A), 'K possesses weight w of A'. Two results not in the literature and not in prior CALC theory: (1) the PARTIAL-⊕ fenced grade algebra — generalizing THY_0022's fence (where only ⊖ is partial) to make ⊕ itself partial — with the observation that ⊕-partiality is definitionally identical to no-cross-principal-collapse (says/knows/has do not collapse across distinct principals) and, at the cut layer, DELETES the mismatched-principal principal-cut cases exactly as THY_0022's partial ⊖ deletes the mismatched-count cases (THY_0023 §6.II). (2) An orthogonality lemma turning THY_0015's semantic orthogonal composition {A}_{q·a} into a proof-theoretic factorization of the combined principal cut case: because the principal grade and the weight grade never share a rule side condition, the combined [K](!_w A) cut peels the outer principal (SELL pattern, THY_0013) and descends the inner weight (delay pattern, THY_0023) as two independent formula-weight-decreasing steps, so cut admissibility is compositional across the two axes with no cross term. Corollary: stake conservation and unique-ownership are cut/identity/linearity theorems of the encoding, not enforced invariants. Authorization logics (Garg ESORICS 2006) have cut elimination for says/knows but ungraded; graded modal calculi (BLL, THY_0018/0023) grade a single axis; no system combines a principal index with a quantitative grade and eliminates cut."
references:
  - "THY_0023 — till Metatheory (Theorem 8: the parametric graded-cut proof this extends; §6.II the counted-bang vacuity trick; §2 the measure)"
  - "THY_0022 — Fenced Grade Algebras (the total-⊕ fence generalized here to partial ⊕; Grade Preservation)"
  - "THY_0018 — The Delay-Graded Lax Monad (the measure-blind dense-grade pattern; §8 cut sketch; §9 instances table; §5 the SELL-style promotion cut cases)"
  - "THY_0015 — Grade-0 Staging / {A}_{q·a} (§3: graded semiring ⊥ indexed monad — the orthogonal-composition result made proof-theoretic here)"
  - "THY_0013 — The Indexed Lax Monad {A}_a (SELL promotion cut pattern; principal = subexponential label)"
  - "THY_0044 — Graded μMALL Unification (the three-axis factorization; cut-as-shared-generic-rule; the mechanization surface fuzz-cut.js / cut-admissibility.test.js)"
  - "TODO_0276 — Governance Layer (the parked theorem 'PROVE FRESH (a)'; the four-judgment says/knows/has table); TODO_0018 (authorization theory); TODO_0269 (variable-binding possessed rules, the v1 engine blocker — orthogonal to this on-paper result)"
  - "Garg, Bauer, Bowers & Pfenning (2006). A Linear Logic of Authorization and Knowledge. ESORICS (cut elimination for says/knows — ungraded; the base this grades)"
  - "Marshall & Orchard (2024). Functional Ownership through Fractional Uniqueness. OOPSLA (sum-to-1 fractional ownership via rational grades — the weight axis' intended reading)"
  - "Girard, Scedrov & Scott (1992). Bounded Linear Logic. TCS (graded exponential !_n — the single-axis quantitative neighbour)"
  - "Nigam & Miller (2009). Algorithmic Specifications in Linear Logic with Subexponentials. PPDP (SELL; the principal-as-label promotion shape)"
---

# Principal-Graded Possession: Cut Admissibility for [K](!_w A)

**Status.** On-paper proof, in the style and standing of THY_0023 (hand-checked,
not machine-checked). Unlike THY_0023 the underlying modalities are **not yet
implemented** — the principal grade algebra and the possession modality are the
governance layer's P1/P2 (TODO_0276), so there is no rule file to quote. The
proof is therefore purely judgmental (the Pfenning–Davies method THY_0023 uses
for its T2 presentation), which is the right level for a modality being designed:
the calculus is specified here, and §7 records the exact plug-in point at which
it becomes a `fuzz-cut.js` instance alongside `ill/fill/gill/grill/trill`.

This discharges TODO_0276's open obligation **"PROVE FRESH (a): cut admissibility
for the combined [K](!_w A) — principal × weight orthogonality, outer-index
decomposition."** The estimate there ("conjectured routine, ~1wk") is confirmed:
once the two deltas below are isolated, the theorem is the parametric core of
THY_0023 applied twice.

## 1. The object and the theorem

The governance layer's ownership datum is *principal `K` owns weight `w` of the
resource `A`*. Written as a formula it is the **combined modality**

```
[K](!_w A)
```

with two grades on two nested modalities:

- **`[K](·)`** — the **principal-indexed possession** modality (TODO_0276's
  `has`, single bracket): "held by `K`". Its proof theory is SELL-style
  promotion (THY_0013): the right rule restricts the context to `K`'s zone
  `Δ|_K`, the left rule dereliction-injects the body into that zone. The
  `says`/`knows` variants (`monad(K,·)` / `bang(K,·)`, TODO_0276's four-judgment
  table) share the same grade algebra and the same cut cases up to the
  monad/bang polarity already handled by THY_0023; we prove `has` and remark on
  the other two in §5.4.
- **`!_w(·)`** — the **weight-graded bang** (TODO_0276 pillar 1, amount):
  `w ∈ ℚ ∩ [0,1]` a fractional stake. Its splitting law is
  `!_{a+b} A ⊣⊢ !_a A ⊗ !_b A` (Marshall–Orchard fractional ownership) — the
  grade is **additive** with fence `[0,1]`, i.e. structurally the delay algebra
  of THY_0018 with a bounded dense fence (crucially NOT the ℕ count algebra;
  see §4).

**Theorem (cut admissibility for `[K](!_w A)`).** In the cut-free system of §3,
all three cuts (linear, lax, persistent) are admissible, including every cut
whose cut formula is `[K](!_w A)`, `[K] B`, or `!_w B`. From cut-free
derivations of the premises a cut-free derivation of the conclusion is
constructible.

The proof (§5) is THY_0023 Theorem 8 plus exactly two new ingredients: the
principal grade algebra (§2) and its orthogonality with the weight algebra (§4,
Lemma O). We first isolate those, then the cut proof is short.

## 2. The principal grade algebra (the fourth fenced instance — with partial ⊕)

THY_0022 defines a fenced grade algebra `(G, ⊕, 0, ≤, V, ⊖)` with a **total**
commutative monoid `⊕` and a **partial** residual `⊖`, and its three instances
(delay, count, weight). The principal grade is the fourth — but it requires one
honest generalization: **`⊕` is partial too.**

**Definition (partial-⊕ fenced grade algebra).** As THY_0022, but `⊕` is a
*partial* commutative monoid operation: `a ⊕ b` may be undefined, `0 ⊕ a = a`
always, and where both `a ⊕ b` and the associativity re-bracketings are defined
they agree. `V` (the fence) is closed under `⊕` **wherever `⊕` is defined**.
Grade Preservation (THY_0022 Thm) holds verbatim: a constructed grade is `a ⊕ b`
or `a ⊖ b`, each in `V` when defined, and when either is undefined the
constructing rule does not fire — the proof never used the totality of `⊕`, only
that a *defined* result lies in `V`. (Total-⊕ algebras are the special case; the
delay/count/weight instances are unchanged.)

**The principal instance.**

| carrier | ⊕ | 0 | fence V | ⊖ |
|---|---|---|---|---|
| `P ∪ {0}` (`P` = principal terms) | `a ⊕ a = a`; `0 ⊕ a = a`; `a ⊕ b` **undefined** for distinct non-unit `a,b` | ambient / "nobody" | well-sorted principal terms | `a ⊖ a = 0`, `a ⊖ 0 = a`, else undefined |

`⊕` is **partial idempotent**: a principal composes only with itself (or the
unit). `≤` is the flat order (`0 ≤ a`, incomparable otherwise); `⊕` is trivially
monotone on its domain.

**Fact P1 (⊕-partiality = no-cross-principal-collapse).** The load-bearing
property of authorization modalities — `K₁ says φ` and `K₂ says φ` do not
collapse to a single affirmation for `K₁ ≠ K₂` (Garg et al. 2006; a `says` that
collapsed would let any principal speak for any other) — is *exactly*
`K₁ ⊕ K₂` undefined. In the graded reading `[K]` is a modality graded by the
principal, and the only rule that would fuse two principal indices is the
graded-`μ` composition `[K₁][K₂] B ⊢ [K₁ ⊕ K₂] B` (the bind of the indexed
modality, THY_0018 §4 derived rule). With `⊕` undefined off the diagonal, that
composition exists **only** for `K₁ = K₂`. Non-degeneracy is not an axiom to
check; it is the shape of `⊕`.

**Fact P2 (the unit is ILL).** `0` = "nobody / ambient": `[0] B = B` (says-by-
nobody is plain truth; TODO_0276 "clean theory"). So ILL embeds in the principal
instance exactly as it embeds in the delay instance via `{S}@0 = {S}`, and every
ungraded ILL cut case is the `K = 0` shadow of a principal case.

## 3. The judgmental calculus (the graded fragment; ILL rules unchanged)

Following THY_0023's T2 presentation. Judgments: `Γ; Δ ⊢ A true`, and — reusing
the lax judgment for the `says` variant — `Γ; Δ ⊢ S lax@(w·K)`. The rules for
the two new modalities (ILL, the ω/counted bangs, and the delay monad are
exactly THY_0023 §1):

**Weight-graded bang `!_w` (additive dense grade, fence [0,1]).**

```
Γ; · ⊢ A true   0 ≤ w ≤ 1          Γ; Δ, A, !_{w'} A ⊢ J   w = w₀ + w'
──────────────────────────  !_w R   ────────────────────────────────────  !_w L(split)
Γ; · ⊢ !_w A true                   Γ; Δ, !_w A ⊢ J

Γ; Δ, A ⊢ J   (w = 1)              Γ; Δ ⊢ J   (w = 0)
────────────────────  !_w D         ───────────────────  !_w W
Γ; Δ, !_w A ⊢ J                     Γ; Δ, !_0 A ⊢ J
```

`!_w L(split)` is the fractional split `!_{w₀+w'} A ⊢ A ⊗-into-context !_{w'} A`
read bottom-up; its side condition is the residual `w₀ = w ⊖ w'` over the weight
algebra (defined iff `w' ≤ w`, both in `[0,1]`). Dereliction `!_w D` uses one
whole unit; weakening `!_w W` discards a zero stake. (This is the graded
exponential of THY_0044 §3 — "semiring operations are the structural rules" —
specialized to the additive `([0,1], +, 0)` share algebra with residual.)

**Principal possession `[K]` (SELL-style, grade = principal).**

```
Γ|_K ; Δ|_K ⊢ B true                       Γ; Δ, B ⊢ J
──────────────────────  [K]R (promotion)    ───────────────────  [K]L (dereliction)
Γ; Δ|_K ⊢ [K] B true                        Γ; Δ, [K] B ⊢ J
```

`Δ|_K` is the sub-context of resources held by (or ambient to) `K` — the acting-
principal restriction (TODO_0276: possession = "rules running as `K` see only
`K`'s resources", generalizing THY_0013's `sourceLabel` from strings to principal
terms). `[K]R` is the promotion condition of THY_0013 §2 with the label preorder
instantiated at the principal algebra; `[0]R`/`[0]L` collapse to identity by
Fact P2. The `says` variant replaces `[K]R/[K]L` by the lax-monad pair
`{}R/{}L` of THY_0023 §1 with grade `K` in place of the delay `d` (a monad,
context-restriction only in the promotion premise of `@fire`-style firing — §5.4).

The derived **graded-μ / bind** rule, the only principal-fusing rule, and the
locus of Fact P1:

```
Γ; Δ ⊢ [K₁]([K₂] B)        K = K₁ ⊕ K₂   (defined ⟹ K₁ = K₂ = K)
──────────────────────────────────────────────────────────────────  [μ]
Γ; Δ ⊢ [K] B
```

## 4. Measure and orthogonality

**Measure.** Extend THY_0023 §2's formula weight `w(·)` by
`w([K] B) = w(B) + 1` and `w(!_w B) = w(B) + 1` for **every** grade value
(ground or not). Two points, both decisive and both inherited from THY_0018/0023:

1. **Both new grades are measure-blind.** The principal grade is idempotent
   (`a ⊕ a = a`) and the weight grade is dense on `[0,1]`. Neither peels a
   well-founded ℕ counter the way the count bang does (`w(!_K A) =
   (K+1)(w(A)+1)`, THY_0023 §2). Every `[K]`-cut and every `!_w`-cut **descends
   to the body `B`** (§5), so — exactly as THY_0023 makes cut "measure-blind to
   the dense delay grade" — the induction measure is carried **solely by the ℕ
   count fence**, untouched by this document. No new well-foundedness obligation
   arises. This is why the additive weight uses fence `[0,1]` (dense) rather than
   ℕ: a share is split, never counted, so it must stay out of the measure.
2. `w([K](!_w A)) = w(A) + 2`: the two nested modalities each add 1; the cut
   on the combined formula reduces (§5.3) to a `[K]`-cut and a `!_w`-cut on
   strictly lighter formulas.

**Lemma O (orthogonality / disjoint grade positions).** In any derivation, the
principal grade appears only on `[K]`-nodes and the weight grade only on
`!_w`-nodes; no rule has a side condition mentioning both a principal and a
weight. Consequently the combined grade algebra is the **product**
`(P ∪ {0}) × ([0,1])` with componentwise `⊕`/`⊖`, each factor partial exactly
where its own algebra is, and the two axes never interact.

*Proof.* By inspection of §3: `[K]R/[K]L/[μ]` carry only principal side
conditions (`K = K₁ ⊕ K₂`); `!_w R/L/D/W` carry only weight side conditions
(`w = w₀ + w'`, `0 ≤ w ≤ 1`); the ILL and count/delay rules carry neither. There
is no rule whose grade arithmetic couples the two. This is the proof-theoretic
form of THY_0015 §3's semantic result that the indexed monad (`a` = principal
stratum) and the graded semiring (`q` = weight) are orthogonal dimensions,
composing to `{A}_{q·a}`: here `q·a = w·K`, the product grade of `[K](!_w A)`. ∎

## 5. Cut admissibility (proof)

Lexicographic induction on `(w(cut formula), kind, 𝒟, ℰ)` exactly as THY_0023
Theorem 8 (`kind`: `cut! ≻ cut_lax ≻ cut`; `𝒟`,`ℰ` structural). The **entire
axiom / ILL / count-bang / delay-monad / commutative apparatus is THY_0023
Theorem 8 verbatim** — its induction is already parametric in the grade algebra,
using only the ordered-commutative-monoid laws (unit, monotonicity,
associativity, commutativity), which the principal and weight algebras satisfy on
their domains (§2, §3). We give only the four new principal cases and the
combined case; every other case is a citation.

### 5.1 Principal case for `!_w` (weight bang)

`A = !_w B`, `𝒟` ends in `!_w R`, `ℰ` in a `!_w` left rule.

- **`!_w R` vs `!_w D`** (`w = 1`): `𝒟` gives `Γ; · ⊢ B`; `ℰ`'s premise is
  `Γ; Δ', B ⊢ J`. Cut `B` — weight drops (`w(B) < w(!_w B)`). Identical to
  THY_0023's `!R` vs `!D` dereliction, with the whole-unit condition `w = 1`.
- **`!_w R` vs `!_w W`** (`w = 0`): `ℰ`'s premise `Γ; Δ' ⊢ J` is already the
  conclusion; discard `𝒟` (persistent/zero weakening, THY_0023 Lemma 7a form).
- **`!_w R` vs `!_w L(split)`** (`w = w₀ + w'`): `𝒟` promotes `B` at weight `w`;
  `ℰ` splits into `Γ; Δ', B, !_{w'} B ⊢ J` with `w₀ = w ⊖ w'` **defined**
  (`w' ≤ w`, Lemma 1 form). Cut `B` (weight `w(B)`, drops) against the `B`
  slot, then cut `!_{w'} B` (weight `w(!_{w'}B) = w(B)+1 < w(!_w B)`... — equal
  by the measure! so appeal via the structural component: `ℰ`'s premise is a
  subderivation) against the `!_{w'}B` slot. The residual arithmetic
  `w = w₀ + w'` is the additive law of the weight algebra; no case on the
  *value* of `w` beyond definedness of `⊖` is needed. This is THY_0023's delay
  `{}@d` case (measure-blind, descends to body) transported to fence `[0,1]`.
- **Vacuous cross-cases** `!_w R(w>0)` vs `!_w W(w=0)` and `!_0 R` vs
  `!_w D/split(w>0)`: the side conditions demand `w = 0` and `w > 0`
  simultaneously — no such pair of derivations exists. The weight residual/fence
  **deletes** these principal-cut cases, exactly as the count fence deletes
  `!Rpeel` vs `!L0` in THY_0023 §6.II.

### 5.2 Principal case for `[K]` (possession)

`A = [K] B`, `𝒟` ends in `[K]R`, `ℰ` in `[K]L` (dereliction).

`𝒟`'s premise: `Γ|_K; Δ|_K ⊢ B`. `ℰ`'s premise: `Γ; Δ', B ⊢ J`. **Cut `B`**
(weight `w(B) < w([K]B)`, drops). The resources `Δ|_K` promoted by `[K]R` are a
sub-multiset of the ambient split, so the cut's context split is the SELL
promotion case of THY_0013 §2 / THY_0018 §8(v): the restriction `·|_K` is
re-established from the premise (the promoted context is what `[K]R` recorded),
and the only fact used is that `|_K` is monotone under the split. No principal
arithmetic enters a *matching* dereliction.

**Vacuous mismatched-principal case** (`[μ]` over distinct principals). If a
derivation attempts to compose `[K₁]([K₂] B)` with `K₁ ≠ K₂` via `[μ]`, the side
condition `K = K₁ ⊕ K₂` is **undefined** (§2), so `[μ]` does not fire and no such
principal formula `[K] B` is introduced to be cut. Hence a cut whose formation
would require cross-principal fusion **does not exist** — Fact P1 removes the
case. This is the THY_0023 §6.II vacuity trick moved from the partial `⊖`
(count) to the partial `⊕` (principal): *partiality deletes principal-cut cases
rather than adding case obligations.*

### 5.3 The combined case `[K](!_w A)`

`𝒟` ends in `[K]R` whose body was introduced by `!_w R`; `ℰ` in `[K]L` exposing
`!_w B`, then a `!_w` left rule. By **Lemma O** the two grades never share a side
condition, so the reduction factors with no cross term:

1. **Peel the outer principal** (§5.2): cut on `[K](!_w B)` reduces to a cut on
   the body `!_w B` (weight drops by 1), with the `Δ|_K` restriction discharged
   by the SELL step. The principal side condition `K = K` is the matching-
   dereliction identity; any mismatch is already vacuous (§5.2).
2. **Descend the inner weight** (§5.1): the resulting cut on `!_w B` reduces to a
   cut on `B` (weight drops again), with the weight residual `w = w₀ + w'`
   discharged by the weight algebra.

The two steps are independent formula-weight-decreasing appeals; the combined
grade `w·K` is never manipulated as a single object — it is the product grade of
Lemma O, and each projection is handled by its own axis' case. This is the
**outer-index decomposition** TODO_0276 names, made precise: cut admissibility
for the product modality is the *conjunction* of cut admissibility on each axis,
with orthogonality guaranteeing no interaction.

### 5.4 The `says`/`knows` variants

`says` = `monad(K, ·)` (lax, TODO_0276): replace §5.2's `[K]R/[K]L` by
THY_0023's `{}R/{}L` with grade `K`. The cut is then `cut_lax` (THY_0023 §6.V),
which is *already parametric in the grade algebra*: its only grade facts are
unit, monotonicity, associativity, commutativity — all holding for the principal
algebra on its domain, with the extra bonus that off-diagonal composition is
undefined, so the `{}L` associativity step `K' ⊕ (K₀ ⊕ e)` fires only when all
three principals coincide (Fact P1 again). `knows` = `bang(K, ·)` is THY_0023's
`cut!`/`!` cases (§6.VI, §6.II) with the principal grade riding the promotion's
context restriction (`[[K]]R` is the `!R` promotion shape, TODO_0276). In both
variants the combined `says`/`knows`-over-`!_w` case factors by Lemma O exactly
as §5.3. ∎

## 6. Corollaries (the governance safety pack, as cut/identity theorems)

The point of an admissible cut is that the composed governance operations add no
theorems and the invariants are *properties of the encoding*, not enforced
guards (TODO_0276 open question 5):

- **Stake conservation.** `!_{a+b} A ⊣⊢ !_a A ⊗ !_b A` is derivable by
  identity-expansion + `!_w L/R` (the THY_0023 Theorem 6 counted-bang argument
  with `+` on `[0,1]` instead of ℕ), and cut on it is admissible (§5.1). So
  splitting and merging a stake is invertible and total-preserving: the "sum-to-1
  free from linearity" claim (TODO_0276 pillar 1; Marshall–Orchard) is the cut
  elimination / identity expansion of `!_w`, not an arithmetic side check.
- **No cross-principal theft.** `[K₁] A ⊬ [K₂] A` for `K₁ ≠ K₂` — a stealing
  rule is not merely disallowed, it is **underivable**: the only bridge is `[μ]`,
  vacuous off-diagonal (Fact P1). Cut cannot manufacture it (§5.2).
- **Ownership transfer composes.** A transfer proof `[K₁](!_w A) ⊢ [K₂](!_w A)`
  (an explicit authorized rule, TODO_0276 v1) cut against a downstream consumer
  of `[K₂](!_w A)` yields a cut-free derivation (§5.3) — proxy-upgrade /
  re-ownership chains are analytic.
- **Consistency & subformula** (THY_0023 Cor 9): `·;· ⊢ [K] a` underivable for
  atomic `a` and non-unit `K`; every formula in a cut-free derivation is a
  subformula of the endsequent with grades produced by `⊕`/`⊖` from endsequent
  grades — now on the *product* grade, per axis.

Unique-current (exactly one `current n T`) and append-only history are
consequences of ILL linearity and the `!hist` persistence discipline
respectively (TODO_0276 pillar 2); they are not cut properties and are stated
there, not here.

## 7. Status, scope, and mechanization path

**On-paper, honest boundary (as THY_0023 §8).** The proof is hand-checked. It is
*lighter* than THY_0023's because it adds no new well-founded measure component
(§4.1) and reuses the parametric core wholesale; the genuinely new content is
§2 (partial-⊕ algebra), Lemma O (§4), and the two vacuity observations
(§5.1, §5.2). What is **not** proved here, and is deliberately out of scope:

- The **combined-modality metatheorem by construction** (a display-calculus /
  adjoint proof giving cut-for-free over `modes × semiring × fixpoints ×
  principals`) — TODO_0276 P4 / THY_0044 §4 item 4, deferred there and here.
- **Graded non-interference** for the principal extension (TODO_0276 "prove
  fresh (b)") — a different theorem (information flow), not cut.
- The **v1 engine blocker** TODO_0269 (variable-binding possessed rules in
  `till`) is *orthogonal* to this result: this is the pure calculus' cut theorem;
  P0's untimed-ILL demo needs only ground possessed rules, which already run.

**Mechanized (2026-09-14).** A `dill` calculus (`calculus/dill/`, gill + the
possession modality) now realizes this as a `fuzz-cut.js` instance exactly as
`grill` (THY_0044 §4; `tests/engine/cut-admissibility.test.js`, dill the 6th
calculus, and `tools/fuzz-cut.js`): cut is admissible over the combined
`says K (!!_d A)` through the UNCHANGED generic cut (30/30 kernel-valid), and the
headline §5.2 vacuity is pinned as a **refutation** — `tests/engine/dill-possession.test.js`
asserts `says k1 a ⊬ says k2 a`, `says k1 (says k2 b) ⊬ says k1 b`, and the
non-degeneracy `says k a ⊬ a`, alongside the derivable diagonal and combined
cases (9/9). Two honest scope notes on the mechanization: (i) it realizes the
`says`/affirmation reading (§5.4) — no-cross-principal-collapse via **index
unification** in the elimination rule (the `!le 0 E` fence grounds the principal
= fence V), which needs no residual predicate and no shared-engine change; the
full possession-with-`Δ|_K` restriction (P2) and a first-class partial-⊕ grade
algebra remain the P1 upgrade. (ii) The inner `!_w` is stood in by gill's graded
comonad `!!_d A` (an orthogonal graded modality), which is what makes the
combined case exercise Lemma O; the additive-share weight algebra of §2 is the
P1 refinement. The refutations are the sharpest witness the family carries — the
same search-completeness-relative reading as `!!_5 a ⊬ !!_3 a`.

**Novelty ledger.** Authorization logic (Garg et al. 2006) eliminates cut for
`says`/`knows` but ungraded; the graded neighbours (BLL, THY_0018/0023) grade one
axis; THY_0015 composes indexed-monad × semiring semantically but proves no cut
theorem for the composite. The combination *principal index × quantitative grade
with cut elimination* — and the identification of no-cross-principal-collapse
with `⊕`-partiality at the cut layer — is new (TODO_0276 novelty audit; RES_0003
gap table).

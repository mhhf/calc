---
title: "A Next-Time Modality for Guarded Signals, by Promotion Shape"
created: 2026-09-11
modified: 2026-09-11
summary: "A sound, non-collapsing next-time modality ○ added to intuitionistic linear μMALL as a forked calculus (rill @extends fill). ○ is given a SINGLE rule — the whole-context TICK (G ; ○Δ ⊢ ○C ⟸ G ; Δ ⊢ C): it fires only when the succedent is ○C and every linear formula is ○-wrapped, strips one ○ from each, and passes the persistent context through. Its empty-Δ case is the promotion-shaped ○R (introduction); its non-empty case is ○-elimination / temporal cut. One rule gives BOTH introduction and elimination, and ○ still does not collapse (○a ⊬ a because the succedent is not ○; a ⊬ ○a because the context is not ○-wrapped) — yet signals are now CONSUMED, not only produced: the applicative ○(A⊸B),○A ⊢ ○B and the lax-monoidal ○A,○B ⊢ ○(A⊗B) hold. Guarded coinduction over signals νX.(A & ○X) still needs NO change to the cyclic-proof global trace condition (νR is the trace progress, ○ the syntactic guard). The tick is a whole-sequent transform, so it is fully RE-DERIVED in the kernel (a new soundness case, adversarially fenced), never a trusted step. Every result is kernel- and GTC-verified."
tags: [temporal-modalities, next-modality, guarded-recursion, FRP, signals, streams, coinduction, cyclic-proofs, muMALL, linear-logic, focusing, proof-theory]
category: "Proof theory"
unique_contribution: "The observation that a genuine (non-collapsing) next-time modality ○ for intuitionistic LINEAR logic needs only ONE rule — a whole-context TICK (G ; ○Δ ⊢ ○C ⟸ G ; Δ ⊢ C) that fires only when the succedent is ○C and every linear formula is ○-wrapped — of which the promotion-shaped ○R (empty Δ) is the introduction base case and the non-empty case is ○-elimination / temporal cut (the applicative ○(A⊸B),○A ⊢ ○B and lax-monoidal ○A,○B ⊢ ○(A⊗B)). Two twists distinguish it: (1) a SINGLE whole-context rule supplies both introduction and elimination while STAYING non-collapsing — the two guards (○-succedent AND all-○ context) block ○a ⊢ a and a ⊢ ○a simultaneously, so no separate left rule (which would collapse) is needed; (2) guarded coinductive signals νX.(A & ○X) are proved by the EXISTING μMALL cyclic-proof machinery with ZERO extension to the global trace condition (νR is the semantic progress, ○ the syntactic guard). The tick's whole-sequent transform is bypassed in search and fully re-derived in the kernel (strip discipline: all-○ pool, premise = stripped context, no smuggled persistent fact), keeping it in the checked TCB rather than a trusted mode switch; the same generic cut is cut-admissible over ○-bearing sequents (THY_0044 §4). Distinct from the graded lax monad (with which TODO_0203 floated conflating ○)."
references:
  - "TODO_0203 (Intuitionistic μMALL + ○ foundation for FRP) — this is its ○ layer"
  - "THY_0042 / lib/prover/gtc-check.js (the cyclic-proof GTC this reuses unchanged for guarded signals; §4's exhaustive-search weakening recovery landed alongside)"
  - "Nakano, 'A modality for recursion', LICS 2000 (the ▸/○ guard for productive recursion)"
  - "Krishnaswami, 'Higher-order functional reactive programming without spacetime leaks', ICFP 2013 (leak-freedom as a type-level ○-nesting discipline)"
  - "Baelde, TOCL 2012 / Baelde–Doumane–Saurin, CSL 2016 (μMALL and the global trace condition)"
---

# A Next-Time Modality for Guarded Signals, by Promotion Shape

## 1. What this adds

`rill` (reactive ILL) extends `fill` (ILL + μ/ν, THY_0042) with a single new
connective: the **next-time modality** `○A` — "A is available at the next tick,
not now." With μ/ν already present, ○ is exactly the piece TODO_0203 names as the
foundation for FRP: **signals** `□A = νX.(A & ○X)` (available every tick,
coinductive) and **streams/events** `◇A = μX.(A ⊕ ○X)` (fires at some future
tick, inductive). It is a **fork** — ○ lives in rill, not in fill — so the
soundness-subtle temporal machinery is firewalled from fill's audited μMALL core,
exactly as fill firewalls μMALL from production ILL. fill (and ILL) declare no ○.

## 2. ○ as a promotion, and why that is the whole design

The temptation (TODO_0203's "Key Identification: {A} = ○A") is to reuse the graded
lax monad as ○. That is right *operationally* — one forward-engine settle step is
one tick — but wrong for the *proof theory* of guarded coinduction: the monad is
negative and its `monad_l` is sticky (once in computation context, stay there),
which blocks the ν-unfold that a signal proof must perform, and its verification
runs the engine dynamically, whereas guardedness is a static, syntactic condition.

So ○ is a **fresh positive primitive** with a **single rule** — the whole-context
**tick**, which both introduces and eliminates ○ in one shape:

$$\frac{\Gamma \;;\; \Delta \vdash C}{\Gamma \;;\; \bigcirc\!\Delta \vdash \bigcirc C}\ \ ○\ \text{(tick)}
\qquad(\Gamma\ \text{persistent, passed through};\ \ \bigcirc\!\Delta\ \text{= every linear formula is}\ \bigcirc\text{-wrapped})$$

It fires only when the succedent is `○C` **and every linear formula is ○-wrapped**;
it strips one ○ from each, advancing the whole sequent one tick. The empty-`Δ`
case is exactly the promotion-shaped **○R** (`Γ ; · ⊢ ○A ⟸ Γ ; · ⊢ A`); the
non-empty case is **○-elimination / temporal cut**. Three consequences:

- **Non-collapse (soundness).** The tick needs an ○-succedent, so `○a ⊬ a` (the
  succedent `a` is not ○). It needs an *all-○* context, so `a ⊬ ○a` for *linear*
  `a` (the context `a` is not ○-wrapped — a resource consumed now cannot be
  re-offered next tick). ○ is a genuine modality, not an identity in disguise —
  both directions and their iterates are machine-checked to FAIL.
- **Elimination is the same rule, generalized (temporal cut).** Advancing the
  *whole* context is what lets a signal be *consumed*: the applicative
  `○(a⊸b), ○a ⊢ ○b` ticks to `a⊸b, a ⊢ b`. And ○ is **strong monoidal** over ⊗ —
  *both* `○a, ○b ⊢ ○(a⊗b)` and `○(a⊗b) ⊢ ○a ⊗ ○b` hold — because for the
  time-shift reading `○(A⊗B)` and `○A⊗○B` are the *same* resource multiset (`A`
  and `B` both at `t+1`). The re-wrap of a tick's leftover (`○` over the part of
  `Δ` a branch does not consume) is what realizes distribution: it is linear
  accounting through a multiplicative split, not duplication — machine-checked
  that no duplication (`○a ⊬ ○a⊗○a`), creation (`⊬ ○a⊗○b`), over-extraction, or
  discard (`○(a⊗b) ⊬ ○a`, the leftover `○b` fails root emptiness) rides it. No
  separate left rule is needed — one whole-context rule gives introduction *and*
  elimination, and non-collapse survives because both guards (○-succedent, all-○
  context) must hold at once. The kernel **re-derives** the tick (succedent ○C,
  all-○ pool, premise = the stripped context *by exact match*, leftover re-wrapped,
  no smuggled persistent fact) — not a trusted mode switch. (An audit found and
  fixed a subtlety: the premise-body check must be exact hash-equality, not
  `unify` — a `unify` fallback let a metavar premise succedent forge `○a ⊢ ○b`.)
- **The no-carry-forward discipline is exactly promotion.** Only what persists —
  the persistent (`!`) zone, passed through unchanged, or an ○-wrapped resource
  advancing one step — reaches the next tick; a bare linear resource is stranded.
  The empty-`Δ` base case is `!R`/promotion's shape (empty linear + preserved
  persistent) minus the exponential's left rules.

## 3. Guarded signals reuse the GTC unchanged

The headline: proving a signal available forever from a persistent resource,

$$!a \;\vdash\; \nu X.\,(a \mathbin{\&} \bigcirc X),$$

is a **cyclic proof** that needs **no change to the global trace condition** of
THY_0042. The derivation: `νR` unfolds to `a & ○(νX. a & ○X)`; `&R` splits; the
`a`-branch is dereliction from `!a`; the `○`-branch is `!a ⊢ ○(νX. a & ○X)`, and
`○R` advances the persistent `!a` across the tick to `!a ⊢ νX. a & ○X` — the
companion — closing a `nu_cycle` back-edge. The cycle contains `νR` on a ν-formula,
so the GTC progress condition (a νR-on-ν unfold in the cycle) is already satisfied;
context conservation holds because companion and bud share the sequent hash. **○
is the syntactic guard, νR is the trace progress** — the checker (`gtc-check.js`)
sees ○ only as an ordinary step and is untouched. Because ○ is `@category
modality` (a fresh category), `deriveRoles` assigns it no engine role, so the
role-gated cyclic engine cannot even observe it. Finite search fails (the signal
is genuinely coinductive); the cyclic proof succeeds and kernel-verifies.

Dually, `a ⊢ μX.(a ⊕ ○X)` — an event firing *now* — is a finite inductive proof
(`μR`, `⊕R₁`, identity); "always defer" has no finite proof, correctly.

## 4. Scope and frontier

Sound and machine-checked for **construction and coinductive reasoning** about
signals/streams **and their consumption**: ○-**elimination / temporal cut** is now
the whole-context tick above (`○Δ ⊢ ○C ⟸ Δ ⊢ C`), so the applicative
`○(A⊸B), ○A ⊢ ○B` and the lax-monoidal `○A, ○B ⊢ ○(A⊗B)` hold — a signal can be
ticked and consumed, not only produced. Because the tick is a whole-sequent
transform (not a one-principal rule), it is bypassed in the search and **fully
re-derived in the kernel** (a new soundness case, adversarially fenced), never a
trusted step; cut-admissibility across the family (THY_0044 §4) exercises the same
generic cut over ○-bearing sequents.

The two connective-level frontier items are now **closed**. The **graded ○** is
the `trill` calculus (grill + ○, THY_0044 roadmap item 3): all three axes compose
with zero engine change. And **⊤** (the additive unit, unit of &, the last MALL
connective) is now present in ILL — a fresh nullary `top` (@category additive,
@polarity negative), the exact DUAL of `0`: a whole-context-absorbing RIGHT rule
`top_r` (`G ; Δ ⊢ ⊤`, no premises, Δ discarded into ⊤) and NO left rule, so ⊤ does
not collapse (`⊤ ⊬ a`). It rides the kernel's `discardsContext` machinery (0L's
dual) with a succedent-tag guard that closes a latent forgery hole a
context-absorbing right rule would otherwise open (it also fixes the same latent
hole for `one_r`). The additive fragment's completeness corner — ⊤ absorbs an
arbitrary SUBSET of the pool, so `Δ ⊢ ⊤ ⊗ b` with ⊤ before a resource-consuming
sibling — is discharged by the don't-know **exhaustive** driver (it offers each
absorbed subset; the committed path absorbs all, complete for `Δ ⊢ ⊤` and the
additive positions). ⊤ needed the `additiveUnit`/`additiveZero` role SPLIT (both
nullary additives previously collapsed onto one role). MALL is complete.

The operational reading `{A} = ○A` (one settle = one tick) remains the right story
for *running* reactive programs in the forward engine — a separate face from this
backward proof theory, exactly as intended.

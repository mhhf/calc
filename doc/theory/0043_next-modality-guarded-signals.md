---
title: "A Next-Time Modality for Guarded Signals, by Promotion Shape"
created: 2026-09-11
modified: 2026-09-11
summary: "A sound, non-collapsing next-time modality ○ added to intuitionistic linear μMALL as a forked calculus (rill @extends fill). ○ is given a single rule — ○R, PROMOTION-SHAPED (empty linear context, persistent context preserved) — and deliberately no left/elimination rule, so it does not collapse (○a ⊬ a and a ⊬ ○a) yet lets guarded signals νX.(A & ○X) be built from persistent resources. The key reuse: guarded coinduction over signals needs NO change to the cyclic-proof global trace condition — the ν-unfold is the trace progress and ○ is merely the syntactic guard whose ○R advances the persistent context across each tick. Every result is kernel- and GTC-verified."
tags: [temporal-modalities, next-modality, guarded-recursion, FRP, signals, streams, coinduction, cyclic-proofs, muMALL, linear-logic, focusing, proof-theory]
category: "Proof theory"
unique_contribution: "The observation that a genuine (non-collapsing) next-time modality ○ for intuitionistic LINEAR logic needs only ONE rule — a PROMOTION-SHAPED right rule ○R (empty linear context, persistent context passed through) and NO elimination rule — and that with this shape guarded coinductive signals νX.(A & ○X) are proved by the EXISTING μMALL cyclic-proof machinery with ZERO extension to the global trace condition: νR is the semantic progress step and ○ is only the syntactic guard, its ○R the operator that advances the persistent context one tick to reach the companion. The promotion shape is exactly the linear-temporal 'no-carry-forward' discipline (a linear resource consumed now cannot be re-offered next tick; only persistent resources, or a signal's tail, advance), which makes ○ sound and non-collapsing for free, distinct from the graded lax monad (with which TODO_0203 floated conflating it)."
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

So ○ is a **fresh positive primitive** with a single rule, **promotion-shaped**:

$$\frac{\Gamma \;;\; \cdot \vdash A}{\Gamma \;;\; \cdot \vdash \bigcirc A}\ \ ○R
\qquad(\Gamma\ \text{persistent; linear context empty})$$

and **no left/elimination rule**. Two consequences, both essential:

- **Non-collapse (soundness).** With no elimination, `○a ⊬ a`: an ○A cannot be
  used in the present. With the empty-linear premise, `a ⊬ ○a` for *linear* `a`:
  a resource consumed now cannot be re-offered next tick. ○ is therefore a genuine
  modality, not an identity in disguise — both are machine-checked to FAIL, as are
  their iterates and `○a, ○b ⊬ ○(a ⊗ b)` (○ is not monoidal here).
- **The no-carry-forward discipline is exactly promotion.** Only what persists
  across time may be promised for the next tick: persistent (`!`) resources, or —
  crucially — the tail of a signal, reached across the ν back-edge. `○R` passes
  the persistent context `Γ` through unchanged and requires the linear context
  empty. This is `!R`/promotion's shape (empty linear + preserved persistent),
  minus the exponential's left rules — a modality whose resource is available only
  in the future, never now.

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
signals/streams. What is deliberately *not* here is ○-**elimination** — the
"advance the whole world" rule `○Δ ⊢ ○C ⟸ Δ ⊢ C` that lets one *consume* a
signal by ticking (temporal modus ponens / the applicative `○(A⊸B) ⊸ ○A ⊸ ○B`).
That rule acts on the entire context at once rather than one principal formula and
carries its own metatheory (a temporal cut-elimination); it is the honest next
frontier, alongside ⊤ (the additive unit, listed in TODO_0203 but unused by the
signal/stream encodings and blocked on the ⊤-vs-multiplicative-split search
corner). The operational reading `{A} = ○A` (one settle = one tick) remains the
right story for *running* reactive programs in the forward engine — a separate
face from this backward proof theory, exactly as intended.

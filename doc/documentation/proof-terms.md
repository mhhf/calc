---
title: Proof Terms (Curry-Howard)
modified: 2026-03-10
summary: Two-layer proof term architecture — generic terms from descriptors, optional interpretation maps.
tags: [Curry-Howard, proof-theory, linear-logic, architecture, verification, type-checking, logical-framework, soundness]
---

# Proof Terms

CALC assigns proof terms to ILL derivations via the Curry-Howard correspondence. A derivation of `Gamma; Delta |- A` produces a term `t : A` recording *how* A was proved.

## Two-Layer Architecture

**Layer 1 — Generic terms (automatic from rule descriptors):**

The rule name IS the proof term constructor. Descriptor fields (`side`, `premises`, `binding`, `copyContext`) mechanically determine each constructor's arity and binding structure. No manual term definitions needed.

This follows Harper-Honsell-Plotkin (1993, LF): one constructor per inference rule, adequacy guaranteed (bijection between proofs and well-typed terms).

**Layer 2 — Interpretation maps (optional, swappable):**

A fold over generic terms assigning computational meaning. Same logic, different readings:

```
Layer 1: tensor_l(z, x y -> u)
Layer 2a (lambda):   let (x, y) = z in [[u]]
Layer 2b (session):  z?(x).z?(y).[[u]]
Layer 2c (planning): decompose(z, x, y); [[u]]
```

Layer 2 is render-only for now. Term parsing/reduction deferred.

## Term Language

Dual-context judgment (DILL, Barber-Plotkin 1996): `Gamma; Delta |- t : A` where `Gamma` = cartesian (weakening + contraction), `Delta` = linear (use exactly once).

**Convention:** Principals are always variables naming hypotheses. Left rules decompose the *type* of the principal, binding fresh variables for components.

### All Constructors (Layer 1)

```
id(x)                              identity
tensor_r(u0, u1)                   tensor-R (context split)
tensor_l(z, x0 x1 -> u0)          tensor-L (decompose, bind two)
one_r()                            one-R (empty context)
one_l(z, u0)                       one-L
loli_r(x0 -> u0)                   loli-R (bind argument)
loli_l(z, u0, x1 -> u1)           loli-L (apply, bind result)
with_r(u0, u1)                     with-R (context copied)
with_l1(z, x0 -> u0)              with-L1 (first projection)
with_l2(z, x1 -> u0)              with-L2 (second projection)
oplus_r1(u0)                       oplus-R1
oplus_r2(u0)                       oplus-R2
oplus_l(z, x0 -> u0, x1 -> u1)   oplus-L (case split)
zero_l(z)                          zero-L (abort, discards context)
promotion(u0)                      !R (empty linear context)
absorption(z, y0 -> u0)           !L (y0 to Gamma)
dereliction(z, x0 -> u0)          !D (x0 stays linear)
copy(u, x0 -> u0)                 copy (duplicate from Gamma to Delta)
monad_r(E)                         monad-R (mode switch, evidence E)
monad_l(z, x0 -> u0)              monad-L
forall_r(a, u0)                    forall-R (eigenvariable)
forall_l(z, s, x0 -> u0)          forall-L (witness s)
exists_r(s, u0)                    exists-R (witness s)
exists_l(z, a, x0 -> u0)          exists-L (eigenvariable)
unreachable(reason)                dead branch (unverified)
ffi(name, args, result)            FFI axiom (unverified)
```

### Typing Rules (Selected)

**Tensor:**
```
Gamma; Delta1 |- t1 : A    Gamma; Delta2 |- t2 : B
------------------------------------- *R
   Gamma; Delta1, Delta2 |- tensor_r(t1, t2) : A * B

Gamma; Delta, x:A, y:B |- t : C
-------------------------------- *L
Gamma; Delta, z:A*B |- tensor_l(z, x y -> t) : C
```

**Loli:**
```
Gamma; Delta, x:A |- t : B
--------------------------- -oR
Gamma; Delta |- loli_r(x -> t) : A -o B

Gamma; Delta1 |- t : A    Gamma; Delta2, x:B |- u : C
------------------------------------------------------ -oL
Gamma; Delta1, Delta2, z:A-oB |- loli_l(z, t, x -> u) : C
```

**Monad (lax):**
```
Gamma; Delta |-_lax t : A
-------------------------- {A}R
Gamma; Delta |- monad_r(t) : {A}

Gamma; Delta, x:A |-_lax t : C
------------------------------- {A}L
Gamma; Delta, z:{A} |-_lax monad_l(z, x -> t) : C
```

The `|-_lax` judgment is **sticky**: once entered via `monad_r`, cannot return to `|-`. This is the type-theoretic expression of the mode switch (Pfenning-Davies 2001).

## Type Checker

`lib/prover/check-term.js` (~310 LOC) — trusted kernel extension verifying `t : A`.

**De Bruijn criterion:** The prover (untrusted, complex) produces terms; the checker (trusted, small) validates them.

The checker uses a generated map from rule name → checking function, built at calculus load time from descriptors. At runtime, each rule has its own explicit function — no descriptor interpretation at check time.

**Context splitting is deterministic.** The term dictates which sub-term uses which variables. Each linear variable consumed exactly once. No search needed.

**Focused loli_l (2-subterm variant):** For guided execution terms, `loli_l` has two subterms — first proves the antecedent (consuming resources), second continues with the consequent. Sequential context split: remaining delta from the first subterm flows to the second.

**Trust boundary:**

| Trusted | Role |
|---|---|
| `kernel.js` | Backward proof step verification |
| `check-term.js` | Forward proof term type-checking |
| `substitute.js` (debruijnSubst) | Substitution for quantifier opening |

Everything else (Store, forward engine, backward prover, FFI, strategy) is untrusted.

## Theory Compliance

**Soundness.** If `checkTerm(Gamma, Delta, t, A)` returns valid, then `Gamma; Delta |- t : A` is a valid ILL+lax derivation. Each checker case corresponds to exactly one ILL inference rule.

**Adequacy** (LF sense, Harper-Honsell-Plotkin 1993) for Layer 1:
- **Canonical forms:** Terms built post-hoc from completed proofs — no redexes, always normal form
- **Faithfulness:** Different proofs → different terms (one constructor per rule, bijection by construction)
- **Fullness:** Every well-typed term corresponds to a proof
- **Compositionality:** `extractTerm(D[s/x]) = extractTerm(D)[extractTerm(s)/x]`

Layer 2 adequacy is separate — the mapping could be many-to-one.

**No definitional equality (yet).** CLF identifies monadic expressions up to reordering of independent let-bindings. CALC doesn't need this — the forward engine commits to a specific execution order.

## Key Files

| File | Purpose |
|---|---|
| `lib/prover/generic-term.js` | `extractTerm` — backward proof tree → generic term |
| `lib/prover/guided-term.js` | `buildGuidedTerm` — forward trace → complete ILL term |
| `lib/prover/check-term.js` | Type checker (trusted kernel extension) |
| `lib/prover/bridge.js` | `buildMonadicTerm`, `rightFocusTerm` — monadic term assembly |

## References

- Barber & Plotkin (1996) — "Dual Intuitionistic Linear Logic" (DILL). Dual-context judgment
- Harper, Honsell & Plotkin (1993) — "A Framework for Defining Logics" (LF). Canonical forms, adequacy
- Watkins, Cervesato, Pfenning, Walker (2004) — "CLF: A Concurrent Logical Framework". Monadic proof terms
- Pfenning & Davies (2001) — "A Judgmental Reconstruction of Modal Logic". Lax modality

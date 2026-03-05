---
title: "Proof Terms for Quantifiers in Linear Logic"
created: 2026-03-05
modified: 2026-03-05
summary: "Survey of proof term assignments for universal and existential quantifiers in linear logic sequent calculus systems (DILL, LLF, CLF), with focus on left/right rule correspondence and generic derivation."
tags: [proof-theory, linear-logic, quantifiers, Curry-Howard, sequent-calculus, proof-terms, eigenvariable, existential, focusing, polarity, logical-framework, llf, clf, dependent-types, type-theory]
category: "Proof Theory"
---

## 1. Sequent Calculus Quantifier Rules (No Proof Terms)

The bare sequent calculus rules for first-order quantifiers are:

```
    Gamma ; Delta |- A[a/x]
   -------------------------  forall_r   (a fresh eigenvariable)
    Gamma ; Delta |- forall x. A

    Gamma ; Delta, A[t/x] |- C
   -----------------------------  forall_l   (t any term)
    Gamma ; Delta, forall x. A |- C

    Gamma ; Delta |- A[t/x]
   -------------------------  exists_r   (t any term, the "witness")
    Gamma ; Delta |- exists x. A

    Gamma ; Delta, A[a/x] |- C
   -----------------------------  exists_l   (a fresh eigenvariable)
    Gamma ; Delta, exists x. A |- C
```

The eigenvariable condition requires `a` not free in the lower sequent.

Symmetry: forall_r and exists_l introduce eigenvariables; forall_l and exists_r instantiate with witnesses.

## 2. Polarity and Focusing

In Andreoli focusing (which CALC implements):

| Quantifier | Polarity | Invertible rule | Focusable rule |
|---|---|---|---|
| forall | negative | forall_r (right, async) | forall_l (left, sync) |
| exists | positive | exists_l (left, async) | exists_r (right, sync) |

This matches CALC's `ill.calc` declarations: exists has `@polarity positive`, forall is negative by default.

## 3. Standard Proof Term Assignments

### 3a. Natural Deduction Style (System F / DILL)

Universal (System F, Barber-Plotkin DILL):
```
    Gamma |- M : A          alpha not free in Gamma
   -----------------------------------------------  forall-I
    Gamma |- Lambda alpha. M : forall alpha. A

    Gamma |- M : forall alpha. A
   --------------------------------  forall-E
    Gamma |- M [B] : A[B/alpha]
```
- Introduction: type abstraction `Lambda alpha. M` (capital lambda)
- Elimination: type application `M [B]`

Existential:
```
    Gamma |- M : A[B/alpha]
   ----------------------------------------  exists-I
    Gamma |- pack [B, M] as exists alpha. A : exists alpha. A

    Gamma |- M : exists alpha. A     Gamma, x : A |- N : C     alpha not free in C
   ----------------------------------------------------------------------------------  exists-E
    Gamma |- unpack M as [alpha, x] in N : C
```
- Introduction: `pack [B, M]` — pairs a type witness with a term
- Elimination: `unpack M as [alpha, x] in N` — opens the existential

### 3b. Sequent Calculus Style (Left/Right Rules)

The key difference from natural deduction: every rule is an introduction rule (left or right), there are no elimination rules. The Curry-Howard correspondence maps each rule to a term constructor.

**Universal quantifier:**
```
    Gamma ; Delta, u : A[a/x] |- M : C
   ----------------------------------------  forall_l
    Gamma ; Delta, u : forall x. A |- u[t] . M : C

    Gamma ; Delta |- M : A[a/x]       a fresh
   -------------------------------------------  forall_r
    Gamma ; Delta |- lambda a. M : forall x. A
```
- forall_l proof term: instantiation `u[t]` — applies the hypothesis to a witness term `t`
- forall_r proof term: abstraction `lambda a. M` — abstracts over eigenvariable

**Existential quantifier:**
```
    Gamma ; Delta |- M : A[t/x]
   ----------------------------------------  exists_r
    Gamma ; Delta |- (t, M) : exists x. A

    Gamma ; Delta, u : A[a/x] |- M : C       a fresh
   ---------------------------------------------------  exists_l
    Gamma ; Delta, u : exists x. A |- let (a, v) = u in M : C
```
- exists_r proof term: witness pair `(t, M)` — term `t` is the witness
- exists_l proof term: `let (a, v) = u in M` — unpacks the existential

### 3c. Summary Table

| Rule | Side | Proof term constructor | Analogy |
|---|---|---|---|
| forall_r | right | `lambda a. M` | type abstraction |
| forall_l | left | `u[t]` | type application / instantiation |
| exists_r | right | `(t, M)` | pack / witness pair |
| exists_l | left | `let (a,v) = u in M` | unpack / case split |

## 4. How Major Systems Handle Quantifiers

### DILL (Barber-Plotkin)

Dual-context system `Delta ; Gamma |- M : A` separating intuitionistic (Delta) and linear (Gamma) contexts. Quantifiers live in the intuitionistic fragment. Term constructors are `Lambda alpha. M` and `M [A]` for forall, same as System F. Barber's thesis confirms DILL is conservative over ILL at the level of proofs/terms.

### LLF (Cervesato-Pfenning)

The linear logical framework `lambda-Pi-loli-&-top`. Quantifiers are encoded via dependent types: `forall x:A. B` becomes the dependent function type `Pi x:A. B` (intuitionistic), with term constructor `lambda x. M` and application `M N`. Existentials are not primitive in LLF; they are encoded or left to extensions. The Pi type lives in the intuitionistic context (not linear), so quantified parameters and linear state are in separate namespaces.

### CLF (Watkins-Cervesato-Pfenning)

Extends LLF with synchronous connectives inside a monad: `lambda-Pi-loli-&-top-{exists-tensor-1-!}`. The existential quantifier `exists` is encapsulated inside the monadic type `{S}`, where `S ::= exists x:A. S | A tensor S | 1 | !A`. Term constructor for `exists x:A. S` inside the monad is `let {[x, E]} = M in N`, unpacking the existential witness. This is analogous to CALC's `{A}` monad with forward-engine mode switch.

### Session Types (Caires-Pfenning-Toninho)

In the session type interpretation of linear logic:
- `forall X. A` = receive a type (data input), polymorphic session
- `exists X. A` = send a type (data output), existential session
- Proof terms become process terms in the pi-calculus: type input and type output operations

## 5. CALC's Current Implementation

CALC handles quantifiers via the `binding` annotation on rule descriptors:

```javascript
// lib/prover/rule-interpreter.js
if (d.binding === 'eigenvariable') {
  // exists_l, forall_r: open with fresh eigenvariable
  ch[0] = debruijnSubst(ch[0], 0n, freshEvar());
} else if (d.binding === 'metavar') {
  // exists_r, forall_l: open with fresh metavar (unification finds witness)
  ch[0] = debruijnSubst(ch[0], 0n, freshMetavar());
}
```

This is already a generic/parametric approach: the rule descriptor says `binding: 'eigenvariable'` or `binding: 'metavar'`, and the rule interpreter handles both quantifiers uniformly. The `.rules` file declares:
```
exists_r: ... @binding metavar.     % witness found by unification
exists_l: ... @binding eigenvariable.
forall_r: ... @binding eigenvariable.
forall_l: ... @binding metavar.
```

No proof terms are currently extracted from these rules.

## 6. Generic Proof Term Derivation

### The Pattern

Proof term constructors follow directly from the rule structure:

1. **Right rules that abstract** (eigenvariable): term constructor is `lambda a. _` where `a` is the fresh variable
2. **Left rules that abstract** (eigenvariable): term constructor is `let (a, v) = _ in _` (destructuring)
3. **Right rules that instantiate** (metavar/witness): term constructor is `(t, _)` (pairing with witness)
4. **Left rules that instantiate** (metavar/witness): term constructor is `_[t]` (application)

This pattern is visible in a descriptor-based system:

| `binding` | `side` | Proof term shape | Name |
|---|---|---|---|
| eigenvariable | right | `lambda a. (premise_proof)` | abstraction |
| eigenvariable | left | `let (a, v) = hyp in (premise_proof)` | unpack |
| metavar | right | `(witness, premise_proof)` | pack |
| metavar | left | `hyp[witness] . (premise_proof)` | instantiation |

### Toward Generic Derivation

A fully generic system would derive proof terms from rule descriptors:
- For each premise, the proof term of that sub-derivation is a sub-term
- `binding: 'eigenvariable'` on side `r` wraps the premise proof in a lambda
- `binding: 'metavar'` on side `r` pairs the witness with the premise proof
- Context split (`contextSplit: true`) yields tensor-like pair terms
- `copyContext: true` yields `!`-like box terms
- `modeShift: true` (as in `monad_r`) yields monadic return/bind terms

The existing CALC descriptor fields (`arity`, `side`, `binding`, `copyContext`, `contextSplit`, `modeShift`, `premises`) contain enough information to mechanically derive proof term constructors for all connectives, not just quantifiers.

## 7. Key References

- Barber, "Dual Intuitionistic Linear Logic" (LFCS-96-347) — DILL term calculus
- Cervesato & Pfenning, "A Linear Logical Framework" (LICS 1996, IC 2002) — LLF dependent types
- Watkins et al., "CLF: A Dependent Logical Framework" (2004) — monadic + existential
- Caires, Pfenning, Toninho, "Linear Logic Propositions as Session Types" (MSCS 2013) — quantifiers as type I/O
- Benton, Bierman, de Paiva, Hyland, "A Term Calculus for ILL" (TLCA 1993) — foundational ILL term assignment
- Wadler, "A Taste of Linear Logic" (1993) — propositions as types for linear logic
- Wadler, "Down with the Bureaucracy of Syntax!" (2004) — pattern-matching proof terms
- Andreoli, "Logic Programming with Focusing Proofs" (JLC 1992) — polarity of quantifiers

---
title: "Dependent Types in Sequent Calculus: The Cut Problem"
created: 2026-03-02
modified: 2026-03-03
summary: "Why dependent types resist sequent calculus presentation: the cut/dependency interaction, Herbelin's and Krishnaswami's approaches, hereditary substitution, and the fire triangle."
tags: [dependent-types, sequent-calculus, cut-elimination, proof-theory, linear-logic, hereditary-substitution, type-theory, focusing, logical-framework, lnl, Curry-Howard]
category: "Proof Theory"
---

# Dependent Types in Sequent Calculus: The Cut Problem

## 1. Why Is It Awkward?

### 1.1 The Core Tension

In simple (non-dependent) sequent calculus, the cut rule is:

```
  G |- A      G, A |- C
  ────────────────────── Cut
        G |- C
```

The formula `A` in the left premise matches the formula `A` in the right premise. The types `G` and `C` are static -- they do not change depending on which proof of `A` we supply.

With dependent types, types can depend on terms. Consider the dependent function type `Pi x:A. B(x)`. The return type `B(x)` depends on the value `x` of type `A`. Now the cut rule must handle a situation where the type on one side of the cut *depends on the proof term being cut out*:

```
  G |- t : A      G, x:A |- u : B(x)
  ───────────────────────────────────── Cut
        G |- u[t/x] : B(t)
```

The result type `B(t)` is obtained by substituting `t` into `B(x)`. This substitution must:
1. Be type-preserving (the result `B(t)` must be a well-formed type)
2. Preserve canonical forms (if we work with normal forms)
3. Terminate (the substitution might trigger further reductions)

In simple type theory these are trivial. With dependent types, all three become hard.

### 1.2 The Desynchronization Problem

Miquey and Herbelin (ESOP 2017, TOPLAS 2019) identify the core problem as **desynchronization**: the type system and the reduction relation fall out of sync.

In natural deduction, reduction corresponds to beta-reduction on proof terms: `(lambda x.u) t --> u[t/x]`. The typing derivation for the redex and the reduct are closely related.

In sequent calculus, reduction corresponds to cut elimination: a cut between an introduction (right rule) and an elimination (left rule) is removed by substitution. But with dependent types, the left rule for `Pi x:A. B(x)` is:

```
  G, f : Pi x:A. B(x) |- t : A     G, y : B(t) |- C
  ──────────────────────────────────────────────────── Pi-L
  G, f : Pi x:A. B(x) |- C
```

Note how `B(t)` in the second premise depends on the proof term `t` from the first premise. During cut elimination, when we replace `f` with an actual lambda abstraction, the result type changes. The "shape" of the derivation tree must reorganize in a way that respects type dependencies.

The problem: a term can be well-typed but after one step of cut elimination, the intermediate term is ill-typed. The type system has fallen behind the reduction. This is what Miquey calls "the natural relation of reduction one would expect is not safe with respect to types."

### 1.3 Simple Example of What Goes Wrong

Consider a dependent sum (Sigma type) in the presence of a control operator (like call/cc). In natural deduction:

```
  G |- t : A      G |- u : B(t)
  ────────────────────────────── Sigma-I
  G |- (t, u) : Sigma x:A. B(x)
```

Projection gives:
```
  G |- p : Sigma x:A. B(x)
  ──────────────────────── proj1
  G |- fst(p) : A
```

Now consider what happens with call/cc. A control operator can "abort" a computation and return to a saved continuation. If we have:

```
  G |- callcc(k. (t, throw k s)) : Sigma x:A. B(x)
```

The pair `(t, throw k s)` is typed with `B(t)` for the second component. But `callcc` might abort, never actually producing the pair. If we then project:

```
  fst(callcc(k. (t, throw k s)))
```

This reduces to `callcc(k. fst(t, throw k s))` (by commuting conversion). But `fst(t, throw k s)` = `t`, while the second component `throw k s` was typed at `B(t)`, but `s` might have a completely different type. The types have desynchronized.

This is **Herbelin's 2005 paradox**: unrestricted dependent types + control operators = inconsistency. He showed that `call/cc + Sigma-types --> proof of 0=1`.

### 1.4 Why Sequent Calculus Makes This Worse

Natural deduction has introduction and elimination rules. Sequent calculus has left and right rules plus the cut rule. The additional structure of sequent calculus creates more places where type dependencies can go wrong:

1. **Cut is explicit.** In natural deduction, substitution is implicit (beta-reduction). In sequent calculus, cut is an explicit rule with explicit interaction between the two premises. With dependent types, the two premises of a cut share type information that must be kept consistent during elimination.

2. **Left rules decompose hypotheses.** The left rule for `Pi x:A. B(x)` requires producing a term of type `A` and then using the result at type `B(t)`. This creates a dependency between the sub-derivations that does not exist in simple types.

3. **Commuting conversions.** In sequent calculus, cut elimination involves commuting a cut past other rules. With dependent types, commuting a cut past a rule that introduces a type dependency can invalidate the typing of the remaining derivation.

---

## 2. Herbelin's Work

### 2.1 The lambda-bar-mu-mu-tilde Calculus

Curien and Herbelin (ICFP 2000) introduced the **lambda-bar-mu-mu-tilde calculus** (written lambda-bar-mu-mu-tilde, or just LK-mu-mu-tilde), a term assignment for classical sequent calculus LK.

**Syntax.** Three syntactic categories reflecting the structure of sequent calculus:

```
Terms (producers):     v, w ::= x | lambda x. v | mu alpha. c
Contexts (consumers):  e    ::= alpha | v . e | mu-tilde x. c
Commands (interactions): c  ::= <v || e>
```

- **Terms** are proofs of formulas on the right of the turnstile (the succedent). Variable `x` is an axiom; `lambda x. v` is a right-introduction for implication; `mu alpha. c` binds a co-variable (captures a continuation).
- **Contexts** (or co-terms) are proofs of formulas on the left of the turnstile (the antecedent). Co-variable `alpha` is an axiom; `v . e` is a left-introduction for implication (apply `v` and continue with `e`); `mu-tilde x. c` binds a variable (captures a term).
- **Commands** `<v || e>` represent the cut rule: term `v` interacts with context `e`.

**Typing.** A command `c` is typed by a sequent `G |- D` where `G` assigns types to term variables and `D` assigns types to co-variables:

```
  G |- v : A | D     (term v proves A, with co-variable context D)
  G | e : A |- D     (context e consumes A, with variable context G)
  c : (G |- D)       (command c connects G to D)
```

The cut rule becomes the command constructor:

```
  G |- v : A | D      G | e : A |- D
  ─────────────────────────────────── Cut
  <v || e> : (G |- D)
```

**The critical pair.** The key reduction rule is:

```
  <lambda x. v || w . e>  -->  <w || mu-tilde x. <v || e>>   (call-by-name)
  <lambda x. v || w . e>  -->  <v[w/x] || e>                  (call-by-value, when w is a value)
```

The two orientations correspond to call-by-name vs call-by-value evaluation. This is Curien-Herbelin's main insight: the duality of computation.

### 2.2 Herbelin's 2005 Paradox: Sigma + call/cc = False

In "On the Degeneracy of Sigma-Types in Presence of Computational Classical Logic" (TLCA 2005), Herbelin proved that:

A minimal dependent type theory with Sigma-types, equality, and a classical control operator (call/cc) is inconsistent (proves 0=1).

The argument shows that call/cc allows constructing a Sigma-pair where the first component can be observed to have two different values -- once when building the pair, and once when projecting -- leading to a proof that two distinct values are equal.

**Consequence:** Any system combining dependent types with classical logic must restrict either the dependency or the control operator. This directly constrains sequent calculus presentations because classical sequent calculus *is* a calculus with control operators (the mu and mu-tilde binders correspond to continuations).

### 2.3 The dL Calculus (Miquey-Herbelin, ESOP 2017 / TOPLAS 2019)

Étienne Miquey, building on Herbelin's work, developed **dL** (also written dL-hat-tp), a classical sequent calculus with dependent types.

**The approach:**

1. **Start from lambda-bar-mu-mu-tilde** (the Curien-Herbelin term calculus for classical sequent calculus).

2. **Add dependent types** but restrict dependencies to the **negative-elimination-free fragment**. This means: the type `B` in a dependent product `Pi x:A. B` can depend on `x`, but only if `x` is not eliminated by a control operator.

3. **Track dependencies explicitly** via an explicit list of dependencies in the typing derivation. The typing judgment becomes:

```
  G ; sigma |- v : A | D
```

where `sigma` is an explicit dependency store recording which variables have been bound to which terms. This lets the type system "keep up" with reductions that the cut elimination performs.

4. **Introduce delimited continuations** (via a delimiter `hat-tp`) to force the purity needed for dependent types. The delimiter ensures that when a term is used in a type dependency, it must have been evaluated to a value -- no control effects can escape from a dependency.

**Key metatheorems:**
- Type safety (well-typed terms do not get stuck)
- Soundness via CPS translation to a simply-typed target
- Normalization (proved later via a realizability model)

**The value restriction:** Dependencies in types are restricted to values (fully evaluated terms). If a type `B(t)` depends on a term `t`, then `t` must be a value -- not an arbitrary computation that might invoke a control operator. This is the minimal restriction needed to avoid Herbelin's paradox.

### 2.4 Extension to Classical Arithmetic (Miquey, 2018)

In the sequel paper "A Sequent Calculus with Dependent Types for Classical Arithmetic" (arXiv:1805.09542), Miquey extended dL to a system dPA-omega that can express:
- Dependent choice (an axiom of arithmetic)
- Countable universal quantification (encoded as streams)
- Lazy evaluation with sharing

The normalization proof uses Krivine-style classical realizability, resolving a conjecture from Herbelin's earlier work.

### 2.5 Summary of Herbelin's Program

| Year | Paper | Contribution |
|------|-------|-------------|
| 2000 | Curien-Herbelin, ICFP | lambda-bar-mu-mu-tilde: term assignment for classical sequent calculus |
| 2005 | Herbelin, TLCA | Paradox: Sigma + call/cc = inconsistency |
| 2010 | Herbelin, talk at DTP | Sequent calculus presentation of CIC (Calculus of Inductive Constructions), work in progress |
| 2017 | Miquey-Herbelin, ESOP | dL: classical sequent calculus with dependent types (value restriction + explicit dependencies) |
| 2018 | Miquey, arXiv | dPA-omega: extension to classical arithmetic with normalization |
| 2019 | Miquey-Herbelin, TOPLAS | Extended journal version of dL with full proofs |

---

## 3. Krishnaswami's Work

### 3.1 Integrating Linear and Dependent Types (POPL 2015)

Krishnaswami, Pradic, and Benton (POPL 2015) show how to extend Benton's linear/non-linear (LNL) adjunction with dependent types.

**Presentation:** Natural deduction (NOT sequent calculus). The paper does not give a sequent calculus formulation.

**Structure:** Two separate judgment forms connected by an adjunction:

```
  Intuitionistic judgment:  G |- t : A       (standard dependent types, contraction/weakening)
  Linear judgment:          G ; D |- t : A   (linear types, no structural rules on D)
```

where `G` is the intuitionistic (cartesian) context and `D` is the linear context.

**The split:**
- **Intuitionistic side:** Full dependent types including `Pi x:A. B(x)`, `Sigma x:A. B(x)`, identity types. Standard Martin-Lof type theory.
- **Linear side:** Linear implication `A -o B` (non-dependent), tensor `A * B`, additive conjunction `A & B`, the `!` modality connecting the two sides.

**Key restriction:** Linear types can depend on intuitionistic variables but NOT on linear variables. This is the same Cervesato-Pfenning restriction from LLF.

**Additional features:**
- **Computationally irrelevant quantification:** `forall^0 x:A. B(x)` where `x` is erased at runtime. Used for proof-irrelevant indices.
- **Proof irrelevance:** A type `Squash(A)` that packages a proof of `A` into a computationally irrelevant form.
- **Monad of computations:** A monad `T(A)` for stateful computation, enabling Hoare-triple reasoning.

**Soundness:** Proved via a realizability model in Nuprl style, validating both beta and eta laws.

**Why no sequent calculus?** The paper does not address this question. The LNL framework is naturally expressed in natural deduction because the adjunction between the two categories corresponds to the introduction/elimination structure of natural deduction. A sequent calculus version would require carefully coordinating left/right rules across the two judgment forms.

### 3.2 Relationship to the Sequent Calculus Question

Krishnaswami's system demonstrates that linear + dependent types can coexist consistently (in natural deduction), but leaves the sequent calculus presentation as an open problem. The specific challenges for a sequent calculus version:

1. **Left rules for Pi.** The intuitionistic Pi type needs left rules that decompose a hypothesis `f : Pi x:A. B(x)` by applying it to a term. The resulting type `B(t)` depends on which term `t` is chosen, creating a dependency between the sub-derivations.

2. **Cut across the adjunction.** A cut might involve a linear term on one side and an intuitionistic type dependency on the other. The adjunction must mediate this interaction.

3. **Focusing.** Krishnaswami's earlier work on focusing (ICFP 2009 "Focusing on Pattern Matching") gives a focused sequent calculus for pattern matching, but without dependent types.

### 3.3 Recent Extension: Speight (2025)

Speight's "Impredicativity in Linear Dependent Type Theory" (arXiv:2602.08846) extends Krishnaswami's system with an impredicative universe, adding:
- A universe `U` with two decoding operations (cartesian and linear)
- Injectivity of the `M` modality (linear-to-cartesian)
- Encoding of linear inductive types (lists over linear data)

This work is also in natural deduction, formalized in Rocq. No sequent calculus version.

---

## 4. The Cut Problem in Detail

### 4.1 Non-Dependent Cut (Review)

In simply-typed sequent calculus, cut elimination is straightforward. The key case is when the cut formula is introduced on both sides:

```
  G |- A    A, G |- B
  ──────────────────── Cut
       G |- B
```

Elimination proceeds by structural induction on the cut formula `A`. If `A = C -> D`:

```
         D
  Left:  C -> D, G |- B   means we have G |- C and D, G |- B
  Right: G |- C -> D       means we have C, G |- D
```

Replace the cut on `C -> D` with two smaller cuts on `C` and `D`. The formula decreases in size, ensuring termination.

### 4.2 Dependent Cut

Now consider cutting on a dependent type. Suppose `A = Pi x:C. D(x)`:

```
  Right:  G |- f : Pi x:C. D(x)    means G, x:C |- body : D(x)
  Left:   G, f : Pi x:C. D(x) |- B  means G |- t : C  and  G, y:D(t) |- B
```

The cut elimination should produce `G |- B` by substituting `body[t/x]` for `y` in the derivation of `B`. But:

1. The type of `y` in the right premise is `D(t)`, which depends on `t`.
2. After substitution, we need the derivation of `body[t/x] : D(t)`.
3. This requires proving that substitution preserves typing: if `body : D(x)` and `t : C`, then `body[t/x] : D(t)`.
4. The substitution `body[t/x]` might not be in normal form even if `body` and `t` are.
5. The resulting type `D(t)` involves a substitution into a type, which might require further normalization.

**The cascade:** Cut elimination on a dependent type triggers substitution, which triggers normalization of terms inside types, which might trigger further cuts. This cascade must terminate, and each intermediate step must be well-typed. Proving both termination and type preservation simultaneously is the hard part.

### 4.3 The Substitution Admissibility Problem

In simple sequent calculus, the substitution lemma says:

> If `G, x:A |- t : B` and `G |- s : A`, then `G |- t[s/x] : B`.

With dependent types, this becomes:

> If `G, x:A |- t : B(x)` and `G |- s : A`, then `G |- t[s/x] : B(s)`.

Note that the result type changes from `B(x)` to `B(s)`. This requires:
1. `B(s)` is a well-formed type (substitution into types is valid).
2. The substitution preserves the derivation structure.
3. If we work with normal forms, `t[s/x]` is in normal form.

Point 3 is where hereditary substitution enters (see Section 6).

### 4.4 The Problem with Non-Values

Consider the dependent cut where the term being substituted is not a value:

```
  G |- (callcc k. e) : A      G, x:A |- t : B(x)
  ────────────────────────────────────────────────── Cut
  G |- t[callcc k. e / x] : B(callcc k. e)
```

The result type `B(callcc k. e)` contains a computation (callcc) inside a type. This is problematic because:
- Type equality requires normalizing types.
- Normalizing `B(callcc k. e)` requires evaluating `callcc k. e`, which has side effects.
- The type cannot be determined without running the program.

This is why the value restriction is necessary: only values (not arbitrary computations) can appear in type dependencies.

---

## 5. What Needs to Be Proved

### 5.1 The Key Metatheorems

Anyone implementing dependent types in a sequent calculus must establish:

1. **Cut elimination (admissibility of cut).** If `G |- A` and `G, A |- C` are derivable without cut, then `G |- C` is derivable without cut. With dependent types, this is much harder because the "size" of the cut formula can increase during elimination (type substitution can produce larger types).

2. **Substitution admissibility.** If `G, x:A |- J` and `G |- t:A`, then `G |- J[t/x]`. The tricky part: `J` might be a typing judgment where the type itself mentions `x`. So you need simultaneous substitution into terms and types.

3. **Type preservation (subject reduction).** If `G |- t : A` and `t --> t'`, then `G |- t' : A'` where `A = A'` (up to definitional equality). The tricky part: definitional equality for dependent types requires normalization, creating a circular dependency.

4. **Termination of reduction.** Cut elimination terminates (strong normalization). With dependent types, the standard structural induction argument fails because substitution can increase term size. Typically proved via:
   - Hereditary substitution (makes substitution structurally recursive)
   - Realizability / logical relations (semantic argument)
   - CPS translation (reduce to a known-terminating target)

5. **Decidability of type checking.** Is it decidable whether `G |- t : A`? Requires decidable type equality, which requires decidable normalization.

### 5.2 The Tricky Parts

**The substitution-cut-dependency triangle.** Cut elimination requires substitution. Substitution changes types (because of dependency). Changed types require new typing derivations. New typing derivations might require new cuts. New cuts require cut elimination. This circularity must be broken.

**Breaking the circle:** There are two main strategies:

1. **Hereditary substitution (Pfenning et al.):** Define a special substitution operation that simultaneously substitutes and normalizes, using the type of the substituted variable as a termination measure. This avoids the need for separate normalization and breaks the circularity. See Section 6.

2. **Realizability/CPS (Herbelin-Miquey):** Instead of proving cut elimination directly, translate to a simpler system (via CPS) where normalization is known. This establishes consistency indirectly. The dL calculus uses this approach.

### 5.3 The Fire Triangle (Pedrot-Tabareau, POPL 2020)

Pedrot and Tabareau formalized the fundamental tension as a **no-go theorem**:

> A dependent type theory with all three of (1) unrestricted substitution, (2) dependent elimination, and (3) observable effects is inconsistent.

This generalizes Herbelin's 2005 paradox. You must give up at least one:
- **Give up unrestricted substitution:** Only substitute values into types (Miquey-Herbelin's value restriction).
- **Give up dependent elimination:** Restrict pattern matching on dependent types (call-by-name approach).
- **Give up effects:** Work in a pure system (standard MLTT, Coq, Agda).

For sequent calculus, this means: since the mu/mu-tilde binders of classical sequent calculus ARE effects (control operators), a classical sequent calculus with dependent types must either restrict substitution or restrict dependency. Miquey-Herbelin's dL chooses to restrict substitution to values.

For intuitionistic sequent calculus (no mu binder), the fire triangle does not apply directly, but cut elimination still creates intermediate terms that might not be in canonical form, which is why hereditary substitution is needed.

---

## 6. Hereditary Substitution

### 6.1 The Problem It Solves

In a type theory that works with **canonical forms** (beta-normal, eta-long terms), ordinary substitution does not preserve canonicity.

**Example.** In the simply-typed lambda calculus, consider:

```
  Canonical terms:   f = lambda y. y     (identity, type A -> A)
  Canonical terms:   t = x z             (application, where x : A -> A, z : A)
```

Ordinary substitution `t[f/x] = (lambda y. y) z`. This is a beta-redex, NOT canonical.

Hereditary substitution instead continues reducing:

```
  [f/x](x z) = (lambda y. y) z  -->  z
```

The result `z` is canonical. Hereditary substitution performs the substitution and reduces any newly created redexes in one combined operation.

### 6.2 How It Works

Terms are stratified into two levels:

```
  Atomic terms (neutral):    R ::= x | R N | fst R | snd R
  Canonical terms (normal):  N ::= lambda x. N | (N1, N2) | R   (at base type only)
```

The restriction that atomic terms appear in canonical position only at base type forces eta-long forms: functions must be lambdas, pairs must be pair constructors.

Three mutually recursive substitution operations:

1. **`[N0/x]_A N`** — substitute canonical `N0` (of type `A`) into canonical `N`, producing canonical result.

2. **`[N0/x]_A R`** — substitute into atomic `R`. Two sub-cases:
   - If `x` is NOT the head variable of `R`: recurse into sub-terms, result is atomic.
   - If `x` IS the head variable of `R`: the substitution creates a redex. Continue reducing.

3. **Head reduction case:** `[N0/x]_A (x N1 ... Nk)` where `N0 = lambda y. M`:
   - First, substitute `N1` for `y` in `M` hereditarily: `[N1/y]_B M` where `A = B -> C`.
   - Then continue with the remaining arguments: `[... ] (M' N2 ... Nk)`.
   - The type `A` decreases at each step (from `B -> C` to `C`), ensuring termination.

### 6.3 Termination

The **type of the substituted variable** serves as the termination measure. In the head reduction case, the type `A` is decomposed: if `A = B -> C`, the recursive call uses `B` (for the body substitution) or `C` (for the remaining applications). Both are structurally smaller than `A`.

The termination argument is lexicographic:
1. First: the type `A` of the substituted variable (strictly decreasing in head reduction).
2. Second: the structure of the term being substituted into (decreasing in structural cases).

This is why hereditary substitution works for LF (and extensions): the type structure provides a well-founded measure that ordinary substitution lacks.

### 6.4 Connection to Cut Elimination

Hereditary substitution IS cut elimination, viewed algorithmically. The cut rule says:

```
  G |- N : A      G, x:A |- M : B
  ─────────────────────────────────
  G |- [N/x]_A M : B
```

The hereditary substitution `[N/x]_A M` simultaneously eliminates the cut and normalizes. No separate normalization step is needed. This is why hereditary substitution is central to dependent types in sequent calculus: it makes cut elimination terminating by construction.

### 6.5 Connection to Dependent Types

In LF (and LLF, CLF), types can contain terms. Type checking requires comparing types for equality, which requires normalizing the terms inside types. With hereditary substitution:

- All terms in the system are in canonical form at all times.
- Substitution (= cut elimination) preserves canonical form by construction.
- Type equality is syntactic equality of canonical forms -- no separate normalization needed.
- Type checking is decidable because all types are already in normal form.

This is the Watkins-Cervesato-Pfenning-Walker insight from the CLF work (2002): define the type theory directly over canonical forms, using hereditary substitution as the only substitution operation.

### 6.6 Example: Dependent Types

Consider LF with types depending on terms:

```
  Types:   vec : nat -> type.
  Terms:   vnil : vec z.
           vcons : Pi n:nat. A -> vec n -> vec (s n).
```

Suppose we have a cut (substitution):

```
  G |- three : nat           (where three = s (s (s z)))
  G, n:nat |- t : vec n
  ────────────────────────
  G |- [three/n] t : vec three
```

Hereditary substitution `[three/n] t` replaces `n` with `three` everywhere in `t` including inside the type annotations. Since `three` is already canonical, no redexes are created and the result type `vec (s (s (s z)))` is already canonical.

The interesting case is when the substituted term appears in a head position:

```
  f : nat -> nat,  n : nat  |-  body : vec (f n)
  f : nat -> nat  |-  lambda n. body : Pi n:nat. vec (f n)
  |- inc : nat -> nat
  ─────────────────────────────────────────────────────────
  |- [inc/f] (lambda n. body) : Pi n:nat. vec (inc n)
```

Hereditary substitution replaces `f` with `inc` inside the type `vec (f n)`, producing `vec (inc n)`. If `inc = lambda m. s m`, then `inc n` is a redex inside the type. Hereditary substitution reduces it: `vec (s n)`. The result is canonical.

---

## 7. The Lengrand-Dyckhoff-McKinna PTSC

### 7.1 Pure Type Sequent Calculi

Lengrand, Dyckhoff, and McKinna (CSL 2006) introduced **Pure Type Sequent Calculi (PTSC)**, a family of sequent calculi corresponding to Barendregt's Pure Type Systems (PTS).

**Approach:** Start from Herbelin's LJT (a sequent calculus for intuitionistic logic with explicit substitutions) and enrich it with dependent types.

**Key features:**
- Equipped with a normalization procedure defined by local rewrite rules (cut-elimination style).
- Uses **explicit substitutions** instead of hereditary substitution.
- Subject reduction and confluence proved.
- A PTSC is logically equivalent to its corresponding PTS (same inhabited types).
- Strong normalization of PTSC iff strong normalization of PTS.

**Significance:** This gives a sequent calculus presentation for each system in Barendregt's lambda-cube, including:
- `lambda-arrow` (STLC)
- `lambda-2` (System F)
- `lambda-P` (LF)
- `lambda-C` (Calculus of Constructions)

### 7.2 Focused PTSC

Lengrand, Dyckhoff, and McKinna later developed a **focused** version (LMCS 2011), combining Andreoli's focusing discipline with PTSC. This enables proof search in dependent type systems via sequent calculus.

The focused PTSC uses metavariables for incomplete proofs and supports backward proof search through root-first application of focused rules.

---

## 8. Munch-Maccagnoni's Polarised Approach

### 8.1 Dependent Type Theory in Polarised Sequent Calculus (TYPES 2020)

Miquey, Montillet, and Munch-Maccagnoni proposed **Ldep**, a polarised sequent calculus for dependent types.

**Motivation:** Polarisation (positive/negative types) determines evaluation order locally: positive types are strict (call-by-value), negative types are lazy (call-by-name). This corresponds to Levy's call-by-push-value (CBPV).

**Approach:** Combine the Extended Calculus of Constructions (ECC) with a polarised sequent calculus. The polarisation resolves the value restriction: positive types are inherently value-like, so dependencies on positive types are safe without additional restrictions.

**Key result:** Ldep factorizes a dependently-typed CPS translation for ECC+call/cc. The adjoint resolution of effects corresponds to polarisation.

**Status:** Preliminary (conference abstract). Full metatheory not yet published.

---

## 9. Cervesato and Pfenning's Linear Logical Frameworks

### 9.1 LLF and CLF

Cervesato and Pfenning's Linear Logical Framework (LLF, 1996/2002) and its extension CLF (Watkins et al., 2002-2004) are the most mature systems combining dependent types with linear logic.

**Both are natural deduction, not sequent calculus.** The type theory is formulated over canonical forms using hereditary substitution.

**LLF's type theory** `lambda-Pi-(-o)-(&)-T`:
- Dependent function types `Pi x:A. B` (unrestricted)
- Linear implication `A -o B` (non-dependent)
- Additive conjunction `A & B`, additive truth `T`

**CLF extends** with synchronous connectives inside a monad: `{S}` where `S` uses tensor, 1, !, exists.

**No sequent calculus version exists** for either system. The reason is precisely the cut/dependency interaction: hereditary substitution on canonical forms works well in natural deduction but has no standard sequent calculus counterpart. A sequent calculus for CLF would need to solve the cut elimination problem for dependent + linear + monadic types simultaneously.

### 9.2 Why Natural Deduction Wins (For Now)

The natural deduction + canonical forms + hereditary substitution approach avoids the problems of sequent calculus by:

1. **No cut rule.** Cut is admissible, not primitive. Hereditary substitution establishes this once and for all.
2. **Canonical forms only.** All terms are in beta-normal, eta-long form. No intermediate ill-typed states during reduction.
3. **Type-directed.** Hereditary substitution uses type information to guide reduction, avoiding the need for a separate normalization oracle.

The trade-off: natural deduction loses the symmetry and proof-search properties of sequent calculus. Specifically:
- No focusing discipline (though PTSC adds this, see Section 7)
- No direct left/right rule symmetry
- Proof search requires additional machinery (e.g., Celf's backward/forward search engine is built on top of CLF's natural deduction, not derived from it)

---

## 10. Other Approaches

### 10.1 Lepigre's Semantical Value Restriction (ESOP 2016)

Lepigre proposed a type system for programs with control operators and dependent types where the value restriction is relaxed to a **semantical** criterion: a term can appear in a type dependency if it is **observationally equivalent to a value**, even if syntactically it is not one.

Consistency is proved by a three-layer classical realizability model (values, stacks, terms).

### 10.2 The QTT Approach (Atkey 2018)

Quantitative Type Theory resolves the dependency problem differently: every variable binding carries a **semiring grade** indicating usage. A variable at grade 0 is available for type formation but erased at runtime. This avoids the fire triangle: "type formation" happens at grade 0 (no computational effect), while "actual use" happens at grade 1 (linear) or omega (unrestricted).

QTT is formulated in natural deduction. A sequent calculus presentation would need to handle graded contexts in left/right rules.

### 10.3 Structural Cut Elimination (Pfenning 2000)

Pfenning's "Structural Cut Elimination" (I&C 2000) gives new proofs of cut elimination for intuitionistic, classical, and linear sequent calculi using three nested structural inductions. These proofs are implemented in Elf (LF-based). The technique is directly applicable to simple linear logic but does not handle dependent types.

---

## 11. Summary: The State of the Art

### 11.1 What Exists

| System | Logic | Presentation | Dependent? | Linear? | Cut elim? |
|--------|-------|-------------|-----------|---------|-----------|
| lambda-bar-mu-mu-tilde | Classical | Sequent calculus | No | No | Yes (SN) |
| PTSC (Lengrand et al.) | Intuitionistic | Sequent calculus | Yes | No | Yes (via PTS) |
| dL (Miquey-Herbelin) | Classical | Sequent calculus | Yes (restricted) | No | Yes (CPS/realizability) |
| Ldep (Munch-Maccagnoni et al.) | Classical | Polarised seq. calc. | Yes | No | Preliminary |
| LLF/CLF | Intuitionistic | Natural deduction | Yes (restricted) | Yes | Hereditary subst. |
| Krishnaswami et al. | Intuitionistic | Natural deduction | Yes (restricted) | Yes | Realizability |
| QTT (Atkey) | Intuitionistic | Natural deduction | Yes (full) | Yes (graded) | Yes (normalization) |

### 11.2 What Does NOT Exist

No system currently provides ALL of:
- Sequent calculus presentation
- Full dependent types (Pi types where the return type depends on the argument)
- Linear logic connectives (tensor, loli, bang, with, oplus)
- Cut elimination theorem
- Proof search (focusing)

The closest candidates:
- **PTSC + focusing** gives sequent calculus + dependent types + proof search, but no linearity.
- **CLF** gives dependent types + linearity + proof search, but in natural deduction.
- **dL** gives sequent calculus + dependent types (restricted) + cut elimination, but no linearity.

### 11.3 What CALC Would Need

For CALC to support dependent types (if ever), the most viable path is:

1. **Stay in natural deduction** for the type-theoretic layer (following CLF/LLF) and keep sequent calculus for proof search. This is essentially what Celf does.

2. **Or adopt PTSC-style sequent calculus** with explicit substitutions, extending it with linear connectives. This is open research.

3. **The practical minimum:** Types indexed by unrestricted variables (LLF-style). This is already how CALC's `.ill` declarations work. No change to the sequent calculus core is needed; the typing discipline lives in the `.calc` / `.ill` declarations, enforced by the loader, not by the prover.

---

## References

### Herbelin Line
- Curien, P.-L., Herbelin, H. [The Duality of Computation](http://pauillac.inria.fr/~herbelin/publis/icfp-CuHer00-duality+errata.pdf). ICFP 2000.
- Herbelin, H. [On the Degeneracy of Sigma-Types in Presence of Computational Classical Logic](http://pauillac.inria.fr/~herbelin/articles/tlca-Her05-callcc-sigma-types.pdf). TLCA 2005.
- Miquey, E., Herbelin, H. [A Classical Sequent Calculus with Dependent Types](https://dl.acm.org/doi/10.1145/3230625). TOPLAS 41(2), 2019. (Conference version ESOP 2017.)
- Miquey, E. [A Sequent Calculus with Dependent Types for Classical Arithmetic](https://arxiv.org/abs/1805.09542). 2018.

### Fire Triangle
- Pedrot, P.-M., Tabareau, N. [The Fire Triangle: How to Mix Substitution, Dependent Elimination, and Effects](https://dl.acm.org/doi/10.1145/3371126). POPL 2020.

### Pure Type Sequent Calculi
- Lengrand, S., Dyckhoff, R., McKinna, J. [A Sequent Calculus for Type Theory](https://link.springer.com/chapter/10.1007/11874683_29). CSL 2006.
- Lengrand, S., Dyckhoff, R., McKinna, J. [A Focused Sequent Calculus Framework for Proof Search in Pure Type Systems](https://lmcs.episciences.org/842). LMCS 7(1), 2011.

### Polarised
- Miquey, E., Montillet, X., Munch-Maccagnoni, G. [Dependent Type Theory in Polarised Sequent Calculus](https://inria.hal.science/hal-02505671/). TYPES 2020.

### Linear Dependent Types
- Krishnaswami, N., Pradic, P., Benton, N. [Integrating Linear and Dependent Types](https://www.cl.cam.ac.uk/~nk480/dlnl-paper.pdf). POPL 2015.
- Cervesato, I., Pfenning, F. [A Linear Logical Framework](https://www.sciencedirect.com/science/article/pii/S0890540101929517). I&C 179(1), 2002.
- Watkins, K., Cervesato, I., Pfenning, F., Walker, D. [CLF: A Dependent Logical Framework for Concurrent Computations](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). 2004.
- Speight, S. [Impredicativity in Linear Dependent Type Theory](https://arxiv.org/abs/2602.08846). 2025.

### Hereditary Substitution
- Watkins, K. et al. [A Concurrent Logical Framework I: Judgments and Properties](http://www.cs.cmu.edu/~fp/papers/CMU-CS-02-101.pdf). CMU-CS-02-101, 2002.
- Twelf. [Hereditary Substitution](https://twelf.org/wiki/hereditary-substitution/). Wiki.
- Twelf. [Hereditary Substitution for the STLC](https://twelf.org/wiki/Hereditary_substitution_for_the_STLC). Wiki.

### Structural Cut Elimination
- Pfenning, F. [Structural Cut Elimination: I. Intuitionistic and Classical Logic](https://www.cs.cmu.edu/~fp/papers/ic00.pdf). I&C 157(1-2), 2000.

### Value Restriction and Realizability
- Lepigre, R. [A Classical Realizability Model for a Semantical Value Restriction](https://arxiv.org/abs/1603.07484). ESOP 2016.

### Sequent Calculus as Programming Language
- Downen, P., Ariola, Z. [A Tutorial on Computational Classical Logic and the Sequent Calculus](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/tutorial-on-computational-classical-logic-and-the-sequent-calculus/4C5D37F74D95ED7CCFC0BB3E37F342A5). JFP 28, 2018.
- Downen, P. [Sequent Calculus: A Logic and a Language for Computation and Duality](https://www.cs.uoregon.edu/Reports/PHD-201706-Downen.pdf). PhD thesis, U. Oregon, 2017.

### Quantitative Type Theory
- Atkey, R. [Syntax and Semantics of Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.pdf). LICS 2018.

### Cross-References
- RES_0071 -- Dependent Types, Polymorphism, and Pi Types in Linear Logic
- RES_0008 -- CLF, Celf, Ceptre
- RES_0056 -- Quantitative Type Theory

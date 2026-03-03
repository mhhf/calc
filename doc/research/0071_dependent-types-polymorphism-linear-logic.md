---
title: "Dependent Types, Polymorphism, and Pi Types in Linear Logic"
created: 2026-03-02
modified: 2026-03-03
summary: "Deep survey of the LF/LLF/CLF hierarchy, dependent linear type theory, Pi types in linear settings, polymorphism (System F through QTT), and the precise relationship between polymorphism and dependent types."
tags: [dependent-types, polymorphism, linear-logic, clf, llf, lf, pi-types, type-theory, logical-framework, second-order, QTT, Idris-2, linear-types, category-theory]
category: "Proof Theory"
---

# Dependent Types, Polymorphism, and Pi Types in Linear Logic

## 1. The LF / LLF / CLF Hierarchy

### 1.1 LF (Edinburgh Logical Framework)

Harper, Honsell, Plotkin (1993). The type theory is **lambda-Pi** (also written lambda-P or the dependent function calculus).

**Syntax:**

```
Kinds:      K ::= type | Pi x:A. K
Type families: A, B ::= a | A M | Pi x:A. B
Objects:    M, N ::= x | c | lambda x:A. M | M N
```

Three levels: kinds classify type families, type families classify objects. The only binding form is `Pi x:A. B` (dependent function type) and its term-level counterpart `lambda x:A. M`.

**Key properties:**
- Canonical forms: every well-typed term has a unique beta-normal eta-long form
- Decidable type checking (checking and inference)
- Adequacy: bijection between LF terms and object-language derivations
- No polymorphism, no type operators, no linear resources

**What LF provides:** A meta-language for encoding deductive systems. Object-language judgments become LF types; object-language derivations become LF terms. The judgments-as-types methodology.

**Implementations:** Twelf (SML), Beluga (OCaml).

### 1.2 LLF (Linear Logical Framework)

Cervesato & Pfenning (1996/2002). The type theory is **lambda-Pi-lolli-with-top** (written lambda-Pi-(-o)-(&)-T).

**Syntax (extending LF):**

```
Kinds:      K ::= type | Pi x:A. K
Type families: A, B ::= a | A M | Pi x:A. B | A -o B | A & B | T
Objects:    M, N ::= x | c | lambda x:A. M | M N
                   | lambda^ u:A. M     (linear lambda)
                   | <M1, M2>            (additive pair)
                   | <>                  (unit for T)
```

LLF adds to LF:
- **Linear implication** `A -o B` with linear lambda `lambda^ u:A. M` (the linear variable `u` must be used exactly once)
- **Additive conjunction** `A & B` with projections
- **Additive truth** `T` (unit for &)

**Contexts split into two zones:**

```
Gamma; Delta |- M : A
```

where `Gamma` is the unrestricted (intuitionistic) context and `Delta` is the linear context.

**Critical restriction:** In `Pi x:A. B`, the bound variable `x` lives in the unrestricted context `Gamma`. You CANNOT form a dependent type that depends on a linear variable. The linear arrow `A -o B` is non-dependent -- `B` cannot mention the linear variable bound by `-o`.

**Why only these connectives?** The asynchronous/negative connectives (`-o`, `&`, `T`) are precisely those whose proofs admit unique canonical forms without commuting conversions. This is essential for LLF's adequacy theorem.

**Key properties:**
- Canonical forms still unique (no commuting conversions)
- Decidable type checking
- Adequacy for systems with state (Mini-ML with mutable references)
- Implemented in Twelf

### 1.3 CLF (Concurrent Logical Framework)

Watkins, Cervesato, Pfenning, Walker (2002-2004). The type theory is **lambda-Pi-(-o)-(&)-T-{exists-tensor-1-!}**.

**Syntax (extending LLF with a monadic layer):**

```
Kinds:        K ::= type | Pi x:A. K
Async types:  A, B ::= a | A M | Pi x:A. B | A -o B | A & B | T | {S}
Sync types:   S ::= a | S1 * S2 | 1 | !A | exists x:A. S
Normal terms: N ::= lambda x:A. N | lambda^ u:A. N | <N1, N2> | <> | {E}
Monadic terms: M ::= <N1, N2> | <> | !N | [N, M]_exists
Expressions:  E ::= let {p} = R in E | M
```

CLF adds the **synchronous/positive connectives** `tensor`, `1`, `!`, `exists` but confines them inside a monadic type `{S}`. Three syntactic categories of proof terms:

| Category | Types | Role |
|---|---|---|
| Normal terms N | Asynchronous (A) | Values, backward-chaining results |
| Monadic terms M | Synchronous (S) | Data constructors inside monad |
| Expressions E | Computations | Sequences of let-bindings ending in M |

**The monadic type `{S}`** is the bridge from synchronous to asynchronous. It is the ONLY way synchronous types can appear at top level.

**Concurrent definitional equality:** Two expressions `E1` and `E2` are definitionally equal if they differ only by permuting independent let-bindings. This captures "true concurrency" -- the order of independent steps is irrelevant. This equality is decidable precisely because synchronous types are confined to the monad (no commuting conversions leak into the rest of the type theory).

**What CLF provides over LLF:**
- Representation of concurrent computations (pi-calculus, CCS, Petri nets)
- Forward chaining inside the monad, backward chaining outside
- Existential quantification over terms (witness introduction)
- The bang modality `!` for persistent resources
- Tensor `*` for simultaneous resource production

**Limitation: no additives inside the monad.** CLF deliberately excludes `&` (with), `oplus` (plus), `T` (top), `0` (zero) from the synchronous fragment. These break the canonical forms property inside the monad. CALC's extensions (oplus and loli inside the monad, documented in RES_0052 Section 8) go beyond CLF's type theory.

**Implementation:** Celf (Standard ML). Celf uses backward-chaining (goal-directed) for asynchronous goals and forward-chaining (committed choice) for monadic goals.

### 1.3.1 CLF is Natural Deduction, NOT Sequent Calculus

An important point for CALC (which IS a sequent calculus system): **CLF has no standard sequent calculus presentation.** CLF's type theory λΠ⊸&⊤{} is formulated in natural deduction with canonical forms. LLF likewise.

Why: dependent types + sequent calculus is awkward. In natural deduction, `Πx:A.B` and `λx:A.M` work naturally. In sequent calculus, you need left/right rules for `Π` that interact with cut in complex ways. Herbelin and Krishnaswami have explored this, but nobody has done it for the full CLF with monad + dependent types + linear logic together.

This does NOT matter for Phases 1-3 of CALC's roadmap — polymorphism, muMALL, cyclic proofs, lax monad, and adjoint logic all have clean sequent calculus presentations. Full Π (Phase 4) is the one extension that would require moving away from sequent calculus.

### 1.4 The Hierarchy Summarized

```
LF        = lambda-Pi
            Dependent function types only. No linearity.

LLF       = LF + (-o) + (&) + T
            Adds negative/asynchronous linear connectives.
            Dependent types only on unrestricted variables.

CLF       = LLF + {S} where S has (tensor, 1, !, exists)
            Adds positive/synchronous connectives inside a monad.
            Concurrent definitional equality.
```

Each level is a **conservative extension** of the previous -- any well-typed LF term is also a well-typed LLF term, and any well-typed LLF term is a well-typed CLF term.

**What none of them have:**
- Second-order quantification over types (polymorphism)
- Type operators (type -> type)
- Additives inside the monad (oplus, zero)
- Dependent types on linear variables

---

## 2. Dependent Types in Linear Logic

### 2.1 The Core Challenge

The fundamental tension: in a dependent type `Pi x:A. B(x)`, the type `B` depends on the value `x`. But if `x` is a linear variable (used exactly once), how can `B(x)` "inspect" `x` for type formation without "using" it?

Three aspects of the problem:

1. **Type formation is free.** In standard dependent type theory, forming the type `B(x)` is a compile-time operation with no runtime cost. But in linear logic, every use of a variable "counts." If forming `B(x)` counts as a use, we cannot also use `x` computationally.

2. **Substitution with grades.** In `f : (x : A) -> B(x)` applied to `a : A`, the result type is `B(a)`. The substitution `B[a/x]` must be well-typed, which requires that `a`'s context flows correctly. If `a` is linear, its context cannot be duplicated for both the substitution and the computation.

3. **Structural rules in types.** Type equality requires comparing `B(a)` and `B(b)` when `a = b`. If `a` and `b` are linear, this comparison may require duplicating them (for reduction/normalization), which linearity forbids.

### 2.2 The Cervesato-Pfenning Restriction (LLF/CLF)

The LLF solution: **types depend only on unrestricted variables.** The Pi type `Pi x:A. B` requires `x` to be in the unrestricted context. Linear variables are bound by `-o` which is non-dependent: `A -o B` where `B` does not mention the bound variable.

This means:
- `Pi n:nat. vec n` is valid (nat is unrestricted, vec's index depends on n)
- `A -o B` is valid (linear function, B independent of the argument)
- `Pi^lin x:A. B(x)` is **NOT expressible** (no linear dependent function)

**Practical consequence:** You can index type families by terms (`plus : bin -> bin -> bin -> type`) because the indices are unrestricted. You cannot form types that depend on linear resources.

### 2.3 Krishnaswami, Pradic, Benton (POPL 2015)

Paper: "Integrating Linear and Dependent Types."

**Approach:** Extend Benton's linear/non-linear (LNL) calculus with dependent types on the intuitionistic side only.

The LNL calculus has two separate worlds connected by an adjunction:
- **Intuitionistic world** (cartesian closed category): standard types, contraction/weakening allowed
- **Linear world** (symmetric monoidal closed category): linear types, no structural rules

Krishnaswami et al. make the intuitionistic world dependent (replacing `->`  with `Pi`) while leaving the linear arrow `-o` non-dependent.

**Key insight:** The adjunction `F -| G` between the two worlds (where `F` is the "of-course" modality `!` and `G` is the forgetful functor) preserves the separation. Dependent elimination on the intuitionistic side never needs to inspect linear values.

**What it supports:**
- Dependent function types `Pi x:A. B` (intuitionistic)
- Linear function types `A -o B` (non-dependent)
- Computationally irrelevant quantification (proof irrelevance)
- Hoare triples decomposed into simpler type-theoretic connectives
- A monad for imperative computation

**Semantics:** Realizability model in Nuprl style, validating both beta and eta laws.

**Limitation:** Linear types cannot depend on linear values. The linear and dependent features coexist but do not deeply interact. This is the same fundamental restriction as LLF.

### 2.4 Fu, Kishida, Selinger (LICS 2020)

Paper: "Linear Dependent Type Theory for Quantum Programming Languages."

**Motivation:** Quantum computing requires linear types (no-cloning theorem) and dependent types (circuit size indices, qubit counts).

**Approach:** Define semantics for linear dependent type theory via fibrations of monoidal categories. Unlike Krishnaswami et al., they aim for types that depend on linear variables.

**Key idea:** A type depending on a linear variable does not "use" the variable -- dependence is a structural/compile-time relation, not a computational one. The challenge is formalizing this distinction.

**Result:** A general semantic structure (indexed symmetric monoidal categories with certain properties) that can accommodate both linear and dependent types. This is a semantic framework -- the paper does not give a complete syntactic type theory.

**Status:** Open. The full syntax for a linear dependent type theory where types can depend on linear variables remains an active research problem.

### 2.5 Speight (2025)

Paper: "Impredicativity in Linear Dependent Type Theory."

**Contribution:** Constructs a realizability model of LDTT featuring an impredicative universe. The universe `U` has two decoding operations:
- `ElC` maps codes to cartesian (unrestricted) types
- `ElL` maps codes to linear types

The universe is impredicative: closed under large cartesian dependent products AND large linear dependent products. This enables Church-style encodings of inductive types over linear data:

```
List*(A) = forall X:U. ElL(X) -o !(A -o ElL(X) -o ElL(X)) -o ElL(X)
```

This is the first realizability model for LDTT with impredicativity, formalized in Rocq.

**Significance for polymorphism:** Impredicative universes are exactly what enables System-F-style polymorphism in a dependent setting. The universal quantification over `U` is polymorphism; the impredicativity means you can instantiate at any type, including polymorphic types.

### 2.6 Quantitative Type Theory (Atkey 2018, McBride 2016)

QTT resolves the linear/dependent tension differently: **every variable binding carries a semiring annotation** `x :_r A` recording how many times `x` is used computationally.

- Grade `0`: variable used only in types (erased at runtime)
- Grade `1`: used exactly once (linear)
- Grade `omega`: unrestricted

The Pi type becomes `(x :_r A) -> B` where `B` can depend on `x` regardless of `r`. The resolution: type formation always happens at grade `0`, so inspecting `x` in `B` does not "count" as a computational use.

**The substitution fix (Atkey):** McBride's original formulation had inadmissible substitution. Atkey's fix: when substituting `a` for `x :_r A`, the resulting context is `Gamma + r * Delta` where `Delta` typed `a`. The grade `r` scales the substitute's context.

**Implementation:** Idris 2 (Brady, ECOOP 2021) with the `{0, 1, omega}` semiring.

See RES_0056 for a complete analysis of QTT and its relationship to CALC.

### 2.7 Dynamic Multiplicities (Dore et al., ICFP 2025)

Paper: "Linear Types with Dynamic Multiplicities in Dependent Type Theory."

Extends the Krishnaswami-Benton LNL approach by making multiplicities computable at the type level. Instead of fixed `1` or `omega`, a variable's multiplicity can be a function of other values. This bridges the gap between the static LNL separation and QTT's semiring approach.

### 2.8 Summary: What Is Well-Understood

| Approach | Types depend on | Linear Pi? | Status |
|---|---|---|---|
| LLF/CLF (Cervesato-Pfenning) | Unrestricted vars only | No | Implemented (Twelf, Celf) |
| LNL+Dep (Krishnaswami et al.) | Intuitionistic vars only | No | Proven sound (realizability) |
| QTT (Atkey/McBride) | Any var (grade controls use) | Yes (via grade 0) | Implemented (Idris 2) |
| Semantic LDTT (Fu et al.) | Linear vars (semantically) | In principle | Semantic framework only |
| Impredicative LDTT (Speight) | Both (with impredicative U) | Yes | Realizability model in Rocq |

**Well-understood:** Types depending on unrestricted variables. QTT's grade-based resolution.

**Still open:** Complete syntactic type theory where types truly depend on linear variables with full linear connectives (tensor, with, loli, exponentials). Normalization and decidability for such a system. Proof search (not just type checking) in dependent linear type theory.

---

## 3. Pi Types in Linear Logic

### 3.1 What "Pi Types in Linear Logic" Means

There are two distinct questions:

**Question A: First-order quantification (forall x:A. B(x)).** Universal quantification where `x` ranges over terms (individuals). This is standard in first-order linear logic and well-understood.

**Question B: Dependent function types (Pi x:A. B(x)).** A function type where the return type depends on the argument value. This is a type-theoretic construct that goes beyond first-order quantification.

In standard (non-linear) type theory, these coincide: `forall x:A. B(x)` IS `Pi x:A. B(x)` (the Curry-Howard correspondence identifies universal quantification with dependent function types).

In linear logic, they diverge because of the linearity restriction on the bound variable.

### 3.2 First-Order Universal Quantification in Linear Logic

Girard's original linear logic (1987) includes first-order quantifiers:

```
Gamma |- A[y/x]
────────────────── forall-R  (y not free in Gamma)
Gamma |- forall x. A

Gamma, A[t/x] |- C
─────────────────── forall-L
Gamma, forall x. A |- C
```

These are straightforward -- the bound variable `x` ranges over a fixed domain. The quantifiers interact with linear resources in the expected way: `forall x. (A(x) -o B(x))` means "for every x, one A(x) gives one B(x)."

**In CALC:** First-order quantification is implemented via metavariables and eigenvariables. `forall X. P(X)` in a rule means "for any X."

### 3.3 Linear Pi Types (Dependent Linear Functions)

A linear Pi type `Pi^lin x:A. B(x)` would be a function that (a) consumes its argument linearly, and (b) has a return type depending on that argument.

**Example motivation:**

```
% A function that takes a vector and returns a vector of the same length:
Pi^lin (n:nat) (v:vec n A). vec n B

% A session type that depends on the message received:
Pi^lin (m:msg). response(m)
```

**The problem:** If `x` is consumed by the function body, how can the caller know the return type `B(x)`? The caller must know `x` to determine the return type, but `x` has been consumed by the function.

**Resolution approaches:**

1. **QTT approach:** `x` at grade 0 in the type, grade 1 in the body. Type formation doesn't count as use. This works but requires the QTT machinery.

2. **Irrelevant quantification:** Separate the "type index" from the "linear resource." Instead of `Pi^lin x:A. B(x)`, use `Pi n:nat. (A(n) -o B(n))` where `n` is an unrestricted index. This is the LLF approach.

3. **Bracket types:** Use an explicit "type-level copy" of a linear value: `Pi [x]:A. B(x)` where `[x]` is erased at runtime but available for type formation. Related to proof irrelevance.

### 3.4 Open Problems

1. **Normalization for linear Pi.** Does a type theory with linear-variable-dependent Pi types normalize? QTT says yes (for its notion of "linear Pi" via grades), but a direct linear Pi without QTT's apparatus is unresolved.

2. **Proof search with linear Pi.** Type checking with linear Pi is decidable (given decidable equality). But proof SEARCH (finding a term of a given dependent type) is much harder. Unification with dependent types is undecidable in general (Miller's higher-order unification). Adding linearity constraints does not obviously help.

3. **Linear sigma types.** The dependent pair `Sigma x:A. B(x)` in linear settings: if `x` is linear and packed into a pair, projecting the first component to determine `B(x)` consumes `x`. This requires a "let-pair" elimination that binds both components simultaneously, which is exactly what CLF's tensor elimination does.

4. **Interaction with focusing.** How does Andreoli's focusing discipline extend to dependent linear types? The polarity of `Pi x:A. B` depends on A and B. If A is positive and B is negative, is the Pi type negative (as in standard focusing)? QTT's grade annotations add another dimension.

---

## 4. Polymorphism in Linear Logic

### 4.1 Second-Order Linear Logic (Girard 1987)

Girard's original linear logic includes second-order quantifiers over propositions:

```
forall X. A(X)     -- universal quantification over formulas
exists X. A(X)     -- existential quantification over formulas
```

These are exactly the polymorphic types of System F, transplanted into linear logic:

```
forall X. (X -o X)           -- polymorphic linear identity
forall X. (!X -o X)          -- polymorphic dereliction
forall X. ((X -o X) -o X)    -- not typable (would require contraction)
```

**Proof rules:**
```
Gamma |- A[B/X]
────────────────── forall-R  (X not free in Gamma)
Gamma |- forall X. A

Gamma, A[B/X] |- C
───────────────────── forall-L
Gamma, forall X. A |- C
```

**Status:** Well-understood proof-theoretically. Cut elimination for second-order propositional linear logic was claimed by Girard (1987) but the complete proof of strong normalization appeared only in Pagani & Tortora de Falco (2010).

### 4.2 System F with Linear Types: Key Approaches

**Wadler (1990): "Linear Types Can Change the World."** Extended the Girard-Reynolds polymorphic lambda calculus with linear types. Types are classified into linear (used exactly once) and unrestricted. Polymorphism via explicit type application (`Lambda X. M` and `M [A]`). Wadler noted it was unclear whether Hindley-Milner inference could be extended to the linear setting.

**Bierman, Pitts, Russo: Lily.** A second-order polymorphic linear lambda calculus with recursion. Operational semantics based on Plotkin's sketches. Key result: parametricity (in Reynolds' sense) holds for Lily -- relational parametricity for polymorphic linear types.

**Mazurak, Zhao, Zdancewic (2010): System F-degree.** Extended System F with **two base kinds**: `star` (unrestricted types) and `degree` (linear types). Subkinding `star <: degree` allows unrestricted values to be used linearly. DFA-representable protocols encodable as F-degree types. Mechanized soundness and parametricity proofs in Coq.

**Bernardy et al. (2018): Linear Haskell.** Retrofitted linearity into Haskell via multiplicity annotations on function arrows: `a %1 -> b` (linear), `a %Many -> b` (unrestricted), `a %m -> b` (multiplicity-polymorphic). Implemented in GHC. Multiplicity polymorphism is incomplete and experimental as of GHC 9.12 (2026).

### 4.3 Bounded Quantification in Linear Settings

Bounded quantification (`forall X <: A. B(X)`) restricts the range of the type variable. In the linear setting:

**System F-degree's kinded approach:** Instead of bounded quantification, use kinds to separate linear from unrestricted types. `forall X:degree. ...` quantifies over all types (linear and unrestricted); `forall X:star. ...` quantifies over unrestricted types only.

**Subkinding:** `star <: degree` provides a form of bounded quantification -- anything expecting a linear type can accept an unrestricted type (since unrestricted values can be treated linearly by using them once).

**Open:** Full bounded quantification (`forall X <: A. B(X)` where `A` is a linear type with specific operations) in a linear setting. This would combine subtyping with linearity, which creates complex interactions (subtyping on linear types must preserve the use-once discipline).

### 4.4 Parametric Polymorphism

Parametric polymorphism means a polymorphic function behaves uniformly across all type instantiations. Reynolds' abstraction theorem formalizes this.

**For linear polymorphism:** A function `f : forall X. X -o X` must be the identity (by parametricity + linearity). It cannot inspect `X` (parametricity) and cannot discard or copy its argument (linearity).

**Key results:**
- Bierman & Pitts proved relational parametricity for Lily (second-order linear lambda calculus with recursion)
- Parametricity interacts well with linearity: linear functions have FEWER possible behaviors, so parametricity theorems are often stronger
- Free theorems for linear polymorphic types are more restrictive than their non-linear counterparts

### 4.5 What CALC Would Need for Polymorphism

CALC's formulas are currently first-order: type families indexed by terms, no quantification over types.

**Option 1: Second-order formulas.** Add `forall X. A(X)` and `exists X. A(X)` at the formula level. This is second-order linear logic and is well-understood proof-theoretically. It would enable polymorphic rules like:

```
swap : forall X. forall Y. X * Y -o Y * X
```

**Option 2: Kind-level polymorphism (System F-degree style).** Extend the kind system to distinguish linear and unrestricted types. Quantify over type variables of appropriate kinds.

**Option 3: Encoding via explicit type passing (current workaround).** Define monomorphic instances for each needed type. See RES_0024 Section 3.1.

**Recommendation:** Option 1 is the most natural extension for a logic-based system. It adds expressive power without requiring dependent types, type operators, or kind polymorphism.

---

## 5. Polymorphism vs Dependent Types

### 5.1 The Lambda Cube (Barendregt)

The lambda cube identifies three independent axes of extension from the simply-typed lambda calculus:

```
Axis 1 (x): Types depending on terms     = Dependent types    (lambda-P)
Axis 2 (y): Terms depending on types      = Polymorphism       (System F)
Axis 3 (z): Types depending on types      = Type operators     (System F-omega)
```

The eight corners of the cube are:

| System | Axis 1 (dep) | Axis 2 (poly) | Axis 3 (typeop) |
|---|---|---|---|
| lambda-arrow (STLC) | No | No | No |
| lambda-P (LF) | Yes | No | No |
| System F | No | Yes | No |
| System F-omega | No | Yes | Yes |
| lambda-P2 | Yes | Yes | No |
| lambda-P-omega | Yes | No | Yes |
| lambda-P2-omega | Yes | Yes | Yes |
| lambda-C (Calculus of Constructions) | Yes | Yes | Yes |

### 5.2 Polymorphism as a Special Case of Dependent Types

In full dependent type theory, the Pi type subsumes both `->` and `forall`:

```
Pi x:A. B     where B depends on x      = dependent function
Pi x:A. B     where B does NOT depend on x  = simple arrow A -> B
Pi X:Type. B  where X is a type variable = polymorphism forall X. B
```

So yes: **polymorphism IS a special case of dependent types.** Specifically, polymorphism is the case where we have Pi types whose domain is the universe of types (`Type`).

The non-dependent arrow `A -> B` is `Pi x:A. B` with `x` not free in `B`.
System F's `forall X. B(X)` is `Pi X:Type. B(X)`.

### 5.3 Can You Get Polymorphism WITHOUT Full Dependent Types?

**Yes, absolutely.** The lambda cube shows that polymorphism (axis 2) and dependent types (axis 1) are independent extensions. System F has polymorphism without dependent types. You can add `forall X. A(X)` (quantification over types) without adding `Pi x:a. B(x)` (types depending on term values).

Concretely:

**System F** has `forall X. A(X)` but NOT `Pi n:nat. vec n`. Type variables are second-class -- they exist only at the type level, never at the term level.

**LF** has `Pi x:A. B(x)` but NOT `forall X. A(X)`. Term variables can appear in types, but there is no quantification over types themselves.

**The Calculus of Constructions** has both: Pi types range over both terms and types.

### 5.4 The Impredicativity Connection

In a system with BOTH dependent types and polymorphism, a key question is whether the universe is **impredicative**:

- **Predicative:** `forall X:Type_0. A(X) : Type_1` (the polymorphic type lives at a higher universe level)
- **Impredicative:** `forall X:Type. A(X) : Type` (the polymorphic type lives at the SAME level)

Impredicativity is what allows Church encodings of data types:

```
Nat = forall X. X -> (X -> X) -> X    -- Church numerals
List A = forall X. X -> (A -> X -> X) -> X
```

Coq's `Prop` is impredicative; its `Type` hierarchy is predicative. System F is impredicative.

Speight (2025) showed that impredicativity is consistent with linear dependent type theory (see Section 2.5), enabling linear Church encodings.

### 5.5 In the Linear Setting

For CALC's purposes, the independent axes mean:

| Feature | Requires | Systems |
|---|---|---|
| Polymorphic rules (`forall X. ...`) | Second-order quantifiers | System F, second-order LL |
| Term-indexed type families (`vec n`) | Dependent types (Pi on terms) | LF, LLF, CLF |
| User-defined type operators (`List : Type -> Type`) | Type-level lambda (axis 3) | System F-omega |
| All three combined | Calculus of Constructions | CoC, Idris, Agda |

**CALC currently has:** First-order term-indexed type families (like LLF). `plus : bin -> bin -> bin -> type` is a type family indexed by terms.

**CALC does NOT have:** Polymorphism (no `forall X:type`), type operators (no `type -> type`), or full dependent types (no types depending on linear variables).

**Polymorphism WITHOUT dependent types** is perfectly achievable: add second-order quantifiers `forall X. A(X)` to ILL. This is well-studied (Girard 1987) and does not require the machinery of dependent types at all.

### 5.6 Practical Options for CALC

**Minimal (second-order ILL):** Add `forall X. A(X)` and `exists X. A(X)` at the formula level. Proof search via eigenvariable introduction (forall-R) and witness selection (exists-R). This is a natural extension of CALC's existing quantifier machinery. Cost: higher-order unification for type-variable instantiation (semi-decidable, but practical with Miller's pattern fragment).

**Moderate (QTT-style):** Grades on variable bindings provide a linear-compatible notion of dependent types. QTT's Pi type `(x :_r A) -> B` subsumes both `forall` and `->`. Cost: semiring annotation infrastructure, grade-aware proof search (see RES_0056).

**Maximal (full Calculus of Constructions with linearity):** All three lambda cube axes plus linearity. This is Idris 2 (with QTT) or a hypothetical linear CoC. Cost: enormous implementation effort, proof search becomes undecidable in general.

---

## 6. Categorical Semantics Overview

### 6.1 Dependent Linear Type Theory

The nLab identifies the categorical semantics of dependent linear type theory as **indexed symmetric monoidal categories** (also called fibrations of monoidal categories):

For each context `Gamma`, a symmetric monoidal closed category `C_Gamma` (the "linear types over Gamma"). For each context morphism `f : Gamma1 -> Gamma2`, an adjoint triple:

```
f_! -| f* -| f_*  :  C_Gamma1 <-> C_Gamma2
```

satisfying Frobenius reciprocity and Beck-Chevalley conditions. This is the Wirtmuller version of the six-operations formalism from algebraic geometry.

### 6.2 Benton's LNL Adjunction

The foundation for many systems. A symmetric monoidal adjunction between:
- A cartesian closed category `C` (intuitionistic types)
- A symmetric monoidal closed category `L` (linear types)

The adjunction `F -| G : C <-> L` decomposes the `!` modality: `! = F . G` (comonad on L) and `lax = G . F` (monad on C).

Krishnaswami et al. (2015) extend this by making `C` a category with dependent types (a CwF = Category with Families).

### 6.3 Schreiber's Linear Homotopy Type Theory

Urs Schreiber (2014) generalizes to indexed monoidal (infinity,1)-categories, combining:
- Homotopy type theory (for the intuitionistic part)
- Linear type theory (for the linear part)
- Fibrations for dependence

This is motivated by applications in quantum physics and is the most general semantic framework, but no practical implementation exists.

---

## 7. Working Implementations

| System | Type Theory | Polymorphism | Dependent Types | Linear | Proof Search |
|---|---|---|---|---|---|
| Twelf | LF | No | Yes (Pi on unres.) | No | Yes (logic programming) |
| Celf | CLF | No | Yes (Pi on unres.) | Yes | Yes (backward + forward) |
| Idris 2 | QTT | Yes (via Pi) | Yes (full) | Yes (via grades) | No (type checking only) |
| Agda | MLTT | Yes (via Pi) | Yes (full) | No* | No (checking + tactics) |
| GHC (Linear Haskell) | System F + mult. | Yes | No | Partial (arrows only) | No |
| Granule | Graded lambda | Yes (limited) | No | Yes (graded) | No |
| CALC | ILL | No | No** | Yes | Yes (focused) |

*Agda has experimental linear types via `@0` and `@1` annotations.

**CALC has first-order term-indexed type families (LLF-style) but not full dependent types.

---

## 8. Implications for CALC

### 8.1 What CALC Can Get Cheaply

**Second-order quantification (polymorphism):** Adding `forall X:type. A(X)` to ILL is proof-theoretically clean. CALC already has eigenvariable infrastructure for first-order quantifiers. Extending to second-order requires type-variable eigenvariables and type-level substitution, but no dependent types.

### 8.2 What Requires Moderate Effort

**Graded contexts (QTT-lite):** Replace binary persistent/linear with semiring-graded contexts. RES_0056 Path 1 details this. No dependent types needed.

### 8.3 What Requires Major Effort

**Dependent types (LLF-style):** Allow type families to depend on unrestricted term variables via Pi. Requires type-level substitution, kind checking, and changes to the Store.

**Full QTT:** Dependent types + semiring grades. Requires everything in RES_0056 Section D.

### 8.4 What Is Still Open Research

**Linear Pi (types depending on linear variables):** No complete syntactic system with normalization proof.

**Proof search in dependent linear type theory:** Type checking is decidable; proof search is not. No focused proof search for dependent linear types.

**Focusing for graded/quantitative linear logic:** How does Andreoli's discipline extend when grades are not just 1/omega?

---

## References

### LF/LLF/CLF
- Harper, R., Honsell, F., Plotkin, G. [A Framework for Defining Logics](https://doi.org/10.1145/138027.138060). JACM 40(1):143-184, 1993.
- Cervesato, I., Pfenning, F. [A Linear Logical Framework](https://www.sciencedirect.com/science/article/pii/S0890540101929517). I&C 179(1):19-75, 2002.
- Watkins, K., Cervesato, I., Pfenning, F., Walker, D. [A Concurrent Logical Framework I: Judgments and Properties](http://www.cs.cmu.edu/~fp/papers/CMU-CS-02-101.pdf). CMU-CS-02-101, 2002.
- Watkins, K., Cervesato, I., Pfenning, F., Walker, D. [CLF: A Dependent Logical Framework for Concurrent Computations](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). 2004.
- Schack-Nielsen, A., Schurmann, C. [Celf: A Logical Framework for Deductive and Concurrent Systems](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28). IJCAR 2008.

### Dependent Linear Type Theory
- Krishnaswami, N., Pradic, P., Benton, N. [Integrating Linear and Dependent Types](https://www.cl.cam.ac.uk/~nk480/dlnl-paper.pdf). POPL 2015.
- Fu, P., Kishida, K., Selinger, P. [Linear Dependent Type Theory for Quantum Programming Languages](https://dl.acm.org/doi/10.1145/3373718.3394765). LICS 2020.
- Speight, S. [Impredicativity in Linear Dependent Type Theory](https://arxiv.org/abs/2602.08846). 2025.
- Luo, Z., Zhang, Y. [A Linear Dependent Type Theory](https://www.cs.rhul.ac.uk/~zhaohui/TYPES16.pdf). TYPES 2016.
- Riley, M. [A Linear Dependent Type Theory with Identity Types](https://ncatlab.org/nlab/files/Riley-QuantumCertification.pdf). 2022.

### Quantitative Type Theory
- McBride, C. "I Got Plenty o' Nuttin'." LNCS 9600, pp. 294-316, 2016.
- Atkey, R. [Syntax and Semantics of Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.pdf). LICS 2018.
- Brady, E. [Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/abs/2104.00480). ECOOP 2021.
- Dore, M. et al. [Linear Types with Dynamic Multiplicities in Dependent Type Theory](https://www.cs.ox.ac.uk/people/maximilian.dore/icfp25.pdf). ICFP 2025.

### Polymorphism in Linear Settings
- Girard, J.-Y. [Linear Logic](https://doi.org/10.1016/0304-3975(87)90045-4). TCS 50(1):1-101, 1987.
- Wadler, P. [Linear Types Can Change the World](https://homepages.inf.ed.ac.uk/wadler/papers/linear/linear.ps). IFIP TC 2, 1990.
- Bierman, G., Pitts, A., Russo, C. [Operational Properties of Lily, a Polymorphic Linear Lambda Calculus](https://www.cl.cam.ac.uk/~amp12/papers/opeplp/opeplp.pdf). TCS 2000.
- Mazurak, K., Zhao, J., Zdancewic, S. [Lightweight Linear Types in System F-degree](https://www.cis.upenn.edu/~stevez/papers/MZZ10.pdf). TLDI 2010.
- Bernardy, J.-P. et al. [Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language](https://arxiv.org/abs/1710.09756). POPL 2018.
- Pagani, M., Tortora de Falco, L. Strong Normalization for Second-Order CLL. 2010.

### Categorical Semantics
- Benton, P.N. [A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models](https://link.springer.com/chapter/10.1007/BFb0022251). CSL 1994.
- Barber, A. Dual Intuitionistic Linear Logic. ECS-LFCS-96-347, Edinburgh, 1996.
- nLab. [Dependent Linear Type Theory](https://ncatlab.org/nlab/show/dependent+linear+type+theory).
- Schreiber, U. [Quantization via Linear Homotopy Types](https://arxiv.org/abs/1402.7041). 2014.

### Lambda Cube
- Barendregt, H. Lambda Calculi with Types. Handbook of Logic in Computer Science, Vol. 2, 1992.

### Second-Order ILL Proof Language
- (2023). "A Linear Proof Language for Second-Order Intuitionistic Linear Logic." arXiv:2310.08517. (Polymorphic linear lambda calculus — Church-style type abstraction `ΛX.t` proves `∀X.A`.)

### CALC's Type Status
CALC uses LF-style declaration syntax (`bin: type.`, `plus: bin -> bin -> bin -> type.`) but does NOT type-check them. The loader reads them only for parser generation (constructor names, arities) and tag assignment. CALC is "Prolog with LF syntax" — type annotations are metadata, not enforcement. See RES_0073 §10.

### Cross-References
- RES_0008 -- CLF, Celf, Ceptre
- RES_0024 -- Higher-Order Linear Types
- RES_0052 -- CLF Lax Monad Deep Study
- RES_0056 -- Quantitative Type Theory
- RES_0073 -- Higher-Order Expressiveness Survey (§8 presentation status, §10 type status)

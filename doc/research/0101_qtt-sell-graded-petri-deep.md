---
title: "QTT, SELL, Graded Modalities, and Petri Nets: Deep Intersections"
created: 2026-04-01
modified: 2026-04-05
summary: "Deep research on the intersections of QTT with SELL, graded comonads, erasure/staging, the {0,1,ω} semiring's algebraic structure, Petri net correspondences, and resource-graded monads. Identifies established versus novel connections."
tags: [QTT, semiring, subexponentials, graded-types, Petri-nets, coeffects, staging, erasure, linear-logic, forward-chaining, multiset-rewriting, multimodal, SELL, Granule, Idris-2, category-theory]
category: "Multi-Type Framework"
---

# QTT, SELL, Graded Modalities, and Petri Nets: Deep Intersections

This document synthesizes deep research on the intersections named in the title. The existing docs RES_0056 and RES_0074 cover the fundamentals; this document fills specific gaps and investigates the more novel connections.

---

## 1. QTT and ILL's Bang: Does QTT Subsume the Exponential?

### Established connection

The {0,1,ω} semiring encodes ILL's linear/persistent distinction as a special case:

- Variable at grade 1 = linear fact (consumed once)
- Variable at grade ω = bang'd fact (persistent, re-usable)
- Grade 0 = erased (meaningful only with dependent types)

In QTT, the bang modality `!A` appears as the type of a variable that is used at grade ω. More precisely, in Atkey (LICS 2018), the promotion rule reads:

```
  ω * Gamma |- A
  ─────────────────
  ω * Gamma |- !A
```

where all resources in the context must already be at grade ω. This is identical in effect to ILL's promotion rule (which requires an empty linear context), because: ILL's "empty linear context + full cartesian context" = QTT's "all resources at grade ω."

**QTT subsumes ILL's bang in this precise sense:** bang is the ω-grade modality. ILL's copy rule (duplicating a !A fact) becomes the observation that grade ω allows arbitrary reuse. ILL's discard rule becomes the observation that ω ≥ 0 in the semiring order.

**What QTT adds that ILL lacks:**
- Dependent types: Pi/Sigma with grade annotations on binders
- The 0-grade (erased variables, meaningful only with dependent types)
- Arbitrary semiring instantiation (ILL has exactly one "bang" flavor)

**Status: Established.** Well-known in the QTT literature (Atkey 2018, McBride 2016). The connection is syntactic: there is a faithful embedding of ILL into QTT.

### What QTT does NOT give

QTT with {0,1,ω} has exactly one exponential flavor. SELL has multiple exponentials !_a indexed by labels from a preorder. QTT cannot express this unless you use a richer semiring. See Section 2.

---

## 2. QTT and SELL: Semirings vs. Subexponentials

### The gap

SELL (Nigam & Miller, PPDP 2009; DOI: 10.1145/1599410.1599427) replaces the single `!` of ILL with a family `!_a` indexed by a **subexponential signature** Σ = (I, ≤, W, C) where:
- I = set of labels
- ≤ = preorder on I
- W ⊆ I = labels allowing weakening
- C ⊆ I = labels allowing contraction
- Upward closure: a ∈ W and a ≤ b implies b ∈ W (same for C)

This is structurally different from QTT's semiring. In SELL, the "grade" of a formula is its storage zone label, and the structural rules allowed at each label are determined by set membership (W, C). In QTT, the grade is a semiring element and structural rules are determined by the semiring order.

### The c-semiring connection (ESTABLISHED but narrow)

Pimentel, Olarte, Nigam (TPLP 2014, arXiv:1405.2329) showed that SELL subexponentials can be ordered using a **c-semiring** (constraint semiring) structure when encoding soft concurrent constraint programming. C-semirings (Bistarelli et al.) are semirings where + is idempotent (making it a bounded lattice), used to model preference/cost in constraint programming. In this special case, SELL labels are elements of a c-semiring.

**This is an isolated special case, not a general equivalence.** The full connection between SELL's preorder signature and QTT-style semirings is NOT established in the literature.

### Can QTT grades model SELL subexponentials?

**Partially, but not fully.** Here is the precise analysis:

| SELL concept | QTT analogue | Fidelity |
|---|---|---|
| Subexponential label `a` | Semiring element `r` | Approximate |
| Weakening at `a` (a ∈ W) | Grade r ≥ 0, so 0 ≤ r | Captured if semiring order matches W |
| Contraction at `a` (a ∈ C) | r + r = r (idempotent) | Only if semiring addition is idempotent |
| Storage zone isolation | No analogue | Not captured |
| Preorder on labels | Semiring order | Can match if semiring preorder = SELL preorder |
| Promotion tests zone emptiness | Promotion requires r * Gamma = Gamma | Structurally different |

**What is missing:** SELL's key property is that promotion for `!_a` tests whether the *specific zone `a`* is empty (no linear facts at label a). QTT has no notion of zones — all resources are in one context, differentiated only by grade. To recover SELL from QTT, you would need a semiring where each element represents a distinct zone AND the grade determines which zone the resource lives in. This is not standard QTT.

**The Glad system (Hanukaev & Eades, TyDe 2023)** is the current closest work: it combines adjoint logic (which CAN express SELL via modes = subexponential labels) with graded types (semiring per mode). This gives both named zones (modes) and quantitative tracking (grades). Glad is described in RES_0074 Section 8.

**Status: No general QTT ↔ SELL equivalence theorem exists.** The c-semiring observation is narrow. Glad is the most complete unification but is unpublished at conference level.

### SELL and forward chaining

SELL's focused proof search (SELLF, developed by Chaudhuri, Miller, Nigam) is directly compatible with CALC's architecture. Each subexponential label is a named storage zone. In CALC's forward engine terms:
- `state.linear` = the unlabeled linear zone
- `state.persistent` = the zone !_∞ (with W and C)
- New subexponentials = additional zones with their own W/C flags

The key papers for SELLF are:

1. Nigam & Miller (PPDP 2009): "Algorithmic Specifications in Linear Logic with Subexponentials" — original SELL
2. Kanovich, Kuznetsov, Nigam, Scedrov (MSCS 2019, arXiv:1709.03607): "Subexponentials in Non-Commutative Linear Logic" — extends to non-commutative settings
3. Pimentel, Olarte, Nigam (TPLP 2014, arXiv:1405.2329): "A Proof Theoretic Study of Soft CCP" — c-semiring ordering of SELL labels
4. Despeyroux, Olarte, Pimentel (arXiv:1608.08779): "Hybrid and Subexponential Linear Logics" — HyLL vs. SELL comparison; SELL is strictly more expressive than LL
5. Olarte, Pimentel (arXiv:2404.11445): "Multi-modalities and non-commutativity in functorial linear logic" (2024) — latest SELL extension with varied structural behaviors per modality

---

## 3. Graded Modalities: The Granule Ecosystem

### Key papers

| Paper | Venue | arXiv | Main contribution |
|---|---|---|---|
| Orchard, Liepelt, Eades (2019) | ICFP 2019 | — | Granule language, graded modal types for quantitative program reasoning |
| Moon, Eades, Orchard (2020/2021) | ESOP 2021 | 2010.13163 | GrTT: graded modal dependent type theory |
| Choudhury, Eades, Eisenberg, Weirich (2020/2021) | POPL 2021 | 2011.04070 | GraD: graded dependent type theory with usage-aware heap semantics; Lemma 6.2 proves grade-0 non-interference |
| Abel, Danielsson, Eriksson (2026 preprint) | ICFP 2023 | 2603.29716 | GrTT formalized in Agda; subject reduction, normalization, decidability, erasure soundness |
| Vollmer, Marshall, Eades, Orchard (2024/2025) | CSL 2025 | 2401.17199 | Mixed linear and graded logic (mGL); generalizes Benton's LNL to graded setting |
| Eades, Orchard (2020) | LINEARITY/TLLA 2020 | 2006.08854 | Grading Adjoint Logic: combines adjoint logic with graded necessity modalities |
| Wood, Atkey (2020/2021) | TLLA/LINEARITY 2020 | 2005.02247 | Linear algebra approach to metatheory of linear lambda calculi via semirings |
| Sefl, Svoboda (2022) | WoLLIC 2022 | — | Additive types in QTT (non-trivial extension) |
| Hughes, Marshall, Wood, Orchard (2021) | TLLA 2021 | — | Linear exponentials as graded modal types |
| Marshall, Orchard (2022) | — | 2203.12875 | Non-linear communication via session types + graded modal types |
| Orchard, Wadler, Eades (2020) | TLLA 2020 | 2001.10274 | Unifying graded and parameterised monads |
| Gaboardi, Katsumata, Orchard, Breuvart (2016) | ICFP 2016 | — | Combining Effects and Coeffects via Grading |
| Fujii, Katsumata, Melliès (2016) | FoSSaCS 2016 | — | Towards a Formal Theory of Graded Monads (DOI: 10.1007/978-3-662-49630-5_30) |
| Marshall, Orchard (2023) | — | 2310.18166 | Functional Ownership via Fractional Uniqueness (Rust's ownership ≅ graded uniqueness) |
| Marshall, Orchard (2023) | — | 2309.04324 | Graded Modal Types for Integrity and Confidentiality |
| Breuvart, Kerjean, Mirwasser (2024/2026) | LMCS 2026 | 2402.09138 | Graded linear logic unified with differential linear logic via monoid-indexed exponentials |

### GraD: graded types with usage-aware heap semantics (Choudhury-Eades-Eisenberg-Weirich, POPL 2021)

GraD bridges the gap between QTT's type-level grade tracking and operational heap behavior. Key contributions relevant to CALC:

1. **Grade-0 non-interference (Lemma 6.2):** Grade-0 heap entries are provably irrelevant to computation. The heap partitions into "used" and "erased" segments; the erased segment has no observable effect. This validates THY_0015's staging claim from the dependent-types side.

2. **Graded substitution:** When substituting a term used `q` times, context cost is `Γ₁ + q·Γ` — the grade scales the substituted context. This is the operational content of the semiring multiplication.

3. **V-shaped partial order:** GraD uses {0 ≤ ω, 1 ≤ ω, 0 ∥ 1} (same as Granule, same as CALC's implementation). The incomparability of 0 and 1 prevents erased resources from being used linearly.

4. **Usage-aware heap semantics:** Resources are tracked in the heap with grade annotations. This is the closest published work to CALC's forward-engine state model where `state.linear` (grade-1) and `state.persistent` (grade-ω) are operationally distinct zones.

### The graded comonad decomposition (Fujii-Katsumata-Melliès 2016)

The key categorical result: **every graded comonad decomposes as an adjunction + strict monoidal action.** This means:

```
Graded comonad T_r  ≅  G ∘ F  (adjunction) + monoid action (grade r)
```

This generalizes Benton's LNL decomposition (`! = G ∘ F` across two categories) to the graded setting. The grade `r` now acts as a "how many times" parameter on the adjunction.

For CALC: CALC's existing LNL adjunction (F: linear → cartesian, G: cartesian → linear) is the r=ω special case. The graded comonad framework would allow CALC to have `!_r` for any semiring element `r`, decomposing as the same adjunction but parameterized by grade.

### Linear exponentials as graded modal types (Hughes-Marshall-Wood-Orchard, TLLA 2021)

This paper establishes the precise connection: ILL's linear exponential `!A` is a special case of the graded modal type `□_ω A` (resource at grade ω). The graded modal type framework subsumes the standard linear exponential.

### Mixed linear and graded logic (Vollmer-Marshall-Eades-Orchard, CSL 2025, arXiv:2401.17199)

Shows that the graded comonad `!_r` on a linear base decomposes into two modalities:
1. A modality connecting the linear world to a graded world (analogous to `G: U → L` in LNL)
2. A graded action modality (the grade `r`)

This gives the equation: `!_r A ≅ G(r ⊗ F(A))` where F, G are the LNL adjoint functors and ⊗ is the graded tensor. The system can be understood as "Linear/Non-Linear logic composed with an action that adds the grading."

**Practical meaning for CALC:** CALC's LNL infrastructure (persistent zone = cartesian, linear zone = linear) is already the ungraded version of this. Adding grades to CALC means adding a grade parameter to the LNL adjunction without changing its categorical structure.

### Grading adjoint logic (Eades-Orchard, TLLA 2020, arXiv:2006.08854)

Combines Pfenning-style adjoint logic (mode preorder, shifts ↑/↓) with graded necessity modalities. Each mode carries its own semiring, and the modal operators are parameterized by both a mode transition and a grade. This is the intermediate system between SELL (modes only) and full graded QTT (grades only with dependent types).

**This paper directly answers "can QTT grades model SELL modes?":** Not fully, but the combination in Graded Adjoint Logic can model both simultaneously.

---

## 4. QTT and Erasure in Idris 2

### What 0-multiplicity means precisely

From the Idris 2 documentation and Brady (ECOOP 2021, arXiv:2104.00480):

1. **Definition:** A 0-multiplicity binding `(0 x : A)` means `x` has zero occurrences at runtime. The value exists only at the type level.

2. **Pattern matching restriction:** 0-quantity variables may NOT be pattern matched in general. They can be used in types, type indices, and to constrain other computations, but their computational content is inaccessible. Exception: the value is matchable when "uniquely inferrable from the type of another argument."

3. **Primary use cases:**
   - **Parametric polymorphism:** `id : (0 a : Type) -> a -> a` — the type argument `a` is erased, enabling parametricity
   - **Type indices:** `length : (0 n : Nat) -> Vect n a -> Nat` — the vector length constrains the type but is not computed at runtime
   - **Irrelevance:** proof-irrelevant arguments that constrain types but are not inspected

4. **When erasure happens:** At code generation time (after type checking). The type checker verifies the 0-quantity constraint; the code generator removes 0-annotated content from the runtime representation.

5. **Not the same as dependent elimination:** A 0-quantity term `(0 x : A)` can appear in types (which are also checked at grade 0 per the "sigma=0" trick) but cannot be eliminated (case-analyzed) in terms. This is McBride's key insight: type formation happens at sigma=0, which is why type-level uses of variables don't count against their multiplicities.

### Abel-Danielsson-Eriksson formalization (arXiv:2603.29716, ~ICFP 2023)

The most rigorous treatment. Key results:
- **Subject reduction:** Grade assignments are preserved under reduction
- **Consistency:** The system is consistent (no proof of False)
- **Normalization:** Terms normalize
- **Decidability:** Definitional equality is decidable
- **Extraction soundness:** The extraction function (erasing 0-graded content to untyped λ-calculus) is sound — programs with ground types have the same values before and after erasure

The system is **parameterized by a modality structure** — a partially ordered semiring. Different semiring instantiations give different type disciplines.

### Connection to staging: tenuous but real

The 0-grade is semantically related to the "compile-time" phase of staged computation, but the connection is informal/conceptual rather than a formal correspondence:

| Staging concept | QTT 0-grade analogue |
|---|---|
| Phase 1 (compile-time) computation | Type-level computation at grade 0 |
| Phase 2 (runtime) computation | Term-level computation at grade 1/ω |
| Quote/splice operators | No direct analogue in vanilla QTT |
| Staging correctness | Erasure soundness theorem |

**Kovács (arXiv:2209.09729, POPL 2023)** showed that **Two-Level Type Theory (2LTT)** gives staged compilation with full dependent types. 2LTT uses two levels (object level and meta level) with a clean phase separation. This is architecturally similar to QTT's sigma=0/1 distinction but the correspondence is not a formal embedding: 2LTT has explicit staging operators (quote/splice); QTT just has grade 0.

**Status:** The connection between QTT erasure and staging is conceptually well-understood but there is no published paper proving a formal equivalence. The two systems solve related but distinct problems (erasure = removing irrelevant information; staging = generating specialized code at compile time).

---

## 5. Resource-Graded Monads: Effects and Coeffects

### The graded monad framework

**Fujii, Katsumata, Melliès (FoSSaCS 2016):** "Towards a Formal Theory of Graded Monads"

A **graded monad** is a family of functors T_r (r from a monoid M) with:
- Unit: `1_A : A → T_1(A)` (using monoid unit)
- Multiplication: `μ_{r,s} : T_r(T_s(A)) → T_{r*s}(A)` (using monoid multiplication)

This generalizes ordinary monads (take M = {*}, the trivial monoid).

A **graded comonad** is the dual: `ε : D_0(A) → A` and `δ_{r,s} : D_{r+s}(A) → D_r(D_s(A))`.

The decomposition theorem: every graded comonad T_r on a cartesian category decomposes as `T_r ≅ G ∘ L_r ∘ F` where F, G are the adjoint pair of the underlying monad and L_r is a "level" functor parameterized by the grade.

### Combining effects and coeffects (Gaboardi, Katsumata, Orchard, Breuvart, ICFP 2016)

The central paper for the indexed monad / graded combination. Key result: effects (monads) and coeffects (comonads) can be combined via **grading**, giving a unified framework:

- **Graded monads** model *effects* parameterized by resource consumption (e.g., "this computation uses exactly r units of resource X")
- **Graded comonads** model *coeffects* parameterized by resource availability (e.g., "this computation requires r units of context")

The combined system has typing judgments of the form `Γ_r ⊢ t : A { e }` where:
- `r` is a grade (coeffect: what resources the term uses from the context)
- `e` is an effect annotation (what side effects the term produces)

### Relevance to CALC's `{A}_r` monad

CALC's lax monad `{A}` is an ordinary (ungraded) monad at the type level: `{A}` means "forward execution produces A." The grade would be the resource consumption of the forward computation.

A **resource-graded version** `{A}_r` would mean: "forward execution of A consumes exactly r linear resources." This is well-supported by the graded monad framework:

- The effect (what the monad produces) = the sequent type A
- The coeffect (what resources are consumed) = the grade r

The Gaboardi-Katsumata-Orchard ICFP 2016 framework directly applies. Whether CALC should adopt this is a design question (see RES_0054, RES_0056).

**Graded Hoare Logic** (Gaboardi, Katsumata, Orchard, Sato, arXiv:2007.11235) extends this to imperative programs, giving a Hoare triple `{P}_r t {Q}` where r is the preordered monoidal annotation. This is directly relevant to CALC's forward engine: each rule application could carry a grade annotation, and the resulting "resource Hoare triple" would certify the resource usage of a forward computation.

---

## 6. QTT for Compilation and Staging

### Current state of the art

There are **no published papers** directly using QTT's 0-grade for staged compilation in the sense of "partial evaluation" or "MetaML-style staging." The closest works are:

1. **Brady (ECOOP 2021):** Idris 2 uses 0-grade for erasure. Parameters like `(0 a : Type)` are erased at compile time. This is not staged computation in the MetaML/Template Haskell sense — there are no quote/splice operators, no runtime code generation.

2. **Kovács (POPL 2023, arXiv:2209.09729):** Two-Level Type Theory (2LTT) provides staged compilation with dependent types. The system has object level (runtime code) and meta level (compile-time code). The staging correctness theorem says: meta-level computation is safe to run at compile time. This is architecturally similar to QTT's grade-0/grade-1 distinction but uses different machinery.

3. **Atkey (POPL 2023/2024, arXiv:2307.09145):** Polynomial Time and Dependent Types — uses QTT to ensure that term-level computation is polynomial time while type-level computation is unrestricted. This is effectively a compile-time/runtime distinction encoded via QTT grades.

### The conceptual connection

In QTT:
- Grade 0 terms are "compile-time only" in the sense that they exist only in types (the "0-world")
- Grade 1 terms are "runtime" in the sense that they are computationally relevant
- Grade ω terms are "freely usable" at runtime

In staged computation:
- Stage 1 (compile-time) = corresponds to grade 0 (erased at runtime, used only for type-checking)
- Stage 2 (runtime) = corresponds to grade 1 or ω (computationally relevant)

The formal connection would be: grade-0 terms in QTT ARE stage-1 terms in a two-stage computation. But this has not been formally proved. The difficulty is that QTT's grade-0 forbids *all* runtime use, not just "not yet specialized" use as in staging.

**Novel connection (not yet established in literature):** Compile-time cut elimination in CALC (RES_0099) uses a 0-grade intuition: forward rules that are "only for type inference" can be reduced at compile time. This is a specific application of the grade-0/grade-1 distinction to CALC's dual backward/forward structure.

---

## 7. Petri Nets with Weighted Tokens and Linear Logic

### The classical connection (Kanovich 1995, ESTABLISHED)

**Kanovich (1994/1995):** "Petri Nets, Horn Programs, Linear Logic, and Vector Games." TACS 1994 / APAL 75(1-2):107-135.

The key theorem: **Petri net reachability reduces to ILL provability** (and is EXPSPACE-complete in both cases). The encoding:

- Each Petri net place `p` with k tokens = k copies of formula `p` in the linear context
- A Petri net transition that consumes places `p₁,...,pₙ` and produces places `q₁,...,qₘ` = ILL rule: `p₁ ⊗ ... ⊗ pₙ ⊸ q₁ ⊗ ... ⊗ qₘ`
- Transition firing = applying the ILL rule (consuming antecedent formulas, producing consequent formulas)
- Reachability from marking M to marking M' = ILL provability of M' from M

This is the canonical correspondence: **ILL's multiplicative fragment = Petri net rewriting**. The tensor is multiset union, loli is transition, multiplicative unit is the empty marking.

**Meseguer & Montanari (LICS 1988 / Information and Computation 1990):** "Petri Nets are Monoids: A New Algebraic Foundation for Net Theory." Established that Petri nets have a categorical (monoidal) structure that aligns with the categorical semantics of linear logic.

### Weighted Petri nets and the semiring connection

Standard Petri nets have integer token counts: a transition consumes exactly `w(t,p)` tokens from place `p`. This corresponds to:

- Arc weight `w(t,p) = n` means the rule requires exactly n copies of formula `p`
- In QTT/graded types: this is grade n for the formula p

**Colored Petri nets** have tokens with values from a color set (a type). This corresponds to:
- Formula predicates in CALC: `p(x)` where x ranges over a domain
- Transitions fire on specific color patterns

**Weighted automata over semirings** (Droste, Kuich; see Droste, Ésik, Kuich 2017, arXiv:1708.06463): A semiring-weighted automaton assigns semiring values to transitions. The semiring operations (+ for branching, × for sequencing) compute the total weight of a run. This is related but not directly to Petri nets.

### Semiring Petri nets = QTT forward engine?

This connection is **largely novel** — no paper explicitly establishes the correspondence:

| Petri net concept | QTT / graded types | CALC engine |
|---|---|---|
| Place p | Linear fact type | Fact hash in `state.linear` |
| k tokens at place p | Grade k annotation | k copies of fact in linear state |
| Arc weight w(t,p) = k | Rule requires grade k | Pattern expects k copies |
| Transition firing | Rule application | `applyMatch` in `forward.js` |
| Integer token counts | Natural numbers semiring | CALC uses count in `FactSet` |
| Marking (multiset of tokens) | Graded context | `state.linear` |
| Reachability | Provability | `explore.js` exhaustive search |

**The grades ARE token counts.** A rule that consumes n copies of fact A and produces m copies of fact B is exactly a Petri net arc with weight n on the input and m on the output. The semiring for Petri net token arithmetic is (ℕ, +, ×, 0, 1) — natural numbers. The {0,1,ω} semiring is a quotient: ℕ/{≥2} where all counts ≥ 2 are collapsed to ω.

**Practical consequence:** CALC's existing forward engine already implements weighted Petri net semantics, with weights from the truncated semiring {0, 1, ω}. The engine counts copies of linear facts (weights 0, 1, or many) and rules consume/produce specific weight amounts.

---

## 8. The {0, 1, ω} Semiring: Algebraic Properties

### Definition and tables (from Idris 2 / Atkey 2018)

```
+  | 0  1  ω         ×  | 0  1  ω
───+──────────        ───+──────────
0  | 0  1  ω         0  | 0  0  0
1  | 1  ω  ω         1  | 0  1  ω
ω  | ω  ω  ω         ω  | 0  ω  ω
```

Natural (algebraic) order: 0 ≤ 1 ≤ ω (induced by addition: a ≤ b ⟺ ∃c: a+c=b). But the **usage ordering** for structural rules and promotion in QTT is the partial order {0 ≤ ω, 1 ≤ ω} with 0 ∥ 1 (incomparable) — a "V" shape, not a total chain. This prevents erased (0) resources from being used linearly (1).

### Is it the natural numbers truncated at 2?

Precisely: {0, 1, ω} ≅ ℕ / (n ≥ 2 → ω). The quotient identifies all natural numbers ≥ 2 with ω. Under this quotient:
- Addition truncates: 1+1 = ω (because 2 is collapsed to ω)
- Multiplication truncates: ω × 1 = ω (because n × 1 = n for n ≥ 2 is collapsed)

This is sometimes called a **truncated natural numbers semiring** or a **bounded semiring**. More precisely, it is the Rees quotient of (ℕ, +, ×) by the ideal {n ∈ ℕ | n ≥ 2}.

### Algebraic classification

The semiring {0, 1, ω} is:
- **Commutative**: + and × are both commutative
- **NOT a ring**: has no additive inverses (no subtraction)
- **NOT an integral domain**: ω × 0 = 0 but ω ≠ 0
- **A bounded distributive lattice** under the order 0 ≤ 1 ≤ ω (with ω as top)
- **NOT idempotent** under addition: 1 + 1 = ω ≠ 1 (unlike boolean semirings)
- **Partially ordered semiring**: the order 0 ≤ 1 ≤ ω is compatible with + and ×

### Comparison with other semirings used in the literature

| Semiring | Elements | Properties | Use in graded types |
|---|---|---|---|
| {0, 1, ω} | Idris 2 / QTT | Truncated ℕ; 1+1=ω | Linear/erased/unrestricted |
| ℕ | Natural numbers | Exact counting; 1+1=2 | Bounded Linear Logic (Girard-Scedrov-Scott 1992); exact usage bounds |
| Bool | {0, 1} (= {false, true}) | 1+1=1 (idempotent) | Used/unused; relevance typing |
| ℤ | Integers | Has negatives; full ring | Resource debt (overdraft) |
| ℝ≥0 | Non-negative reals | Continuous | Probabilistic/cost tracking |
| Lattice | Security levels {L, H} | With ⊔, ⊓ | Information flow (public/secret) |
| Interval semiring | [a, b] ⊆ ℕ | Usage bounds | AARA (amortized resource analysis) |
| {0, 1-, 1, 1+, ω} | Five-point | McBride's "richer" semiring | Affine (≤1), linear (=1), relevant (≥1) |

The {0, 1, ω} semiring is the **minimal useful** semiring for practical type theory: it captures erasure (0), linearity (1), and unrestricted use (ω) with the fewest elements. The natural numbers semiring ℕ is strictly more expressive (can bound exact usage) but requires a solver for grade constraints (Z3 or similar).

**Bounded Linear Logic (BLL)** (Girard, Scedrov, Scott, TCS 1992) uses natural number grades on the exponential: `!_n A` means "A can be used at most n times." This is the ℕ semiring special case of the graded types framework, predating QTT by 24 years. BLL is the earliest graded modal logic for linear logic.

### Monotone semirings

A **monotone semiring** (or **partially ordered semiring**) requires compatibility of the order with operations:
- a ≤ b implies a + c ≤ b + c (+ is monotone)
- a ≤ b implies a × c ≤ b × c (× is monotone)

{0, 1, ω} is a monotone semiring. This is required for the subsumption rule in QTT:

```
Gamma |- t : A     rho' ≤ rho
─────────────────────────────────
rho' * Gamma |- t : A
```

("if you can build t using grade rho, you can build it using fewer resources rho' ≤ rho").

---

## 9. Summary: Established vs. Novel Connections

### Established (papers exist)

1. **QTT subsumes ILL's bang:** Bang = ω-grade modality. (Atkey 2018, McBride 2016)
2. **{0,1,ω} as truncated ℕ:** Well-known in the QTT community.
3. **Graded comonad = LNL adjunction generalized:** Fujii-Katsumata-Melliès (FoSSaCS 2016)
4. **Graded LNL:** `!_r ≅ G ∘ (r-action) ∘ F`. Vollmer-Marshall-Eades-Orchard (CSL 2025)
5. **Linear exponential as graded modal type:** Hughes-Marshall-Wood-Orchard (TLLA 2021)
6. **ILL forward chaining = Petri net rewriting:** Kanovich (APAL 1995)
7. **Graded types + adjoint logic combination:** Eades-Orchard (TLLA 2020) and Glad (TyDe 2023)
8. **0-grade erasure in Idris 2:** Brady (ECOOP 2021), formalized by Abel-Danielsson-Eriksson
9. **Grade-0 non-interference:** Choudhury-Eades-Eisenberg-Weirich (POPL 2021, Lemma 6.2) — grade-0 heap irrelevance
10. **Graded effects + coeffects combined:** Gaboardi-Katsumata-Orchard-Breuvart (ICFP 2016)
11. **SELL c-semiring connection:** Pimentel-Olarte-Nigam (TPLP 2014)
12. **BLL = ℕ-graded exponential:** Girard-Scedrov-Scott (TCS 1992) — earliest graded modal logic

### Novel / Unestablished (no direct paper)

1. **QTT semiring ↔ SELL subexponential signature:** No formal equivalence theorem. The c-semiring observation is narrow. General correspondence is open.
2. **QTT 0-grade = staging:** Conceptual but no formal equivalence. 2LTT (Kovács) is the closest.
3. **Graded forward engine = weighted Petri nets with semiring tokens:** The correspondence is clear from first principles but no paper explicitly identifies CALC-style graded forward chaining with semiring-weighted Petri nets.
4. **Compile-time cut elimination via 0-grade:** CALC's RES_0099 direction is novel.
5. **Resource-graded monad `{A}_r` for CALC:** Applying Gaboardi et al.'s framework to CALC's lax monad is straightforward but unpublished.
6. **Focusing discipline for graded linear logic:** Open. Andreoli's focusing works for ILL; how it extends to graded exponentials `!_r` is not published. (Mentioned as open in RES_0056 Section H.4.)

---

## 10. Bibliography

### QTT foundations

- McBride (2016): "I Got Plenty o' Nuttin'." LNCS 9600. [PDF](https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf)
- Atkey (2018): "Syntax and Semantics of QTT." LICS 2018. [PDF](https://bentnib.org/quantitative-type-theory.pdf)
- Brady (2021): "Idris 2: QTT in Practice." ECOOP 2021. arXiv:2104.00480

### Graded dependent types

- Moon, Eades, Orchard (2021): "Graded Modal Dependent Type Theory." ESOP 2021. arXiv:2010.13163
- Choudhury, Eades, Eisenberg, Weirich (2021): "A Graded Dependent Type System with Usage-Aware Semantics." POPL 2021. arXiv:2011.04070
- Abel, Danielsson, Eriksson (2026 preprint): "A Graded Modal Dependent Type Theory with Erasure, Formalized." arXiv:2603.29716
- Sefl, Svoboda (2022): "Additive Types in Quantitative Type Theory." WoLLIC 2022. DOI: 10.1007/978-3-031-15298-6_16

### Graded modal types (Granule ecosystem)

- Orchard, Liepelt, Eades (2019): "Quantitative Program Reasoning with Graded Modal Types." ICFP 2019. [PDF](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- Wood, Atkey (2021): "A Linear Algebra Approach to Linear Metatheory." TLLA/LINEARITY 2020. arXiv:2005.02247
- Eades, Orchard (2020): "Grading Adjoint Logic." LINEARITY/TLLA 2020. arXiv:2006.08854
- Orchard, Wadler, Eades (2020): "Unifying Graded and Parameterised Monads." TLLA 2020. arXiv:2001.10274
- Marshall, Orchard (2023): "Functional Ownership through Fractional Uniqueness." arXiv:2310.18166
- Marshall, Orchard (2023): "Graded Modal Types for Integrity and Confidentiality." arXiv:2309.04324
- Marshall, Orchard (2022): "Replicate, Reuse, Repeat: Non-Linear Communication via Session Types and Graded Modal Types." arXiv:2203.12875

### Mixed graded/linear logic

- Vollmer, Marshall, Eades, Orchard (2025): "A Mixed Linear and Graded Logic: Proofs, Terms, and Models." CSL 2025. arXiv:2401.17199
- Hughes, Marshall, Wood, Orchard (2021): "Linear Exponentials as Graded Modal Types." TLLA 2021.

### Effects, coeffects, and graded monads

- Gaboardi, Katsumata, Orchard, Breuvart (2016): "Combining Effects and Coeffects via Grading." ICFP 2016. (no arXiv; ACM DL)
- Fujii, Katsumata, Melliès (2016): "Towards a Formal Theory of Graded Monads." FoSSaCS 2016. DOI: 10.1007/978-3-662-49630-5_30
- Gaboardi, Katsumata, Orchard, Sato (2020): "Graded Hoare Logic and its Categorical Semantics." arXiv:2007.11235
- Katsumata, Rivas, Uustalu (2019): "Interaction Laws of Monads and Comonads." arXiv:1912.13477

### Staging and erasure

- Brady (2021): see QTT foundations
- Kovács (2023): "Staged Compilation with Two-Level Type Theory." POPL 2023. arXiv:2209.09729
- Atkey (2023): "Polynomial Time and Dependent Types." POPL 2023/2024. arXiv:2307.09145

### SELL and subexponentials

- Nigam, Miller (2009): "Algorithmic Specifications in Linear Logic with Subexponentials." PPDP 2009. DOI: 10.1145/1599410.1599427
- Pimentel, Olarte, Nigam (2014): "A Proof Theoretic Study of Soft CCP." TPLP 14:649-663. arXiv:1405.2329
- Kanovich, Kuznetsov, Nigam, Scedrov (2019): "Subexponentials in Non-Commutative Linear Logic." MSCS 29(8). arXiv:1709.03607
- Despeyroux, Olarte, Pimentel (2016): "Hybrid and Subexponential Linear Logics." arXiv:1608.08779
- Olarte, Pimentel (2024): "Multi-modalities and Non-commutativity in Functorial Linear Logic." arXiv:2404.11445

### Petri nets and linear logic

- Kanovich (1995): "Petri Nets, Horn Programs, Linear Logic, and Vector Games." APAL 75(1-2):107-135. DOI: 10.1016/0168-0072(94)00060-G
- Meseguer, Montanari (1988/1990): "Petri Nets are Monoids." LICS 1988 / Information and Computation 88.
- Olarte, de Paiva, Pimentel, Reis (2019): "The ILLTP Library for ILL." LINEARITY/TLLA 2018. arXiv:1904.06850

### Bounded Linear Logic (BLL — earliest graded exponentials)

- Girard, Scedrov, Scott (1992): "Bounded Linear Logic." TCS 97(1):1-66. DOI: 10.1016/0304-3975(92)90386-T

### Graded differential linear logic

- Breuvart, Kerjean, Mirwasser (2026): "Unifying Graded Linear Logic and Differential Operators." LMCS 22(1). arXiv:2402.09138

### Cross-references

- RES_0056: QTT sequent calculus and gap analysis for CALC
- RES_0074: QTT, Graded Types, Adjoint Logic, SELL, MTDC expressiveness hierarchy
- RES_0022: Graded resource tracking — QTT and graded modalities (earlier survey)
- RES_0054: Graded resource analysis implementation options
- RES_0097: Subexponentials and scoped persistence
- RES_0098: ILL/SELL/LNL relationship
- RES_0099: Compile-time cut elimination

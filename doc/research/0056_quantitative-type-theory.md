---
title: "Quantitative Type Theory: Sequent Calculus and Gap Analysis for CALC"
created: 2026-02-24
modified: 2026-02-24
summary: "Deep analysis of QTT — its sequent calculus presentation, relationship to ILL, and a concrete gap analysis for extending CALC from ILL to QTT compliance."
tags: [QTT, graded-types, semiring, dependent-types, linear-logic, sequent-calculus, gap-analysis, Idris-2]
category: "Multi-Type Framework"
---

# Quantitative Type Theory: Sequent Calculus and Gap Analysis for CALC

---

## A. What QTT Is

Quantitative Type Theory (McBride 2016, Atkey 2018) is a dependent type theory where every variable binding carries a **semiring annotation** indicating how many times the variable is used at runtime. The core judgment is:

```
Delta ; Gamma |- t : A
```

where `Delta` is an unrestricted typing context (for type formation, always at usage 0) and `Gamma` is a **graded context** mapping variables to `(type, usage)` pairs:

```
Gamma = x1 :_{r1} A1, x2 :_{r2} A2, ...
```

The grade `r_i` is drawn from a semiring `(R, +, *, 0, 1)` and records how many times `x_i` is used in `t`.

### Core Insight

Usage annotations are **not types** -- they are metadata on the context. A variable `x :_3 A` has type `A`; the `3` says "x is used 3 times in this term." This is fundamentally different from wrapping the type in a modality like `!_3 A` (the Granule approach).

### How It Unifies Substructural Disciplines

| Semiring element | Structural property | Traditional system |
|---|---|---|
| `0` | Erasure (used only in types, not computation) | Irrelevance |
| `1` | Exactly-once use | Linear types |
| `omega` | Unrestricted use | Standard types |
| `r >= 1` | At-least-once use | Relevant types |
| `r <= 1` | At-most-once use | Affine types |

With a single mechanism, QTT subsumes linear, affine, relevant, and unrestricted type disciplines.

### Context Operations

QTT requires three operations on graded contexts:

- **Zero context** `0 * Gamma`: all usages set to 0 (for type formation)
- **Scalar multiplication** `r * Gamma`: scale all usages by `r`
- **Pointwise addition** `Gamma_1 + Gamma_2`: add usages position-wise (for combining sub-derivations)

These operations correspond to semiring operations: `0 * Gamma` uses the semiring zero, `r * Gamma` uses semiring multiplication, and `+` uses semiring addition.

### Relationship to Curry-Howard

QTT extends the Curry-Howard correspondence: proofs carry **resource information**. A proof term `t` of type `A` in context `Gamma` is not just evidence that `A` holds -- it also certifies that the resources in `Gamma` are used according to their grades. This makes QTT proofs inherently resource-aware.

---

## B. QTT Typing Rules (Sequent-Style Presentation)

QTT is standardly presented in natural deduction. No published sequent calculus for full QTT exists. Below we present Atkey's rules in a sequent-adjacent style, then derive the closest sequent calculus analogue where possible.

### B.1 Natural Deduction Rules (Atkey 2018)

**Variable:**
```
                                  sigma in {0, 1}
──────────────────────────────────────────────────
 0*Gamma, x :_sigma A |- x : A
```
The variable `x` gets grade `sigma` (0 or 1); all other variables get grade 0. Atkey restricts `sigma` to `{0, 1}` to ensure substitution is admissible.

**Lambda (Pi-introduction):**
```
 Gamma, x :_rho A |- t : B
────────────────────────────
 Gamma |- lambda x.t : (x :_rho A) -> B
```
The grade `rho` on the binder records how `x` is used in `t`.

**Application (Pi-elimination):**
```
 Gamma_1 |- f : (x :_rho A) -> B       Gamma_2 |- a : A
─────────────────────────────────────────────────────────
 Gamma_1 + rho * Gamma_2 |- f a : B[a/x]
```
The argument context is **scaled** by `rho` (the function's declared usage of its argument), then added to the function's context. This is the rule where the semiring structure is essential.

**Tensor (Sigma-introduction):**
```
 Gamma_1 |- a : A       Gamma_2 |- b : B[a/x]
────────────────────────────────────────────────
 Gamma_1 + Gamma_2 |- (a, b) : (x :_rho A) * B
```
Both components contribute their usages additively. Note: this is a **dependent** pair -- `B` may mention `x`.

**Tensor elimination (let-pair):**
```
 Gamma_1 |- p : (x :_rho A) * B       Gamma_2, x :_rho A, y :_1 B |- t : C
──────────────────────────────────────────────────────────────────────────────
 Gamma_1 + Gamma_2 |- let (x,y) = p in t : C
```

**Unit introduction:**
```
──────────────────────
 0*Gamma |- () : Unit
```

**Unit elimination:**
```
 Gamma_1 |- u : Unit       Gamma_2 |- t : C
─────────────────────────────────────────────
 Gamma_1 + Gamma_2 |- let () = u in t : C
```

**Type formation (Pi):**
```
 0*Gamma |- A : Type_i       0*Gamma, x :_0 A |- B : Type_j
──────────────────────────────────────────────────────────────
 0*Gamma |- (x :_rho A) -> B : Type_max(i,j)
```
Type formation always uses the **zero context** -- types are formed at compile time and have no runtime cost.

**Type formation (Sigma):**
```
 0*Gamma |- A : Type_i       0*Gamma, x :_0 A |- B : Type_j
──────────────────────────────────────────────────────────────
 0*Gamma |- (x :_rho A) * B : Type_max(i,j)
```

### B.2 Derived Sequent Calculus Rules

Translating to a sequent calculus `Gamma |- C` (single-succedent, ILL-style), we can derive rules for the non-dependent fragment. Below, `r*A` means "A with grade r in context" and `+` is context merge.

**Identity:**
```
────────────────
 A :_1 |- A
```

**Cut:**
```
 Gamma_1 |- A       Gamma_2, x :_rho A |- C
──────────────────────────────────────────────
 Gamma_1 + rho * Gamma_2 |- C
```
Note the grade scaling on cut: the usage of the cut formula `A` is `rho`, so the context that produced `A` gets scaled by `rho`.

**Tensor-right (non-dependent):**
```
 Gamma_1 |- A       Gamma_2 |- B
──────────────────────────────────
 Gamma_1 + Gamma_2 |- A * B
```
Identical to ILL's tensor-right, but with graded context addition.

**Tensor-left:**
```
 Gamma, x :_rho A, y :_1 B |- C
──────────────────────────────────
 Gamma, z :_1 (x :_rho A) * B |- C
```

**Loli-right (non-dependent, rho = 1):**
```
 Gamma, x :_1 A |- B
─────────────────────
 Gamma |- A -o B
```
Standard ILL loli-right is the `rho = 1` case.

**Loli-left:**
```
 Gamma_1 |- A       Gamma_2, y :_1 B |- C
────────────────────────────────────────────
 Gamma_1 + Gamma_2, z :_1 (A -o B) |- C
```

**Bang-right (promotion):**
```
 r * Gamma |- A
─────────────────────
 r * Gamma |- !_r A
```
The entire context must be scaled by `r`. This generalizes ILL's promotion (which requires all linear context resources to have grade omega).

**Bang-left (dereliction):**
```
 Gamma, x :_r A |- C
──────────────────────────
 Gamma, y :_1 !_r A |- C
```
Opens the box: one use of `!_r A` yields `r` uses of `A`.

### B.3 Comparison with CALC's Current ILL Rules

| CALC ILL Rule | QTT Analogue | Key Difference |
|---|---|---|
| `tensor_r: D, D' |- A*B <- D |- A, D' |- B` | Same, but `D + D'` is graded addition | Grades make the split explicit |
| `tensor_l: D, A*B |- C <- D, A, B |- C` | Same structure | QTT adds grade on each component |
| `loli_r: D |- A -o B <- D, A |- B` | Same for `rho = 1` | QTT generalizes to `rho`-graded arrow |
| `loli_l: D, D', A -o B |- C <- D |- A, D', B |- C` | Same structure | Grade scaling on argument context |
| `promotion: ; |- !A <- ; |- A` | `r*Gamma |- A => r*Gamma |- !_r A` | Graded: scales by `r` not binary empty/full |
| `dereliction: D, !A |- C <- D, A |- C` | `D, !_r A |- C <- D, A :_r |- C` | Grade `r` flows to the opened variable |
| `copy: G, A; D |- C <- G, A; D, A |- C` | No direct analogue | QTT uses grades instead of structural copy |
| `with_r`, `with_l1`, `with_l2` | Same (additive) | Context shared, not split |
| `oplus_r1/r2`, `oplus_l` | Same (additive) | Context shared, not split |

The key structural difference: CALC's ILL uses a **binary split** (linear vs cartesian contexts) while QTT uses **graded annotations per variable**.

---

## C. What CALC Already Has (The Overlap)

CALC's current ILL implementation is precisely the `{0, 1, omega}` fragment of QTT, viewed through a different lens.

### C.1 The Persistent/Linear Split = Grades {omega, 1}

| CALC Concept | QTT Grade |
|---|---|
| `state.persistent[hash]` (never consumed) | Grade `omega` |
| `state.linear[hash]` with count `n` | Grade `1` (count `n` = `n` copies at grade 1) |
| Absent from state | Grade `0` |

The `provePersistentGoals` function in `match.js` implements the two-level resolution that distinguishes omega-graded (persistent) from 1-graded (linear) facts. This IS the `{0, 1, omega}` semiring.

### C.2 Context Flow in Rule Descriptors

CALC's rule descriptors already track how contexts flow through rules via `contextFlow` and `contextSplit` fields. The descriptor for `tensor_r` specifies `contextSplit: true`, meaning the linear context is partitioned between premises. This is exactly the QTT rule for tensor where `Gamma_1 + Gamma_2` splits the graded context.

### C.3 Content-Addressed Hashing

CALC's Store provides O(1) structural equality via content-addressing. QTT's **definitional equality** (beta/eta) requires checking whether two terms are "the same." CALC's hash equality is a fragment of this: it handles syntactic identity but not beta-reduction.

### C.4 The LNL Adjunction

CALC's `ill.calc` defines bang as arising from an LNL adjunction (`@extends lnl`). The `absorption` rule moves a banged formula from linear to cartesian context (= applying the G functor), and `promotion` requires an empty linear context (= applying the F functor). This is Benton's linear/non-linear model, which QTT generalizes from a binary adjunction to a graded family.

### C.5 Quantifiers

CALC already has `exists` and `forall` with de Bruijn indices, eigenvariables, and metavariable opening. These correspond to QTT's Sigma-introduction (existential witness) and Pi-introduction (universal abstraction), but without dependent types -- CALC's quantifiers range over terms, not types depending on terms.

---

## D. The Gap Analysis

### D.1 Dependent Types

**QTT has:** Dependent function types `(x :_rho A) -> B` where `B` may mention `x`. Dependent pair types `(x :_rho A) * B` where `B` may mention `x`.

**CALC has:** Simple (non-dependent) connectives. `A -o B` where `B` cannot mention variables bound by `A`. `A * B` where components are independent.

**The gap:** This is the largest structural gap. Dependent types require:
1. **Terms in types:** The Store would need to represent types that contain term-level variables. Currently, formulas (types) and terms (atoms, applications) are separate — a formula `tensor(h1, h2)` cannot have `h1` depend on a runtime value.
2. **Substitution into types:** When applying `f : (x :_1 A) -> B` to `a : A`, the result type is `B[a/x]`. CALC's `substitute.js` handles term substitution but not type-level substitution (because types don't contain term variables).
3. **Type checking during proof search:** Dependent types require checking that a term has the correct type during proof construction. CALC's prover searches for proofs by decomposing the goal; it doesn't check that intermediate terms have well-formed types.

**Code impact:** `lib/kernel/store.js` (new node types for Pi/Sigma), `lib/kernel/substitute.js` (type-level substitution), `lib/kernel/sequent.js` (sequents with dependent types), `lib/prover/rule-interpreter.js` (new rules for Pi/Sigma).

**Assessment:** HIGH effort. This is a fundamental extension, not an incremental change.

### D.2 Universe Hierarchy

**QTT has:** `Type_0 : Type_1 : Type_2 : ...` with universe polymorphism. Type formation rules compute universe levels via `max(i, j)`.

**CALC has:** A single `type` tag in the Store with no universe stratification. `formula: type.` in `ill.calc` declares that `formula` is a type, but there's no hierarchy.

**The gap:** Without universes, CALC cannot distinguish between "types of terms" and "types of types." This matters for QTT's type formation rules (which must ensure consistency) and for the 0-grade separation (type formation always at grade 0 requires knowing what's a type).

**Code impact:** `lib/kernel/store.js` (universe-indexed type tag), calculus definitions, prover rules.

**Assessment:** MEDIUM effort for a simple universe hierarchy; HIGH for full universe polymorphism.

### D.3 Semiring Annotations on Bindings

**QTT has:** Every variable binding carries an explicit grade `x :_r A`.

**CALC has:** Grades are implicit and binary: a fact is either in `state.linear` (grade 1) or `state.persistent` (grade omega). The grade is a property of the **storage location**, not the variable binding.

**The gap:** Making grades explicit requires:
1. **Graded contexts in sequents:** `sequent.js` currently has `{ linear: [...], cartesian: [...] }`. A graded sequent would be `{ graded: [{ hash, grade }, ...] }`.
2. **Grade arithmetic in rule application:** When applying tensor-right, the prover must solve `Gamma_1 + Gamma_2 = Gamma` — splitting a graded context into two parts whose grades sum correctly. This is a constraint satisfaction problem over the semiring.
3. **Grade tracking in the forward engine:** `applyMatch` in `forward.js` must update grades, not just decrement counts.

**Code impact:** `lib/kernel/sequent.js` (graded contexts), `lib/prover/context.js` (graded multiset operations), `lib/engine/forward.js` and `lib/engine/match.js` (grade-aware matching).

**Assessment:** MEDIUM effort. RES_0054 already outlines the implementation path (Options A/B/C).

### D.4 Zero-Graded Variables (Erasure)

**QTT has:** Variables at grade 0 exist only in types, not in computation. `id : (0 a : Type) -> a -> a` means `a` is erased at runtime. Idris 2 uses this for compile-time type indices.

**CALC has:** No notion of erasure. All formulas in a sequent are "present." The closest analogue is a persistent fact that is never consumed — but it still exists in state and can be matched.

**The gap:** Erasure requires:
1. **A type/term distinction:** Knowing which variables are "type-level only" vs "computational."
2. **Grade-0 checking:** The prover must verify that 0-graded variables are used only in type positions.
3. **Erasure in the engine:** 0-graded facts should not appear in the execution state at all.

**Code impact:** Pervasive. Requires the dependent type infrastructure from D.1.

**Assessment:** HIGH effort. Depends on D.1 and D.2.

### D.5 Substitution with Grade Scaling

**QTT has:** When substituting `a` for `x :_rho A` in a judgment `Gamma, x :_rho A |- t : B`, the resulting context is `Gamma + rho * Delta` where `Delta` is the context used to type `a`. Grades scale through substitution.

**CALC has:** `substitute.js` performs structural substitution (replace variable occurrences with terms). No grade information flows through substitution.

**The gap:** Grade-aware substitution requires:
1. Tracking which context was used to derive the substituted term.
2. Multiplying that context's grades by the grade of the substituted variable.
3. Adding the result to the remaining context.

This is the rule McBride originally got wrong and Atkey fixed. Getting it right is essential for QTT's soundness.

**Code impact:** `lib/kernel/substitute.js` (grade-aware apply), `lib/prover/` (grade propagation during proof search).

**Assessment:** MEDIUM effort, but mathematically subtle.

### D.6 Type Checking vs Proof Search

**QTT is:** A type theory designed for **checking mode** — given a term `t` and a type `A`, verify that `Gamma |- t : A`. Idris 2 uses bidirectional type checking (synthesis + checking).

**CALC is:** A proof search engine in **search mode** — given a goal `Gamma |- ?A`, find a proof term. The focused prover (L3) searches by decomposing the goal formula.

**The gap:** These are fundamentally different operational modes:
- **Checking** is decidable for QTT (assuming the semiring's operations are decidable).
- **Searching** is undecidable in general for dependent type theories.
- CALC's proof search works because ILL has well-behaved proof search properties (focusing, invertibility). Adding dependent types breaks some of these properties.

**Interaction:** QTT's grade checking could coexist with CALC's proof search if:
1. Grade checking is a **side condition** on each proof step (the prover finds a proof, then verifies grades).
2. Grade constraints guide search (prune branches that would violate grade bounds).
3. The forward engine uses grades for resource tracking (RES_0054 Option B) while the backward prover handles the logic.

**Assessment:** This is the deepest conceptual gap. Not just engineering — it requires theoretical work on how grade-aware focusing works.

### D.7 Conversion / Definitional Equality

**QTT has:** Beta-reduction (`(lambda x.t) a = t[a/x]`), eta-expansion, and potentially more equational reasoning. Type checking requires deciding whether two types are definitionally equal.

**CALC has:** Content-addressed equality (hash comparison). Two terms are equal iff they have the same hash, which means they are syntactically identical (up to hash collisions). No beta-reduction, no eta-expansion.

**The gap:** Content-addressed equality is **stronger** than needed (no false positives for syntactic terms) but **weaker** than required (misses beta/eta equalities). For QTT:
- `(lambda x. f x)` and `f` should be equal (eta), but have different hashes.
- `(lambda x.x) A` and `A` should be equal (beta), but have different hashes.

**Possible approach:** Normalize terms before hashing. Beta-normal eta-long forms would give correct equality via hash comparison. This requires a normalizer, which CALC doesn't have.

**Code impact:** New normalizer module, changes to Store.put (normalize before interning).

**Assessment:** MEDIUM-HIGH effort. Normalization is well-understood but requires careful implementation.

---

## E. Possible Implementation Paths

### Path 1: Extend ILL with Grade Annotations (Minimal QTT)

Keep CALC's current non-dependent type structure. Replace the binary persistent/linear split with explicit semiring grades on context formulas.

**What changes:**
- Sequents become `Gamma_graded |- A` where each formula has a grade
- Context splitting in tensor-right becomes grade addition
- Promotion becomes grade scaling
- The engine's `state.linear` and `state.persistent` merge into `state.resources` with per-fact grades

**What stays:** No dependent types, no universes, no erasure. Same connectives, same proof search.

**Benefit:** Enables RES_0054's graded resource tracking without the complexity of dependent types.

**Effort:** MEDIUM. Mostly engineering, little new theory.

### Path 2: Add Dependent Types to CALC (Full QTT)

Implement dependent function types (Pi) and dependent pair types (Sigma) in the kernel. Add universe hierarchy. Implement grade-aware substitution.

**What changes:** Everything in Section D.

**Benefit:** Full QTT compliance. CALC becomes a dependently-typed proof engine with quantitative resource tracking.

**Effort:** VERY HIGH. This is essentially building a new type theory implementation.

### Path 3: Embed QTT Judgments as Linear Logic Propositions

Encode QTT's typing judgment `Gamma |- t : A` as a linear logic formula and use CALC's existing proof search to verify QTT derivations.

**Encoding sketch:**
```ill
% QTT judgment as a linear logic proposition
hasType: term -> type -> formula.
graded: grade -> term -> type -> formula.

% Variable rule: x :_1 A in context
var_rule: graded(1, X, A) -o hasType(X, A).

% Application rule (simplified, non-dependent)
app_rule: hasType(F, arrow(rho, A, B)) * hasType(Arg, A)
          -o hasType(app(F, Arg), B).
```

**Benefit:** No kernel changes. QTT checking runs on the existing engine. Could be prototyped in an afternoon.

**Limitation:** Encoding is shallow — loses QTT's meta-theoretic properties (e.g., subject reduction must be proved about the encoding, not inherited from QTT). Grade arithmetic would need FFI support.

**Effort:** LOW for prototype, MEDIUM for production.

### Path 4: QTT as a Separate Layer Compiling to CALC's Engine

Build a QTT type checker as a standalone module that compiles verified QTT programs into CALC's forward engine format. QTT handles type checking and grade verification; CALC handles execution.

**Architecture:**
```
QTT source → QTT type checker → verified core terms → CALC engine rules → execution
```

**Benefit:** Clean separation of concerns. QTT's checking mode and CALC's search mode don't interfere. Each layer does what it's good at.

**Effort:** HIGH. Requires building a QTT type checker, but it's a well-understood problem (Idris 2 is an existence proof).

### Recommended Path

**Phase 1:** Path 1 (graded ILL) — aligns with RES_0054's recommended Option C then B.

**Phase 2:** Path 3 (encode QTT in CALC) — prototype to understand the interaction between grades and proof search.

**Phase 3:** Path 4 (QTT layer) if full dependent types are needed for verification goals.

Path 2 (full QTT in CALC) is likely not worth the effort unless CALC's mission shifts from "proof search engine for linear logic" to "dependently-typed programming language."

---

## F. The Idris 2 Connection

Idris 2 (Brady, ECOOP 2021) is the primary practical implementation of QTT. Key lessons for CALC:

### F.1 Semiring Choice: {0, 1, omega}

Idris 2 uses exactly the `{0, 1, omega}` semiring — the same grades CALC already implements. This is not a coincidence: this semiring captures the three practically important distinctions (erased, linear, unrestricted) without the complexity of arbitrary natural numbers.

**Semiring tables:**
```
+  | 0  1  w        *  | 0  1  w
---+--------        ---+--------
0  | 0  1  w        0  | 0  0  0
1  | 1  w  w        1  | 0  1  w
w  | w  w  w        w  | 0  w  w
```

CALC's current behavior matches: `1 + 1 = omega` (two linear uses = unrestricted), `omega * 1 = omega` (using a linear resource inside a persistent context = persistent).

### F.2 Erasure Mechanism

In Idris 2, a `0`-graded argument is guaranteed erased at runtime:
```idris
id : (0 a : Type) -> a -> a
id _ x = x    -- 'a' is erased, only 'x' exists at runtime
```

For CALC's forward engine, the analogue would be: facts at grade 0 exist only for proving persistent goals (backward chaining) and are never part of the linear execution state. This is close to how `state.persistent` works — persistent facts are consulted but never consumed. The difference is that 0-graded facts shouldn't even be matchable as persistent goals; they exist only for type formation.

### F.3 Bidirectional Checking

Idris 2 uses bidirectional type checking: terms synthesize types (elimination forms) or check against types (introduction forms). CALC's proof search is bottom-up (goal-directed), which is closer to checking mode. The connection: CALC's `succedent` in a sequent plays the role of the "checking type."

### F.4 Elaboration

Idris 2 elaborates surface syntax into a core QTT term, filling in implicit arguments and solving unification constraints. CALC's metavariable unification (`unify.js`) does similar work during proof search — finding witnesses for existential quantifiers and matching rule patterns. The difference: Idris 2's elaboration produces a fully annotated term; CALC's proof search produces a proof tree.

---

## G. Relationship to Other Approaches

### G.1 Adjoint Logic (Reed & Pfenning)

**Approach:** Instead of grades on variables, use a preorder of **modes** (e.g., linear, affine, cartesian) with adjoint functors between them. The bang modality `!A` decomposes into `F(G(A))` where `F` is left adjoint to `G`.

**CALC connection:** CALC already uses the LNL adjunction (`ill.calc` extends `lnl.family`). The `absorption` and `promotion` rules implement the adjoint functors.

**Trade-off:** Adjoint logic provides cleaner categorical semantics but is less flexible than QTT's semiring approach. QTT allows arbitrary grades; adjoint logic allows only the modes in the preorder. However, Licata and Shulman (2016) showed that the adjoint approach can be generalized to a 2-category of modes, recovering much of QTT's expressivity.

**For CALC:** The adjoint approach might be more natural for CALC's existing architecture (extend the LNL adjunction to multiple modes) than the QTT approach (replace binary split with graded contexts).

### G.2 Granule (Graded Comonads)

**Approach:** Place grades on types, not bindings: `[]_r A` is a type meaning "an `A` that must be used `r` times." Uses graded comonads as the semantic foundation.

**Key difference from QTT:** In QTT, `x :_3 Int |- x + x + x : Int` puts the grade on the binder. In Granule, `|- lambda x. x + x + x : []_3 Int -> Int` puts the grade on the type.

**For CALC:** Granule's approach maps to extending CALC's formula language with a graded modality connective (RES_0054 Option A). This is architecturally simpler than QTT's approach (no need to change context representation), but less expressive (no dependent types with grades).

### G.3 Linear Haskell

**Approach:** Multiplicity annotations on function arrows: `a %1 -> b` (linear), `a %Many -> b` (unrestricted), `a %m -> b` (polymorphic).

**Trade-off:** More practical than QTT (retrofitted into an existing language) but less principled (only function arrows carry multiplicities, not all binders). No dependent types.

**For CALC:** Linear Haskell's approach is too shallow — it annotates only arrows, while CALC needs grades on all context formulas (for resource tracking in the forward engine).

### G.4 Comparison Table

| System | Grades on | Dependent types | Proof search | Semiring |
|---|---|---|---|---|
| QTT (Atkey) | Binders | Yes (Pi, Sigma) | No | Arbitrary |
| Idris 2 | Binders | Yes | No | {0, 1, omega} |
| Granule | Types (modality) | Limited | No | Multiple |
| Adjoint logic | Modes (structural) | Via modes | Via focusing | Preorder |
| Linear Haskell | Arrows only | No | No | {1, Many} |
| CALC (current) | Context zones | No | Yes (focused) | {1, omega} implicit |
| CALC (Path 1) | Context formulas | No | Yes (focused) | Arbitrary |

---

## H. Open Questions for CALC

### H.1 Can QTT's Type Checking Coexist with Proof Search?

QTT checking is decidable (for decidable semirings). CALC's proof search is semi-decidable (complete for the propositional fragment, incomplete for quantifiers). Two coexistence models:

1. **Check-then-search:** Type-check the program (verify grades), then use proof search for logical goals. Grades constrain the search space.
2. **Search-with-grades:** Integrate grade checking into the focusing discipline. Grade violations prune branches during search, improving performance.

Model 2 is more interesting but requires understanding how grades interact with polarity and invertibility.

### H.2 How Do Grades Interact with Forward Chaining?

In CALC's forward engine, rules fire when their antecedents match the state. With grades:
- A rule requiring `A :_3` can fire only if `A` has at least grade 3 in state.
- Firing the rule **decreases** `A`'s grade by 3 (for linear resources) or leaves it unchanged (for persistent).
- Multiple rules competing for the same graded resource create a constraint: their total demand must not exceed the supply.

This is essentially Petri net semantics with weighted arcs — the grade is the arc weight. CALC's forward engine already implements this for the special case of weight 1 (linear) and weight infinity (persistent).

### H.3 Can Execution Trees Carry QTT Typing Information?

THY_0001's execution tree judgment `Sigma; Delta |-_fwd T : A` could be extended with grades:

```
Sigma; Delta_graded |-_fwd T : A
```

Each node in the tree records the grade changes: `step(r, theta, T')` would annotate the resource consumption. Leaves would have residual grades. This connects to RES_0054's Option C (post-hoc grade analysis of execution trees).

### H.4 What Happens to Focusing Under QTT?

Andreoli's focusing discipline partitions connectives by polarity (positive = focusable, negative = invertible). In graded linear logic:
- `!_0 A` is always invertible (erased, no computational content)
- `!_1 A` follows standard linear focusing
- `!_omega A` follows standard bang focusing
- Intermediate grades (`!_3 A`) — unclear. Is dereliction (opening the box) invertible? It depends on whether the grade allows it.

This is an open research question noted in RES_0054 Section 9. A focusing discipline for graded linear logic would be a theoretical contribution.

### H.5 Grade Inference for Forward Rules

Given a set of forward rules, can we infer optimal grade bounds for persistent facts? This reduces to:
- **Covering analysis:** How many times can each persistent fact be needed across all execution paths?
- **AARA connection:** Amortized resource analysis (Hofmann & Jost) infers resource bounds via linear programming. Could similar techniques infer grade bounds for CALC's persistent facts?
- **Practical approach:** Run RES_0054 Option C (post-hoc analysis), observe actual usage counts, use those as grade annotations for Option B.

---

## I. Bibliography

### QTT Foundations
- McBride, C. (2016). "I Got Plenty o' Nuttin'." A List of Successes That Can Change the World, LNCS 9600, pp. 294-316. [PDF](https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf)
- Atkey, R. (2018). "Syntax and Semantics of Quantitative Type Theory." LICS 2018, pp. 56-65. [PDF](https://bentnib.org/quantitative-type-theory.pdf)
- Choudhury, P., Eades III, H.B., Eisenberg, R.A., Weirich, S. (2021). "A Graded Dependent Type System with a Usage-Aware Semantics." POPL 2021.
- Abel, A., Danielsson, N.A., Eriksson, A. (2023). "A Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized." ICFP 2023.

### Idris 2
- Brady, E. (2021). "Idris 2: Quantitative Type Theory in Practice." ECOOP 2021, LIPIcs 194, pp. 9:1-9:26. [PDF](https://arxiv.org/pdf/2104.00480)
- Idris 2 Multiplicities Documentation. [Link](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html)

### Granule and Graded Modal Types
- Orchard, D., Liepelt, V.-B., Eades III, H.B. (2019). "Quantitative Program Reasoning with Graded Modal Types." ICFP 2019. [PDF](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- Moon, B., Eades III, H.B., Orchard, D. (2021). "Graded Modal Dependent Type Theory." ESOP 2021, LNCS 12648.
- Liepelt, V., Marshall, D., Orchard, D., Rajani, V., Vollmer, M. (2025). "A Mixed Linear and Graded Logic: Proofs, Terms, and Models." CSL 2025.

### Adjoint Logic
- Reed, J. (2009). "A Judgmental Deconstruction of Modal Logic." Unpublished manuscript.
- Licata, D.R., Shulman, M. (2016). "Adjoint Logic with a 2-Category of Modes." LICS 2016.
- Pruiksma, K., Pfenning, F. (2018). "Adjoint Logic." [PDF](https://ncatlab.org/nlab/files/PCPR18-AdjointLogic.pdf)

### LNL Models
- Benton, P.N. (1995). "A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models." CSL 1994, LNCS 933.

### Unified Frameworks
- Abel, A., Bernardy, J.-P. (2020). "A Unified View of Modalities in Type Systems." ICFP 2020. [PDF](https://www.cse.chalmers.se/~abela/icfp20.pdf)
- Wood, J., Atkey, R. (2022). "A Framework for Substructural Type Systems." ESOP 2022. [PDF](https://strathprints.strath.ac.uk/79767/1/Wood_Atkey_ESOP_2022_A_framework_for_substructural_type_systems.pdf)

### Linear Dependent Types
- Krishnaswami, N., Pradic, P., Benton, N. (2015). "Integrating Linear and Dependent Types." POPL 2015. [PDF](https://www.cl.cam.ac.uk/~nk480/dlnl-paper.pdf)
- Dal Lago, U., Gaboardi, M. (2012). "Linear Dependent Types and Relative Completeness." LMCS 12(3:7).
- Sefl, V., Svoboda, T. (2023). "Additive Types in Quantitative Type Theory." [PDF](https://ksvi.mff.cuni.cz/~sefl/papers/pairs_in_qtt.pdf)
- Svoboda, T. (2021). "Additive Pairs in Quantitative Type Theory." Master thesis, Charles University. [PDF](https://dspace.cuni.cz/bitstream/handle/20.500.11956/127263/120390854.pdf)

### Linear Haskell
- Bernardy, J.-P., Boespflug, M., Newton, R.R., Peyton Jones, S., Spiwack, A. (2018). "Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language." POPL 2018.

### Graded Linear Logic
- Girard, J.-Y., Scedrov, A., Scott, P.J. (1992). "Bounded Linear Logic." TCS 97(1), pp. 1-66.
- Brunel, A., Gaboardi, M., Mazza, D., Zdancewic, S. (2014). "A Core Quantitative Coeffect Calculus." ESOP 2014.
- Breuvart, F., et al. (2024). "Unifying Graded Linear Logic and Differential Operators." [arXiv:2402.09138](https://arxiv.org/abs/2402.09138)

### Cross-References
- RES_0022 -- Graded Resource Tracking: QTT and Graded Modalities
- RES_0026 -- Linear Logic Connectives: Par, Why Not, and Polarity
- RES_0054 -- Graded Resource Analysis for Linear Logic
- TODO_0015 -- Pacioli Grading Semiring
- THY_0001 -- Exhaustive Forward Chaining in MALL with the Lax Monad

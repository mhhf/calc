---
title: "Symbolic Values in Forward-Chaining Linear Logic: Three Isolated Problems"
created: 2026-02-20
modified: 2026-02-21
summary: "Three independent problems in handling symbolic values during forward chaining: ∃-elimination, witness representation, and term simplification. Each analyzed with theoretical foundations and examples."
tags: [theory, forward-chaining, symbolic-execution, existential, Skolem, eigenvariable, CLP, linear-logic]
---

# Symbolic Values in Forward-Chaining Linear Logic

## 0. The Obstruction

A forward rule with a persistent antecedent:

```
evm/add: pc(PC) * code(PC, 0x01) * stack(1, A) * stack(0, B)
         * !inc(PC, PC') * !plus(A, B, C)
         -o { pc(PC') * stack(0, C) }
```

When A is symbolic (e.g., calldata — not a ground numeral), proving `plus(A, B, C)` fails at all three levels:
1. FFI: `binToInt(A)` → null (not a numeral)
2. State lookup: no `plus` facts in persistent context
3. Backward clauses: `plus(e,Y,Y)`, `plus(i(X),...)` don't unify with symbolic A

Execution stalls. The rule can't fire. No PC advances.

This obstruction decomposes into **three independent problems**.

---

## Problem 1: ∃-Elimination in Forward Chaining

### 1.1 The Question

The persistent antecedent `!plus(A, B, C)` is a proof obligation with an implicit existential:

```
∃C. plus(A, B, C)
```

When the obligation can't be discharged (because A is symbolic), **how does the system produce a C so execution can continue?**

This is purely about the proof-theoretic mechanism. It says nothing about what C looks like or how to simplify it later.

### 1.2 Three Mechanisms

**Skolem witness:** Add axiom `∀X,Y. plus(X, Y, f(X,Y))` to the persistent theory. The catch-all clause always provides a C. Zero engine changes — uses existing fallback chain.

**Eigenvariable (CLF ∃R):** Introduce a fresh parameter α. Record `!plus(A, B, α)` as a persistent constraint. Standard ∃-introduction in the CLF monad.

**Loli-freeze:** Don't produce C. Suspend the entire computation: `!plus(A,B,C) ⊸ {body(C)}`. Resume when provable. Standard loli-left.

### 1.3 Information Flow

| Mechanism | After ADD | Can next opcode fire? |
|---|---|---|
| Skolem | `stack(0, f(A,1))` — a value | Yes |
| Eigenvariable | `stack(0, α₀)` + `!plus(A,1,α₀)` — placeholder + constraint | Yes |
| Loli-freeze | `!plus(A,1,C) ⊸ {pc(45) * stack(0,C)}` — suspended | **No** (no pc fact) |

**Skolem and eigenvariable produce a value. Loli-freeze blocks sequential computation.** Loli-freeze alone is insufficient for sequential programs (EVM bytecode). It works for boolean guards (where ⊕ branching explores both paths) and parallel dataflow.

### 1.4 Theoretical Foundations

**CLF (Watkins, Cervesato, Pfenning, Walker 2004):** ∃ inside the monad `{A}` creates fresh parameters during forward chaining. The parameter is scoped to the monadic computation. Celf implements this. Well-understood machinery.

**Simmons (2012), "Substructural Logical Specifications":** Formalizes forward chaining with existentials. Fresh parameters in rule conclusions = "runtime Skolemization." The execution trace forms a nominal abstraction — two traces differing only in fresh names are α-equivalent.

**Bruni, Ritter, Schurmann (IJCAR 2024):** First Skolemization procedure for focused intuitionistic linear logic. **Naive Skolemization is unsound in ILL** — specific counterexamples with tensor and bang. Fix: explicit dependency tracking through substitutions. For CALC's flat state (no nested quantifier scoping), the unsoundness doesn't arise — all eigenvariables live at the same scope level.

**QCHR (Barichard & Stéphan, TOCL 2025):** The ω_l^{∃∀} framework unifies all three mechanisms:
- Skolem = ground the ∃ immediately by providing a witness
- Eigenvariable = introduce ∃ dynamically, resolve later
- Loli-freeze = delay ∃-elimination until guard succeeds

**CLP (Jaffar & Maher 1994):** Loli-freeze is Prolog's `freeze(Var, Goal)`. Attributed variables carry attached constraints checked on unification.

### 1.5 Assessment

| Dimension | Skolem | Eigenvariable | Loli-freeze |
|---|---|---|---|
| Theory | Conservative extension | Standard CLF ∃R | Standard loli-left |
| Engine changes | 0 | ~10 LOC | ~20 LOC |
| Sequential flow | Works | Works | **Blocks** |
| Theoretical purity | Extends term language | Preserves terms | Preserves terms |
| Foundation | Equational completion | CLF monad | CLP |

Eigenvariable has the cleanest proof theory (standard CLF). Skolem has the simplest implementation (zero engine changes). Loli-freeze is standard but insufficient alone.

### 1.6 Independence

This problem is independent of Problems 2 and 3. You can decide the mechanism without knowing what the witness term looks like or how normalization works. The mechanism choice affects the downstream problems, but can be studied on its own.

### 1.7 Worked Example: Symbolic ADD

```
State: { pc(44), code(44,0x01), stack(1, ?D), stack(0, binlit(1)), ... }
       ?D = calldata value (arbitrary 256-bit)

Obligation: plus(?D, binlit(1), C)
```

**Skolem:**
```
Catch-all fires: C = f(?D, binlit(1))    (some Skolem term — shape is Problem 2)
State': { pc(45), stack(0, C), ... }
```

**Eigenvariable:**
```
∃R: C = α₀ (fresh), record !plus(?D, binlit(1), α₀)
State': { pc(45), stack(0, α₀), !plus(?D, binlit(1), α₀), ... }
```

**Loli-freeze:**
```
Suspend: !plus(?D, binlit(1), C) ⊸ { pc(45) * stack(0, C) * ... }
State': { !plus(?D,binlit(1),C) ⊸ {...}, code(44,0x01), ... }
         — no pc fact, STALLED
```

---

## Problem 2: Witness Representation

### 2.1 The Question

Given that Problem 1 decided on a mechanism, **what does the symbolic value look like in the content-addressed Store?**

This is about data design: constructor choice, hashing properties, compositionality, confluence. Independent of the ∃-elimination mechanism (Problem 1) and simplification (Problem 3).

### 2.2 Skolem Path: Expression Constructors

The Skolem witness for `plus(A, B, C)` needs a function symbol f such that `C = f(A, B)`. Natural choice: a new constructor `plus_expr`:

```
plus_expr(A, B)    — "the sum of A and B, not yet computed"
```

In the content-addressed Store, this is a node with tag `plus_expr` and two children (hashes of A and B). It gets a deterministic hash. It IS a value, exactly like `binlit(8)` or `cons(a, nil)`.

**Properties:**
- **Self-describing:** carries operation + arguments. You can inspect `plus_expr(X, 0)` and see it's an identity.
- **Content-addressed:** identical inputs → identical hash. `plus_expr(?D, 1)` computed at step 5 and step 100 produce the same hash.
- **Pattern-matchable:** normalizers can inspect structure.
- **Composable:** `mul_expr(plus_expr(?D, 1), 2)` nests naturally.
- **Growth:** O(depth) per chain of symbolic operations. `plus_expr(plus_expr(plus_expr(?D, 3), 5), 7)` after three ADDs.

**Conservative extension:** Adding `∀X,Y. plus(X, Y, plus_expr(X, Y))` to Γ doesn't change any ground theorem — for ground numeral inputs, FFI fires first (fallback ordering). Catch-alls only provide results for previously-undefined (symbolic) inputs.

**Confluence requirement:** For ground inputs, both paths must produce the same Store hash:
- FFI path: `plus(3, 5, ?)` → `binlit(8)`
- Catch-all path: `plus(3, 5, ?)` → `plus_expr(binlit(3), binlit(5))`

These differ unless `plus_expr(binlit(3), binlit(5))` redirects to `binlit(8)` at Store.put time (**ground folding**). Without ground folding, confluence breaks. Ground folding is a minimal normalization: when `Store.put('plus_expr', [h1, h2])` is called and both children have tag `binlit`, compute the result and store `binlit(result)` instead.

**The Knuth-Bendix perspective:** Catch-all + ground folding = a convergent TRS:
```
plus_expr(n, m) → n+m    when n, m ground numerals
```
No critical pairs, trivially terminating. This is equational completion (Knuth-Bendix 1970) applied to the backward clause theory.

### 2.3 Eigenvariable Path: Opaque Parameters

The eigenvariable witness is an opaque node `evar(N)`:

```
evar(0), evar(1), evar(2), ...    — monotonic counter
```

**Properties:**
- **Opaque:** looking at `evar(42)` tells you nothing about its provenance.
- **Unique:** each evar has a distinct N, hence distinct hash.
- **Flat constraints:** the relationship is in `!plus(?D, 1, evar(0))`, not in the term structure.
- **No deduplication:** `plus(?D, 1)` at step 5 and step 100 produce different evars (even for identical computation).
- **SMT-ready:** flat constraints export directly to `(assert (= (+ d 1) e0))`.

**The naming problem:** Equivalent computations get different evars (unsound if shared). The counter guarantees uniqueness but loses content-addressing benefits.

**Late resolution:** When `?D` becomes ground (e.g., via branching), constraint `!plus(5, 1, evar(0))` can be re-checked → FFI gives 6 → propagate `evar(0) ↦ 6` everywhere. Requires evar→facts index + substitution machinery.

**CLF connection:** In Celf, ∃R generates fresh logic variables during synchronous monadic decomposition. Unresolved variables remain as free parameters of the quiescent state. This is exactly the eigenvariable approach — each evar IS a CLF fresh parameter.

### 2.4 Comparison

| Dimension | Skolem (`plus_expr`) | Eigenvariable (`evar`) |
|---|---|---|
| Information in term | Operation + arguments | Just an ID |
| Content-addressing | Identical inputs → same hash | Each evar unique |
| Composability | Nested trees | Flat constraint graph |
| Simplification | Pattern match on structure | Constraint propagation |
| Late resolution | Normalizer re-walk | Re-check constraint, propagate |
| SMT export | Flatten expression tree | Direct (already flat) |
| Engine changes | 0 (catch-all clauses) | ~90 LOC (fresh gen + propagation) |

**Chained arithmetic example:**

After ADD (`?D + 1`) then MUL (`result * 2`):

```
Skolem:         mul_expr(plus_expr(?D, 1), 2)
                — nested tree, self-describing

Eigenvariable:  α₁ with {!plus(?D, 1, α₀), !mul(α₀, 2, α₁)}
                — flat graph, constraints separate
```

Both represent the same computation. The Skolem tree is self-contained. The eigenvariable graph separates data from provenance.

### 2.5 Initial Algebra Perspective (Skolem)

In universal algebra, `plus_expr(A, B)` is a **free element** in the term algebra extension. The only equalities are those forced by axioms (ground folding: `plus_expr(n,m) = n+m` for numerals). Unnormalized terms with symbolic children remain **free** — genuinely new elements. This is the **initial algebra** (minimal conservative extension with no accidental identifications).

Analogues: hevm's `Add(Var x, Lit 3)`, K's stuck `+Int` applications, Rosette's hash-consed terms.

### 2.6 Independence

This problem is independent of Problem 3. You can design the term language without deciding on simplification. Ground folding for confluence is the ONLY normalization required at this level. Everything else (identity, AC, cancellation) is Problem 3.

---

## Problem 3: Symbolic Term Simplification

### 3.1 The Question

Given symbolic expression terms (from Problem 2, Skolem path), **how do we prevent unbounded growth?**

This is a **pure term rewriting problem**. No linear logic. No forward chaining. Just: given a set of rewrite rules over expression constructors, is the system confluent and terminating? How much does it reduce expression size?

For the eigenvariable path, the parallel question is **constraint propagation** — a CLP problem, also independent of linear logic.

### 3.2 The Growth Problem

Without simplification, expressions grow O(steps):
```
Step 1: plus_expr(?D, 3)
Step 2: plus_expr(plus_expr(?D, 3), 5)
Step 3: mul_expr(plus_expr(plus_expr(?D, 3), 5), 2)
Step 4: plus_expr(mul_expr(plus_expr(plus_expr(?D, 3), 5), 2), 7)
```

For 1000+ steps (k-dss scale), depth-100+ terms. Content-addressing shares subterms across states, but individual terms grow.

### 3.3 Rewrite Rules (Incremental, Each Independent)

**Level 0: Ground folding (required for confluence — already in Problem 2)**
```
plus_expr(n, m) → n+m       when n, m ground numerals
mul_expr(n, m)  → n*m       when n, m ground numerals
```
Eliminates all fully-concrete subexpressions. ~50 LOC. **This is not optional** — it's needed for confluence. But it's also the simplest and highest-value simplification.

**Level 1: Identity / annihilation**
```
plus_expr(X, 0) → X         additive identity
mul_expr(X, 1) → X          multiplicative identity
mul_expr(X, 0) → 0          annihilation
```
Reduces ~15% of expressions for typical EVM. ~30 LOC. No critical pairs with Level 0 (ground folding handles the overlap case where X is also a numeral).

**Level 2: AC-normalization**
```
plus_expr(X, plus_expr(Y, Z)) → ac_plus([X, Y, Z])    flatten
ac_plus([..., n, ..., m, ...]) → ac_plus([..., n+m, ...])   constant fold
ac_plus(sorted) = ac_plus(sorted)                        canonical form
```
Flatten associative-commutative operators into sorted multisets with constant folding. `plus(plus(X, 3), 5)` → `ac_plus([X, 8])`. **Highest single-technique impact** for arithmetic — reduces depth by ~30%. ~300 LOC. This is the Maude philosophy: compute modulo equational theory E.

**Level 3: Cancellation**
```
minus_expr(X, X) → 0
plus_expr(X, minus_expr(0, X)) → 0
```
Critical for gas computation (17-deep cancellations in k-dss). Needs care: interact with AC-normalization. Analyze critical pairs.

**Dangerous rules (NEVER add):**
- Distribution: `mul(X, plus(Y,Z)) → plus(mul(X,Y), mul(X,Z))` — breaks termination
- Deep cancellation: `plus(minus(X,Y), Y) → X` — needs flatten-then-cancel, not structural rewrite

### 3.4 Confluence Analysis

Each level can be verified independently:

| Level | Critical pairs | Termination | Confluent? |
|---|---|---|---|
| 0 (ground folding) | None (only fires on numerals) | Weight: binlit=0, expr=1 | Yes (trivial) |
| 0+1 (+ identity) | None (disjoint conditions) | Reduces term size | Yes |
| 0+1+2 (+ AC) | Need analysis | AC-RPO with status | Likely yes |
| 0+1+2+3 (+ cancel) | Need analysis | Needs care | Verify with AProVE |

Tools: CSI, AProVE, CiME can verify confluence automatically given `.trs` rule files.

### 3.5 When to Normalize

**At Store.put time (Maude philosophy):** Bottom-up construction normalizes inner expressions before outer ones. Content-addressing then deduplicates. Zero per-step cost. Store becomes theory-aware.

**Post-step pass:** Normalize all new facts after each forward step. Store stays generic. O(new_facts) per step.

**Argument for Store.put:** `plus(a, plus(b, c))` — inner `plus(b,c)` is constructed first, normalized, THEN outer `plus(a, result)` is constructed and normalized. The bottom-up discipline gives AC-normalization for free. This is why Maude does it.

### 3.6 For the Eigenvariable Path: Constraint Propagation

The parallel problem: given constraints `{!plus(?D, 1, α₀), !mul(α₀, 2, α₁)}`, how to:
- Resolve when variables become ground (cascade through constraint graph)
- Detect contradictions (prune infeasible branches)
- Simplify (transitive resolution, domain narrowing)

This is CLP / CHR territory:
- **Attributed variables (Holzbaur 1992):** Variables carry constraints, checked on unification
- **CHR propagation:** `!plus(X, 0, Y) ==> X = Y` (identity as propagation rule)
- **Interval reasoning:** `!plus(X, Y, Z), domain(X, [0,100]) ==> domain(Z, [Y, Y+100])`

Different theory from term rewriting, but same structural role: keeping accumulated information manageable.

### 3.7 Independence

This problem is **completely independent of linear logic**. It's a standalone question in term rewriting (Knuth-Bendix completion) or constraint solving (CLP). You can study AC-normalization of `plus_expr` terms without knowing anything about forward chaining, ∃-elimination, or proof theory.

---

## 4. Dependency Order and Composition

```
Problem 1: ∃-Elimination
    │ "which mechanism?"
    ├──→ Skolem path ──→ Problem 2a: Expression Constructors
    │                        │ "what terms?"
    │                        └──→ Problem 3a: Term Simplification
    │                                (optional — works without)
    │
    └──→ Eigenvariable path ──→ Problem 2b: Constraint Store Design
                                    │ "what constraints?"
                                    └──→ Problem 3b: Constraint Propagation
                                            (optional — works without)
```

**Each level can be studied, prototyped, and tested before proceeding.** Problem 3 is optional — Skolem terms work without normalization (they just grow), eigenvariables work without propagation (they just accumulate). But both paths eventually need their respective Problem 3 for scalability.

**Priority order for CALC:**
1. Problem 1 (decide mechanism) — gates everything
2. Problem 2 (design representation) — enables symbolic execution
3. Problem 3 (add simplification) — enables scale

**Composability:** All three ∃-elimination mechanisms compose:
- **Skolem + loli-freeze:** Skolem for arithmetic (values flow), loli for boolean guards (⊕ branching). This is CALC's natural first step.
- **Eigenvariable + loli-freeze:** Evars for arithmetic, loli for triggers on resolution.
- **Skolem + eigenvariable (hybrid R4):** Skolem terms flow in state, flat constraints emitted alongside for reasoning.

---

## 5. Cross-Cutting Concerns

### 5.1 Mode-Agnosticism of ∃

The `plus` predicate appears in multiple modes across EVM rules: `+ + -` (ADD: C = A+B), `- + +` (SUB: C = A-B), `+ + -` (gas deduction). The ∃ mechanism is mode-agnostic — it emits the constraint regardless of which arguments are ground. Resolution depends on the solver (FFI modes, backward clauses). Multi-mode resolution and constraint rewriting (e.g., deducing B from known A, C) are P3 concerns, orthogonal to the ∃-elimination mechanism.

### 5.2 Relationship to the CLF Monad

CALC's `{...}` in rule consequents implements the CLF monad `{A}` implicitly. `expandItem` performs monadic decomposition: ⊗ → split, ⊕ → fork, ⊸ → suspend, ! → persistent. The gap: ∃ is not handled. Adding ∃ completes the monadic decomposition. The implementation is incomplete, not incorrect.

### 5.3 ⊕ Semantics Beyond Exclusive Binary Guards

EVM rules use ⊕ in the `P ⊕ ¬P` pattern (eq/neq, exclusive and exhaustive). General ⊕ is broader:

- **Unguarded:** `coin -o { heads ⊕ tails }` — pure non-determinism, both explored
- **Non-exclusive:** overlapping guards where both branches may survive
- **N-ary:** `(A ⊕ (B ⊕ C))` — recursive decomposition gives three branches
- **Non-exhaustive:** both guards may fail, both branches die

Eigenvariables compose with all patterns: ∃ handles fresh values, ⊕ handles branching, loli guards filter feasibility. The mechanisms are orthogonal.

### 5.4 Branch Pruning

⊕ always creates a fork node + 2 children. For ground guards, infeasible children die immediately (FFI definitively rejects the guard). For symbolic guards, both survive with path-condition constraints. Later resolution prunes when values become ground. This is standard path-condition accumulation — no backtracking needed.

### 5.5 Eager Resolution

When a constraint appears in the consequent, try immediate resolution via the same three-level fallback (FFI → state lookup → backward clauses). For ground inputs, this has zero overhead vs current behavior (same FFI call, same result). Only symbolic inputs generate eigenvariables.

---

## References

**Problem 1 (∃-elimination):**
- Watkins, Cervesato, Pfenning, Walker (2004). A Concurrent Logical Framework. LNCS 3085
- Schack-Nielsen, Schurmann (2008). Celf. IJCAR
- Simmons (2012). Substructural Logical Specifications. PhD thesis, CMU-CS-12-142
- Bruni, Ritter, Schurmann (2024). Skolemisation for Intuitionistic Linear Logic. IJCAR
- Barichard, Stephan (2025). Quantified CHR. ACM TOCL 26(3)
- Jaffar, Maher (1994). Constraint Logic Programming: A Survey. JLP

**Problem 2 (witness representation):**
- Knuth, Bendix (1970). Simple Word Problems in Universal Algebras
- Cervesato, Scedrov (2009). Relating State-Based and Process-Based Concurrency. I&C 207(10)
- Girard (1987). Linear Logic. TCS 50(1)

**Problem 3 (simplification):**
- Eker (2003). Associative-Commutative Rewriting on Large Terms (Maude)
- Meseguer (1992). Conditional Rewriting Logic. TCS 96(1)
- Holzbaur (1992). Metastructures vs. Attributed Variables. PLILP
- Willsey et al. (2021). egg: Fast and Extensible Equality Saturation. POPL
- Rocha, Meseguer (2013). Rewriting Modulo SMT. NASA/TM-2013-218033
- Whitters, Nigam, Talcott (2023). Incremental Rewriting Modulo SMT. CADE

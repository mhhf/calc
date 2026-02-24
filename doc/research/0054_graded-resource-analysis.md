---
title: "Graded Resource Analysis for Linear Logic"
created: 2026-02-24
modified: 2026-02-24
summary: "Survey of graded linear logic, semiring-indexed modalities, and three implementation strategies for quantitative resource tracking in CALC's forward execution engine."
tags: [graded-types, semiring, BLL, QTT, Granule, coeffects, AARA, resource-tracking, forward-chaining]
category: "Multi-Type Framework"
---

# Graded Resource Analysis for Linear Logic

Graded linear logic replaces the binary bang modality `!A` with a family of modalities `!_r A` indexed by elements of a semiring, enabling fine-grained quantitative tracking of resource usage. This document surveys the theoretical landscape and evaluates three implementation paths for CALC.

---

## 1. What Is Graded Linear Logic?

Standard linear logic has a single exponential `!A` meaning "unlimited copies of A." This is a coarse distinction: a resource is either used exactly once (linear) or arbitrarily many times (persistent). Graded linear logic refines this with a **family of modalities** `!_r A` where `r` is drawn from a **semiring** `(R, +, *, 0, 1)`:

- `!_0 A` -- unused (erased, type-level only)
- `!_1 A` -- used exactly once (linear)
- `!_n A` -- used exactly n times
- `!_omega A` -- used arbitrarily (standard bang)

The semiring operations correspond to resource combination:
- **Addition** `r + s`: using a resource in two sub-derivations (context split)
- **Multiplication** `r * s`: using a resource inside a graded context (scaling)
- **Zero** `0`: no usage
- **One** `1`: single usage

### The Dereliction and Promotion Rules (Graded)

Standard linear logic rules for `!` become parameterized:

```
Gamma, A |- C
──────────────── dereliction_r
Gamma, !_r A |- C    (provided r >= 1)

!_r1 A1, ..., !_rn An |- B
──────────────────────────── promotion_s
!_(s*r1) A1, ..., !_(s*rn) An |- !_s B
```

The promotion rule scales all grades by `s`, capturing nested resource usage.

---

## 2. The Semiring Framework

### Useful Semirings

| Semiring | Elements | + | * | 0 | 1 | Tracks |
|---|---|---|---|---|---|---|
| Zero-One-Many | {0, 1, omega} | max-like | min-like | 0 | 1 | Standard linearity |
| Natural numbers | N | + | x | 0 | 1 | Exact usage count |
| Intervals [lo,hi] | N x N | [a+c,b+d] | [ac,bd] | [0,0] | [1,1] | Usage bounds |
| Booleans | {0,1} | or | and | 0 | 1 | Used/unused |
| Tropical (min-plus) | R+ union {inf} | min | + | inf | 0 | Minimum cost |
| Security levels | {public,secret} | join | meet | public | secret | Information flow |
| Real numbers | R>=0 | + | x | 0 | 1 | Quantities/amounts |

### CALC's Current System = {0, 1, omega}

CALC already implements the simplest graded system. The `state.persistent` dictionary holds facts with grade omega (unlimited use), while `state.linear` holds facts with grade 1 (exactly-once use, tracked by count). The `provePersistentGoals` function in `match.js` implements the two-level resolution that distinguishes these grades:

1. **State lookup** -- match against `state.persistent` (grade omega: never consumed)
2. **Backward prove** -- FFI or clause resolution (computes new persistent facts)

Linear facts in `state.linear` are consumed by `applyMatch` in `forward.js`, which decrements counts and deletes entries at zero. This is precisely the {0, 1, omega} semiring with:
- 0 = absent from state
- 1 = present in `state.linear` with count 1
- omega = present in `state.persistent`

### Semirings for EVM Verification

For CALC's EVM verification goals, several semirings are directly useful:

**Natural numbers (N):** Count how many times each storage slot is read/written, how many times each opcode executes, how many token transfers occur.

**Intervals [lo, hi]:** "This contract reads slot X between 1 and 3 times across all execution paths." Computed by taking min/max over path-specific counts.

**Tropical (min, +):** Track minimum gas cost per execution path. The min-plus structure means: when paths branch (oplus), take the minimum; when steps compose sequentially, add costs.

**Pacioli group (R x R, +, *):** Double-entry bookkeeping where each quantity carries debit/credit columns. See TODO_0015 for the Pacioli grading semiring, which would express conservation laws as the semiring equation `debit_total = credit_total`. The multiplication operation for this semiring remains an open question (TODO_0015).

---

## 3. Theoretical Landscape

### 3.1 Bounded Linear Logic (BLL)

Girard, Scedrov, and Scott (1992) introduced BLL, where the exponential `!_p A` is annotated with a **resource polynomial** `p` bounding the number of uses. Cut elimination in BLL runs in polynomial time bounded by the resource polynomial, giving a direct proof-theoretic characterization of PTIME.

Key results:
- Every proof in BLL normalizes in at most `m(P)^3` steps where `m(P)` is the resource measure.
- BLL captures exactly the polynomial-time computable functions.
- Girard's Light Linear Logic (LLL) refines BLL by eliminating explicit polynomial bounds at the cost of more subtle typing distinctions.

**Relevance to CALC:** BLL shows that resource bounds on the bang modality directly control computational complexity. For EVM verification, bounding `!_n A` controls how many times a rule can fire, which bounds execution length and gas consumption.

### 3.2 Quantitative Type Theory (QTT)

McBride (2016) and Atkey (2018) developed QTT, a dependent type theory where every variable binding carries a semiring annotation `x :_r A` indicating "x is used r times." Atkey fixed McBride's substitution issue and gave categorical semantics.

QTT uses context operations:
- **Scalar multiplication** `r * Gamma` -- scale all usages by r
- **Pointwise addition** `Gamma_1 + Gamma_2` -- add usages across sub-derivations
- **Zero context** `0*Gamma` -- all usages are 0

Idris 2 (Brady, ECOOP 2021) implements QTT with the {0, 1, omega} semiring, providing erasure (0), linearity (1), and unrestricted use (omega) in a practical dependently-typed language.

**Relevance to CALC:** QTT's approach of annotating **variable bindings** (not types) maps to annotating **facts in state** (not formulas). See RES_0022 for detailed QTT/CALC comparison.

### 3.3 Granule and Graded Modal Types

Orchard, Liepelt, and Eades (ICFP 2019) developed Granule, a functional language implementing graded modal types via graded comonads. Unlike QTT which annotates variable bindings, Granule annotates **types** with a graded modality `[]_r A`.

Granule features:
- Multiple built-in semirings (natural numbers, security levels, effects)
- Grade polymorphism (`forall {r : Nat}. []_r a -> []_r a`)
- Z3 backend for grade constraint solving
- BLL-style resource-bounded graded necessity

The Granule project has produced recent work (2025) on "A Mixed Linear and Graded Logic: Proofs, Terms, and Models" (Liepelt, Marshall, Orchard, Rajani, Vollmer) which provides a proof-theoretic foundation combining linear and graded reasoning.

**Relevance to CALC:** Granule's graded comonad approach is the closest existing system to what CALC would need for formula-level grading (Option A). Granule does not do proof search, but its grade constraint solving via Z3 maps to CALC's FFI arithmetic.

### 3.4 Coeffect Calculus

Petricek, Orchard, and Mycroft (ICFP 2014) introduced coeffects as the dual of effects: where effects track what a computation **does**, coeffects track what a computation **needs**. The system uses semiring annotations to capture per-variable context requirements.

The generalized coeffect system provides:
- Flat coeffects (whole-context properties like platform version)
- Structural coeffects (per-variable properties like usage count)
- Categorical semantics via indexed comonads

**Relevance to CALC:** Coeffects provide the conceptual framework for what graded resources mean operationally. In CALC's forward engine, a rule's persistent antecedents are coeffects -- they describe what the rule needs from the context without consuming it.

### 3.5 Core Quantitative Coeffect Calculus

Brunel, Gaboardi, Mazza, and Zdancewic (ESOP 2014) developed a core quantitative coeffect calculus that unifies linear and graded reasoning. Their system features typing contexts with both linear variables and non-linear variables marked with semiring elements, plus modal operators `[]_r A` internalizing coeffect information.

This work is foundational for the GrLL (Graded Linear Logic) framework and has influenced subsequent systems including Granule and Grtt.

### 3.6 Linear Dependent Types and Sensitivity

Gaboardi et al. (POPL 2013) developed DFuzz, extending Fuzz (Reed and Pierce) with linear dependent types for differential privacy. The key idea: semiring annotations track **sensitivity** -- how much the output can change when the input changes by one unit. This is a resource-counting semiring applied to function sensitivity.

**Relevance to CALC:** For EVM verification, sensitivity analysis answers: "if one input storage value changes, how many output values can change?" This is exactly a graded analysis over the natural number semiring.

### 3.7 Graded Comonads (Categorical Semantics)

Katsumata (FoSSaCS 2018) and Fujii, Katsumata, Melliès (FoSSaCS 2016) gave categorical foundations for graded modalities:

- A **graded linear exponential comonad** models `!_r` as a family of functors indexed by a semiring, with natural transformations encoding dereliction and promotion.
- Every graded comonad decomposes into an adjunction and a "strict action."
- The decomposition connects graded types to the adjoint logic framework (Reed, Pfenning; Licata, Shulman).

This means CALC's persistent/linear distinction, which is already an adjunction (bang as `F . U`), naturally extends to a graded comonad by parameterizing the adjunction.

### 3.8 Amortized Resource Analysis (AARA)

Hofmann and Jost (2003) introduced AARA, a type system for deriving worst-case resource bounds on functional programs. Extended by Hoffmann to polynomial bounds (2009) and exponential bounds.

Key characteristics:
- **Potential method:** each data structure carries "potential" (prepaid resource credits)
- **Type-based:** resource annotations are part of types, checked by constraint solving
- **Automatic:** bound inference reduces to linear programming
- **Two decades of development:** 2003-2025, covering heap, time, stack, gas

Nomos (Das, Balzer, Hoffmann, Pfenning; CSF 2021) applies AARA to session types for smart contracts, automatically inferring gas bounds. See RES_0033.

**Relevance to CALC:** AARA's potential annotations map directly to Petri net place invariants (see RES_0050 Section 1). Both assign weights to resources and check conservation. AARA automates what P-invariant computation does algebraically.

### 3.9 Ghica and Smith: Bounded Linear Types in a Resource Semiring

Ghica and Smith (ESOP 2014) developed bounded linear types parameterized by an arbitrary resource semiring, with type inference parameterized by the semiring's decision procedure. Their categorical semantics provides a framework for resource-sensitive compilation.

**Relevance to CALC:** Their work shows that semiring-parameterized type systems can be made practical with automated inference, and that the choice of semiring can be deferred to instantiation time. CALC could similarly parameterize its resource tracking by semiring.

### 3.10 Abel and Bernardy: Unified View of Modalities

Abel and Bernardy (ICFP 2020) propose a unified treatment of modalities in typed lambda calculi, showing that a generic structure of modalities arises naturally from intuitionistic logic. Their framework unifies linearity, parametricity, and dependency analysis through grade contexts.

**Relevance to CALC:** Suggests that CALC's ownership modalities, linearity, and resource grades could all be instances of a single graded modality framework.

---

## 4. Connection to CALC's Existing Architecture

### The Persistent/Linear Split in the Engine

CALC's forward engine (`lib/engine/forward.js`, `lib/engine/match.js`) maintains two dictionaries:

```javascript
state = {
  linear:     { hash: count, ... },    // grade 1 resources
  persistent: { hash: true, ... }       // grade omega resources
}
```

The `applyMatch` function consumes linear facts (decrement count, delete at zero) and copies persistent facts unchanged. The `provePersistentGoals` function resolves persistent antecedents via state lookup or backward proving.

A graded system would generalize this to:

```javascript
state = {
  resources: { hash: { grade: r, ... }, ... }  // grade r resources
}
```

Where consumption checks `r >= needed` and updates `r' = r - needed` according to the semiring's subtraction (if the semiring has one) or a pre-order check.

### Execution Trees and Path Analysis

CALC's symexec (`lib/engine/symexec.js`) builds execution trees with node types: `leaf` (quiescent), `branch` (nondeterministic choice), `bound` (depth limit), `cycle` (back-edge). Each root-to-leaf path is a complete execution trace.

This tree structure is ideal for post-hoc resource analysis because every path is explicitly enumerated. Resource counts per path can be aggregated into per-tree summaries using the interval semiring:

```
path_count(resource) -> N                    // exact count per path
tree_count(resource) -> [min_path, max_path] // interval over all paths
```

---

## 5. EVM Verification Examples

### 5.1 Counting Storage Reads/Writes Per Slot

Each EVM `SLOAD` and `SSTORE` instruction reads/writes a specific storage slot. In CALC's EVM rules:

```ill
evm/sload: code(PC, sload) * stack(SH, Slot) * !storage(Slot, Val)
           -o { code(PC', ...) * stack(SH', Val) }.
```

**Post-hoc analysis (Option C):** Walk the execution tree. For each path, count how many times each `storage(Slot, _)` fact appears as a persistent antecedent in rule applications. Result: `sload_count(slot) -> [min, max]` across paths.

**Grade-aware analysis (Option A/B):** Annotate `storage` with a grade: `!_r storage(Slot, Val)` where `r` tracks read count. The promotion rule checks that the total reads across all rule applications don't exceed the bound.

### 5.2 Bounding Gas Consumption Per Path

Each EVM opcode has a gas cost. Currently gas is implicit (CALC doesn't model it). With graded resources:

**Post-hoc (Option C):** Assign a gas cost to each forward rule (from EVM gas schedule). Sum costs along each root-to-leaf path. Report `gas_cost -> [min_path, max_path]`.

**Grade-aware (Option B):** Add a `gas(N)` linear fact to state. Each rule consumes `gas(cost)` and produces `gas(remaining)`. The execution tree naturally bounds gas because paths where `gas` reaches zero have no further applicable rules.

### 5.3 Token Flow Conservation

ERC-20 transfers must conserve total supply: `sum(balances) = total_supply`. In CALC:

```ill
evm/transfer: token(From, AmtF) * token(To, AmtT) * !transfer_request(From, To, Amt)
              -o { token(From, AmtF - Amt) * token(To, AmtT + Amt) }.
```

**Post-hoc (Option C):** At each leaf state, sum all `token(_, Amt)` values and verify equality with initial sum. This is a P-invariant check (see RES_0050 Section 1).

**Pacioli grading (TODO_0015):** Grade tokens with debit/credit pairs. Conservation becomes a semiring equation: the sum of all grades must be the zero element `[0 // 0]` (debits equal credits).

---

## 6. Three Implementation Approaches

### Option A: Grade Annotations on Formulas

**What changes:** Add a graded modality `!_r` to the formula language. The store would support `graded(r, A)` as a connective. Rules would have grade-annotated antecedents and consequents.

**Pros:**
- Logically clean: grades are part of the proof theory
- Supports grade inference and grade polymorphism
- Can express grade constraints in rules

**Cons:**
- Requires changes to the kernel (Store, AST, parser)
- Requires new inference rules (graded promotion, dereliction)
- Content-addressing must handle grade annotations
- Significant implementation effort

**Effort estimate:** High. Touches kernel, parser, prover, and engine.

### Option B: Grade Tracking in the Execution Engine

**What changes:** Extend `state` to carry per-fact grade annotations. The matching engine tracks resource consumption against grades. No formula-level changes.

**Implementation sketch:**

```javascript
state = {
  resources: {
    hash: { count: n, grade: r, maxUse: bound },
    ...
  }
}
```

`provePersistentGoals` would check `grade >= needed` before resolving a persistent fact. `applyMatch` would update grades on consumption.

**Pros:**
- No kernel changes
- Grade tracking is orthogonal to proof theory
- Can be added incrementally (start with counting, add semiring later)
- Configurable per-program (choose semiring at runtime)

**Cons:**
- Grades are not part of formulas, so can't appear in rule definitions
- Grade checking happens in the engine, not in the logic
- No formal connection to graded linear logic proof theory

**Effort estimate:** Medium. Touches engine modules only.

### Option C: Post-Hoc Analysis of Execution Trees

**What changes:** No changes to the logic or engine. After symexec builds the execution tree, a separate analysis pass walks the tree and computes resource statistics.

**Implementation sketch:**

```javascript
function analyzeResources(tree, costModel) {
  if (tree.type === 'leaf') {
    return { paths: [{ costs: {}, state: tree.state }] };
  }
  if (tree.type === 'branch') {
    // Merge all children's paths
    return mergePaths(tree.children.map(c => analyzeResources(c, costModel)));
  }
  // ... step nodes accumulate costs
}
```

For each path from root to leaf:
- Count how many times each rule fires (natural number semiring)
- Sum gas costs per rule (tropical semiring for min-cost path)
- Track per-resource consumption (interval semiring for bounds)
- Verify conservation at leaves (P-invariant check)

**Pros:**
- Zero changes to existing code
- Can be implemented as a standalone module
- Immediately useful for EVM analysis
- 80% of the value with 20% of the effort
- Results feed directly into the verification landscape (RES_0050)

**Cons:**
- No enforcement during execution (analysis is after-the-fact)
- Can't prune execution based on grade violations
- No grade-aware rule matching
- Doesn't extend the logic

**Effort estimate:** Low. A new analysis module with no dependencies on engine internals.

### Recommended Path

**Start with Option C**, then evolve:

1. **Phase 1 (Option C):** Build `lib/engine/analyze.js` that walks execution trees and computes resource statistics. Integrate with P-invariant computation from RES_0050. Immediately useful for EVM verification.

2. **Phase 2 (Option B):** Add optional grade tracking to the engine state. This enables grade-based pruning during symexec (don't explore branches where a resource is exhausted). Backward-compatible: programs without grade annotations work as before.

3. **Phase 3 (Option A):** If the logic needs to express grade constraints in rules (e.g., "this rule requires at least 3 copies of A"), add graded formulas to the kernel. This is a research contribution -- no existing system combines graded linear logic with forward chaining proof search.

---

## 7. Connection to Pacioli (TODO_0015)

The Pacioli group represents quantities as formal differences `[a // b]` (debit `a`, credit `b`). This is a group under addition: `[a // b] + [c // d] = [a+c // b+d]`. The conservation law is `a = b` (debits equal credits).

For Pacioli to serve as a **grading semiring**, we need multiplication. TODO_0015 identifies this as the open question: `[a // b] * [c // d] = ???`. Candidates:

- **Componentwise:** `[ac // bd]` -- preserves semiring laws but loses the debit/credit interpretation of multiplication
- **Convolution:** `[ac+bd // ad+bc]` -- the standard multiplication for formal differences, giving the **Grothendieck group** of (N, +). This makes the Pacioli group isomorphic to Z with `[a//b] = a - b`.

The Grothendieck construction is the mathematically natural choice: it embeds N into Z, giving signed quantities (positive = debit, negative = credit). As a semiring, this is just (Z, +, *, 0, 1) -- the integers.

**Implication:** The Pacioli grading semiring is (Z, +, *, 0, 1). This is well-known, well-behaved, and supports all standard semiring operations. The "double-entry" aspect comes from the **representation** `[a // b]` of the integer `a - b`, not from novel algebraic structure. The conservation law `total_grade = 0` (sum of all grades is zero) captures double-entry bookkeeping.

---

## 8. Interaction with the Forward Engine

### provePersistentGoals Would Need Grade-Aware Matching

In Option B, `provePersistentGoals` (`lib/engine/match.js`, line 269) currently resolves persistent patterns by:
1. State lookup (O(1) predicate guard, then scan)
2. FFI (O(1) arithmetic)
3. Backward chaining (full prove)

With grades, step 1 would additionally check that the resource's remaining grade permits another use:

```javascript
// Current: persistent facts are unlimited
if (persistentPreds.has(pPred)) { ... }

// Graded: check remaining grade
if (persistentPreds.has(pPred)) {
  const grade = state.resources[h].grade;
  if (semiringGte(grade, needed)) { ... }
}
```

### applyMatch Would Update Grades

Currently `applyMatch` (`lib/engine/forward.js`, line 25) decrements linear fact counts and copies persistent facts unchanged. With grades:

```javascript
// Linear consumption: decrease grade
newResources[hash].grade = semiringMinus(grade, consumed);
if (semiringEq(newResources[hash].grade, semiringZero)) delete newResources[hash];

// Persistent "consumption": grade stays but usage counter increments
newResources[hash].usageCount++;
```

### symexec Branching Would Be Grade-Aware

In Option B, execution tree exploration could prune branches where resources are exhausted:

```javascript
// Before exploring a match:
if (!hasEnoughGrade(state, match)) {
  // Skip this branch -- resource exhausted
  continue;
}
```

This is a significant optimization: it reduces tree size by eliminating infeasible branches early, complementing the existing fingerprint and disc-tree indexing strategies.

---

## 9. Open Questions

### Grade Inference

Can grades be inferred automatically from rule structure? AARA shows this is possible via linear programming when grades are natural numbers. For CALC, inferring "how many times can this persistent fact be used before the program quiesces?" is a coverability question (RES_0050 Section 2), which is decidable but EXPSPACE.

A practical alternative: run Option C analysis on a few execution trees, observe the resource counts, and use those as grade annotations for Option B.

### Subgrading

If a rule expects `!_3 A` but state has `!_5 A`, should this match? Yes, via **subgrading**: `5 >= 3` in the natural number semiring. This requires the semiring to have a pre-order compatible with addition and multiplication. Most useful semirings are naturally ordered.

### Grade Polymorphism

Can rules be polymorphic in their grades? Granule supports this (`forall {r : Nat}. []_r a -> []_r a`). For CALC, grade polymorphism would allow writing rules that work for any resource bound, which is useful for reusable library rules.

### Interaction with Focusing

The focusing discipline (RES_0050 Section 6; THY_0001 Section on Q4) determines rule application order. With grades, polarity depends on grade: `!_0 A` is always invertible (erased), `!_1 A` follows linear focusing, `!_omega A` follows standard bang focusing. Intermediate grades would need new focusing rules -- an open research question.

### Grade Composition Across Loli Continuations

CALC's loli-in-monad pattern (`!G -o {B}`) creates dynamic rules. If G has grade `r`, the loli continuation should fire at most `r` times -- but currently lolis are linear (fire once and consumed). Graded lolis `!_r G -o {B}` would fire `r` times, creating `r` copies of `B`. This interacts with the linearity safety guarantee from THY_0001.

---

## 10. Bibliography

### Graded Linear Logic and Bounded Linear Logic
- Girard, J.-Y., Scedrov, A., Scott, P.J. (1992). "Bounded linear logic: a modular approach to polynomial-time computability." TCS 97(1), pp. 1-66.
- Girard, J.-Y. (1998). "Light Linear Logic." I&C 143(2), pp. 175-204.
- Brunel, A., Gaboardi, M., Mazza, D., Zdancewic, S. (2014). "A Core Quantitative Coeffect Calculus." ESOP 2014, LNCS 8410, pp. 351-370.
- Gaboardi, M., Katsumata, S., Orchard, D., Breuvart, F., Uustalu, T. (2016). "Combining Effects and Coeffects via Grading." ICFP 2016, pp. 476-489.
- Ghica, D.R., Smith, A.I. (2014). "Bounded Linear Types in a Resource Semiring." ESOP 2014, LNCS 8410, pp. 331-350.

### Quantitative Type Theory
- McBride, C. (2016). "I Got Plenty o' Nuttin'." A List of Successes, LNCS 9600, pp. 294-316.
- Atkey, R. (2018). "Syntax and Semantics of Quantitative Type Theory." LICS 2018, pp. 56-65.
- Brady, E. (2021). "Idris 2: Quantitative Type Theory in Practice." ECOOP 2021, LIPIcs 194, pp. 9:1-9:26.
- Choudhury, P., Krishnaswami, N., Weirich, S. (2021). "A Graded Dependent Type System with a Universe and Erasure." POPL 2021.

### Granule and Graded Modal Types
- Orchard, D., Liepelt, V.-B., Eades III, H.B. (2019). "Quantitative Program Reasoning with Graded Modal Types." ICFP 2019, Proc. ACM Program. Lang. 3, Art. 110.
- Moon, B., Eades III, H.B., Orchard, D. (2021). "Graded Modal Dependent Type Theory." ESOP 2021, LNCS 12648, pp. 462-490.
- Liepelt, V., Marshall, D., Orchard, D., Rajani, V., Vollmer, M. (2025). "A Mixed Linear and Graded Logic: Proofs, Terms, and Models." CSL 2025, LIPIcs.

### Coeffects
- Petricek, T., Orchard, D., Mycroft, A. (2014). "Coeffects: A Calculus of Context-Dependent Computation." ICFP 2014, pp. 123-135.
- Petricek, T., Orchard, D., Mycroft, A. (2013). "Coeffects: Unified Static Analysis of Context-Dependence." ICALP 2013, LNCS 7966, pp. 385-397.

### Categorical Semantics
- Katsumata, S. (2018). "A Double Category Theoretic Analysis of Graded Linear Exponential Comonads." FoSSaCS 2018, LNCS 10803, pp. 110-127.
- Fujii, S., Katsumata, S., Melliès, P.-A. (2016). "Towards a Formal Theory of Graded Monads." FoSSaCS 2016, LNCS 9634, pp. 513-530.

### Abel and Bernardy
- Abel, A., Bernardy, J.-P. (2020). "A Unified View of Modalities in Type Systems." ICFP 2020, Proc. ACM Program. Lang. 4, Art. 90.

### Linear Dependent Types and Sensitivity
- Gaboardi, M., Haeberlen, A., Hsu, J., Narayan, A., Pierce, B.C. (2013). "Linear Dependent Types for Differential Privacy." POPL 2013, pp. 357-370.
- Reed, J., Pierce, B.C. (2010). "Distance Makes the Types Grow Stronger: A Calculus for Differential Privacy." ICFP 2010, pp. 157-168.

### Amortized Resource Analysis
- Hofmann, M., Jost, S. (2003). "Static Prediction of Heap Space Usage for First-Order Functional Programs." POPL 2003, pp. 185-197.
- Hoffmann, J., Jost, S. (2022). "Two Decades of Automatic Amortized Resource Analysis." MSCS 32(6), pp. 729-759.
- Hoffmann, J., Hofmann, M. (2010). "Amortized Resource Analysis with Polynomial Potential." ESOP 2010, LNCS 6012, pp. 287-306.

### Implicit Computational Complexity
- Dal Lago, U., Hofmann, M. (2005). "Quantitative Models and Implicit Complexity." FSTTCS 2005, LNCS 3821, pp. 189-200.

### Adjoint Logic and Modes
- Reed, J. (2009). "A Judgmental Deconstruction of Modal Logic." Unpublished manuscript.
- Licata, D.R., Shulman, M. (2016). "Adjoint Logic with a 2-Category of Modes." LICS 2016, pp. 219-228.

### Nomos and Resource-Aware Session Types
- Das, A., Balzer, S., Hoffmann, J., Pfenning, F. (2021). "Resource-Aware Session Types for Digital Contracts." CSF 2021.
- Das, A., Pfenning, F. (2022). "Rast: A Language for Resource-Aware Session Types." LMCS 18(1).

### Cross-References
- RES_0022 — Graded Resource Tracking: QTT and Graded Modalities
- RES_0033 — Nomos: Session Types + Linear Types for Smart Contracts
- RES_0038 — Resource Semantics: What Are Terms?
- RES_0050 — Metaproof & Verification Landscape (P-invariants, AARA connection)
- TODO_0015 — Pacioli Grading Semiring
- THY_0001 — Exhaustive Forward Chaining in MALL with the Lax Monad
- THY_0007 — Financial Primitives in CALC

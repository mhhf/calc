---
title: "Grade-0 Staging and Stratified Cut Elimination for Forward-Chaining ILL"
created: 2026-04-01
modified: 2026-04-01
summary: "QTT's grade-0 quantity is meaningful in forward-chaining ILL WITHOUT dependent types — as a staging annotation ('compile-time only, composed away via cut'). Cut elimination in graded ILL can be stratified by grade: grade-0 cuts at compile time, grade-1 at runtime, grade-ω never. The graded semiring {0,1,ω} (established: Atkey 2018) and the indexed monad {A}_a (THY_0013) are orthogonal dimensions that compose into {A}_{q·a}."
tags: [linear-logic, QTT, graded-types, forward-chaining, staging, cut-elimination, proof-theory]
category: "Forward Chaining"
unique_contribution: "Two novel results: (1) QTT's grade-0 quantity is meaningful in forward-chaining ILL WITHOUT dependent types — as a staging annotation where the compiler eliminates grade-0 types via cut. This corrects RES_0056 §10. (2) Stratified cut elimination by grade: a phased procedure where grade-0 cuts are eliminated at compile time, grade-1 at runtime, grade-ω never. RES_0102 confirms this is not a named theorem in the literature."
references:
  - "THY_0013 — The Indexed Lax Monad"
  - "THY_0014 — Compile-Time Evaluation of the Indexed Monad"
  - "RES_0054 — Graded Resource Analysis for Linear Logic"
  - "RES_0056 — QTT Sequent Calculus and Gap Analysis"
  - "RES_0074 — QTT/Graded/Adjoint/SELL/MTDC Expressiveness Hierarchy"
  - "RES_0101 — QTT, SELL, Graded Modalities, and Petri Nets"
  - "RES_0102 — Stratified and Phased Cut Elimination (literature survey)"
  - "Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS."
  - "McBride (2016). I Got Plenty o' Nuttin'."
  - "Girard, Scedrov, Scott (1992). Bounded Linear Logic. TCS."
  - "Vollmer, Marshall, Eades, Orchard (2025). A Mixed Linear and Graded Logic. CSL."
  - "Baillot, Mazza (2010). Linear Logic by Levels. TCS."
  - "Kovács (2023). Staged Compilation with Two-Level Type Theory. POPL."
  - "Davies (1996). A Temporal Logic Approach to Binding-Time Analysis. LICS."
---

# Grade-0 Staging and Stratified Cut Elimination for Forward-Chaining ILL

## Prior art

The {0,1,ω} semiring is established: BLL (Girard-Scedrov-Scott 1992) → Ghica-Smith / Brunel et al. (ESOP 2014) → McBride (2016) → Atkey (2018, QTT) → Brady (Idris 2, 2021). See RES_0054, RES_0056, RES_0074 for surveys. Indexed monads are established: Atkey (2009), Katsumata (2014). Graded + indexed monads combined: Gaboardi et al. (ICFP 2016). The indexed lax monad `{A}_a` for CALC's forward chaining is THY_0013.

This document contributes two results that are NOT in the literature.

## 1. Grade 0 as Staging Without Dependent Types

RES_0056 §10 states: *"Grade 0 requires dependent types to be meaningful."*

This is correct for QTT proper, where grade 0 means "exists in types but not computation" — requiring dependent types for types to mention erased values. But in forward-chaining ILL, grade 0 has a different, equally rigorous meaning:

| | QTT grade 0 | Forward-chaining grade 0 |
|---|---|---|
| **Meaning** | Type-level only, erased from computation | Compile-time only, erased from execution |
| **Requires** | Dependent types | Type declarations with grade annotations + compiler that eliminates grade-0 types |
| **Mechanism** | Type checker ensures 0-grade values don't appear in terms | Compiler composes away 0-grade types via cut elimination |
| **Violation** | Type error: "using erased variable at runtime" | Composition error: "abstract type M not fully eliminated" |
| **Example** | `id : (0 a : Type) -> a -> a` | `@abstract step : ... type.` |

**The staging interpretation of grade 0 needs only:**
1. Type declarations with grade annotations — `@abstract M : ... type.` declares M as grade-0
2. A compilation step that performs cut elimination on grade-0 types
3. A static check that no grade-0 types remain after compilation

No indexed monad. No dependent types. No module algebra. The graded semiring on type declarations is **standalone**.

### Three interpretations of "0"

The literature conflates three distinct meanings of grade 0:

1. **Irrelevance** — the value doesn't matter; any value gives the same result (Pfenning, LICS 2001; Mishra-Linger, PhD thesis 2008)
2. **Erasure** — present at type level, passively *removed* before runtime (QTT: Atkey 2018; Idris 2: Brady 2021)
3. **Staging** — actively participates in compile-time computation, then erased (this document)

Brady (Idris 2) writes "compile-time only (erased)" — conflating erasure with staging. But in Idris 2, grade-0 values are passively removed, not actively computed with. Our interpretation is different: grade-0 types actively participate in compile-time cut elimination (rule composition), producing new rules, then are erased. The types DO work at compile time.

### Why this is novel

Exhaustive search across all major PL venues (POPL, ICFP, ESOP, LICS, CSL) confirms no paper gives grade 0 a staging interpretation in a non-dependent system:

- **All non-dependent graded systems** (Granule: Orchard et al. ICFP 2019; Ghica-Smith ESOP 2014; Brunel et al. ESOP 2014; Wood-Atkey ESOP 2022) interpret grade 0 as "unused/discarded" — pure resource counting, not staging
- **All dependent graded systems** (QTT, Idris 2, GrTT, Moon-Eades-Orchard ESOP 2021) interpret grade 0 as erasure/irrelevance — leveraging dependent types for the "type-level" meaning
- **Linear Haskell** (Bernardy et al. POPL 2018) excluded 0 entirely: "there is no use case" in a non-dependent setting
- **The Granule project** explicitly lists "multi-stage semantics and typing via graded modalities" as an **open PhD research project** (granule-project.github.io/projects.html), confirming no published work bridges this gap
- **Davies-Pfenning** (JACM 2001): `□A` for staging via S4 modality — modal, not graded, no semiring
- **Kovács 2LTT** (POPL 2023): two-level staging — modal levels, not semiring grades

RES_0101 §9 independently lists "QTT 0-grade = staging formal equivalence" as novel/unestablished.

## 2. Stratified Cut Elimination by Grade

**Claim:** Cut elimination in graded forward-chaining ILL can be performed in phases, stratified by grade.

### The graded cut

A cut on type M at grade q (forward-chaining formulation):

```
Γ₁ ⊢ M ⊗ Δ₁       M ⊗ Γ₂ ⊢ Δ₂
─────────────────────────────────── cut_q(M)
        Γ₁ ⊗ Γ₂ ⊢ Δ₁ ⊗ Δ₂
```

The grade determines **when** the cut is performed:

| Grade | Cut behavior | When eliminated |
|---|---|---|
| **0** | M erased — producer/consumer fused, M disappears | Compile time |
| **1** | M consumed linearly — standard multiplicative cut | Runtime |
| **ω** | M persistent — available to all, never consumed | Never |

Grade-0 cut is the forward-chaining analog of BLL's weakening case (cut formula used 0 times). In standard ILL this is forbidden (no weakening on linear types), but grade 0 explicitly marks types that exist only to be composed away.

### The phased procedure

1. **Phase 0 (compile time):** Eliminate all grade-0 cuts. Each composes a producer rule with a consumer rule, erasing the grade-0 type.
2. **Phase 1 (runtime):** Eliminate grade-1 cuts by forward execution (multiset rewriting).
3. **Phase ω:** Grade-ω resources persist as axioms. No elimination.

**Invariant:** After phase k, no grade-k types remain. The proof is cut-free at all grades ≤ k.

**Termination:**
- Phase 0: terminates when the grade-0 type dependency graph is a DAG (THY_0014 §4)
- Phase 1: application-dependent (same as standard forward chaining termination)
- Phase ω: trivially terminates

### Soundness of phase 0

Grade-0 cut elimination is sound when:
1. Every grade-0 type is fully eliminated (no tokens remain)
2. Grade-0 types don't appear in initial states or goals
3. Each (producer, consumer) pair has a unique cut result (guaranteed by linearity)

Under these conditions: `reachable(S, composed_rules) = reachable(S, original_rules)` for all base-type initial states S.

### Novelty

RES_0102 surveys all known work. No paper states "cut elimination stratified by formula grade" as a named theorem. The closest results each capture a fragment:
- **Baillot-Mazza (2010):** level-indexed cut elimination in light logics — complexity bounds, not staging
- **Davies (LICS 1996):** "normalization can be done in stage order" — λ-calculus observation, not sequent calculus theorem
- **Kovács 2LTT (2023):** two-phase staging algorithm — operational, not proof-theoretic
- **BLL (1992):** grade-bounded duplication — complexity, not phased elimination
- **SELL (Nigam-Miller 2009), Adjoint logic (Pruiksma 2024):** cut admissibility by simultaneous induction, not phase-by-phase

## 3. Orthogonal Composition: `{A}_{q·a}`

The graded semiring (§1–2) and the indexed monad (THY_0013) are **orthogonal** dimensions:

| Dimension | Source | What it governs |
|---|---|---|
| **Quantity q ∈ {0,1,ω}** | QTT semiring (Atkey 2018) | *When* a type exists: compile-time, linear runtime, persistent |
| **Stratum label a** | SELL / indexed monad (THY_0013) | *Where* rules are visible: which phase/module/scope |

Neither requires the other. They compose into `{A}_{q·a}`: "execute rules at stratum a with quantity q."

```
{A}_{0·a}  =  evaluate stratum a at COMPILE TIME, erase
{A}_{1·a}  =  execute stratum a at RUNTIME (linear)
{A}_{ω·a}  =  execute stratum a at RUNTIME (persistent)
```

Two-phase staged execution: `{B}_{1·target} ∘ {M}_{0·expansion}` — phase 0 composed away at compile time, phase 1 executed at runtime.

### Monadic bind by grade

The indexed monad's bind `{A}_a >>= f` is a cut. When graded:

- **Grade-0 bind** = `simplify` (THY_0014): compile-time rule composition, intermediate types erased
- **Grade-1 bind** = standard runtime phase sequencing
- **Grade-ω bind** = persistent knowledge accumulation (always available)

### Reduction of CALC concepts

| Existing concept | Graded interpretation |
|---|---|
| Linear resource `P` | Grade-1 resource |
| Persistent fact `!P` | Grade-ω resource |
| `$P` preserved sugar | Grade-1 with net-zero delta (NOT grade 0) |
| `@abstract M` type | Grade-0 type declaration |
| `simplify(T, E)` | Evaluate grade-0 types via cut elimination |
| `{A}_a` indexed monad | `{A}_{1·a}` (grade-1 at stratum a) |
| Compile-time monad (THY_0014) | `{A}_{0·a}` (grade-0 at stratum a) |
| SELL subexponential `!_a` | Grade-ω at stratum a |

### Staging interpretation of semiring arithmetic

The {0,1,ω} operations (see RES_0056 for tables) gain staging meaning in forward-chaining:
- `0 × q = 0` — resources inside a compile-time phase are themselves compile-time
- `0 + 1 = 1` — a type used both at compile-time and runtime must survive to runtime
- `ω + ω = ω` — contraction is idempotent (standard)

The `0 × q = 0` rule is why composition through a grade-0 type eliminates all traces: resources "inside" the 0-phase are scaled by 0.

## 4. Open Questions

### Can grades be inferred from rule structure?

BTA (binding-time analysis) for forward-chaining ILL: a type M is inferrably grade-0 if (1) no rule both produces and consumes M, and (2) M doesn't appear in initial states or goals. This is the bipartite condition from THY_0014. Novel aspect: **linear BTA**, where static types are linear (consumed once during specialization). No BTA literature addresses linear programs.

### Is there a graded focusing theorem?

No focused proof system for semiring-graded ILL exists. Andreoli focusing + the graded semiring would yield a system where focus phases respect grades. Proving cut elimination for such a system is open (noted in RES_0054 §9).

### Grade-0 persistent facts

A persistent fact `!P` at grade 0 would be a compile-time-only axiom — available for backward chaining during composition but erased before runtime. This could model compile-time assumptions ("for this contract, slot 0 always holds the owner address").

### Multi-stage compilation towers

Multiple grade-0 types with a dependency order form a tower of compile-time stages (THY_0014 §4). Each layer is eliminated before the next. The DAG condition guarantees termination. Relationship to multi-level staging (MetaOCaml, Kovács 2LTT) is unclear.

## 5. References

- THY_0013 — The Indexed Lax Monad
- THY_0014 — Compile-Time Evaluation of the Indexed Monad
- RES_0054 — Graded Resource Analysis for Linear Logic
- RES_0056 — QTT Sequent Calculus and Gap Analysis (§10 corrected here)
- RES_0074 — QTT/Graded/Adjoint/SELL/MTDC Expressiveness Hierarchy
- RES_0101 — QTT, SELL, Graded Modalities, and Petri Nets
- RES_0102 — Stratified and Phased Cut Elimination (literature survey)
- Atkey, "Syntax and Semantics of Quantitative Type Theory" (LICS 2018)
- McBride, "I Got Plenty o' Nuttin'" (2016)
- Girard, Scedrov, Scott, "Bounded Linear Logic" (TCS 1992)
- Baillot, Mazza, "Linear Logic by Levels and Bounded Time Complexity" (TCS 2010)
- Vollmer, Marshall, Eades, Orchard, "A Mixed Linear and Graded Logic" (CSL 2025)
- Kovács, "Staged Compilation with Two-Level Type Theory" (POPL 2023)
- Davies, "A Temporal Logic Approach to Binding-Time Analysis" (LICS 1996)
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, "Combining Effects and Coeffects via Grading" (ICFP 2016)

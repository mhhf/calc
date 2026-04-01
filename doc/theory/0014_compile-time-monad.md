---
title: "Compile-Time Evaluation of the Indexed Monad"
created: 2026-03-31
modified: 2026-03-31
summary: "The indexed monad {A}_a can be lifted from runtime (states) to compile-time (rules) — simplify as compile-time phase evaluation, qui as the compile-time monad, and the termination question"
tags: [linear-logic, forward-chaining, lax-monad, cut-elimination, category-theory, multicategory, subexponentials]
category: "Forward Chaining"
unique_contribution: "The observation that the indexed monad {A}_a (THY_0013) lifts from runtime state-level execution to compile-time rule-level composition — with simplify(T,E) as the terminating directed fragment and qui() as the general (potentially non-terminating) fixed point. The decomposition simplify(A,B) = qui(A+B) - B and the identification of productive cycles as the termination obstacle."
references:
  - "THY_0013 — The Indexed Lax Monad"
  - "THY_0015 — The Graded Indexed Monad (QTT quantities on monadic phases)"
  - "RES_0099 — Compile-Time Cut Elimination for Forward Rule Composition"
  - "Lambek (1969). Deductive Systems and Categories."
  - "Cockett & Seely. Proof Theory of the Cut Rule."
  - "Meseguer & Montanari (1990). Petri Nets Are Monoids."
---

# Compile-Time Evaluation of the Indexed Monad

## 1. The Two Levels

THY_0013 defines the indexed monad `{A}_a`: "forward-execute with rules at stratum a to quiescence, return A." This operates at **runtime** on multisets of resource tokens (states).

The same concept lifts to **compile-time**, operating on multisets of forward rules:

| | Runtime | Compile-time |
|---|---|---|
| **Domain** | States (multisets of resources) | Rule sets (multisets of forward rules) |
| **Operation** | Run rules on state to quiescence | Compose rules through internal types to quiescence |
| **Monad** | `{A}_a` — forward-execute at stratum a | `qui(X)` — compose through internal types in X |
| **Boundary** | Quiescence (no rule can fire) | Fixed point (no new compositions possible) |
| **Result** | Transformed state (no stratum-a resources) | Transformed rule set (no internal types) |

The key claim: these are the **same operation at different abstraction levels**. `qui()` is the compile-time lift of `{}_a`.

## 2. `simplify` as Compile-Time Phase Evaluation

Consider two-phase staged execution via the indexed monad:

```
Phase 1: {mid}_expansion    — run expansion rules to quiescence, get intermediate state
Phase 2: {result}_target    — run target rules to quiescence, get final state
```

`simplify(target, expansion)` precomputes this at compile time. It composes expansion rules into target rules, producing single-phase rules that achieve the same result without the intermediate types ever existing at runtime.

The equivalence theorem (informal):

> For all base-type initial states S, the reachable states under `simplify(T, E)` equal the reachable states under the two-phase execution `{T after E}`, provided the intermediate types satisfy the conservative extension conditions (abstract, fully produced/consumed, not observable).

This gives a spectrum:

| Approach | Modularity | Runtime cost |
|---|---|---|
| Monolithic rules (longhand) | None | Optimal |
| `simplify(T, E)` | Write phases separately, compose at compile time | Same as monolithic |
| `{A}_a` runtime phases | Full runtime modularity | Phase-switching overhead |

`simplify` gives the modularity of phases with the performance of monolithic.

## 3. The Algebraic Decomposition

The `simplify` operation decomposes into existing module algebra plus one new primitive:

```
simplify(A, B) = qui(A + B) - B
```

Where:
- `A + B` = union of rule sets (existing)
- `qui(X)` = quiescent closure — compose rules in X through internal types until fixed point (NEW)
- `- B` = subtraction of expansion rules (existing)

This decomposition reveals that `simplify` is not a special-purpose operation but the combination of a general primitive (`qui`) with existing algebra.

## 4. Termination: The Open Problem

### `qui()` does not always terminate

`qui(X)` iterates composition until no new rules are produced. This is a fixed point computation that may not converge:

**Productive cycle example:**
```
inc: type.
r1: A -o { inc (s X) }.
r2: inc X -o { inc (s X) }.    % both consumes and produces inc
```

Round 1: compose (r1, r2) → `A -o { inc (s (s X)) }` — new rule, deeper term
Round 2: compose that with r2 → `A -o { inc (s (s (s X))) }` — deeper still
...never terminates. Each round produces a genuinely new rule (distinct content-addressed hash).

The problem: `r2` both consumes and produces `inc` with a **growing** term. Each composition produces a strictly larger term.

### `simplify` always terminates

The directed version `simplify(T, E)` avoids this because:
- Expansion rules produce abstract type M from base types
- Target rules consume M and produce base types
- Composed rules don't mention M at all
- One round. No feedback. Always terminates.

### Sufficient condition for `qui()` termination

The internal-type dependency graph must be a **DAG**: no directed cycle among internal types. Equivalently, no rule in X both consumes and produces the same internal type (even transitively).

- **DAG check is polynomial** (standard graph cycle detection)
- **Sound but not complete** — rejects some non-growing cycles that would actually terminate
- **Covers all practical cases**: EVM (bipartite), chained abstractions (linear DAG)

### The analogy to runtime termination

Runtime `{A}_a` can also fail to terminate (non-terminating forward execution). We handle this by assuming the user writes terminating rule sets. Similarly, compile-time `qui()` can fail to terminate for pathological rule sets. The DAG condition is the compile-time analog of "your rules don't loop forever."

## 5. The Categorical Picture

Forward rules are multimorphisms in a free symmetric multicategory (Lambek 1969, Cockett-Seely). `simplify` = composing morphisms along an internal wire. Cut elimination = this composition terminates and is canonical.

See RES_0099 §"The Categorical Picture" for the full explanation with string diagrams.

`qui()` = the closure of the multicategory under composition through internal objects. When the internal-object dependency graph is a DAG, this closure is finite.

## 6. Open Questions

### Is there a cleaner primitive?

`simplify(A, B)` works and terminates, but feels special-purpose (two explicit arguments). `qui(X)` is general but has termination issues. Is there a middle ground — a primitive that is both general and always terminating?

Possible directions:
- **`@abstract` type annotations**: declare types that must be composed away before execution. The compiler resolves them automatically. Termination guaranteed by construction (abstract types can only be produced by expansion rules, consumed by target rules — bipartite by annotation).
- **Directed composition operator**: like `qui` but restricted to producer→consumer direction. Always terminates but less general than full `qui`.
- **Stratified `qui`**: process internal types in dependency order, one at a time. Terminates if dependency graph is a DAG. Equivalent to iterated `simplify`.

### What is the right level of abstraction?

The indexed monad `{A}_a` operates on types (stratification). `simplify` operates on rule sets (module algebra). `qui` tries to bridge these. The question: should the compile-time composition be expressed at the type level (`@abstract`), the rule level (`simplify`), or the module level (`qui`)?

### Relationship to partial evaluation

`simplify` is a form of partial evaluation: specializing the two-phase interpreter (indexed monad) by fixing the expansion rules at compile time. The Futamura projection analogy: `PE(two-phase-interpreter, expansion-rules) = monolithic-rules`. Is there a deeper connection to the partial evaluation literature that could guide the design?

## 7. Relationship to THY_0015 (The Graded Indexed Monad)

The compile-time monad described here is the **grade-0 case** of the graded indexed monad `{A}_{q·a}` (THY_0015). The grading comes from QTT's {0, 1, ω} semiring:

- `{A}_{0·a}` = this document's compile-time monad (evaluate at compile time, erase)
- `{A}_{1·a}` = THY_0013's runtime monad (forward-execute linearly)
- `{A}_{ω·a}` = persistent phase (always-available knowledge)

The key insight of THY_0015: grade 0 doesn't require dependent types (contra RES_0056 §10) — it's a staging annotation, meaningful through the indexed monad's phase structure.

## 8. References

- THY_0013 — The Indexed Lax Monad
- THY_0015 — The Graded Indexed Monad
- RES_0099 — Compile-Time Cut Elimination (literature survey + categorical perspective)
- Lambek, "Deductive Systems and Categories" (1969)
- Cockett & Seely, "Proof Theory of the Cut Rule"
- Meseguer & Montanari, "Petri Nets Are Monoids" (1990)
- Martens, "Ceptre" (2015) — stages as special case of indexed monad
- Atkey, "Syntax and Semantics of Quantitative Type Theory" (LICS 2018)
- Cockett, "Deforestation, Program Transformation, and Cut-Elimination" (ENTCS 2001)

---
title: "Symbolic Execution: Three Isolated Problems"
created: 2026-02-18
modified: 2026-02-21
summary: "Decomposition of symbolic value handling into three independent problems: ∃-elimination, witness representation, and term simplification"
tags: [symexec, expressions, design-decision, decomposition]
type: design
cluster: Symexec
status: done
priority: 9
depends_on: []
required_by: []
---

# Symbolic Execution: Three Isolated Problems

## Decision

**P1 (∃-Elimination): Explicit ∃ connective with eigenvariables and eager resolution.** Skolem path backlogged as fallback.

Rationale:
- ∃ is standard CLF — completes CALC's monadic decomposition (`expandItem` already handles ⊗, ⊕, ⊸, !; ∃ fills the gap)
- Eigenvariables keep constraints flat (SMT-ready) without nested expression trees
- Eager resolution: same FFI → state → backward fallback as today. Ground inputs resolve immediately (zero overhead). Symbolic inputs accumulate constraints.
- Skolem is "dirty theory" — catch-all axioms make fallback ordering an implementation detail, leads toward K-framework (term rewriting replaces backward chaining)
- Skolem path preserved in [TODO_0003](0003_symexec-expression-foundation.md) (backlogged)

**P2 (Witness Representation):** Opaque `evar(N)` nodes (monotonic counter). Flat constraints in persistent context. Constraint index for dependency tracking.

**P3 (Simplification):** Deferred. Eigenvariable constraints work without propagation (they just accumulate). See [TODO_0005](0005_symexec-simplification.md).

## The Obstruction

When a forward rule needs `!plus(A, B, C)` and A is symbolic, the three-fallback chain (FFI → state lookup → backward clauses) fails. Execution stalls.

This decomposes into **three independent problems**, each with its own theoretical foundation.

## Decomposition

### Problem 1: ∃-Elimination in Forward Chaining

**Question:** When a persistent antecedent can't be proved, what mechanism produces a value so execution continues?

**Three mechanisms:**

| Mechanism | Theory | What happens | Sequential flow? |
|---|---|---|---|
| Skolem witness | Conservative extension | Add axiom `∀X,Y. plus(X,Y,f(X,Y))` | Yes |
| **Eigenvariable (CLF ∃R)** | **Standard CLF** | **Fresh param α, constraint `!plus(A,B,α)`** | **Yes** |
| Loli-freeze | Standard loli-left | Suspend: `!plus(A,B,C) ⊸ {body}` | **No** (blocks) |

**Decision: Eigenvariable via explicit ∃ connective.**

**Theoretical foundations:** CLF (Watkins 2004), QCHR ω_l^{∃∀} (Barichard & Stéphan 2025), CLP freeze (Jaffar & Maher 1994), Simmons 2012 (forward chaining with ∃). Bruni et al. IJCAR 2024: first Skolemization for ILL — naive Skolemization unsound in general ILL, but safe for CALC's flat state.

### Problem 2: Witness Representation

**Question:** Given eigenvariable mechanism, what does the symbolic value look like in the Store?

**Decision:** Opaque `evar(N)` nodes with constraint index. Flat constraints as persistent facts. No expression constructors, no catch-all clauses, no ground folding needed. SMT-ready.

### Problem 3: Term Simplification

**Question:** Given accumulated constraints, how to prevent unbounded growth?

**Deferred.** Constraints accumulate without propagation. Still useful (SMT export, symbolic traces). Propagation levels (equality resolution → FFI re-check → chain simplification → domain propagation) added incrementally per [TODO_0005](0005_symexec-simplification.md).

## Dependency Order

```
TODO_0002 (this — decided)
    │
    └──→ TODO_0004: Add ∃ connective + forward engine eigenvariables
              │
              └──→ TODO_0005: Constraint propagation (optional)
```

Skolem path backlogged: TODO_0003, TODO_0028.

## Implementation Findings

**EVM rule audit (11 need ∃, 26 unchanged):**
- Restructure: evm/add, mul, sub, exp, lt, gt, and, or, not, concatMemory/s, calldatacopy/s
- Unchanged: all rules with `!inc PC PC'` or `!plus N GAS GAS'` (literal N) — PC and gas always ground
- ⊕ guards (eq/neq/iszero/jumpi): stay as loli guards inside ⊕

**Key simplification:** ∃ in rule consequents is immediately decomposed by `expandItem`. It never persists as a formula in state. Therefore:
- Unification/substitution don't need ∃ support (no ∃-formulas to unify)
- ∃-bound variables are just metavar slots not matched by antecedent — existing `metavarSlots` infrastructure suffices
- ∃ is metadata on compiled rules: "this slot is existential"

**Estimated effort:** ~200 LOC total (grammar ~10, parser ~20, forward engine ~50, constraint index ~20, EVM rules ~50, tests ~50). NOT the 44-72h general-purpose estimate — CALC only needs forward-engine ∃.

## Open Questions

**Q3 (P3, deferred):** Store.put-time normalization vs post-step pass? Only relevant when P3 is tackled.

**Q4 (cross-cutting, deferred):** Rewriting modulo SMT (Rocha & Meseguer 2013) — long-term architecture. Push/pop solver stack maps to CALC's mutation+undo.

**NQ1 (implementation):** Store representation for `exists` node: de Bruijn index for bound variable, or just mark the metavar slot as existential in the compiled rule? For the forward engine, slot-marking suffices. For the backward prover (later), de Bruijn may be needed.

**NQ2 (implementation):** evar nodes: `Store.put('evar', [N])` with new tag, or reuse `freevar` with naming convention? New tag is cleaner (no collision risk, easy to detect).

**NQ3 (phasing):** Forward-engine-only first (minimal ~150 LOC), backward prover ∃ as Phase 2? Recommended: yes, forward-only first.

## Resolved Questions

**RQ1 (P1): Can plus be moved to the consequent without ∃?**
No. Without ∃, the variable C in `stack(SH, C)` has no binding mechanism. Each rule firing needs a *fresh* C — universal quantification gives the same C to every firing. ∃ provides the scoped fresh binding.

**RQ2 (P1): Why keep inc in the antecedent?**
Mode analysis: PC is always ground (concrete program counter from `pc(PC)` match). `inc(PC, PC')` always succeeds via FFI. No reason to move it — it's an optimization (resolve immediately, don't accumulate as constraint). General rule: predicates with always-ground inputs stay in the antecedent; predicates with potentially-symbolic inputs move to the consequent with ∃.

**RQ3 (P1): When does constraint resolution trigger?**
Eager resolution at emission time. When `!plus(A, B, C)` appears in the consequent, immediately try the three-level fallback (FFI → state lookup → backward clauses). If any succeeds → C bound concretely (no eigenvariable). If all fail → C stays as fresh parameter, constraint accumulates. For ground inputs, zero overhead vs current behavior.

**RQ4 (P1): Does the ∃ approach handle multimodal predicates?**
∃ is mode-agnostic — it emits the constraint. Resolution depends on the solver. Example: `evm/sub` uses `!plus(C, B, A)` in mode `- + +`. With ∃, the constraint accumulates if inputs are symbolic. When they become ground, resolution re-checks. Multi-mode FFI or constraint rewriting (e.g., `!plus(A,B,C) ∧ ground(A,C) ⟹ B = C-A`) extends solvable modes — that's P3 territory, orthogonal to ∃.

**RQ5 (P1): Does eager resolution include backward chaining?**
Yes. Same three-level fallback as today: FFI → state lookup → backward clauses. The only difference: today failure = rule doesn't fire; with ∃, failure = constraint accumulates.

**RQ6 (P1): Does later resolution need dependency tracking?**
Yes. Inverted index `Map<variableHash, [constraintFact, ...]>` (~20 LOC). On resolution, look up dependent constraints, re-check each. Constraint graph is a DAG (monotonic counter prevents cycles). Standard attributed variables (Holzbaur 1992).

**RQ7 (cross-cutting): Do infeasible branches die naturally?**
Yes. ⊕ forks into two children. Each child's loli guard determines feasibility. Ground values → one guard fails immediately → dead leaf. Symbolic values → both branches survive with path-condition constraints. Later resolution prunes when values become ground. Standard path-condition accumulation.

**RQ8 (cross-cutting): Does ⊕ forking create dead nodes?**
Yes. Every ⊕ costs 3 nodes minimum (fork + 2 children), even if one child dies immediately. Possible optimization: guard-first evaluation — check guards before forking, skip dead branches. Saves O(branch_points) dead-leaf nodes.

**RQ9 (P1): What is CALC's `{A}` relative to CLF?**
CALC's `{...}` IS the CLF monad — implemented implicitly in `expandItem`. Correctly handles ⊗ (split), ⊕ (fork), ⊸ (suspend), ! (persistent). Missing: ∃. The implementation is incomplete, not dirty. Adding ∃ fills the main gap and completes the monadic decomposition.

**RQ10 (cross-cutting): Is ⊕ limited to exclusive binary guards?**
No. EVM's `(!eq X Y ⊸ {...}) ⊕ (!neq X Y ⊸ {...})` is a special case (P ⊕ ¬P: exclusive, exhaustive). General ⊕ supports: unguarded choice (both explored), non-exclusive guards (both may survive), n-ary via nesting `(A ⊕ (B ⊕ C))`, non-exhaustive (both may die). Examples: process calculi (service selection), game modeling (multi-way moves), non-deterministic search.

**RQ11 (P1, Skolem): Why is Skolem "dirty" theory?**
The axiom `∀X,Y. plus(X,Y,f(X,Y))` makes the catch-all always available — FFI/backward chaining could be skipped entirely. Fallback ordering (FFI first, catch-all last) is an implementation decision, not a logical property. Leads toward K-framework (term rewriting replaces backward chaining). Also requires deep inference for normalization of nested expression trees.

**RQ12 (cross-cutting): Does forward chaining with ⊕ + ∃ need backtracking?**
No. ⊕ forks (both branches explored in parallel via tree). ∃ generates fresh values. Neither requires backtracking. Backtracking only exists in backward chaining (unchanged).

## Cross-References

- [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) — **main analysis** (three problems isolated, theory, examples)
- [RES_0039](../research/0039_symbolic-arithmetic-design-space.md) — design space comparison (hevm, halmos, K, Tamarin, Rosette)
- `doc/research/equational-completion.md` — confluence for catch-all clauses (Skolem, backlogged)
- `doc/research/evm-modeling-approaches.md` — full design space (R1-R5, S1-S3, T1-T7)
- `doc/research/chr-linear-logic.md` §2.5 — QCHR framework
- `doc/theory/exhaustive-forward-chaining.md` — existentials and QCHR
- [TODO_0003](0003_symexec-expression-foundation.md) — Skolem path (backlogged)
- [TODO_0004](0004_symexec-backward-foundation.md) — **Active: ∃ connective implementation**
- [TODO_0005](0005_symexec-simplification.md) — Constraint propagation (deferred)
- [TODO_0028](0028_confluence-proof.md) — Confluence proof (Skolem, backlogged)

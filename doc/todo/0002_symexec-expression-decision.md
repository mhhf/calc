---
title: "Symbolic Execution: Three Isolated Problems"
created: 2026-02-18
modified: 2026-02-21
summary: "Decomposition of symbolic value handling into three independent problems: ∃-elimination, witness representation, and term simplification"
tags: [symexec, expressions, design-decision, decomposition]
type: design
cluster: Symexec
status: researching
priority: 9
depends_on: []
required_by: [TODO_0003, TODO_0004, TODO_0005]
---

# Symbolic Execution: Three Isolated Problems

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
| Eigenvariable (CLF ∃R) | Standard CLF | Fresh param α, constraint `!plus(A,B,α)` | Yes |
| Loli-freeze | Standard loli-left | Suspend: `!plus(A,B,C) ⊸ {body}` | **No** (blocks) |

Loli-freeze alone is insufficient for sequential computation (no PC fact produced). Must compose with Skolem or eigenvariable.

**Theoretical foundations:** CLF (Watkins 2004), QCHR ω_l^{∃∀} (Barichard & Stéphan 2025), CLP freeze (Jaffar & Maher 1994), Simmons 2012 (forward chaining with ∃). Bruni et al. IJCAR 2024: first Skolemization for ILL — naive Skolemization unsound in general ILL, but safe for CALC's flat state.

**Status:** Understanding phase. Both Skolem and eigenvariable should be prototyped.

### Problem 2: Witness Representation

**Question:** Given a mechanism from P1, what does the symbolic value look like in the Store?

**Skolem path:** New constructors `plus_expr(A,B)`, `mul_expr(A,B)`, etc. Content-addressed, self-describing, pattern-matchable. Requires ground folding for confluence (`plus_expr(3,5)` must equal `binlit(8)`). Conservative extension of backward theory.

**Eigenvariable path:** Opaque `evar(N)` nodes with constraint index. Flat constraints in persistent context. No deduplication (each evar unique). SMT-ready.

**Key tradeoff:** Skolem terms carry provenance in structure (inspectable). Eigenvariables separate data from provenance (constraints external). See comparison in research doc.

**Status:** Depends on P1 decision. Two independent prototyping paths.

### Problem 3: Term Simplification

**Question:** Given expression terms (P2), how to prevent unbounded growth?

**For Skolem path (term rewriting):**
- Level 0: Ground folding (required for confluence — part of P2)
- Level 1: Identity/annihilation (`X+0→X`, `X*0→0`)
- Level 2: AC-normalization (flatten + sort + constant fold) — **highest impact**
- Level 3: Cancellation (`X-X→0`)

**For eigenvariable path (constraint propagation):**
- Resolution when variables become ground
- Transitive propagation through constraint graph
- Domain narrowing / interval reasoning

**This is pure term rewriting / CLP.** No linear logic needed. Can be studied independently.

**Status:** Depends on P2. Completely deferrable — expressions work without normalization, just grow.

## Dependency Order

```
Problem 1: ∃-Elimination
    │
    ├──→ Skolem ──→ P2a: Expression Constructors ──→ P3a: TRS Simplification
    │                                                      (optional)
    └──→ Eigenvariable ──→ P2b: Constraint Store ──→ P3b: Constraint Propagation
                                                          (optional)
```

Each level isolated. Each prototypable and testable independently.

## Open Questions

**Q1 (P1):** Should CALC add ∃ as a first-class connective (~200 LOC: parser, rules, focusing), or is implicit Skolemization / implicit eigenvariable generation sufficient?

**Q2 (P2, Skolem):** Is the initial algebra extension (free elements) the right framing? What about catch-all safety — only for total functions (plus, mul, inc), NOT for partial relations (neq, lt, eq). See `doc/research/equational-completion.md`.

**Q3 (P3):** Store.put-time normalization (Maude philosophy: zero per-step cost, Store theory-aware) vs post-step pass (generic Store, O(new_facts) per step)?

**Q4 (cross-cutting):** Rewriting modulo SMT (Rocha & Meseguer 2013, Whitters et al. CADE 2023) — symbolic states as (constraint, multiset). Push/pop solver stack maps to CALC's mutation+undo. Is this the natural long-term architecture?

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

- `doc/research/symbolic-values-in-forward-chaining.md` — **main analysis** (three problems isolated, theory, examples)
- `doc/research/equational-completion.md` — confluence for catch-all clauses
- `doc/research/evm-modeling-approaches.md` — full design space (R1-R5, S1-S3, T1-T7)
- `doc/research/expression-simplification.md` — simplification techniques survey
- `doc/research/symbolic-branching.md` — ⊕ for boolean branching (separate from these three problems)
- `doc/research/chr-linear-logic.md` §2.5 — QCHR framework
- `doc/theory/exhaustive-forward-chaining.md` — existentials and QCHR
- [TODO_0003](0003_symexec-expression-foundation.md) — Skolem path implementation
- [TODO_0004](0004_symexec-backward-foundation.md) — Eigenvariable path implementation
- [TODO_0005](0005_symexec-simplification.md) — Simplification (Problem 3)
- [TODO_0028](0028_confluence-proof.md) — Confluence proof (Problem 2, Skolem)

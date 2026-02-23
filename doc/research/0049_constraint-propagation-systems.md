---
title: "Constraint Propagation Systems: CLP, CHR, and Attributed Variables"
created: 2026-02-23
modified: 2026-02-23
summary: "Survey of constraint propagation architectures: CLP(FD), CHR, attributed variables, union-find/congruence closure, and incremental constraint solving — with CALC mapping."
tags: [CLP, CHR, attributed-variables, constraint-propagation, union-find, congruence-closure, incremental-solving]
category: "Symbolic Execution"
---

# Constraint Propagation Systems

Survey of constraint propagation architectures relevant to CALC's eigenvariable constraint accumulation (TODO_0005).

## 1. CLP(FD) — Finite Domain Constraints

### Core Architecture

CLP(FD) extends logic programming with **domain variables** — variables carrying finite sets of possible values. Three components:

1. **Domain store** — maps each variable to an interval `[lo, hi]` or explicit set `{1,3,7}`
2. **Constraint store** — set of active constraints referencing domain variables
3. **Propagators** — functions that shrink domains based on constraints

**Propagation cycle:** When a domain shrinks, all propagators involving that variable are **woken up** and re-executed. This repeats until no domain changes (fixpoint) or a domain becomes empty (failure/backtrack).

### Consistency Levels

- **Node consistency:** Each value in a variable's domain satisfies all unary constraints on it
- **Arc consistency (AC-3):** For every value in variable X's domain, every constraint involving X has at least one supporting value in every other variable's domain
- **Bounds consistency:** Only min/max of each domain are checked (cheaper than full AC, sufficient for arithmetic)

**AC-3 algorithm:** Maintain a queue of constraints to check. For each constraint, remove unsupported values from variable domains. If a domain changes, re-enqueue all constraints involving that variable. Complexity: O(ed^3) where e = constraints, d = max domain size.

**Bounds propagation for arithmetic:** For `X + Y = Z`:
- `Z.lo = X.lo + Y.lo`, `Z.hi = X.hi + Y.hi`
- `X.lo = Z.lo - Y.hi`, `X.hi = Z.hi - Y.lo`
- (symmetric for Y)

This is **cheap** (O(1) per constraint per wakeup) and sufficient for path condition feasibility.

### SWI-Prolog Implementation (Triska)

- Domains stored as interval trees on **attributed variables**
- Propagators registered as goals attached to variables
- `clpfd:make_propagator/2` + `clpfd:init_propagator/2` = user-extensible propagator registration
- **Indexicals** — reactive functional rules encoding local consistency. Example: `X in min(Z)-max(Y)..max(Z)-min(Y)` for `X + Y #= Z`
- Queue-based wakeup: domain change → propagator re-execution → fixpoint

### CALC Mapping

| CLP(FD) | CALC |
|---------|------|
| Domain variable | `evar(N)` eigenvariable |
| Domain `[lo, hi]` | Persistent fact `domain(evar(N), lo, hi)` |
| Constraint `X + Y = Z` | Persistent fact `!plus(evar(0), evar(1), evar(2))` |
| Propagator | Forward rule triggered by domain change |
| Domain empty → failure | Branch pruning (infeasible path condition) |
| Wakeup mechanism | Forward rule re-matching after state change |

## 2. CHR — Constraint Handling Rules

### Three Rule Types

```
simplification:  H <=> G | B     (replace H with B if guard G holds)
propagation:     H ==> G | B     (add B alongside H if guard G holds)
simpagation:     H1 \ H2 <=> G | B   (keep H1, replace H2 with B)
```

**Direct ILL mapping** (Betz & Fruhwirth 2013):
- Simplification = linear rule: `H -o B`
- Propagation = persistent-head rule: `!H ⊗ ... -o B`
- Simpagation = mixed: `!H1 ⊗ H2 -o B`

### Refined Operational Semantics (Duck et al. 2004)

The abstract semantics (ω_t) is highly nondeterministic. Implementations use the **refined semantics** (ω_r):

1. Each constraint added to the store is **activated**
2. An active constraint searches for applicable rules by **occurrence** (each position in each rule head)
3. For multi-headed rules, the active constraint tries to find **partner constraints** in the store (join)
4. If guard holds, fire the rule
5. If the active constraint survives, continue to next occurrence

**Propagation history:** Prevents re-firing of propagation rules. A set of tuples `(rule_id, constraint_ids)` — if this combination already fired, skip. Essential for termination of propagation rules.

### Compilation (Holzbaur & Fruhwirth 2000)

CHR rules compile to host-language (Prolog) code:
- **Occurrence indexing:** Each constraint tracks which rule occurrences to try
- **Join ordering:** Multi-headed rules get optimized partner search (most selective first)
- **Guard scheduling:** Cheap guards evaluated early to prune search
- **Constraint indexing:** Hash-based lookup for partner constraints (first-argument indexing)

### Confluence Analysis

A CHR program is **confluent** if all critical pairs (overlapping rule applications) produce the same final state. Decidable for terminating programs. Tools: confluence checker in SWI-Prolog CHR library. For CALC: constraint propagation rules must be confluent to guarantee deterministic simplification.

### CALC Mapping

| CHR | CALC |
|-----|------|
| Constraint store | `state.persistent` + `state.linear` |
| Simplification rule | Forward rule consuming linear facts |
| Propagation rule | Forward rule with persistent antecedents |
| Simpagation | Forward rule with mixed `!A ⊗ B -o C` |
| Guard | FFI check / backward proving |
| Propagation history | `pathVisited` (coarser — state-level, not rule-level) |
| Activation | Forward rule matching after state change |

## 3. Attributed Variables (Holzbaur 1992)

### Mechanism

An **attributed variable** is a logic variable carrying arbitrary metadata (attributes). The key hook: when an attributed variable is about to be **unified** (bound), a user-defined predicate `verify_attributes/3` is called. This predicate can:

1. Check the binding against the variable's constraints
2. Update other variables' domains (propagation)
3. Fail (causing backtracking)
4. Return goals to execute after binding

### Wakeup Protocol

```
1. Variable X (with attributes) is about to be bound to value V
2. System calls verify_attributes(X, V, Goals)
3. X is bound to V
4. Goals is a list of goals to execute (propagation callbacks)
5. System executes Goals
6. If any goal fails → backtrack (unbind X, restore attributes)
```

### Implementation in SWI-Prolog

- `put_attr(Var, Module, Value)` — attach attribute
- `get_attr(Var, Module, Value)` — read attribute
- `attr_unify_hook(AttrValue, Target)` — called on unification (module-level callback)
- Attributes survive across `copy_term/2` — constraints are copied with the term

### CALC Mapping

CALC doesn't have traditional unification-triggered wakeups. Instead:

| Attributed Variable | CALC Equivalent |
|---------------------|-----------------|
| Variable with attribute | `evar(N)` + persistent constraint facts |
| `verify_attributes` on binding | `resolveExistentials` + `provePersistentGoals` |
| Wakeup on unification | Forward rule re-matching when evar appears in matching |
| Attribute = constraint list | Persistent facts referencing `evar(N)` |

**Gap:** CALC lacks an explicit wakeup mechanism. When `evar(N)` gets resolved (equality `!eq(evar(N), value)` added), no automatic propagation triggers. This is what TODO_0005 Level 0 addresses.

## 4. Union-Find / Congruence Closure

### Union-Find for Equality

**Union-Find** (Tarjan 1975) maintains equivalence classes with near-O(1) amortized operations:
- `find(x)` → canonical representative of x's class
- `union(x, y)` → merge x's and y's classes

With **path compression** + **union by rank**: amortized O(α(n)) per operation (inverse Ackermann — effectively constant).

### Congruence Closure

Extends union-find to function applications: if `a = b`, then `f(a) = f(b)`. The algorithm:
1. Maintain a **signature table** mapping `(f, find(a1), ..., find(an))` → node
2. After `union(a, b)`: check if any functions with `a` as argument now have a matching entry for `b`
3. If so, merge the function nodes too (cascade)

**Complexity:** O(n log n) for n terms (Downey-Sethi-Tarjan).

### E-Graphs (egg, egglog)

An e-graph = union-find + hashcons table. Each **e-class** contains multiple **e-nodes** (equivalent representations). Key innovation: **equality saturation** — apply rewrite rules without destructive rewriting, adding new equivalences. Extract cheapest form at the end.

**Deferred rebuild:** Batch union operations, restore hashcons invariant once (up to 87x faster than eager congruence closure).

### CALC Mapping

| Concept | CALC Equivalent |
|---------|-----------------|
| Union-Find equivalence class | Content-addressed hash equality (identical hash = identical term) |
| Congruence closure | Not present — `plus(evar(0), 3)` and `plus(5, 3)` never automatically merge even if `evar(0) = 5` |
| E-graph | Store is "half an e-graph" (hashcons without equivalence classes) |

**Gap:** When `evar(0)` resolves to `5`, every fact containing `evar(0)` must be rebuilt with `5` substituted. This requires either:
- Explicit substitution pass (walk all facts containing evar(0))
- Inverted index: `evar(0) → [fact1, fact2, ...]` for efficient lookup

## 5. Incremental Constraint Solving

### Stack-Based (Z3 push/pop)

```
push()          // save state
assert(P)       // add constraint
check-sat()     // solve
pop()           // restore state
```

Maps directly to CALC's `mutateState` / `undoMutate`:
- `push()` = save state before exploring child
- `assert()` = add persistent facts via `mutateState`
- `check-sat()` = attempt rule matching
- `pop()` = `undoMutate` when backtracking in DFS

**Stack-based is 5x faster** than cache-based approaches (Liu et al., HVC 2014) because the solver can reuse learned lemmas from the parent state.

### Cache-Based (KLEE)

Maintain a cache of `(constraint_set_hash → result)`. Before solving, check cache. Content-addressed Store makes this natural for CALC — the state hash already serves as a cache key.

### Practical Architecture for Symbolic Execution

KLEE, angr, Manticore share this pattern:
1. **Path condition** = conjunction of branch decisions accumulated along execution path
2. **Constraint accumulation** = each branch adds a constraint
3. **Solver query** = check satisfiability of accumulated path condition
4. **Simplification** = pre-solver pass to reduce constraint complexity

**CALC analog:** Path conditions are persistent facts (`!neq(C, 0)`, `!eq(X, Y)`). Constraint accumulation is `mutateState` adding persistent facts. "Solver query" is `provePersistentGoals`. Simplification is TODO_0005.

## 6. Synthesis: Architecture for CALC

### What CALC Already Has

1. **Constraint store** = `state.persistent` (persistent facts, monotonically increasing within a branch)
2. **Propagators** = forward rules (fire when antecedent facts appear)
3. **Guard evaluation** = FFI + backward proving (`provePersistentGoals`)
4. **Coroutining** = loli mechanism (`!P -o {body}` suspends until P provable)
5. **Incremental state** = `mutateState` / `undoMutate` (stack-based solver pattern)
6. **Content addressing** = Store (half an e-graph — hashcons without equivalence classes)

### What CALC Lacks (TODO_0005 Levels)

1. **Equality resolution** (Level 0) — when `!eq(evar(N), value)` appears, substitute `evar(N) → value` everywhere
2. **Wakeup/re-check** (Level 1) — when a constraint's inputs become ground, re-prove via FFI
3. **Chain simplification** (Level 2) — detect and merge constraint chains
4. **Domain propagation** (Level 3) — interval tracking per eigenvariable
5. **Multi-mode resolution** (Level 4) — reverse-mode FFI (deduce input from output)

### Recommended Architecture

```
Forward step fires →
  mutateState produces new persistent facts →
    For each new persistent fact:
      1. Check: does it bind an evar? (equality resolution)
      2. If yes: substitute in dependent constraints (inverted index)
      3. Re-check now-ground constraints via FFI (wakeup)
      4. Repeat until fixpoint (no new bindings)
```

This is the CLP(FD) propagation cycle adapted to CALC's forward engine.

## 7. Performance Comparison of Approaches in Practice

### EVM Symbolic Execution Benchmarks (CAV 2024)

Shared benchmark suite (199 tests: conformance + real-world ERC20/ERC721/deposit contract):
- **hevm** (eager simplification): 1.5-1.6s per test
- **halmos** (delegate to Z3): 4.2-5.8s per test
- **KEVM** (rule-driven, user lemmas): 10min-35min per test

hevm's speed comes from **smart constructors + equivalence propagation + constant folding** — all running before any SMT call. "hevm skips almost all SMT queries during exploration."

### Constraint Solving Latency Comparison

| Approach | Per-operation cost | Total for 1000 constraints | Notes |
|----------|-------------------|---------------------------|-------|
| Equality substitution (union-find) | O(α(n)) ≈ O(1) | ~10μs | Tarjan 1975, every SMT solver |
| Constant folding (smart constructor) | O(1) | ~5μs | Every compiler |
| Bounds propagation (CLP(FD)) | O(1) per constraint | ~50μs | Triska 2012, SWI-Prolog |
| E-graph equality saturation | O(n) per rebuild | ~1-100ms | Risk of blowup. Willsey 2021 |
| SMT query (Z3) | 0.1-10ms per query | 100ms-10s | Complete but high latency |
| AC-matching (Maude) | O(log n) | ~100μs | Eker 2003 |

### E-Graph Scalability Caveat

"Even if a set of rewrite rules terminates as a TRS, it may yield an infinite number of e-classes in equality saturation." Commutativity (`a+b => b+a`) causes infinite loops. "Precisely characterizing when e-graph rewriting blows up is an unsolved research problem" (egg discussion #60).

### Incremental Solving: Stack vs Cache (Liu et al. HVC 2014)

Stack-based incremental solving (Z3 push/pop) achieves median 5x speedup over cache-based approaches on 96 C programs. CALC's `mutateState`/`undoMutate` is already a stack-based architecture.

## References

- Holzbaur (1992) — *Metastructures vs Attributed Variables* (PLILP)
- Triska (2012) — *The Finite Domain Constraint Solver of SWI-Prolog* (FLOPS)
- Fruhwirth (2009) — *Constraint Handling Rules* (Cambridge University Press)
- Duck et al. (2004) — *The Refined Operational Semantics of CHR* (ICLP)
- Holzbaur & Fruhwirth (2000) — *Compiling CHR into Prolog with Attributed Variables*
- Tarjan (1975) — *Efficiency of a Good But Not Linear Set Union Algorithm*
- Willsey et al. (2021) — *egg: Fast and Extensible Equality Saturation* (POPL)
- Nelson & Oppen (1979) — *Simplification by Cooperating Decision Procedures*
- Liu et al. (2014) — *Comparative Study of Incremental Constraint Solving in Symbolic Execution* (HVC)
- Jaffar & Maher (1994) — *Constraint Logic Programming: A Survey* (JLP)
- Betz & Fruhwirth (2013) — *CHR-v via Linear Logic* (connecting CHR to ILL)
- Eker (2003) — *Associative-Commutative Rewriting on Large Terms* (Maude)
- Rocha & Meseguer (2013) — *Rewriting Modulo SMT* (NASA/TM-2013-218033)
- Whitters, Nigam, Talcott (2023) — *Incremental Rewriting Modulo SMT* (CADE)
- Nieuwenhuis & Oliveras (2005) — *Proof-Producing Congruence Closure* (RTA)
- Singher & Shacham (2023) — *Colored E-Graph: Equality Reasoning with Conditions*
- hevm CAV 2024 — *Hevm, a Fast Symbolic Execution Framework for EVM Bytecode*
- Meseguer (1992) — *Conditional Rewriting Logic* (TCS)

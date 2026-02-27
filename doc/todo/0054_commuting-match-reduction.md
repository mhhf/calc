---
title: "Commuting Match Reduction in Exhaustive Exploration"
created: 2026-02-26
modified: 2026-02-27
summary: "Eliminate redundant tree branches caused by commuting matches — grounded in CLF definitional equality, Mazurkiewicz trace theory, and DPOR"
tags: [symexec, forward-chaining, partial-order-reduction, loli, performance, theory, proof-nets, memoization, clf, concurrency]
type: design
cluster: Symexec
status: ready for implementation
priority: 9
depends_on: [TODO_0041]
required_by: [TODO_0042]
---

# Commuting Match Reduction

## Problem

`findAllMatches` returns all applicable matches (forward rules + loli continuations) as equal alternatives. `explore()` branches on ALL of them. When two matches are **independent** (consume disjoint linear facts), both orderings reach the same successor state — the subtrees below are identical.

### Concrete example (EVM)

State: `pc 5 * code 5 0x61 * stack (s ee) V * loli(!neq X Y, {stack SH 0})`

Two matches fire simultaneously:
1. `evm/push2`: consumes `pc`, `code` → produces new `pc`, `stack`
2. `loli:trigger`: consumes `loli` fact, proves `!neq` → produces `stack`

They consume disjoint facts. Both orderings reach the same state S. Each such commuting pair doubles the tree. In MultisigNoCall (solc), 6 commuting points → 2^6 = 64 identical STOP leaves instead of 1.

### Scope

- **Multisig baseline**: 2 STOP → should be 1
- **Multisig + CALL**: 4 STOP → should be 2 (CALL fork is genuine)
- **Solc multisig**: 64 STOP → should be 1
- **General**: any program where independent transitions are simultaneously enabled

## Why Cycle Detection Doesn't Help

`pathVisited` detects **back-edges** (cycles on the current DFS path), not **joins** (diamond convergence). It's a DFS-path set: added before recursion, deleted after all children return.

```
      S₀
     / \
    t1   t2        pathVisited = {S₀}
   /       \
  S₁       S₂      S₁ branch: {S₀, S₁}  /  S₂ branch: {S₀, S₂}
   \       /
    t2   t1
     \   /
      S₃            first visit: full exploration (S₃ not in pathVisited)
      S₃            second visit: full RE-exploration (S₃ was already deleted)
```

S₃ is not in `pathVisited` on the second visit — it was removed when the first branch backtracked. A **global visited set** (never cleared) would detect the join.

## Theoretical Foundation

### CLF Definitional Equality (the key insight)

CLF (Watkins, Cervesato, Pfenning, Walker 2004) provides exactly the concept we need:

> "A simple notion of **definitional equality** that identifies computations differing only in the order of execution of independent steps."

CLF's monad `{A}` defines an **atomic step boundary**. Within the monad, all sub-operations are concurrent — their order is irrelevant (definitionally equal). The monad boundary is where sequencing is imposed (via monadic let).

**Our loli-in-monad extension breaks this.** By producing a loli inside `{A}`, we create a deferred sub-step that becomes visible as a separate transition in the next state. This violates the atomic-step abstraction — what CLF defines as one concurrent computation becomes two sequential transitions that can be interleaved with other transitions.

The fix is to restore CLF's definitional equality: **computations that differ only in the order of independent steps should not create distinct branches.**

### Mazurkiewicz Traces

A Mazurkiewicz trace (Mazurkiewicz 1977) is an equivalence class of action sequences under commutation of adjacent independent actions. Two traces are equivalent iff one can be obtained from the other by swapping independent adjacent actions.

Our execution tree explores all interleavings — every ordering of concurrent actions gets its own path. But each Mazurkiewicz trace class corresponds to a single concurrent computation. The tree should have one path per trace class, not one per interleaving.

### Independence in ILL

Two transitions t₁, t₂ enabled at state S are **independent** iff `consumed(t₁) ∩ consumed(t₂) = ∅`. Independent transitions commute: `t₁; t₂` and `t₂; t₁` reach the same state. This follows from ILL's tensor commutativity: if t₁ consumes resources disjoint from t₂, their applications are independent cuts in the derivation.

### Why Focusing Doesn't Apply

Andreoli focusing (1992) determines the **depth** of formula decomposition (once focused, decompose completely). It does NOT address the **breadth** of choice (which of several independent transitions to fire). The focus CHOICE is still nondeterministic.

"Focus on linear lolis first, then persistent" is a priority ordering, not a focusing discipline. And for exhaustive exploration, priority doesn't help — ALL matches must be explored. Priority only determines tree shape, not reachable states.

The right theoretical concept is not focusing but **CLF's monadic concurrency** (within a monadic step, order is irrelevant) and **Mazurkiewicz trace equivalence** (quotient interleavings by independence).

### Loli Classification

**Persistent-trigger lolis** (`!guard -o {body}`):
- Guard is provable immediately from `state.persistent`
- Consume only the loli fact itself (no linear trigger)
- ALWAYS independent of all forward rules
- Violate CLF monad atomicity unnecessarily — the guard resolution should be part of the atomic oplus step
- **Commuting matches: YES (the source of our problem)**

**Linear-trigger lolis** (`fact -o {body}`):
- Trigger is a linear fact that doesn't exist yet (produced by a later step)
- Represent genuine sequential composition across monadic steps
- In CLF terms, these should use monadic let, not loli-in-monad (see TODO_0006)
- Can't fire at the same time as forward rules (trigger unavailable → causal dependency)
- **Commuting matches: NO (causally dependent)**

## Approaches

### TODO_0054.Option_C — Synchronous Loli Fusion (restore CLF atomicity)

Resolve persistent-trigger lolis atomically with the oplus expansion. The oplus choice + guard resolution become one atomic step — restoring CLF semantics.

Current (two separate transitions):
```
Step N:   oplus fires → produces loli(!neq, {stack 0}) in state
Step N+1: loli fires → proves !neq → produces stack 0
          (OR forward rule fires first → loli fires at N+2 → same result)
```

Fused (one atomic step, as CLF intends):
```
Step N: oplus fires → prove !neq immediately → produce stack 0 (or dead leaf on failure)
```

**Theory compliance: YES.** This restores CLF's monad boundary semantics. The guard resolution was always logically part of the atomic monadic step — we were artificially deferring it by storing a loli. CLF forbids lolis in the monad precisely to prevent this deferred-step problem. Our fusion agrees with CLF for persistent-trigger lolis.

**Correctness: 100%.** For persistent-trigger lolis:
1. Guard provability depends only on persistent state (not affected by any concurrent transition)
2. Only linear fact consumed is the loli itself (no competition with forward rules)
3. Fusion produces identical results regardless of what other transitions are enabled
4. Dead branches (guard fails) are detected earlier (at oplus step, not later)

**Scope**: Handles all persistent-trigger lolis. Does NOT handle:
- Linear-trigger lolis (but these don't cause commuting matches — see classification above)
- Forward-vs-forward commuting (but this doesn't occur in EVM due to `pc` mutual exclusion)

| | |
|---|---|
| Pro | Restores CLF semantics — eliminates the source, not just the symptom |
| Pro | Shallower tree (fewer steps per oplus resolution) |
| Pro | Dead branches detected earlier |
| Pro | Linear-trigger lolis are unaffected (they don't cause commuting matches) |
| Con | Refactor of oplus handling in `go()` |
| Con | Does not address forward-vs-forward commuting (irrelevant for EVM) |

### TODO_0054.Option_E — State Memoization (global visited set)

Add a global `Set<stateHash>` (distinct from `pathVisited`). Before exploring a state, check if already explored. Return `{ type: 'memo' }` instead of re-exploring.

**Theory compliance: YES.** Same state = same future (trivially correct). Standard graph search with closed set.

```javascript
function go(depth, ctx) {
  if (pathVisited.has(ctx.stateHash)) return { type: 'cycle', ... };
  if (globalVisited.has(ctx.stateHash)) return { type: 'memo', ... };
  if (depth >= maxDepth) return { type: 'bound', ... };
  // ... explore children ...
  globalVisited.add(ctx.stateHash);
  pathVisited.delete(ctx.stateHash);
  return { type: 'branch', ... };
}
```

Catches ALL state duplicates regardless of source. Does NOT reduce branching (still creates 2^N branches), but prunes subtrees (2^N − 1 become `memo` leaves).

| | |
|---|---|
| Pro | Most general — catches ALL duplicates |
| Pro | ~5 lines to implement |
| Pro | No independence relation needed |
| Con | Does not reduce branching factor (tree has same structure, just pruned) |
| Con | Hash collision risk (32-bit XOR) — needs mitigation |
| Con | Path information lost at memo nodes |

### TODO_0054.Option_B — DPOR (Dynamic Partial Order Reduction)

Modern approach from Flanagan & Godefroid (POPL 2005). Instead of computing independence statically, discover conflicts dynamically during exploration. Guarantee: explore at least one execution per Mazurkiewicz trace class.

**Theory compliance: YES.** Preserves all reachable states. Grounded in Mazurkiewicz trace theory.

DPOR is more precise than static POR because it only adds backtrack points when actual conflicts are observed. But it's also more complex to implement.

| | |
|---|---|
| Pro | Optimal — one execution per Mazurkiewicz trace |
| Pro | Handles ALL commuting matches (loli-forward, forward-forward) |
| Pro | Dynamic conflict detection (no conservative overapproximation) |
| Con | Complex implementation |
| Con | Requires backtrack point management during DFS |

### TODO_0054.Option_A — Eager Loli Resolution (ad hoc)

**Theory compliance: NO.** Enforces loli-before-forward ordering without proving independence. Unsafe if a loli with linear triggers competes with a forward rule for the same linear fact. Not grounded in any established theory.

Subsumed by Option C (which has a clean CLF justification) + Option E (which catches remaining duplicates).

### Other options considered

**Sleep sets (Godefroid 1996)**: Propagate independence information through DFS frames. Equivalent to POR in power, slightly different bookkeeping. Same complexity concerns.

**Maximal step semantics (Petri net steps)**: Fire all independent transitions simultaneously. Elegant but complex mutation model (multiple matches applied atomically). No existing implementation framework.

**Proof nets**: Explore canonical representatives of derivation equivalence classes. Theoretically ideal but no practical algorithm for forward-chaining proof nets exists.

## Comparison

| | Scope | Complexity | Branching | Work | Theory | Safe |
|---|---|---|---|---|---|---|
| **C. Fusion** | Persistent lolis | Medium | Eliminated | Eliminated | CLF monad | Yes |
| **E. Memoization** | ALL duplicates | **Low** | Unchanged | Pruned | Graph search | Yes |
| **B. DPOR** | All commuting | High | Optimal | Optimal | Mazurkiewicz | Yes |
| A. Eager loli | Persistent lolis | Low | Eliminated | Eliminated | **None** | **No** |

## Recommended Implementation

### Layer 1: State Memoization (E) — implement first

Simplest change, catches everything. Add global visited set to `go()`. Even without any other optimization, this prevents re-exploring identical subtrees. The 2^6 = 64 branches in the solc multisig still exist, but 63 of them terminate immediately at `memo` nodes.

Hash collision mitigation: verify with full state comparison on hit (store `Map<hash, stateSnapshot>` instead of `Set<hash>`).

### Layer 2: Synchronous Loli Fusion (C) — implement second

Eliminates the branching itself for persistent-trigger lolis. After fusion, the solc multisig has 1 STOP leaf (not 64 branches pruned to 1 — just 1 branch). Tree is cleaner and shallower.

This is the theoretically principled fix: restoring CLF's monad boundary semantics. The persistent-trigger loli was never supposed to be a separate step.

### Layer 3: DPOR (B) — future, if needed

For non-EVM programs with forward-vs-forward commuting. Not needed for EVM (pc mutual exclusion prevents it). Research-level implementation.

### Why this layering is clean

Each layer has a distinct theoretical justification:
- **Memoization**: graph search (DFS with closed set) — computer science fundamentals
- **Fusion**: CLF monadic step boundary — proof-theoretic semantics
- **DPOR**: Mazurkiewicz trace equivalence — concurrency theory

Each layer is independently correct. Together they cover all sources of redundancy.

## Also Blocked

This TODO blocks the **symbolic sender/storage benchmark**: with 64× duplication, timing comparisons with hevm are meaningless. Fix commuting matches first, then benchmark.

## References

- Watkins, Cervesato, Pfenning, Walker (2004) ["A Concurrent Logical Framework: The Propositional Fragment"](https://www.cs.cmu.edu/~fp/papers/types03.pdf) — CLF definitional equality for concurrent computations
- Watkins, Cervesato, Pfenning, Walker (2004) ["CLF: A Dependent Logical Framework for Concurrent Computations"](https://www.cs.cmu.edu/~fp/papers/clf04.pdf) — full CLF type theory
- Flanagan, Godefroid (2005) ["Dynamic Partial-Order Reduction for Model Checking Software"](https://users.soe.ucsc.edu/~cormac/papers/popl05.pdf) — DPOR
- Simmons (2012) ["Substructural Logical Specifications"](https://www.cs.cmu.edu/~rwh/students/simmons.pdf) — forward chaining in linear logic, saturation semantics
- Simmons, Pfenning (2008) ["Linear Logical Algorithms"](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf) — cost semantics for forward chaining
- Mazurkiewicz (1977) "Concurrent Program Schemes and their Interpretations" — trace theory
- Peled (1993) "All from One, One for All: On Model Checking Using Representatives" — POR
- Godefroid (1996) "Partial-Order Methods for the Verification of Concurrent Systems" — sleep sets
- Girard (1987) "Linear Logic" — proof nets as canonical representations
- Andreoli (1992) "Logic Programming with Focusing Proofs in Linear Logic" — focusing (backward, NOT forward)
- Martens (2015) ["Programming Interactive Worlds with Linear Logic"](https://www.cs.cmu.edu/~cmartens/thesis.pdf) — Ceptre, CLF for games
- Elsawy, Zaki, Abdennadher (2014) ["Exhaustive Execution of CHR Through Source-to-Source Transformation"](https://link.springer.com/chapter/10.1007/978-3-319-17822-6_4) — CHR exhaustive exploration
- [TODO_0041](0041_unified-rule-matching.md) — unified matching (done, prerequisite)
- [TODO_0042](0042_exhaustive-exploration-completeness.md) — completeness proof
- [TODO_0006](0006_lax-monad-integration.md) — monadic let for sequential composition (future home for linear-trigger lolis)
- `doc/theory/0001_exhaustive-forward-chaining.md` — CALC's loli-in-monad extension

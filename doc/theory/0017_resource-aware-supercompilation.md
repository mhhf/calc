---
title: "Resource-Aware Supercompilation via Linear Logic"
created: 2026-04-08
modified: 2026-04-08
summary: "Grade-0 composition + explore = partial evaluation + driving = supercompilation for linear logic. The first resource-aware supercompiler: driving respects linear consumption, generalization operates on multiset structure, folding uses content-addressed state hashes. Novel contribution: no prior supercompiler handles linear resources."
tags: [supercompilation, forward-chaining, linear-logic, partial-evaluation, exploration, proof-theory]
category: "Forward Chaining"
unique_contribution: "The identification of CALC's explore() + composeGrade0 as resource-aware supercompilation — the first supercompiler that respects linear resource consumption. Classical supercompilation (Turchin 1986, Sørensen-Glück-Jones 1996) operates on functional terms with free copy/discard. Our driving must track resource consumption, generalization must respect linearity, and folding operates on multiset hashes rather than term structure."
references:
  - "THY_0016 — Partial Evaluation as Cut Elimination in SELL"
  - "THY_0001 — Exhaustive Forward Chaining"
  - "Turchin (1986). The Concept of a Supercompiler. TOPLAS."
  - "Sørensen, Glück, Jones (1996). A Positive Supercompiler. JFP."
  - "Sørensen, Glück (1995). An Algorithm of Generalization in Positive Supercompilation. ILPS."
  - "Klyuchnikov, Romanenko (2012). Formalizing and Implementing Multi-Result Supercompilation. PSI."
  - "Bolingbroke, Peyton Jones (2010). Supercompilation by Evaluation. Haskell Symposium."
---

# Resource-Aware Supercompilation via Linear Logic

## 1. The Correspondence

THY_0016 establishes that grade-0 composition is partial evaluation via cut elimination. This document identifies the full supercompilation correspondence when PE is combined with exhaustive exploration.

**Supercompilation** (Turchin 1986) = partial evaluation + driving + generalization:
- **Driving**: symbolic execution that unfolds function calls and follows all branches
- **Generalization**: detect repeated configurations, abstract to avoid infinite unfolding
- **Residualization**: collect the process tree into an output program

In CALC: `composeGrade0` is PE, `explore()` is driving, and the structural memo + cycle detection provide generalization and folding.

## 2. Concrete Mapping

| Supercompilation | CALC realization | Module |
|---|---|---|
| Configuration | `state` (linear FactSet + persistent FactSet) | `fact-set.js` |
| Driving step | `mutateState()` — apply one forward rule | `explore.js` |
| Driving machine | `go(depth, predicted)` DFS loop | `explore.js` |
| Positive info propagation | `provePersistentNaive()` — known facts flow forward | `lnl/persistent.js` |
| Negative info propagation | `EqNeqSolver` — eq/neq constraints accumulate | `constraint.js` |
| Branch pruning | `filterAltsBySAT()` — kill UNSAT alternatives | `opt/constraint.js` |
| Generalization | `computeControlHash()` — abstract to (PC, stack depth) | `opt/structural-memo.js` |
| Memo (shared subtree) | `globalControl` hash map → `{ type: 'memo' }` | `opt/structural-memo.js` |
| Folding (back-edge) | `pathVisited.has(sh)` → `{ type: 'cycle' }` | `explore.js` |
| Process tree leaf | `{ type: 'leaf', state }` — quiescent configuration | `explore.js` |
| Incomplete residual | `{ type: 'bound' }` — depth limit reached | `explore.js` |
| Whistle (termination) | Fixed `maxDepth` bound | `explore.js` |

### 2.1 Driving

Each call to `mutateState(state, m.consumed, m.theta, ...)` is one driving step. The Arena-based undo (`linArena`/`perArena`) gives DFS-with-backtracking — the characteristic structure of a driving machine. The state is mutated in-place and rolled back after each branch, rather than copied.

### 2.2 Information propagation

**Positive**: persistent facts accumulate monotonically along each DFS path. When a rule proves `!gt PC 10 true`, all subsequent rules on the same path can use this fact. `feedPersistent(solver, ...)` extends the constraint solver incrementally after each step.

**Negative**: the `EqNeqSolver` tracks `eq`/`neq` constraints via union-find with a forbid list. `filterAltsBySAT` kills `⊕` alternatives inconsistent with accumulated constraints — branches where `eq X Y` contradicts an earlier `neq X Y`. This is the supercompiler's negative information filtering.

### 2.3 Generalization

`computeControlHash` projects the full state to (PC value, stack depth), discarding symbolic values. Two states with the same control hash execute the same instruction sequence regardless of concrete values. This is a coarse but sound abstraction — it avoids re-exploring isomorphic subtrees.

Classical supercompilation uses the **Homeomorphic Embedding Test** (HET) to detect when a configuration is "growing" relative to an ancestor, then applies **Most Specific Generalization** (MSG) to abstract away the growing part. CALC's `controlHash` is a simpler mechanism that achieves the same goal in a domain-specific way.

### 2.4 Folding

`pathVisited` (Set of state hashes) detects back-edges on the current DFS path → `{ type: 'cycle' }`. This is exactly supercompilation folding: when a descendant configuration matches an ancestor, emit a loop rather than diverging.

`globalVisited` (Set) detects shared join points across sibling branches → `{ type: 'memo' }`. This is not standard in supercompilation (which typically only folds to ancestors) but is an optimization enabled by content-addressed multiset hashing: two states with identical linear resources are definitionally the same, regardless of the path that reached them.

## 3. What Makes It Resource-Aware

Classical supercompilation (Turchin, Sørensen-Glück-Jones) operates on **functional terms** — λ-calculus expressions or first-order term rewriting. Terms can be freely copied (contraction) and discarded (weakening). The supercompiler's process tree is a tree of term transformations.

CALC's driving operates on **linear resource multisets**. Each driving step must consume linear resources exactly — no implicit copying or discarding. This imposes three constraints not present in classical supercompilation:

**3.1 Resource-balanced driving.** Each `mutateState` consumes exactly the resources matched by the rule's antecedent and produces exactly those in the consequent. The Arena undo log must restore the exact multiset — not just a "similar" configuration, but the identical set of hashes.

**3.2 Multiset generalization.** Classical generalization abstracts term structure (replace a subterm with a variable). Our generalization abstracts multiset composition (ignore symbolic values, keep control structure). The abstraction domain is `(PC, stack_depth)` rather than term shape — because what matters for linear execution is which resources are available, not their internal structure.

**3.3 Hash-based folding.** Classical folding compares term structure (renaming equivalence). Our folding compares `stateHash` — a content-addressed hash of the entire linear+persistent multiset. This is exact: two states with the same hash are identical up to Store deduplication. No renaming check needed, because the Store already canonicalizes.

## 4. The Staged Supercompilation Pipeline

Combining PE and driving:

```
Stage 1: composeGrade0 (PE)     — specialize rules against known bytecode
Stage 2: explore() (driving)    — symbolically execute specialized rules
```

This is exactly the standard supercompilation architecture:
1. **PE phase** (offline): partially evaluate the interpreter against the static input
2. **Driving phase** (online): symbolically execute the residual program

The grade semiring provides the staging order: grade 0 is resolved at PE time, everything else at driving time. Multi-level PE (THY_0016 §3) extends this to three stages:

```
Stage 1: grade-0 PE    — bytecode specialization
Stage 2: grade-1 PE    — calldata specialization
Stage 3: explore()     — symbolic driving on remaining unknowns
```

Each PE stage reduces the driving workload — fewer unknowns means fewer branches in the process tree.

## 5. Gaps from Full Supercompilation

### 5.1 Whistle

We use fixed `maxDepth` — a blunt termination guarantee. Full supercompilation uses the Homeomorphic Embedding Test (HET): if a configuration is "homeomorphically embedded" in an ancestor (structurally contained), the driving is about to diverge, and generalization is triggered.

For CALC: HET would operate on multiset structure. A state S₁ embeds in S₂ if S₁'s linear resources are a sub-multiset of S₂'s (modulo structural embedding on individual facts). This is computable but requires defining embedding on content-addressed hashes — currently unexplored.

### 5.2 Proper generalization (MSG)

`computeControlHash` is a fixed abstraction function. Full supercompilation computes the Most Specific Generalization (MSG) of two configurations — the most precise common pattern. For linear multisets, MSG would find the largest common sub-multiset and abstract the remainder.

This is related to anti-unification on multisets — a known problem in the term indexing literature but not studied for linear resource multisets.

## 6. Prior Work on Supercompilation

| System | Domain | Resource model | Generalization |
|---|---|---|---|
| **SPSC** (Klyuchnikov) | First-order terms | None (free copy/discard) | HET + MSG |
| **SCP4** (Nemytykh) | Refal | None | HET + MSG |
| **Supero** (Mitchell) | Haskell Core | None (lazy copying) | Termination check |
| **sc-mini** (Bolingbroke-SPJ) | Core | None | HET + split |
| **This work** | ILL multisets | **Linear** (no copy/discard) | controlHash (coarse) |

No prior supercompiler handles linear resources. The closest is work on CHR confluence analysis (Frühwirth 2009), which reasons about multiset rewriting termination but does not perform supercompilation.

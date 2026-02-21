---
title: "Forward Chaining Networks"
created: 2026-02-21
modified: 2026-02-21
summary: "Production system algorithms (Rete, TREAT, LEAPS) and CHR compilation for forward chaining, with analysis of applicability to linear logic where facts are consumed."
tags: [Rete, TREAT, LEAPS, chr, forward-chaining, production-systems, linear-logic]
category: "Performance"
---

# Forward Chaining Networks

Production system algorithms for forward chaining with linear resources: Rete, TREAT, LEAPS, CHR. How they relate to CALC's forward engine.

**Cross-references:** [[forward-optimization-roadmap]], [[term-indexing]], [[clf-celf-ceptre]], [[de-bruijn-indexed-matching]]

---

## CALC's Current Forward Engine

CALC's forward chaining follows a simple loop:

```
repeat:
  candidates = getCandidateRules(state)    // strategy stack: opcode + predicate layer
  matches = [tryMatch(r, state) for r in candidates]
  if no matches: quiescent
  for each match:
    mutateState(state, consumed, produced)  // consume linear, produce new
    recurse (symexec tree exploration)
    undoMutate(state)                       // restore for next branch
```

Key properties:
- **No cached partial matches.** Every step re-evaluates all candidate rules.
- **Mutation+undo.** State is mutated in-place and restored on backtrack.
- **Incremental index.** `makeChildCtx` incrementally updates `stateIndex` (fact-by-predicate index).
- **No delta tracking.** All candidates are tried every step, regardless of what changed.

This is essentially **TREAT without the alpha network**: no caching, full re-evaluation at each step. Simple and correct, but O(rules × facts) per step.

---

## Rete Algorithm (Forgy, 1982)

### Architecture

Rete ("net" in Latin) builds a **persistent network** that tracks which rules can fire:

```
Facts → Alpha Network → Alpha Memories → Beta Network → Beta Memories → Conflict Set
```

**Alpha network.** Tests individual conditions: "is this fact a `pc(_)` fact?" Each alpha node filters facts by a single predicate/attribute test. Output: alpha memories (sets of facts matching one condition).

**Beta network.** Joins alpha memories pairwise: "for each `pc(X)` fact and `code(X, OP)` fact where the first arg matches..." Each beta node holds partial matches (tuples of facts + bindings that satisfy conditions so far). The final beta node holds complete matches.

**Incremental update.** When a fact is added:
1. Propagate through alpha network → add to relevant alpha memories
2. For each alpha memory changed, propagate through beta network → update beta memories
3. New complete matches enter the conflict set

When a fact is removed (retraction):
1. Remove from alpha memories
2. Propagate deletion through beta network → remove all partial matches that used this fact

### Complexity

| Operation | Rete | CALC current |
|-----------|------|-------------|
| Add fact | O(R × M) amortized | N/A (batch) |
| Remove fact | O(R × M) amortized | N/A (batch) |
| Find all matches | O(1) (read conflict set) | O(R × F) |
| Memory | O(N^K) worst case | O(N) |

R = rules, F = facts, N = facts, K = max conditions per rule, M = max partial match size.

### The Linear Logic Problem

In CALC, **consuming a linear fact** is the primary operation. Every step consumes 2-6 facts and produces 2-6 facts. This means:

1. **Frequent retraction.** Every step retracts consumed facts from the network. Rete's incremental benefit is partially offset by retraction cost.

2. **Partial match explosion.** With 100K facts and a rule with 5 conditions: beta memories can hold O(100K^5) partial matches in the worst case. Each consumed fact must be removed from all partial matches it participates in.

3. **Non-determinism.** CALC's symexec explores ALL possible rule firings (not just one). This means the conflict set is not resolved — all matches are needed. Rete's conflict resolution is irrelevant.

4. **Backtracking.** Symexec backtracks via mutation+undo. Rete has no built-in backtracking — the entire network state would need to be saved/restored.

**Verdict:** Rete is a poor fit for CALC. The memory overhead and retraction cost dominate at scale.

---

## TREAT Algorithm (Miranker, 1987)

### Key Insight

TREAT drops the beta network entirely. It keeps alpha memories but re-evaluates joins from scratch when needed.

```
Facts → Alpha Network → Alpha Memories → (join at fire time) → Conflict Set
```

When a fact is added/removed:
1. Update alpha memories (same as Rete)
2. Mark affected rules as "needs re-evaluation"
3. When a rule needs to fire: perform joins against current alpha memories

### Why Better for Linear Logic

1. **No retraction cost.** Removing a fact from alpha memory is O(1). No partial matches to invalidate.
2. **No memory explosion.** No beta memories → O(N) total memory (just alpha memories).
3. **Trade-off:** Rule activation is slower (must re-join), but join cost is paid only for rules that actually fire.

### Connection to CALC

CALC's `findAllMatches` is already TREAT-like:
- `stateIndex` (predicate-grouped facts) = alpha memories
- `tryMatch()` = join evaluation
- No beta memories anywhere

The difference: TREAT marks rules as "dirty" when facts change and only re-evaluates dirty rules. CALC re-evaluates all candidates every step. Adding dirty tracking would be a TREAT-style optimization.

### Implementation Sketch for CALC

```javascript
// At each step, track which predicates changed
const changedPreds = new Set();
// mutateState adds consumed/produced predicates to changedPreds

// Only re-evaluate rules whose trigger predicates overlap changedPreds
function findDirtyMatches(state, rules, changedPreds) {
  return rules.filter(r =>
    r.triggerPreds.some(p => changedPreds.has(p))
  );
}
```

This reduces candidate set from ALL rules to only rules affected by the last step's changes. For EVM execution (PC changes every step, affecting 1-2 predicates): ~90% of rules are unaffected and skipped.

---

## LEAPS (Miranker et al., 1990)

### Core Idea

LEAPS (Lazy Evaluation Algorithm for Production Systems) defers join evaluation even further than TREAT. Instead of maintaining alpha memories and re-joining, LEAPS:

1. Picks a "driving" condition for each rule
2. Iterates over facts matching the driving condition
3. For each driving fact, lazily evaluates remaining conditions

### Advantage

- Avoids building alpha memories for conditions that are never tested (because the driving condition already eliminates most candidates)
- Lower overhead for rules with highly selective first conditions

### Connection to CALC

CALC's deferral mechanism in `tryMatch()` is conceptually similar to LEAPS:
- Patterns that depend on persistent output vars are **deferred** until those vars are bound
- The "driving" pattern is the one without dependencies
- Remaining patterns are evaluated lazily after the driving pattern binds variables

The existing deferral mechanism IS a form of LEAPS within a single rule. Extending to cross-rule lazy evaluation would be the next step.

---

## CHR (Constraint Handling Rules)

### Simpagation as Linear Logic

CHR rules have three forms:

```
Simplification:  H <=> G | B       (consume H, produce B if guard G)
Propagation:     H ==> G | B       (keep H, produce B if guard G)
Simpagation:     H1 \ H2 <=> G | B (keep H1, consume H2, produce B if guard G)
```

Direct correspondence to ILL forward rules:

| CHR | ILL |
|-----|-----|
| `H <=> B` | `H -o {B}` (pure linear) |
| `H ==> B` | `!H -o {B}` (persistent antecedent) |
| `H1 \ H2 <=> B` | `!H1 * H2 -o {B}` (mixed) |
| Guard `G` | Persistent antecedent proved by FFI/backward |

**Example:** CALC's `evm/add`:
```
!inc PC PC' * !plus A B C    \    pc PC * code PC (i(e)) * sh(s(s(SH))) * stack(s(SH)) A * stack SH B
    <=>
    code PC (i(e)) * pc PC' * sh(s(SH)) * stack SH C
```

The persistent antecedents (`!inc`, `!plus`) are the "kept" head H1. The linear antecedents are the "consumed" head H2. This is simpagation.

### CHR Compilation

The standard CHR compilation strategy (Schrijvers & Demoen, 2004):

1. **Occurrence-based compilation.** For each constraint occurrence in a rule head, generate code that tries to complete the match.
2. **Partner search.** When a constraint is added, search for "partner" constraints to complete the rule.
3. **Propagation history.** Track which rule instances have fired to prevent re-firing.

In CALC terms:
- "Constraint added" = fact produced by mutateState
- "Partner search" = tryMatch's linear pattern matching
- "Propagation history" = not needed (linear facts are consumed, can't re-fire)

### CHR's Refined Operational Semantics

CHR specifies a precise operational semantics (Fruhwirth, 2009):
1. Process constraints left-to-right in the goal
2. For each new constraint, try rules top-to-bottom
3. First matching rule fires (committed choice)

CALC's `run()` uses the same committed-choice semantics. `findMatch()` returns the FIRST matching rule (not all). Only `findAllMatches()` in symexec explores all possibilities.

### CHR Optimizations Relevant to CALC

**Join ordering.** CHR compilers reorder conditions within a rule for efficiency. The most selective condition (fewest matching constraints) is tested first. CALC's deferral mechanism partially does this (defers patterns with unbound dependencies), but doesn't consider selectivity.

**Guard optimization.** When a guard is a simple check (e.g., `X > 0`), CHR compilers inline it. CALC's `tryFFIDirect()` is the analogous optimization — inline FFI checks instead of full backward proving.

**Suspension.** CHR suspends a constraint if no rule matches, reactivating it when partner constraints arrive. CALC doesn't suspend — it re-scans all facts every step.

---

## Comparison Table

| Aspect | Rete | TREAT | LEAPS | CHR | CALC current |
|--------|------|-------|-------|-----|-------------|
| **Alpha memories** | Yes | Yes | Implicit | Yes | stateIndex |
| **Beta memories** | Yes | No | No | No | No |
| **Incremental** | Full | Alpha only | Lazy | Alpha only | Index only |
| **Retraction cost** | O(partials) | O(1) | O(1) | O(1) | O(1) |
| **Memory** | O(N^K) | O(N) | O(N) | O(N) | O(N) |
| **Rule activation** | O(1) | O(join) | O(join) | O(join) | O(join) |
| **Linear logic fit** | Poor | Good | Good | Native | Good |
| **Backtracking** | No | No | No | No | Yes (undo) |

---

## What CALC Should Adopt

### From TREAT: Dirty Rule Tracking

Only re-evaluate rules whose trigger predicates overlap with changed facts. Implementation:

1. `mutateState` already knows which facts changed (consumed/produced hashes)
2. Map changed fact predicates → affected rules (via ruleIndex)
3. Only call `tryMatch()` for affected rules

**Estimated savings:** At 44 rules, EVM execution changes 3-4 predicates per step. Only ~5-10 rules are affected → 80% reduction in tryMatch calls.

### From CHR: Join Ordering

Reorder antecedent patterns in `tryMatch()` by selectivity. The most selective pattern (fewest matching facts in state) should be matched first.

Currently: patterns are matched in declaration order, with deferral for unbound dependencies. This misses selectivity-based ordering.

**Implementation:** In `compileRule()`, compute static selectivity estimates (number of concrete symbols in pattern). At runtime, use state index sizes for dynamic selectivity.

### From LEAPS: Delta-Driven Activation

Instead of scanning all candidates per step, maintain a queue of "activations" (fact, rule) pairs created when facts change:

```javascript
// When fact h is produced:
for (const rule of ruleIndex[pred(h)]) {
  activationQueue.push({ fact: h, rule });
}

// Main loop: process activations instead of scanning
while (activationQueue.length > 0) {
  const { fact, rule } = activationQueue.shift();
  if (tryMatch(rule, state, ...)) {
    applyMatch(state, ...);
    // Produced facts create new activations
  }
}
```

This is the standard CHR activation loop and the natural evolution of CALC's forward engine.

### NOT From Rete: Beta Memories

Beta memories are not worth the complexity for linear logic. The retraction cost and memory overhead make them impractical for a system where facts are consumed every step.

---

## Scale Analysis

| Scale | Current cost/step | With TREAT dirty | With CHR activation |
|-------|------------------|------------------|-------------------|
| 44 rules, 20 facts | ~0.95ms | ~0.5ms | ~0.3ms |
| 400 rules, 50 facts | ~10ms | ~2ms | ~0.5ms |
| 1000 rules, 200 facts | ~50ms | ~5ms | ~1ms |
| 1000 rules, 100K facts | ~500ms | ~50ms | ~5ms |

These are rough estimates. The key insight: **dirty tracking and delta-driven activation provide 10-100x improvement at scale**, far more than micro-optimizations like indexed theta.

---

## Research Directions

### CHR Abstract Machine (CHRiSM)

CHRiSM (Sneyers, 2010) adds probabilistic choice to CHR. Rules fire with specified probabilities. This connects to CALC's symexec tree — instead of exploring ALL branches, sample branches by probability. Potential for Monte Carlo tree search over execution trees.

### Constraint Store = Linear State

CHR's constraint store is analogous to CALC's linear state. The "built-in constraint store" (logical variables, equations) is analogous to CALC's persistent state. This suggests importing CHR optimizations wholesale.

### Tabled Forward Chaining

XSB Prolog's tabling memoizes computed results. Applied to forward chaining: if a state has been seen before (hash match), reuse the result. CALC's `pathVisited` set in symexec is a simple version of this (cycle detection). Full tabling would cache entire subtrees.

**Todo:** Investigate tabling for symexec — could dramatically reduce tree exploration for states that recur across different branches.

### Multi-Set Matching

CHR's `find_partner` must match constraints against a multi-set (multiple copies of the same constraint type). CALC faces the same issue with `consumed` counting in `tryMatch()`. CHR compilers have sophisticated partner search algorithms that could improve `tryMatch()`'s candidate iteration.

---

## References

- Duck, G.J. et al. (2004). *Compiling constraint handling rules.* In ICLP.
- Forgy, C.L. (1982). *Rete: A fast algorithm for the many pattern/many object match problem.* Artificial Intelligence 19(1).
- Fruhwirth, T. (2009). *Constraint Handling Rules.* Cambridge University Press.
- Miranker, D.P. (1987). *TREAT: A better match algorithm for AI production systems.* In AAAI '87.
- Miranker, D.P. et al. (1990). *On the performance of lazy matching in production systems.* In AAAI '90.
- Schrijvers, T. & Demoen, B. (2004). *The K.U.Leuven CHR system.* In CHR '04.
- Sneyers, J. (2010). *CHR(PRISM)-based probabilistic logic learning.* Theory and Practice of Logic Programming.
- Sneyers, J. et al. (2010). *As time goes by: Constraint Handling Rules — A survey of CHR research from 1998 to 2007.* Theory and Practice of Logic Programming 10(1).

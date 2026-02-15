# Incremental Matching and Semi-Naive Evaluation

Delta-driven techniques for avoiding redundant rule evaluation when facts change incrementally.

**Cross-references:** [[forward-chaining-networks]], [[term-indexing]], [[forward-optimization-roadmap]]

---

## The Problem

CALC's `findAllMatches()` tries ALL candidate rules against the ENTIRE state at every step. When only 3-4 facts change per step (out of ~20-200), most rules are re-evaluated against unchanged facts — redundant work.

At 44 rules this is fast. At 1000 rules × 100K facts: O(1000 × 100K) = catastrophic.

The solution from Datalog: **semi-naive evaluation** — only match rules against facts that changed since the last step.

---

## Semi-Naive Evaluation (Datalog)

### Core Idea (Bancilhon, 1986; Ullman, 1989)

In Datalog, rules derive new facts from existing facts. Naive evaluation re-derives everything each iteration. Semi-naive evaluation tracks the **delta** (new facts) each iteration and only applies rules to the delta.

For a rule `P(x) :- Q(x), R(x)`:
- **Naive:** At each iteration, try ALL Q facts × ALL R facts
- **Semi-naive:** At iteration i, try (new Q facts × all R facts) ∪ (all Q facts × new R facts)

Only facts derived in the PREVIOUS iteration are "new." This avoids re-deriving already-known facts.

### Formal Definition

Let `R(Δ, F)` denote applying rule R with delta Δ and full fact set F. Semi-naive computes:

```
F_0 = initial facts
Δ_0 = F_0

repeat:
  Δ_{i+1} = R(Δ_i, F_i) \ F_i    // new facts only
  F_{i+1} = F_i ∪ Δ_{i+1}
until Δ_{i+1} = ∅
```

At each iteration, only the delta is matched against rules. The key operation: `R(Δ_i, F_i)` means "try rule R where at least one antecedent matches a delta fact."

### Complexity

| Evaluation | Per iteration | Total |
|-----------|---------------|-------|
| Naive | O(R × F^K) | O(R × F^K × iterations) |
| Semi-naive | O(R × |Δ| × F^(K-1)) | O(R × total_derived × F^(K-1)) |

R = rules, F = facts, K = max antecedents, |Δ| = delta size per iteration.

For CALC: each step changes 3-10 facts (delta), total facts ~20-200. Semi-naive saves O(F/|Δ|) = ~5-50x per step.

---

## Application to CALC

### Current Architecture

```
findAllMatches(state, rules):
  candidates = strategy.getCandidateRules(state)     // O(1) opcode + O(R) predicate
  matches = [tryMatch(r, state) for r in candidates]  // O(candidates × facts)
  return matches
```

No delta tracking — every step re-evaluates all candidates.

### Delta-Driven Architecture

```
findDeltaMatches(state, rules, delta):
  // Only try rules whose trigger predicates overlap with delta
  dirtyRules = rules.filter(r => r.triggerPreds ∩ delta.changedPreds ≠ ∅)
  matches = [tryMatch(r, state) for r in dirtyRules]
  return matches
```

Where `delta = { added: Set<hash>, removed: Set<hash>, changedPreds: Set<string> }`.

### Implementation in CALC

**Step 1: Track delta in mutateState.**

`mutateState()` already knows which facts are consumed and produced. Extract the delta:

```javascript
function mutateState(state, consumed, theta, linearPats, persistPats) {
  const delta = { added: new Set(), removed: new Set(), changedPreds: new Set() };

  // Consume
  for (const hStr in consumed) {
    const hash = Number(hStr);
    delta.removed.add(hash);
    delta.changedPreds.add(getPredicateHead(hash));
    // ... existing consume logic
  }

  // Produce
  for (const pattern of linearPats) {
    const h = subApply(pattern, theta);
    delta.added.add(h);
    delta.changedPreds.add(getPredicateHead(h));
    // ... existing produce logic
  }

  return { undo, delta };
}
```

**Step 2: Use delta in findAllMatches.**

```javascript
function findAllMatches(state, rules, calc, strategy, stateIndex, delta) {
  if (!delta) {
    // First step: evaluate all (no delta yet)
    return fullFindAllMatches(state, rules, calc, strategy, stateIndex);
  }

  // Subsequent steps: only evaluate rules affected by delta
  const dirtyRules = [];
  for (const rule of rules) {
    for (const pred of rule.triggerPreds) {
      if (delta.changedPreds.has(pred)) {
        dirtyRules.push(rule);
        break;
      }
    }
  }

  return dirtyRules.map(r => tryMatch(r, state, calc)).filter(Boolean);
}
```

**Step 3: Integrate with symexec.**

In `explore()`, pass delta from `mutateState` to `findAllMatches`:

```javascript
const undo = mutateState(state, m.consumed, m.theta, linPats, persistPats);
const matches = findAllMatches(state, rules, calc, strategy, ctx.stateIndex, undo.delta);
```

### Estimated Impact

For EVM execution: each step changes `pc`, `sh`, `stack`, and sometimes `gas`, `storage`. That's 3-5 predicates. Of 44 rules, ~30 have `pc` as a trigger (but opcode layer handles those). The remaining 4 rules in predicateLayer: ~2 are affected by the changed predicates.

**Savings:** predicateLayer goes from trying 4 rules to trying ~2 rules per step. Marginal at 44 rules.

**At 1000 rules:** predicateLayer would try 1000 rules → with delta, ~50-100 rules. 10-20x improvement.

---

## Relational E-Matching (Zhang et al., 2022)

### Core Idea

Pattern matching in equality saturation systems (egg, egglog) is formulated as a **conjunctive query** over a relational database. Each pattern becomes a join of relations.

For a pattern `f(g(X), Y)`:
- Relation `f(id, child1, child2)` → join with
- Relation `g(id, child1)` → on `child1 = g.id`
- Variables X, Y → projected columns

The match is a **join**: `SELECT * FROM f, g WHERE f.child1 = g.id`.

### Worst-Case Optimal Joins (Ngo et al., 2012)

Standard nested-loop joins are O(N^K) for K relations. **Worst-case optimal joins** (generic join, Leapfrog TrieJoin) achieve O(N^(K/2)) by processing one variable at a time across all relations simultaneously.

For CALC's multi-antecedent patterns, this means:
- Instead of matching pattern 1, then pattern 2, then pattern 3 (nested loop)
- Process each **shared variable** across all patterns that mention it (leapfrog)

### Application to CALC

Each antecedent pattern in a CALC rule is a "relation." Shared variables (e.g., `_PC` appearing in `pc(_PC)` and `code(_PC, _OP)`) are join conditions.

**Example: evm/add**
```
pc(_PC)                  → R1(PC)
code(_PC, i(e))          → R2(PC, OP) where OP = i(e)
sh(s(s(_SH)))            → R3(SH)
stack(s(_SH), _A)        → R4(SH, A)
stack(_SH, _B)           → R5(SH, B)
```

Join graph:
- `_PC` shared between R1, R2 → join on PC
- `_SH` shared between R3, R4, R5 → three-way join on SH

**Leapfrog approach for _SH:**
1. Get all SH values from `sh(s(s(_)))` facts → {5, 7, 12}
2. For each SH: check if `stack(s(SH), _)` exists → intersect
3. For each surviving SH: check if `stack(SH, _)` exists → intersect

This is potentially faster than CALC's current sequential match (try all stack facts for each SH value).

### Implementation Complexity

Full relational e-matching requires:
1. Relations indexed by each column (multi-column indexes)
2. Leapfrog trie join iterator
3. Query compilation from patterns to join plans

~500-800 LOC. High complexity. Justified at 100K+ facts where join optimization matters.

### When It Matters

At 20 facts: sequential matching is fine. Each `tryMatch` does 5-10 `match()` calls × 3-5 candidates = ~50 calls. Fast.

At 100K facts: sequential matching tries thousands of candidates per pattern. Leapfrog join processes shared variables once across all patterns, eliminating redundant candidate iteration. 10-100x improvement.

---

## Souffle-Style Optimizations

### Automatic Index Selection (Scholz et al., 2016)

Souffle (a compiled Datalog engine) automatically selects which columns to index based on query patterns. For each relation R and set of bound variables in queries involving R, Souffle creates a B-tree index.

**Application to CALC:** For each predicate (pc, code, sh, stack, ...), analyze all rules to determine which argument positions are queried with bound values. Build appropriate indexes.

Currently: `buildStateIndex` only indexes by predicate head (1st-level). Adding per-predicate per-argument indexes (e.g., `stack` indexed by first argument) would speed up `tryMatch` candidate lookup.

### Compiled Datalog

Souffle compiles Datalog to C++. Rules become nested loops with indexed lookups. This is the "Stage 9 code tree" approach applied to all rules simultaneously.

**Connection to compiled match functions** (see [[compiled-pattern-matching]]): Souffle's compiled loops are essentially per-rule compiled match functions with optimized join ordering.

---

## Comparison of Incremental Techniques

| Technique | When to Apply | Improvement | Complexity |
|-----------|--------------|-------------|-----------|
| Delta predicate tracking | Always (cheap) | 2-10x at 100+ rules | ~30 LOC |
| Full semi-naive | 100K+ facts | 10-50x | ~200 LOC |
| Relational e-matching | 100K+ facts, complex joins | 10-100x | ~600 LOC |
| Souffle-style compilation | 1000+ rules, 100K+ facts | 100x+ | ~1000 LOC |

### Recommendation for CALC

1. **Now:** Add delta predicate tracking to `findAllMatches`. Cheap, helps at any scale.
2. **At 100+ rules:** Full semi-naive with delta fact sets.
3. **At 100K facts:** Relational e-matching or Souffle-style compilation.

---

## Research Directions

### Linear Logic and Semi-Naive

Standard semi-naive assumes monotonic derivation (facts only added, never removed). Linear logic is **non-monotonic** — facts are consumed. This means:

- The delta includes both additions AND removals
- A rule that matched at step i may NOT match at step i+1 (consumed antecedent)
- Semi-naive must re-check "old" matches when facts are removed

**Solution:** Track both positive delta (new facts) and negative delta (consumed facts). For negative delta: re-evaluate rules that previously matched with the consumed fact. This requires storing which facts contributed to each match (provenance tracking).

**Provenance tracking cost:** O(matches × antecedents) additional storage. For 63 steps × 44 rules × 5 antecedents: ~14K entries. Manageable.

### Incremental Matching in Symexec

Symexec explores a tree of states. Each child state differs from its parent by one rule application (delta of 3-10 facts). With delta tracking:

- Parent finds all matches
- Child only re-evaluates rules affected by the delta
- Most rules give the same result as parent → skip

This is essentially **memoized match evaluation** across the symexec tree. If a rule's trigger predicates didn't change between parent and child, the rule's match result is the same.

**Implementation:** Cache `tryMatch` results keyed by `(rule, relevantFactsHash)`. On delta, only invalidate cache entries for affected rules.

### Connection to Stage 7 (Delta Optimization)

Stage 7 already tracks which term positions change between antecedent and consequent (delta patterns). This is a per-rule micro-delta. Semi-naive tracks macro-deltas (which facts changed in the state).

Combining both: for rules identified as affected by the macro-delta, use micro-delta optimization (Stage 7) for the actual matching. Double optimization.

---

## References

- Bancilhon, F. (1986). *Naive evaluation of recursively defined relations.* In On Knowledge Base Management Systems.
- Ngo, H.Q. et al. (2012). *Worst-case optimal join algorithms.* In PODS '12.
- Scholz, B. et al. (2016). *On fast large-scale program analysis in Datalog.* In CC '16.
- Ullman, J.D. (1989). *Principles of Database and Knowledge-Base Systems.* Vol. 2. Computer Science Press.
- Willsey, M. et al. (2021). *egg: Fast and extensible equality saturation.* In POPL '21.
- Zhang, Y. et al. (2022). *Relational e-matching.* In POPL '22.

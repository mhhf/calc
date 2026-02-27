---
title: Speculative State Merging via Anti-Unification
created: 2026-02-27
modified: 2026-02-27
summary: Replace EVM-specific structural memo with general MSG-based state merging at oplus branch points
tags:
  - symexec
  - optimization
  - anti-unification
  - state-merging
  - forward-chaining
  - linear-logic
type: design
status: researching
priority: 4
cluster: Symexec
depends_on: []
required_by: []
---

# TODO 0056: Speculative State Merging via Anti-Unification

## Problem

At oplus branch points, `symexec.explore()` eagerly forks into all alternatives. When multiple alternatives lead to isomorphic subtrees (same control flow, differing only in data values), the tree explodes. The multisig contract demonstrates this: 6 member-check branches produce identical subtrees, inflating the tree from ~300 to 2125 nodes.

The current fix (`computeControlHash` on `pc` and `sh`) is an EVM-specific hack that hardcodes which predicates are "control." It works for the multisig but is not general:
- Turing-complete programs may differ in pc/sh and still be isomorphic (or vice versa)
- Non-EVM calculi have no pc/sh at all
- Rule changes could invalidate the assumption

## Corrected hevm Comparison

hevm's forward-jump merge (`EVM/Merge.hs`) does NOT collapse the member-check pattern. Nested JUMPIs during speculation trigger bail-out (`msActive` check). Actual hevm output on MultisigNoCall.sol:

| Tool | Nodes | Leaves | Time |
|---|---|---|---|
| hevm (actual) | 86 | 56 (36 Success, 20 Failure) | 50ms |
| calc (no memo) | 2125 | 31 (18 STOP, 13 REVERT) | 57ms |
| calc (structural memo) | 477 | 11 (1 STOP, 1 REVERT, 9 memo) | 15ms |

hevm has MORE leaves than calc because hevm explores checked-arithmetic overflow branches (SMT can't always prune them eagerly). calc's structural memo achieves 3.5x better node count than hevm on this contract.

The doc previously claimed "hevm: 7 nodes, 4 leaves" — this was incorrect. Verified by running `hevm symbolic --show-tree` (v0.54.2).

## Approaches Considered

### 1. Automatic Control Predicate Inference

Extract "control" predicates from the strategy stack (fingerprint config) and hash only those.

**Rejected.** Still an approximation: fingerprint predicates determine which rule fires, but don't capture the full bisimulation condition. EVM programs are Turing-complete — any predicate can affect control flow in principle. Generalizes the hack but doesn't eliminate it.

### 2. Symbolic Values with Lazy Branching

Represent unknown values as symbolic expression trees (ITE nodes) like hevm. Branch only when behavior actually diverges.

**Deferred (long-term).** Fundamentally incompatible with CALC's current architecture:
- Content-addressed store operates on ground terms + simple evars. ITE nodes would require compound symbolic expressions, a simplification engine, and deep inference changes.
- Fingerprint indexing requires ground PC values. Symbolic PCs (`ITE(cond, target, pc+1)`) would defeat O(1) code lookup, falling back to O(n).
- Pattern matching would need partial matching on symbolic terms.
- Not achievable within ILL theory without significant architectural changes.

Note: CALC already does a crude form of lazy evaluation for arithmetic (evar results when operands are symbolic). Extending to control flow is the hard part.

### 3. Speculative Merge via Anti-Unification (MSG) **[Recommended]**

At an oplus branch, speculatively execute each alternative forward. If they converge to the same "control shape," merge via anti-unification, creating evars for differing values. Continue with one merged state.

This is the CALC-native equivalent of hevm's ITE merging. Instead of `ITE(cond, v1, v2)`, we use a fresh evar. We lose condition tracking but gain full compatibility with the existing engine.

## Anti-Unification (MSG) Theory

**Most Specific Generalization** (Plotkin 1970): Given terms t1, t2, compute the most informative term `msg(t1, t2)` that subsumes both. Subterms where t1 and t2 differ are replaced by fresh variables. The same variable is used for the same pair of differences (preserving shared structure).

For content-addressed terms:

```
msg(h1, h2):
  if h1 == h2: return h1                    // identical (content-addressed)
  if memo[(h1,h2)]: return memo[(h1,h2)]    // already computed this pair
  t1 = Store.get(h1), t2 = Store.get(h2)
  if t1.tag != t2.tag or t1.arity != t2.arity:
    return memo[(h1,h2)] = fresh_evar()     // incompatible structure
  children = [msg(child(h1,i), child(h2,i)) for i in 0..arity]
  return memo[(h1,h2)] = Store.put(t1.tag, children)
```

For states (multisets of facts): group facts by predicate tag, pair within each group (by structural similarity), anti-unify each pair.

## Speculative Merge Algorithm

```
At multi-alt oplus with alternatives [A0, A1, ..., An]:

1. APPLY each alternative Ai to get resulting state Si
2. CHECK convergence:
   - Same predicate tag multiset (same stateIndex keys with same counts)
   - Same rules applicable (findAllMatches returns same rule names)
3. If converged:
   a. Compute msg(S0, S1, ..., Sn) — pairwise anti-unification
   b. Replace the multi-alt with one merged state
   c. Continue exploration from merged state
4. If not converged:
   Fall back to real branching (current behavior)
```

### Extended Speculation (hevm-style)

The immediate consequents of oplus alternatives usually differ (that's the point of oplus). Convergence happens further downstream. Extended speculation:

```
1. Apply each alternative Ai
2. Execute each Si forward (committed choice, bounded budget)
   until one of:
   - Same control shape as another Sj → convergence candidate
   - Budget exhausted → give up
   - Nondeterminism (multiple matches) → give up
3. At convergence point, compute MSG and merge
```

The budget limits speculation cost. hevm uses `mergeMaxBudget = 100` instructions.

**Complication:** hevm bails out on nested branches during speculation. CALC would face the same: if speculative execution hits another oplus, it must either bail out or handle nested speculation. Start with bail-out (hevm's approach), extend later.

## Precision Analysis

MSG replaces differing values with unconstrained evars. This can introduce spurious paths.

**Example:** States S0 has `eq(Sender, M0)`, S1 has `eq(Sender, M1)`. MSG produces `eq(Sender, _X)` where `_X` is unconstrained. If downstream code checks `eq(_X, M0)`, both `eq` and `neq` alternatives are explored — producing one extra branch vs the original.

**Impact on multisig:** No precision loss. Downstream branching depends on `AND(nonce, voteBit)` where `voteBit` is already symbolic regardless of which member matched. The merged state follows the same control flow as any individual member state.

**General case:** MSG is a sound overapproximation. The merged tree explores a superset of the behaviors of any individual unmerged tree. For verification (no false negatives), this is acceptable. False positives can occur when downstream branching depends on the merged-away values.

**Mitigation:** Only merge when speculation confirms that downstream computation is uniform in the differing values (hevm's soundness check: no side effects, same stack depth). This is the conservative approach.

## Connection to Prior Work

| Framework | CALC Equivalent |
|---|---|
| Anti-unification (Plotkin 1970) | MSG of content-addressed terms |
| Veritesting (Avgerinos ICSE 2014) | Speculative execution + merge at convergence |
| State merging (Kuznetsov PLDI 2012) | QCE cost estimation for merge decisions |
| Bisimulation (Milner 1989) | Exact characterization of isomorphic subtrees |
| Abstract interpretation (Cousot 1977) | Current `computeControlHash` is an abstraction function; MSG is a refinement |
| Supercompilation (Turchin 1986) | Homeomorphic embedding for termination; MSG for generalization |

## Implementation Plan

### Phase 1: Immediate MSG (no speculation)

Compare the immediate consequent states of multi-alt oplus. If same predicate shape, merge. Simple, handles cases where oplus alternatives produce structurally similar states.

- Add `tryMergeAlternatives(state, alternatives, theta, slots)` in `symexec.js`
- MSG operates on `{linear, persistent}` state diffs
- Return merged alternative or null (fall back to branching)

### Phase 2: Bounded speculation

Execute each alternative forward (committed choice) for up to N steps. Check convergence at each step. Merge when found.

- Add `speculateForward(state, rules, calc, budget)` — returns state after N committed-choice steps, or null
- Bail out on nondeterminism or oplus during speculation
- Convergence check: same set of predicate tags in stateIndex

### Phase 3: Replace structural memo

Once speculative merge handles the member-check pattern, `computeControlHash` becomes redundant. Remove the EVM-specific hack.

### Phase 4: Precision tracking (optional)

Track MSG origins: annotate merged evars with their source values. This recovers some precision lost by unconstrained evars. Related to predicate abstraction (Scheurer et al. ICFEM 2016).

## Open Questions

1. **Pairing problem:** When states have multiple facts with the same tag (e.g., multiple `stack` facts), which to pair for MSG? Heuristic: pair by maximum shared substructure. For EVM, stack height is unambiguous.

2. **N-way MSG:** For N > 2 alternatives, compute MSG pairwise or N-way? Pairwise is simpler: `msg(msg(S0, S1), S2)` but may lose shared structure. True N-way MSG (Plotkin) computes the join in the generalization lattice.

3. **Speculation budget:** What's the right budget? hevm uses 100 instructions. For CALC, measure on representative programs. Too low → misses convergence. Too high → wasted work on non-converging paths.

4. **Interaction with constraint solver:** Merged evars are unconstrained. The EqNeqSolver sees `eq(Sender, _X)` — should it treat this differently from a regular evar? Currently no special handling needed (evars are already unconstrained).

5. **Soundness of speculation:** Must verify that speculative execution doesn't observe/produce side effects that differ between alternatives. In CALC, "side effects" = different linear resource shape, different persistent facts. Check: same predicate tags with same counts after speculation.

---
title: Speculative State Merging via Anti-Unification
created: 2026-02-27
modified: 2026-03-03
summary: "Replace EVM-specific structural memo with general fingerprint-based control hash (~30 LOC, Phase 1). Speculation (Phases 2-3) analyzed and rejected for multisig pattern — adds ~21ms overhead with zero convergence. Phase 1 is the only actionable item: generalize computeControlHash to auto-detect control predicates from fingerprint config."
tags:
  - symexec
  - optimization
  - anti-unification
  - state-merging
  - forward-chaining
  - linear-logic
type: design
status: backlogged
priority: 3
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

| Tool | Branch nodes | Leaves | Total nodes | Time |
|---|---|---|---|---|
| hevm (actual) | 30 ITE | 31 (18 Success, 13 Failure) | 61 | 52ms |
| calc (no memo) | 30 oplus | 31 (18 STOP, 13 REVERT) | 2125 | 57ms |
| calc (structural memo) | 30 oplus | 11 (2 real, 9 memo) | 477 | 22ms |

hevm and calc have identical branching behavior: same 30 branch points, same 31 leaves, same 5 behavioral outcomes × 6 members. Neither tool merges per-member subtrees. The node count difference (61 vs 2125) is representation granularity: hevm compresses 50+ opcodes between JUMPIs into single ITE nodes; calc makes each opcode explicit.

Verified by running `hevm symbolic --show-tree` (v0.54.2).

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

**Algorithm** — two rewrite rules applied exhaustively:

1. **Decomposition:** Same root + same arity → recurse into children:
   `f(s1,...,sn) ⊔ f(t1,...,tn) = f(s1 ⊔ t1, ..., sn ⊔ tn)`

2. **Abstraction:** Different root/arity → fresh variable:
   `s ⊔ t = φ(s, t)` where φ is injective (same pair → same variable)

The injective mapping φ preserves structural sharing: `msg(f(a,a), f(b,b)) = f(X, X)` captures "both arguments are the same value."

**Complexity:** O(|t1| + |t2|) time and space — linear. For content-addressed terms, equality is O(1) (hash comparison), making the constant factor very small. Parallel complexity is NC (O(log² N) time) — in contrast to unification which is P-complete.

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

## Empirical Tree Analysis (multisig symbolic, 2026-02-27)

Measured on `multisig_nocall_solc_symbolic.ill` (6-member multisig, symbolic sender + nonce):

### Without structural memo (2125 nodes, 57ms)

| Metric | Value |
|---|---|
| Oplus branches | 30 |
| Branch rules | evm/jumpi: 12, evm/iszero: 18 |
| Det. chain lengths | min: 3, max: 89, median: 18, mean: 33.8 |
| Inter-branch steps | exactly 12 (very regular member-check loop) |

### With structural memo (477 nodes, 22ms)

| Metric | Value |
|---|---|
| Memo nodes | 9 |
| Steps from branch to memo | 6 (member jumpi→jump→memo), 51 (vote-recording path) |
| Branches leading to memo | 5 jumpi paths (6 steps each), 3 iszero paths (0 steps), 1 long path (51 steps) |

### State composition at leaves

| Category | Count | Notes |
|---|---|---|
| Linear facts total | 763 | |
| — `code` facts | 735 | Identical across all states (bytecode) |
| — `stack` facts | 11 | Variable depth, keyed by depth argument |
| — `calldata` facts | 4 | Identical across states |
| — Singleton predicates | 13 | pc, sh, gas, mem, memsize, etc. (1 each) |
| Persistent facts | 51 | eq, neq, plus, not, shl, shr, etc. |

**Key insight for MSG cost:** Of 763 linear facts, 735 are `code` (identical hash → trivially compared). Only ~30 non-code facts differ between states. MSG comparison cost is dominated by these ~30 facts: ~30 hash lookups + Store.get calls ≈ 1–3μs.

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

### Why Speculation is NOT Effective for the Multisig Pattern

The multisig member-check pattern creates branches that **diverge for many steps**:

```
evm/eq(Sender, Member01) → oplus:
  Alt 0: neq(Sender,M1) + stack(SH,0) → jumpi → eq(0,0) → pc=PC' (fall through)
                                        → continues checking Member02 (12+ steps)
  Alt 1: eq(Sender,M1) + stack(SH,1)  → jumpi → neq(1,0) → pc=NPC (jump)
                                        → vote-recording code (50+ steps)
```

Alt 0 and Alt 1 reach **different PC values** immediately (fall-through vs jump). They don't reconverge until alt 0 also reaches the vote code via a later member match — but that's 60-100 steps downstream, well beyond a reasonable speculation budget.

The 9 memo nodes in the structural-memo tree arise because:
- 5 member jumpi paths each take 6 deterministic steps (pop, push1, swap2, swap1, pop, jump) before hitting a previously-memoized control hash
- These are NOT convergence points of a single oplus — they're different oplus branches at different member checks that happen to reach the same downstream code

**Conclusion:** Speculative merge at the oplus level is the wrong tool for the member-check pattern. It targets **quick convergence** (if/else within a few steps). The member-check pattern requires **structural memoization** — detecting that independently-explored subtrees are isomorphic.

## Generalized Structural Memoization

The real replacement for `computeControlHash` is not speculative merge — it's a **generalized control hash** that works for any calculus.

### Current approach (EVM-specific)

```javascript
computeControlHash(stateIndex):
  pcVal = Store.child(stateIndex['pc'][0], 0)   // hardcoded 'pc'
  shHash = stateIndex['sh'][0]                   // hardcoded 'sh'
  return hash(pcVal, shHash)
```

### Generalized approach: fingerprint-based control hash

CALC already auto-detects the fingerprint configuration via `detectFingerprintConfig()` in match.js. This finds the dominant discriminator predicate (`code` for EVM) and its pointer predicate (`pc` for EVM). This detection is fully general — any calculus with a dominant discriminator gets a fingerprint config.

```javascript
computeControlHash(stateIndex, fpConfig):
  // Use auto-detected fingerprint pointer value
  if (fpConfig && fpConfig.pointerPred):
    pointerArr = stateIndex[fpConfig.pointerPred]   // e.g. 'pc'
    pointerVal = Store.child(pointerArr[0], 0)       // e.g. PC value
    // Include predicate tag multiset for structural context
    tagHash = hashPredicateTagCounts(stateIndex)
    return hash(pointerVal, tagHash)

  // No fingerprint: hash the full predicate tag multiset
  return hashPredicateTagCounts(stateIndex)
```

**Why include predicate tag counts?** Two states at the same PC but different stack depths (`sh` values) would have different `stack` fact counts. The tag multiset hash captures this without hardcoding `sh`. Similarly, states with different memory layouts have different `mem` fact structures, reflected in tag counts.

**Why the pointer value, not just tag counts?** The predicate tag multiset may be identical across many PCs (e.g., all arithmetic ops have the same tag profile). The pointer value discriminates between execution points. This is the same information currently hardcoded in `computeControlHash` but extracted automatically.

### With MSG Verification

The generalized control hash is a fast pre-check. For additional soundness, verify with MSG on hash collision:

```
At state entry in explore():
  1. Compute controlHash(stateIndex, fpConfig)     [O(|tags|), ~1μs]
  2. If controlHash in globalControl:
     a. Retrieve stored state S_prev from table
     b. Compute MSG(current, S_prev)                [O(|differing facts|), ~3μs]
     c. If MSG succeeds (same structure): return memo
  3. Explore normally
  4. On exit: store (controlHash, state snapshot) in globalControl
```

MSG verification catches false collisions from the control hash. Cost: O(|differing facts|) per collision, only on actual hits (9 hits for multisig = ~27μs total overhead).

## Open Questions — Resolved

### 1. Pairing Problem — Resolved: Key-Based Pairing

**Problem:** When states have multiple facts with the same tag (e.g., multiple `stack` facts), which to pair for MSG?

**Analysis from multisig state composition:**
- Of 763 linear facts, 735 are `code` — identical hashes across states (trivial: same hash = same fact)
- `stack` facts (11): keyed by depth argument `stack(depth, value)`. Depth is structural, value differs. Pair by matching first child (depth).
- `calldata` (4), `storage` (2): keyed by position/slot
- All other predicates have exactly 1 instance (pc, sh, gas, mem, memsize)

**General algorithm:**

```
pairFacts(tag, facts1, facts2):
  if facts1.length != facts2.length: return null  // can't merge

  // O(1) case: single instance per tag
  if facts1.length == 1: return [(facts1[0], facts2[0])]

  // Key-based pairing: group by first child hash
  byKey1 = groupBy(facts1, h => Store.child(h, 0))
  byKey2 = groupBy(facts2, h => Store.child(h, 0))
  if sameKeys(byKey1, byKey2):
    return zip(byKey1, byKey2)  // pair by key

  // Fallback: maximum structural similarity (bipartite matching)
  return hungarianMatch(facts1, facts2, structuralSimilarity)
```

**Literature:** Yernaux & Vanhoof (CSL 2022) show that variable-minimizing anti-unification of unordered atoms is NP-hard in general, but the **k-swap stability heuristic** (k=1) gives O(n²) near-optimal results. For CALC, the key-based pairing handles all practical cases in O(n).

### 2. N-way MSG — Resolved: Not Needed

**Problem:** For N > 2 alternatives, compute MSG pairwise or N-way?

**Finding:** All EVM oplus rules (`evm/eq`, `evm/iszero`, `evm/jumpi`) produce exactly **2 alternatives**. The 6-member pattern arises from **sequential 2-way oplus branches**, not a single 6-way oplus. The tree structure is:

```
eq(Sender, M1) → 2 alts
  alt 0 (neq): falls through → eq(Sender, M2) → 2 alts
    alt 0 (neq): falls through → eq(Sender, M3) → 2 alts
      ... (sequential binary choices)
  alt 1 (eq): jumps to vote code
```

N-way MSG would only apply if a single oplus had N > 2 alternatives. In ILL's binary `oplus`, alternatives are always pairs. Multi-way choice requires nested oplus (e.g., `A + (B + C)`), but `expandConsequentChoices` in compile.js flattens these into a list. Even then, EVM rules never produce more than 2.

**Conclusion:** Pairwise MSG (2-way) suffices. If future calculi introduce genuine N-way choice, pairwise folding `msg(msg(S0, S1), S2)` is acceptable — the information loss (pairwise may introduce two distinct evars where N-way would use one) is minor.

### 3. Speculation Budget — Resolved: Budget Not the Right Model

**Problem:** What's the right speculation budget?

**Finding from empirical analysis:** The multisig's inter-branch step count is exactly 12 (very regular member-check loop). But the two alternatives of each eq/jumpi branch **don't converge** — one falls through (12 steps to next member check), the other jumps to vote code (50+ steps to exit). Speculation with any budget would fail to find convergence.

Speculation is effective for a different pattern: **short-lived divergences** where both alternatives reach the same PC within a few steps (e.g., conditional assignment `x = cond ? a : b` where both paths continue to the same instruction).

**Budget recommendation if implemented:**
- **Budget 20** catches most if/else patterns (hevm's 100 is generous because hevm uses EVM opcodes as units; CALC uses forward rule applications, which are coarser)
- Cost per oplus: `2 × budget × cost_per_step` = `2 × 20 × 10μs` = 400μs
- For multisig (30 oplus branches): 30 × 400μs = 12ms overhead — comparable to total execution time
- **Important:** bail out IMMEDIATELY on nested oplus (no recursive speculation)

### 4. Constraint Solver Interaction — Resolved: No Special Handling

**Problem:** Should the EqNeqSolver treat merged evars differently?

**Analysis:** The solver already handles evars correctly:
- `addConstraint(h)` where h contains an evar: the constraint is recorded but can't be evaluated to ground truth
- `checkSAT()`: evar-containing constraints don't create forbid pairs (neither eq nor neq can be evaluated)
- Downstream branches produce normal eq/neq constraints on the evar

**Example:** MSG produces `!eq(Sender, _X)` where `_X` is a fresh evar. The solver:
1. Sees `eq(Sender, _X)` — neither arg is ground, no ground short-circuit
2. Performs `union(Sender, _X)` — merges equivalence classes
3. Later `!neq(_X, M3)` — recorded as forbid pair
4. `checkSAT()` — checks if find(\_X) = find(M3), which depends on other constraints

This is exactly the same behavior as for any symbolic value. **No solver changes needed.**

**Precision nuance:** The merged evar `_X` is less constrained than the original values (M1, M2, etc.). This means the solver won't prune branches that depend on which specific member matched. For the multisig, this doesn't matter (downstream code doesn't check the member identity). For other programs, this is the inherent precision cost of MSG.

### 5. Soundness of Speculation — Resolved: State Shape Check

**Problem:** How to verify that speculative execution is sound?

**Sufficient conditions for sound speculative merge:**

1. **Same predicate tag multiset** after speculation: same tags with same counts in stateIndex. This ensures the same rules are applicable and the same facts are consumed/produced.

2. **Deterministic speculation**: each step has exactly one matching rule (committed choice). If `findAllMatches` returns > 1 match, bail out.

3. **No nested oplus**: if speculation hits another oplus branch, bail out. (hevm's approach — nested JUMPIs during speculation trigger `msActive` bail-out.)

4. **Same matching rules**: after speculation, `findAllMatches` returns the same rule names for both states. This is a stronger check than tag multiset — it also verifies that persistent antecedent proving succeeds/fails identically.

**In CALC's linear logic framework:** "side effects" = changes to linear resource shape (fact tags/counts) + changes to persistent fact set. Condition 1 verifies linear equivalence. Persistent facts can be checked separately: same persistent tag multiset after speculation.

**What about the constraint solver?** Speculative execution adds constraints (from persistent facts produced during speculation). If the two alternatives produce different persistent facts, their constraint solver states diverge. After merge, the solver should contain only constraints present in BOTH alternatives. Implementation: checkpoint solver before speculation, restore after, then add only the MSG'd persistent facts.

## Connection to Prior Work

| Framework | CALC Equivalent |
|---|---|
| Anti-unification (Plotkin 1970) | MSG of content-addressed terms |
| Veritesting (Avgerinos ICSE 2014) | Speculative execution + merge at convergence |
| State merging (Kuznetsov PLDI 2012) | QCE cost estimation for merge decisions |
| Bisimulation (Milner 1989) | Exact characterization of isomorphic subtrees |
| Abstract interpretation (Cousot 1977) | Current `computeControlHash` is an abstraction function; MSG is a refinement |
| Supercompilation (Turchin 1986) | Homeomorphic embedding for termination; MSG for generalization |
| Multiset anti-unification (Yernaux & Vanhoof, CSL 2022) | Pairing problem for states as atom multisets |
| Precise state merging (Steinhöfel 2020) | Lattice model for merge precision vs cost |

### Supercompilation Connection

Supercompilation (Turchin 1986, Sørensen & Glück 1995) uses MSG in its generalization step. When the homeomorphic embedding whistle fires (term ti embeds in later term tj, signaling potential non-termination), the supercompiler computes MSG(ti, tj) and restarts with the generalized term.

CALC's structural memoization is analogous: when a state with the same control hash appears twice, the second occurrence is a "generalization point" — we've already explored what happens from this control configuration and can reuse the result.

The key difference: supercompilation generalizes to PREVENT non-termination. CALC memoizes to AVOID redundant computation. Both use the same mathematical tool (MSG) for different purposes.

### Veritesting vs Speculative Merge

Veritesting (Avgerinos ICSE 2014) switches between Dynamic Symbolic Execution (forking at every branch) and Static Symbolic Execution (merging paths through "easy" CFG regions). The switch happens at **transition nodes** — points where the CFG becomes hard (system calls, indirect jumps, loops).

CALC's exploration is closer to veritesting's DSE mode. Speculative merge would add SSE-like behavior for specific oplus patterns. The key difference: veritesting uses the CFG structure (static analysis) to identify merge regions. CALC would use dynamic convergence detection (same predicate tag multiset after N steps).

### State Merging Cost Model (Kuznetsov PLDI 2012)

Kuznetsov's **Query Count Estimation (QCE)** statically estimates the downstream cost of merging two states. Variables that appear in many future branch conditions should NOT be merged (the resulting ITE expressions would appear in many solver queries).

In CALC, this translates to: evars that appear in many future oplus branch alternatives should not be MSG'd. However, CALC doesn't use an SMT solver — evars branch unconditionally at every eq/neq check. So the cost model is simpler: merging always increases the number of branches by (at most) the number of downstream oplus points that test the merged value.

For the multisig: the merged value (`_X` replacing specific member addresses) is never tested downstream → 0 extra branches → merging is always beneficial.

## Performance Estimates

### Generalized structural memo (replacing computeControlHash)

| Operation | Cost | Frequency | Total |
|---|---|---|---|
| Fingerprint-based control hash | ~1μs | 477 per tree | ~0.5ms |
| Predicate tag count hash (fallback) | ~5μs | 477 per tree | ~2.4ms |
| MSG verification on collision | ~3μs | 9 hits | ~27μs |
| Map lookup | ~0.1μs | 477 per tree | ~48μs |
| **Total (fingerprint path)** | | | **~0.6ms** |
| **Total (tag count fallback)** | | | **~2.5ms** |

Current `computeControlHash` cost: ~0.3ms. Generalized version adds ~0.3ms (fingerprint path) or ~2.2ms (fallback path). Both well within the 22ms total budget.

### Speculative merge (if implemented for short-convergence patterns)

| Operation | Cost | Frequency | Total |
|---|---|---|---|
| State snapshot (for rollback) | ~50μs | 30 oplus × 2 alts | ~3ms |
| Speculative steps (budget=20) | ~10μs/step | 30 × 2 × 20 | ~12ms |
| Convergence check per step | ~5μs | 30 × 2 × 20 | ~6ms |
| MSG on convergence | ~3μs | ~0 (multisig never converges) | ~0 |
| **Total (multisig, budget=20)** | | | **~21ms** |

**Verdict:** Speculative merge adds ~21ms to multisig execution (currently 22ms) with zero benefit (no convergence found). It would only help programs with short-lived oplus divergences.

### Cost comparison

| Approach | Multisig time | Generality | Implementation complexity |
|---|---|---|---|
| Current (PC+SH hash) | 13.6ms | EVM only | Low (done) |
| Generalized fingerprint hash | ~14ms | Any fingerprint calculus | Low |
| Fingerprint + MSG verify | ~14ms | Any calculus | Medium |
| Speculative merge (budget=20) | ~35ms | Any oplus pattern | High |
| Speculative merge + gen. memo | ~36ms | Both patterns | High |

(Times updated to reflect structuralMemo=true baseline of 13.6ms per TODO_0058 profiling.)

### Impact on combined optimization pipeline (solc symbolic multisig)

**Phase 1 (generalized controlHash): 0ms savings.** Same performance as current EVM-specific hash for the multisig benchmark. Value is generality — enables structural memo for non-EVM calculi without per-calculus code.

**Speculative merge: negative value for multisig** (adds ~21ms overhead with zero convergence). Only beneficial for contracts with short-lived oplus divergences (if/else converging within ~20 steps). Not included in combined optimization estimate.

## Revised Implementation Plan

### Phase 1: Generalize computeControlHash (low risk, high value)

Replace hardcoded `pc`/`sh` lookup with auto-detected fingerprint config:

```javascript
function computeControlHash(stateIndex, fpConfig) {
  if (fpConfig && fpConfig.pointerPred) {
    const pArr = stateIndex[fpConfig.pointerPred];
    const pVal = (pArr && pArr.length > 0) ? Store.child(pArr[0], 0) : 0;
    // Tag count hash provides structural context (replaces hardcoded 'sh')
    let tagHash = 0;
    for (const key of Object.keys(stateIndex)) {
      if (key[0] === '_') continue;
      tagHash = Math.imul(tagHash ^ stateIndex[key].length, 2654435761);
    }
    return (Math.imul(pVal | 0, 2654435761) ^ tagHash) >>> 0;
  }
  // No fingerprint: full predicate tag multiset hash
  let h = 0;
  for (const key of Object.keys(stateIndex)) {
    if (key[0] === '_') continue;
    h ^= hashFactEntry(stringHash(key), stateIndex[key].length);
  }
  return h;
}
```

Pass `fpConfig` from strategy detection (already available in `explore()` at line 550):
```javascript
const strategy = opts.strategy || detectStrategy(ruleList);
// strategy.fpConfig is auto-detected, null for non-fingerprint calculi
```

**Test plan:** Run multisig benchmark before/after. Verify same memo behavior. Add test with non-EVM calculus to verify fallback path.

**Expected impact:** Same performance as current. Removes EVM-specific hardcoding. Works for any calculus with a dominant discriminator predicate.

### Phase 2: MSG verification layer (optional, adds soundness guarantee)

Add MSG verification on control hash collision before memoizing:

```javascript
// In explore(), replace simple globalControl.get(ch) check:
if (globalControl.has(ch)) {
  const prev = globalControl.get(ch);
  if (prev.complete && tryMSG(state, prev.state) !== null) {
    return { type: 'memo', state: snapshotState(state) };
  }
}
```

`tryMSG(state1, state2)` returns the merged state if structural equivalence holds (same tags, same counts, same recursive structure), or null if states are too different.

**When is this needed?** Only when the control hash has false positives — two states with the same fingerprint value and tag counts but different subtree behavior. For EVM, this would occur if two different instructions at different PCs happened to produce the same tag profile. Unlikely but theoretically possible.

### Phase 3: Speculative merge for short-convergence patterns (independent)

Add `trySpeculativeMerge()` to the multi-alt handler in `explore()`:

```javascript
// In the multi-alt block (line 669), before branching:
if (satAlts.length === 2) {
  const merged = trySpeculativeMerge(state, m, satAlts, solver, strategy, ...);
  if (merged) {
    // Apply merged state, continue as single-alt
    children.push({ rule: m.rule.name + '/merged', child: go(depth + 1, merged.ctx) });
    continue;  // skip normal branching
  }
}
```

`trySpeculativeMerge()`:
1. Snapshot state for each alternative
2. Apply each alternative
3. Run committed-choice forward (budget=20)
4. Check convergence at each step (same predicate tag multiset)
5. If converged: compute MSG, return merged state
6. If budget exceeded or nested oplus hit: return null (bail out)

**When is this useful?** Programs with short conditional patterns:
```
cond -o {
  (!eq C 0 * result 1) +
  (!neq C 0 * result 0)
}
...
use_result Result -o { ... }  // same rule fires regardless of Result value
```

Both alternatives produce the same tag profile after 1 step. MSG replaces `result 1`/`result 0` with `result _X` and continues with one state.

### Phase 4: Precision tracking (optional, future)

Track MSG origins by annotating merged evars:
- `_X` was created from `(M1, M2)` at oplus branch at depth D
- If downstream code tests `_X`, we know the original alternatives
- Could recover precision by splitting back into concrete branches (lazy evaluation)

Related to predicate abstraction (Scheurer et al. ICFEM 2016) and value summaries (MultiSE, Sen et al. ESEC/FSE 2015). The value summary approach replaces each evar with a set of `{guard, value}` pairs — equivalent to ITE but without an SMT solver.

## Remaining Open Questions

1. **Non-EVM validation:** The generalized control hash needs testing on non-EVM calculi. Does the `detectFingerprintConfig` fallback (no fingerprint → tag multiset hash) produce useful memoization? Are there calculi where the tag multiset is too coarse (false positives) or too fine (no memoization)?

2. **Code fact count variation:** In the multisig, `code` fact counts can differ between member paths because the getMemberBit loop consumes and re-produces code facts at different rates. The current `computeControlHash` ignores code counts (only hashes PC+SH). The generalized version hashes tag counts including code. Need to verify this doesn't break memoization for patterns where code counts legitimately differ without affecting behavior.

3. **Interaction between speculation and memoization:** If speculative merge is implemented alongside generalized structural memo, which takes priority? Proposal: speculation first (at the oplus decision point), memoization second (at the state entry point). Speculation catches short-lived divergences before they branch. Memoization catches long-lived isomorphic subtrees after exploration.

4. **Benchmarking strategy:** Need programs beyond multisig to validate. Candidates:
   - EVM contracts with if/else patterns (speculation target)
   - Non-EVM ILL programs with repetitive structure (memoization target)
   - Programs with no isomorphic subtrees (should not regress)

## References

- Plotkin, G.D. (1970). A note on inductive generalization. Machine Intelligence 5, 153–163.
- Avgerinos, T. et al. (2014). Enhancing symbolic execution with veritesting. ICSE 2014.
- Kuznetsov, V. et al. (2012). Efficient state merging in symbolic execution. PLDI 2012.
- Yernaux, G. & Vanhoof, W. (2022). Anti-unification of unordered goals. CSL 2022.
- Steinhöfel, D. (2020). Precise symbolic state merging.
- Sen, K. et al. (2015). MultiSE: Multi-path symbolic execution using value summaries. ESEC/FSE 2015.
- Sørensen, M.H. & Glück, R. (1995). An algorithm of generalization in positive supercompilation. ILPS 1995.
- Cerna, D. & Kutsia, T. (2023). Anti-unification and generalization: A survey. IJCAI 2023.
- Kutsia, T., Levy, J., & Villaret, M. (2014). Anti-unification for unranked terms and hedges. Journal of Automated Reasoning.

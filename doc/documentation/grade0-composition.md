---
title: "Grade-0 Cut Elimination — Compile-Time Composition Pipeline"
created: 2026-04-07
modified: 2026-04-08
summary: Multi-pass compile-time pipeline eliminating grade-0 intermediates via SELL cut admissibility, with basic block fusion, chain strength reduction, McCarthy normalization, and SROA.
tags: [cut-elimination, forward-chaining, graded-types, SELL, implementation, architecture, specialization, optimization]
---

# Grade-0 Cut Elimination

`lib/engine/compose.js` is a calculus-agnostic compile-time optimization pipeline. Rules connected through grade-0 predicates (`!_0`) are composed, specialized, fused, and scalarized before runtime. All domain-specific knowledge (predicate names, number representations) is injected via configuration objects — see `lib/engine/ill/compose-config.js` for the ILL-specific defaults.

## Three-Layer API

```
L1: composePair        — atomic linear cut elimination (grade-agnostic)
    specializePersistent — atomic persistent specialization (ground fact → goal)
    fuseLinearPair       — atomic linear fusion (shared threading predicate)
L2: buildPredicateMap   — analysis (producers/consumers/bridges per grade-0 pred)
    buildEliminationOrder — dependency DAG → Kahn's topological sort
L3: composeGrade0       — multi-pass scheduler → ComposeResult
```

**L1** operations are single cut steps. Each takes two rules and a cut predicate, produces one composed rule or null. Alpha-renames, flattens, unifies the cut formula, merges with θ applied. Three variants for the three cut shapes (linear type, persistent fact, linear threading).

**L2** builds the data structures L3 needs: predicate maps classifying rules as producers/consumers/bridges, and elimination orders via Kahn's algorithm on the dependency DAG.

**L3** orchestrates the full pipeline described below.

## Pipeline

```
Parse → Compile → composeGrade0() → Compile² → Filter → Execute
```

`composeGrade0` runs 7 passes (some conditional):

```
Pass 1:   Linear composition — grade-0 types via composePair (N×M product)
Pass 2:   Persistent specialization — grade-0 facts via specializePersistent
          (multi-stage: DAG-ordered, with compile-time tabling for clauses with premises)
Pass 3+4: Batch residual resolution — safety net for remaining resolvable goals
Pass 5:   Basic block fusion — 1:1 producer→consumer linear chain merging
Pass 5.5: Additive chain fusion — algebraic strength reduction on threading chains
Pass 5.6: Second residual resolution — catch goals grounded by fusion
Pass 6:   McCarthy normalization + SROA — peel acons, scalarize arrays
Pass 6.5: Post-SROA residual resolution — resolve goals grounded by scalarization
```

Passes 5–6.5 require `opts.fuseBasicBlocks = true` and appropriate configs. Each residual resolution pass is idempotent and catches goals that became ground in the preceding transformation.

## Pass Details

### Pass 1: Linear Composition

Pairs producer rules (grade-0 in consequent) with consumers (grade-0 in antecedent) via `composePair`. N producers × M consumers → N×M composed rules. Grade-0 modality admits contraction (SELL structural rule W=C={0,ω}).

Defense-in-depth: composed rules with residual grade-0 content are filtered out with diagnostic errors.

### Pass 2: Persistent Specialization

Grade-0 clauses (backward rules marked `grade0: true`) are resolved into ground facts via compile-time tabling (`resolveAll` — backward proof search). External facts can be injected via `extraGrade0Facts`. A `scopeGuard` callback restricts specialization per-rule.

Elimination order is computed via Kahn's topological sort on the dependency DAG: if predicate A's clauses depend on predicate B, B is eliminated first. Cycles are rejected.

Fact lookup uses argument indexes for O(1) dispatch when fact sets are large.

### Pass 3+4: Residual Resolution

`_resolveResidualBatch` iterates the pool, calling `_resolveResidualOnce` per rule. Each invocation pre-sorts persistent goals by mode metadata (ground-first), then resolves in a single pass with a running substitution θ. Resolved goals are removed; the rule is reassembled via `_makeRule`.

### Pass 5: Basic Block Fusion

`_fuseBasicBlocks(pool, rc, getModeMeta, cutPred)` merges rules chained through a configurable linear threading predicate. A rule producing `pred(V)` in its consequent can fuse with the unique consumer of `pred(V)` in its antecedent — equivalent to CFG basic block merging. Uses `fuseLinearPair` for each cut step. Chains are followed greedily; hidden producers inside oplus/with/exists are excluded (the consumer rule is still needed for runtime choice paths).

Theory: each fusion is a cut step on the linear fragment — justified by ILL cut elimination.

### Pass 5.5: Additive Chain Fusion

`_fuseAdditiveChains(pool, rc, getModeMeta, chainConfigs)` collapses persistent threading chains algebraically. When persistent goals form chains (output feeds input of next), the chain is replaced by a single accumulated goal:

```
step(X,Y) * step(Y,Z) → fused(X, 2, Z)      (unary step)
sub(G,3,G2) * sub(G2,5,G3) → sub(G,8,G3)     (binary accumulate)
```

Safety: intermediate metavars must not appear elsewhere in the rule (linear antecedent, consequent, or other persistent goals). Each `ChainConfig` descriptor specifies predicate names, argument positions, and `parseConstant`/`buildConstant` callbacks for number representation.

### Pass 6: McCarthy Normalization + SROA

Two linked transformations:

1. **McCarthy normalization** (`_mccarthyNormalize`): peels `acons` layers from array-access goals using read-head/read-tail/write-head/write-tail rewrite rules. Replaces `arr_get(acons(H,T), 0, V)` with `V=H`, and shifts indices for tail access. Produces goals with ground indices on flat arrays. These rules are a list-based recursive encoding of McCarthy's select/store axioms (McCarthy 1962; Stump et al. 2001), which are originally stated as first-order logic axioms over flat arrays: `select(store(a,i,v),i)=v` and `select(store(a,i,v),j)=select(a,j)` when `i≠j`. Our `acons(H,T)` head-tail decomposition is semantically equivalent for ground non-negative integer indices and forms a convergent conditional rewrite system on ground terms (terminating by structural recursion on list depth, confluent with no critical pairs when indices are ground).

2. **SROA** (`_trySROA`): once McCarthy normalization grounds all array indices, the linear resource holding the array (e.g., `stack(acons(A,acons(B,empty_stack)))`) is expanded into individual scalar slots (`slot_0(A) * slot_1(B)`). Array-access goals become direct bindings. Configured via `SROAConfig`: `arrayPreds`, `resourcePred`, `parseIndex`/`buildIndex`.

Theory: replacement strategy — SROA'd rules replace originals. Out-of-bounds access stalls (no matching rule) in both versions, so no behavioral difference.

## Configuration

All domain-specific behavior is injected via `opts`:

| Option | Type | Purpose |
|--------|------|---------|
| `residualResolver` | `(goalHash) → factHash \| null` | Resolve persistent goals at compile time |
| `fuseBasicBlocks` | `boolean` | Enable passes 5–6.5 |
| `linearFusionPredicate` | `string` | Threading predicate for block fusion |
| `chainFusionPredicates` | `ChainConfig[]` | Chain fusion descriptors |
| `sroaConfig` | `SROAConfig` | Array/resource config for SROA |
| `canonicalize` | `(hash) → hash` | Normalize terms after tabling resolution |

ILL defaults are injected in `lib/engine/index.js` from `lib/engine/ill/compose-config.js`.

## Caching

Two caches survive across `composeGrade0` calls within the same process:

- **Tabling cache** (`_tablingCache`): keyed on clause+definition hashes. Caches `resolveAll` results (compile-time backward search is expensive).
- **Full compose cache** (`_composeCache`): keyed on all inputs. Returns complete `ComposeResult` for identical Store content.

Both invalidated on `Store.clear()` via the `onClear` hook.

## Diagnostics

`ComposeResult.diagnostics`:

| Field | Meaning |
|-------|---------|
| `pairsAttempted` | Total (producer, consumer) pairs tried |
| `pairsSucceeded` | Pairs that produced composed rules |
| `pairsSkipped` | Unification failures (normal, not errors) |
| `specializations` | Persistent specialization count |
| `grade0Predicates` | Predicate names composed through |
| `residualResolutions` | Goals resolved by residual passes |
| `fusedRuleReduction` | Rules eliminated by basic block fusion |
| `fuseChainLengths` | Lengths of fused basic block chains |
| `sroaTransformed` | Rules transformed by SROA |
| `mccarthyNormalized` | Rules with McCarthy-normalized array goals |
| `errors` | Validation failures |

## Theory

Each `composePair`/`fuseLinearPair` call is one cut step on the SELL calculus (Nigam-Miller PPDP 2009). SELL cut admissibility ensures each step preserves derivability. Grade-0 non-interference (Atkey 2018; Choudhury et al. POPL 2021) justifies that grade-0 intermediates are compile-time scaffolding with no runtime effect. See THY_0015 for the stratified cut elimination proof and THY_0016 for the partial evaluation / Futamura projection framework.

## Version History

| Version | TODO | What changed |
|---------|------|-------------|
| v1 | TODO_0156 | Single-pass linear composition (L1 + L2 + L3) |
| v2 | TODO_0158 | Multi-stage DAG composition with Kahn's sort |
| v3 | TODO_0159 | Grade-0 persistent facts and tabling |
| v4 | TODO_0160 | External fact injection, scope guards, tabling cache |
| v5 | TODO_0164 | Basic block fusion, chain fusion, McCarthy + SROA, residual resolution, generalization |

## Files

| File | Role |
|------|------|
| `lib/engine/compose.js` | Calculus-agnostic pipeline: L1 + L2 + L3 (7 passes) |
| `lib/engine/resolve-all.js` | Compile-time backward proof search (tabling), lazy-loaded |
| `lib/engine/ill/compose-config.js` | ILL-specific configs: chain fusion, SROA |
| `lib/engine/ill/residual-resolver.js` | ILL-specific residual resolver (FFI + clause fallback) |
| `lib/engine/index.js` | Integration: compose pass in `_buildCalc()`, ILL defaults |
| `lib/engine/grades.js` | Grade constants (GRADE_0, GRADE_W) |
| `lib/engine/compile.js` | flattenAntecedent, hasGrade0, discriminator detection |
| `tests/engine/compose.test.js` | L1, L2, L3 integration tests |
| `tests/engine/compose-chain-fusion.test.js` | Additive chain fusion tests |
| `tests/engine/compose-inc-fusion.test.js` | Inc-specific chain fusion tests |
| `tests/engine/compose-batch-resolve.test.js` | Residual resolution tests |
| `tests/engine/sroa.test.js` | McCarthy normalization + SROA tests |
| `benchmarks/engine/specialization-bench.js` | Specialization benchmark |

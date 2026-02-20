---
title: "Forward Chaining Engine — Implementation"
created: 2026-02-18
modified: 2026-02-18
summary: How the CALC forward chaining engine works — files, functions, data flow, optimizations, design decisions.
tags: [implementation, forward-chaining, engine, architecture]
---

# Forward Chaining Engine — Implementation

## 1. Overview

The forward chaining engine executes ILL programs by multiset rewriting. A state (multiset of linear + persistent facts) is transformed by rules until quiescence (no rules fire). Two modes of operation:

- **Single-path** (`forward.run`): committed choice — fires first matching rule, one execution path
- **Exhaustive** (`symexec.explore`): explores ALL execution paths — branches at every non-deterministic choice, builds an execution tree

Both share the same matching and state-manipulation machinery; they differ only in exploration strategy.

## 2. File Map

```
lib/engine/
├── index.js           # Public API: load(), exec(), prove()
├── convert.js         # .ill parser → content-addressed hashes
├── compile.js         # Rule compiler: raw rule → compiled rule with indexes
├── forward.js         # Matching + execution: tryMatch, findMatch, applyMatch, run
├── symexec.js         # Exhaustive exploration: explore(), strategy stack, mutation+undo
├── rule-analysis.js   # Static analysis: delta detection, pattern roles, compiled substitution
├── disc-tree.js       # Discrimination tree indexing for rule selection
├── prove.js           # Backward chaining prover (called for persistent antecedents)
├── show.js            # Debug: show(hash), classifyLeaf(), showInteresting()
├── hex.js             # Hex notation expansion
└── ffi/               # Foreign function interface
    ├── index.js       # FFI registry
    ├── arithmetic.js  # Arithmetic FFI: plus, inc, mul, neq, eq, lt, ...
    ├── mode.js        # Mode checking (+ = ground input, - = computed output)
    └── convert.js     # Binary ↔ BigInt conversion
```

## 3. Data Flow: From .ill to Execution

### 3.1 Loading

```
.ill file → convert.load() → { types, clauses, forwardRules, queries }
                                   │           │           │
                                   │           │    raw rules { name, hash,
                                   │           │    antecedent, consequent }
                                   │           │           │
                                   │           │    compile.compileRule()
                                   │           │           │
                                   │           │    compiled rules with indexes,
                                   │           │    slots, analysis metadata
                                   │           │
                                   │    backward-chaining     forward rules
                                   │    clauses (inc, plus)   (EVM opcodes)
                                   │           │
                                   │    prove.buildIndex()
                                   │           │
                                   │    clause index for
                                   │    backward proving
```

`convert.js` parses .ill files via tree-sitter, converting expressions to content-addressed hashes (`Store.put`). It classifies declarations:
- **Has monad** (`{...}` in consequent) → forward rule
- **Has premises** (`<- ...`) → backward clause
- **Neither** → type/constructor

### 3.2 Rule Compilation (`compile.js`)

`compileRule(rule)` transforms a raw rule into a compiled form optimized for matching:

```
Input:  { name: 'evm/add', hash, antecedent: loli_hash, consequent: monad_hash }

Processing:
1. flattenTensor(antecedent)  → { linear: [pc_pat, code_pat, stack_pat, ...],
                                   persistent: [inc_pat, plus_pat] }
2. unwrapMonad(consequent)    → tensor body
3. flattenTensor(body)        → { linear: [...], persistent: [...] }
4. Extract triggerPreds        → ['pc', 'code', 'stack', ...]  (for rule indexing)
5. Detect discriminator        → { pred: 'code', groundPos: 1, groundValue: 0x01 }
6. Collect metavars            → Set of all freevar hashes
7. Assign de Bruijn slots      → { _PC: 0, _PC': 1, _GAS: 2, ... }
8. analyzeDeltas()             → which linear patterns are preserved (appear in both ante/conseq)
9. computePatternRoles()       → per-pattern: delta bypass info, binding slots, ground checks
10. compileSubstitution()      → per-consequent-pattern: compiled recipe for Store.put
11. expandConsequentChoices()  → if with/plus in consequent, pre-expand all alternatives

Output: compiled rule with all metadata for O(1) decisions during matching
```

### 3.3 The `expandItem` / `expandConsequentChoices` Mechanism

When a rule's consequent contains additive connectives (`&` or `⊕`), the alternatives must be enumerated at **compile time** (stored in `rule.consequentAlts`). `expandItem(h)` recursively walks the consequent, distributing through tensor and splitting at with/plus:

```
expandItem(tensor(A, B))  = cross product of expandItem(A) × expandItem(B)
expandItem(with(A, B))    = expandItem(A) ∪ expandItem(B)
expandItem(plus(A, B))    = expandItem(A) ∪ expandItem(B)
expandItem(bang(A))        = { linear: [], persistent: [A] }
expandItem(atom)           = { linear: [atom], persistent: [] }
```

Each alternative is a `{ linear: [...], persistent: [...] }` — the facts to add to state when choosing that branch. The symexec explorer creates one child per alternative.

**Bug:** `expandItem` also handles `loli(bang(P), monad(Q))` by decomposing it into `{ linear: [Q_body], persistent: [bang(P)] }`. This is **unsound** — see section 7.

## 4. Matching (`forward.js: tryMatch`)

`tryMatch(rule, state, calc, matchOpts)` is the core matching function. It attempts to find state facts that satisfy all of a rule's antecedent patterns.

### 4.1 Algorithm (worklist with persistent deferral)

```
theta = new Array(metavarCount)     // de Bruijn indexed substitution
consumed = {}                        // hash → count of consumed linear facts

REPEAT until all patterns matched or failure:
  Phase 1 — Linear patterns:
    for each unmatched linear pattern P:
      if P depends on unbound persistent outputs → DEFER
      try Strategy A: delta bypass (direct Store.child extraction)
      try Strategy B: secondary index O(1) lookup
      try Strategy C: general matching against indexed candidates
      if no candidate matches → FAIL

  Phase 2 — Persistent patterns:
    for the next unproved persistent pattern:
      try FFI direct (tryFFIDirect) → O(1) arithmetic
      try state lookup (pattern match against persistent facts)
      try backward proving (prove.prove) → recursive search
      if all fail → FAIL

  if no progress made → FAIL

return { rule, theta, slots, consumed }
```

### 4.2 Linear Pattern Matching Strategies

Each linear pattern is tried against state facts in order of cheapness:

**Strategy A — Delta bypass:** For "flat delta" patterns (identified at compile time by `computePatternRoles`), extract children directly via `Store.child` instead of calling `matchIndexed`. This avoids the generic matching loop for simple patterns like `pc(PC)` where the structure is known at compile time.

**Strategy B — Secondary index:** For the fingerprint predicate (e.g., `code`), use the `_byKey` secondary index for O(1) lookup. The key pattern (e.g., `PC` in `code PC 0x14`) is first instantiated from theta, then used to look up the fact directly.

**Strategy C — General matching:** `matchIndexed(pattern, fact, theta, slots)` from `unify.js`. Walks both terms in lockstep, binding metavars in theta. Uses the undo stack for rollback on failure.

### 4.3 Persistent Pattern Proving

Persistent antecedents (`!inc PC PC'`, `!plus 2 GAS GAS'`, `!neq X Y`) are **proved**, not matched against state. The cascade:

1. **FFI direct** (`tryFFIDirect`): Check if the predicate has an FFI implementation (arithmetic, string ops). Call the FFI function with the instantiated arguments. O(1) for ground arguments. FFI failure without reason (e.g., `neq(5,5)`) is **definitive** — the rule cannot fire, break immediately.

2. **State lookup**: Pattern-match against persistent facts already in the state. Handles symbolic/non-ground cases where FFI can't decide.

3. **Backward proving** (`prove.prove`): Full backward chaining search using clause index. Last resort — expensive but complete.

## 5. Rule Selection

### 5.1 Single-Path (`forward.js: findMatch`)

Tries rules in order, returns first match (committed choice):
1. EVM strategy: O(1) lookup via `pc → code → opcode → rule`
2. Predicate filter: skip rules whose trigger predicates are absent from state

### 5.2 Exhaustive (`symexec.js: findAllMatches`)

Tries ALL rules, returns all matches. Uses a **strategy stack** — layered indexing where each layer claims rules it can index efficiently:

```
Layer 1: Fingerprint layer (O(1))
  - Rules with a ground discriminator in a binary+ predicate
  - 40/44 EVM rules claimed
  - Lookup: pc → code → opcode → candidate rules

Layer 2: Discrimination tree (O(depth))
  - Trie over preorder pattern traversals
  - Remaining 4 rules (concatMemory, calldatacopy helpers)
  - Only scans facts from relevant predicates

(Predicate filter is safety net — currently 0 rules reach it)
```

`detectStrategy(rules)` auto-builds the stack based on rule structure.

### 5.3 Loli Continuations (`forward.js: matchLoli`)

After compiled rule matching, the engine scans for fireable loli continuations in `state.linear`. `matchLoli(h, state, calc)` uses the same two-phase pipeline as `tryMatch`:

```
for each loli(trigger, body) in state.linear:
  flattenTensor(trigger) → { linear: [...], persistent: [...] }
  Phase 1: match linear trigger patterns against state.linear (via matchIdx)
  Phase 2: prove persistent triggers via provePersistentGoals (FFI → state → backward)
  if all matched → instantiate body, return match
```

`provePersistentGoals` is a shared helper extracted from `tryMatch` Phase 2. Both compiled rules and loli continuations use the same FFI → state lookup → backward chaining pipeline.

## 6. State Mutation and Execution

### 6.1 Single-Path (`forward.js: run`)

```
while steps < maxSteps:
  m = findMatch(state, rules, calc)
  if no match:
    m = matchFirstLoli(state, calc)
    if no match → QUIESCENT, return
  state = applyMatch(state, m)             // immutable: new state object
  steps++
```

`matchFirstLoli` returns the same match shape as `tryMatch`, so `applyMatch` handles both uniformly. `applyMatch` creates a new state: copies linear/persistent, subtracts consumed facts, adds produced facts.

### 6.2 Exhaustive (`symexec.js: explore`)

DFS with **mutation + undo** (no state copying at branch nodes):

```
go(depth, ctx):
  if ctx.stateHash in pathVisited → CYCLE
  if depth >= maxDepth → BOUND

  matches = findAllMatches(state, rules, calc, strategy, ctx.stateIndex)
  if no matches → LEAF (snapshot state)

  pathVisited.add(ctx.stateHash)
  for each match m:
    if m has 1 alternative:
      undo = mutateState(state, m.consumed, m.theta, m.consequent)
      childCtx = makeChildCtx(ctx, state, undo)   // incremental index + hash update
      child = go(depth+1, childCtx)
      undoIndexChanges(ctx.stateIndex, indexUndo)   // restore index
      undoMutate(state, undo)                        // restore state
    else:  // multiple alternatives (with/plus fork)
      for each alternative alt:
        undo = mutateState(state, m.consumed, m.theta, alt)
        childCtx = makeChildCtx(ctx, state, undo)
        child = go(depth+1, childCtx)
        undoIndexChanges(ctx.stateIndex, indexUndo)
        undoMutate(state, undo)
  pathVisited.delete(ctx.stateHash)
  return branch node with children
```

**Core invariant:** When `go()` returns, state, stateIndex, and pathVisited are in exactly their original state.

**Three mutable structures:**
- `state.linear` / `state.persistent` — mutated by `mutateState`, restored by `undoMutate`
- `ctx.stateIndex` — mutated by `makeChildCtx` (indexAdd/indexRemove), restored by `undoIndexChanges`
- `pathVisited` — mutated by add/delete around the DFS

Only **terminal nodes** (leaf, bound, cycle) snapshot the state. Branch nodes store `state: null`.

### 6.3 Flat Undo Log

`mutateState` returns a flat array `[TYPE, hash, oldValue, TYPE, hash, oldValue, ...]` where TYPE is 0=linear, 1=persistent. Each hash recorded once (first-touch-wins). `undoMutate` iterates backward restoring original values. This eliminates 3 object allocations per step vs the old `{ linearOrig, persistentOrig }` format.

### 6.4 Incremental ExploreContext

`ExploreContext` carries `stateIndex` (facts grouped by predicate) and `stateHash` (commutative XOR fingerprint) through the tree. `makeChildCtx` reads the undo log to compute O(delta) updates instead of rebuilding from scratch:

- Hash: XOR is self-inverse — `h ^= hashPair(old)` removes old, `h ^= hashPair(new)` adds new
- Index: `indexAdd` / `indexRemove` mutate in place; `undoIndexChanges` reverses

## 7. Guarded Loli Continuations

In EVM rules like `evm/iszero`:

```ill
pc PC * code PC 0x15 * !inc PC PC' * gas GAS * !inc GAS GAS' * sh (s SH) * stack SH V
-o {
  code PC 0x15 * pc PC' * gas GAS' * sh (s SH) *
  ((!eq V 0 -o { stack SH 1 }) +
   (!neq V 0 -o { stack SH 0 }))
}.
```

The ⊕ creates two alternatives. Each contains a loli with a persistent trigger (`!eq V 0` / `!neq V 0`). After the parent rule fires, these lolis become linear facts in state. `matchLoli` then:

1. Extracts `bang(eq(V,0))` → `flattenTensor` → persistent trigger `[eq(V,0)]`
2. `provePersistentGoals` proves `eq(V,0)` via FFI (O(1) bigint comparison)
3. Guard succeeds → loli fires, body produced. Guard fails → null, loli stays dormant → stuck leaf.

Dead branches stop immediately instead of running with corrupted state. EVM multisig tree: 210 nodes, 19 leaves (vs 13109/946 with the old unsound decomposition).

Optional future optimization: **eager guard pruning** at ⊕ fork time — before creating a branch, check if its guard is decidable and false, skip it entirely.

## 8. Optimization Summary

| Stage | What | Speedup | Technique |
|-------|------|---------|-----------|
| Strategy stack | Rule selection | 12.7× | O(1) fingerprint + disc-tree vs O(R) scan |
| Incremental context | State hashing + indexing | 1.7× | O(delta) XOR hash + incremental index |
| Mutation + undo | State management | 1.8× | In-place mutation, undo log, snapshot only at terminals |
| Index + Set undo | Index management | 1.25× | Mutable index + undo, mutable pathVisited |
| Direct FFI bypass | Persistent proving | 1.2× | Direct FFI call bypasses full prove() |
| De Bruijn theta | Substitution lookup | 2.1× | Compile-time slot assignment, O(1) vs linear scan |
| Delta bypass | Linear matching | ~8% | Direct Store.child extraction for flat patterns |
| Compiled substitution | Consequent production | ~8% | Store.put recipe vs generic applyIndexed |
| Disc-tree | Catch-all rule selection | ~0% at 44 rules | Trie over preorder traversals |
| Flat undo log | State undo | ~13% | Flat array vs object allocation |
| Numeric tagId | Tag comparison | ~2% | Numeric comparison vs string |

| Unified loli matching | Soundness fix | 62× | matchLoli with provePersistentGoals; dead branches → stuck leaves |

Total: **181ms → ~1ms** median for the 210-node multisig execution tree (EVM, 43 rules). Soundness fix (unified loli matching) reduced tree from 13109 → 210 nodes by eliminating dead branches.

## 9. Key Design Decisions

**TREAT-like, not Rete**: No cached partial matches (beta memories). Full re-evaluation from alpha memories (stateIndex) per step. Simpler, correct for linear logic's non-monotonicity. At 44 rules and ~180 facts, per-step matching is fast enough.

**Strategy stack over Rete network**: Rule selection via layered indexing (fingerprint → disc-tree → predicate filter) rather than a persistent network. Each layer claims rules it can index; unclaimed rules fall through. Auto-detected from rule structure.

**Mutation + undo over immutable state**: DFS exploration mutates one shared state in-place, restoring after each child returns. Only terminal nodes clone. Eliminates O(n) state copies at each of 62 branch nodes (for the multisig tree).

**De Bruijn indexed theta**: Metavariables get compile-time slot indices. Theta is a flat array with O(1) access. Undo stack in `unify.js` for rollback on match failure.

**FFI bypass**: Persistent antecedents with known FFI (arithmetic) are dispatched directly, bypassing the full backward proving pipeline. All 153 prove() calls per 63-node tree eliminated.

**Compiled substitution**: Consequent patterns get compile-time recipes (`{ tag, slots }`) that call `Store.put(tag, [theta[slot0], theta[slot1]])` directly instead of walking the pattern tree with `applyIndexed`.

---
title: Ephemeral Transit States and Basic Block Compilation
created: 2026-02-28
modified: 2026-02-28
summary: Reduce symexec overhead by not materializing deterministic intermediate states, with a path toward composing rule sequences into aggregate transformations
tags:
  - symexec
  - optimization
  - forward-chaining
  - partial-evaluation
type: design
status: researching
priority: 3
cluster: Performance
depends_on: []
required_by: []
---

# TODO 0057: Ephemeral Transit States and Basic Block Compilation

## Problem

calc's symbolic execution tree has 477 nodes (with structural memo) vs hevm's 61 for the same contract and the same behavioral outcomes. Both tools discover identical results: 30 branch points, 31 leaves, 5 outcome types × 6 members. The difference is representation: calc materializes every EVM opcode as an explicit tree node; hevm represents deterministic opcode sequences implicitly inside symbolic expressions.

Of calc's 477 nodes, only ~41 are structurally significant (30 branch points + 11 leaves). The remaining **~436 are deterministic transit states** — single-match, single-alternative steps where the engine has no choice. Each transit state costs:

| Cost | Per step | × 436 steps | Notes |
|---|---|---|---|
| `findAllMatches` | ~15μs | ~6.5ms | Strategy stack + tryMatch |
| `mutateState` + undo | ~5μs | ~2.2ms | Flat undo log + restore |
| `makeChildCtx` + index | ~3μs | ~1.3ms | Incremental stateIndex update |
| `drainPersistentLolis` | ~1μs | ~0.4ms | Usually no-op for EVM |
| solver checkpoint/restore | ~1μs | ~0.4ms | Minimal for single-alt |
| Tree node allocation | ~0.5μs | ~0.2ms | `{ type, children, state }` |
| **Total** | **~25μs** | **~11ms** | ~50% of 22ms total |

The question is which parts of this can be eliminated or amortized.

## Observation: What Transit States Actually Need

A transit state in `explore()` currently does (lines 613-631):

```
1. mutateState()           — ESSENTIAL: state must change
2. makeChildCtx()          — ESSENTIAL: stateIndex must reflect new state for next findAllMatches
3. solver.checkpoint()     — UNNECESSARY: no branching, nothing to backtrack
4. _feedPersistent()       — ESSENTIAL: solver must see new constraints
5. drainPersistentLolis()  — ESSENTIAL: lolis may fire
6. go(depth+1, childCtx)  — ALLOCATES: recursive call + tree node
7. undoDrain()             — NECESSARY only because of recursion
8. undoIndexChanges()      — NECESSARY only because of recursion
9. undoMutate()            — NECESSARY only because of recursion
10. solver.restore()       — UNNECESSARY (paired with #3)
11. children.push({...})   — UNNECESSARY: tree node for transit state
```

Steps 3, 6-11 exist because explore() uses **DFS with recursive backtracking**. For a deterministic chain, there's nothing to backtrack from — we're committed to the one available match. The recursion is doing work only to produce intermediate tree nodes that carry no information.

## Level 1: Iterative Deterministic Chains

Convert the recursive DFS to an iterative loop for deterministic chains.

### Algorithm

```javascript
function go(depth, ctx) {
  // --- Deterministic chain loop ---
  const undoStack = [];

  while (true) {
    // Memo/cycle/bound checks (must happen at every state)
    if (pathVisited.has(ctx.stateHash)) { ... cycle ... break; }
    if (globalVisited.has(ctx.stateHash)) { ... memo ... break; }
    if (globalControl?.get(computeControlHash(ctx.stateIndex)) === true) { ... memo ... break; }
    if (depth >= maxDepth) { ... bound ... break; }

    const matches = findAllMatches(state, ...);
    if (matches.length === 0) { ... leaf ... break; }

    const m = matches[0];
    if (matches.length > 1 || m.rule.consequentAlts.length > 1) {
      // Multi-match or multi-alt: exit loop, handle branching below
      break;
    }

    // Single match, single alt → deterministic step
    pathVisited.add(ctx.stateHash);
    const undo = mutateState(state, ...);
    const { ctx: childCtx, indexUndo } = makeChildCtx(ctx, state, undo);
    _feedPersistent(solver, undo);
    const drain = drainPersistentLolis(state, childCtx, calc);
    for (const dl of drain.undoLogs) _feedPersistent(solver, dl);

    undoStack.push({ stateHash: ctx.stateHash, undo, indexUndo, drain,
                     controlHash: ctx._controlHash, boundBefore: ctx._boundBefore });
    ctx = drain.ctx;
    depth++;
  }

  // --- Handle terminal or branch ---
  const result = handleTerminalOrBranch(...); // leaf/memo/cycle/bound/branch

  // --- Undo entire chain in reverse ---
  for (let i = undoStack.length - 1; i >= 0; i--) {
    const u = undoStack[i];
    undoDrain(ctx.stateIndex, state, u.drain.undoLogs, u.drain.indexUndoLogs);
    undoIndexChanges(ctx.stateIndex, u.indexUndo);
    undoMutate(state, u.undo);
    pathVisited.delete(u.stateHash);
    globalVisited.add(u.stateHash);
    // Record structural memo if applicable
    if (globalControl && u.controlHash !== undefined && u.boundBefore === boundCount) {
      globalControl.set(u.controlHash, true);
    }
  }

  return result;
}
```

### What changes

| Aspect | Before | After |
|---|---|---|
| Tree nodes per det. chain | N | 0 (chain is invisible in tree) |
| Stack frames per det. chain | N | 1 (loop, not recursion) |
| solver.checkpoint/restore | N pairs | 0 |
| Undo work | N individual undos | 1 batch undo (same total work) |
| Memo checks | N (unchanged) | N (unchanged) |
| findAllMatches calls | N (unchanged) | N (unchanged) |
| mutateState calls | N (unchanged) | N (unchanged) |

### What it does NOT change

The per-step computation is identical. `findAllMatches` still runs at every step. `mutateState` still runs. The savings come from:

1. **No tree node allocation**: ~436 fewer `{ type: 'branch', children: [...] }` objects
2. **No solver checkpoint/restore**: eliminates `_undoLog.length` bookkeeping per step
3. **No recursive call overhead**: eliminates ~436 function call frames
4. **Reduced stack depth**: from ~477 to ~30 (branch depth only)

### Estimated savings

- Allocation + GC: ~1ms (436 objects × ~2KB each = ~870KB avoided)
- Solver checkpoint/restore: ~0.5ms (436 × ~1μs)
- Function call overhead: ~0.5ms (436 × ~1μs per call/return)
- **Total: ~2ms** (22ms → ~20ms)

### Side effects on tree consumers

The tree shape changes. Consumers must be aware:

| Consumer | Impact |
|---|---|
| `getAllLeaves()` | Unchanged (still finds all leaves) |
| `countNodes()` | Returns ~61 instead of ~477 (fewer branch nodes) |
| `maxDepth()` | Returns branch depth (~30) not step depth (~477) |
| `toDot()` | Produces much smaller graph |
| `classifyLeaf()` | Unchanged (leaf states are the same) |
| Structural memo | Still works (checks at every step in loop) |
| `symexec-inspect.js` | Needs minor update for compact display |

Optional: store chain metadata (rule names, step count) on branch nodes for debugging:
```javascript
{ type: 'branch', children: [...], chainLength: 12, chainRules: ['evm/push1', 'evm/swap2', ...] }
```

## Level 2: Deferred Index Maintenance

In a deterministic chain, `makeChildCtx` updates the stateIndex at every step. But the next `findAllMatches` only needs the **fingerprint-relevant** part of the index (the `_byKey` secondary index and the pointer predicate bucket).

For each step, makeChildCtx processes ~5-10 fact changes in the undo log. Most of these update predicate buckets (`stack`, `gas`, `mem`) that the fingerprint layer doesn't use. Only 2-3 changes affect the fingerprint index (`pc` bucket, `code` bucket via `_byKey`).

Optimization: maintain a **minimal index** during deterministic chains — only the fingerprint-related buckets. Rebuild the full stateIndex when the chain ends (at a branch point or leaf).

```javascript
// During deterministic chain: lightweight update
function updateFingerprintOnly(ctx, state, undo, fpConfig) {
  for (let i = 0; i < undo.length; i += 3) {
    const type = undo[i], hash = undo[i+1], oldValue = undo[i+2];
    if (type !== 0) continue; // skip persistent
    const pred = getPredicateHead(hash);
    if (pred === fpConfig.pointerPred || pred === fpConfig.pred) {
      // Update only fingerprint-relevant buckets
      updateBucket(ctx.stateIndex, hash, state.linear[hash] || 0, oldValue);
    }
  }
  // Update stateHash (still needed for memo checks)
  ctx.stateHash = recomputeHash(ctx.stateHash, undo, state);
}

// At chain end: rebuild full index
ctx.stateIndex = buildStateIndex(state.linear, fpConfig, state.persistent);
```

### Savings estimate

For each deterministic step, ~5-10 index operations reduced to ~2-3. Savings: ~2μs/step × 436 = ~0.9ms.

### Risk

If a non-fingerprint rule matches during a deterministic chain (e.g., a loli continuation triggered by a `stack` fact), the minimal index would miss it. Mitigation: `findAllMatches` still scans ALL candidate rules — the strategy stack uses the disc-tree/predicate layers as fallback. These layers work without the full stateIndex. So the fingerprint layer might miss, but the fallback catches it.

Actually, this is dangerous. The disc-tree layer uses the stateIndex to check trigger predicates. With a partial index, it would fail to find candidates. **This optimization requires careful analysis of which predicates are actually queried by each strategy layer.**

A safer variant: update ALL predicate buckets but skip the `_byKey` secondary index rebuild for non-fingerprint predicates. This is simpler and still saves ~1μs per step.

**Verdict: defer this optimization.** The savings (~1ms) don't justify the complexity and risk. Level 1 is the right target.

## Level 3: Basic Block Compilation

Pre-compose sequences of deterministic rules into aggregate state transformations. This is where the large win lives.

### What is a basic block?

In the forward engine, a **basic block** is a maximal sequence of rule applications where:
1. Each step has exactly one matching rule (`findAllMatches` returns 1)
2. That rule has exactly one alternative (`consequentAlts.length === 1`)
3. No loli continuation fires during the chain

For EVM programs, basic blocks correspond to sequences of opcodes between control flow points (JUMPI, JUMP, STOP, REVERT). They're identifiable from the code facts at load time.

### What a composite rule looks like

Given a basic block of rules R1, R2, ..., Rn:

```
R1: pc(P0) * code(P0,PUSH1) * sh(SH) * gas(G0)          -o { pc(P1) * code(P0,PUSH1) * sh(s(SH)) * stack(SH,V) * gas(G0') }  [!inc P0 P1, !inc G0 G0']
R2: pc(P1) * code(P1,DUP1) * sh(s(SH)) * stack(SH,V)    -o { pc(P2) * code(P1,DUP1) * sh(s(s(SH))) * stack(SH,V) * stack(s(SH),V) * gas(G1') }  [!inc P1 P2, !inc G0' G1']
R3: pc(P2) * code(P2,ADD) * sh(s(s(SH))) * stack(s(SH),X) * stack(SH,Y) -o { ... }  [!inc P2 P3, !plus 3 G1' G2']
```

The composite transformation:
```
COMPOSITE: pc(P0) * code(P0,PUSH1) * code(P1,DUP1) * code(P2,ADD) * sh(SH) * stack(SH,Y) * gas(G0)
  -o { pc(P3) * code(P0,PUSH1) * code(P1,DUP1) * code(P2,ADD) * sh(s(SH)) * stack(SH, add(V,Y)) * gas(G2') }
  [!inc P0 P1, !inc P1 P2, !inc P2 P3, !inc G0 G0', !inc G0' G1', !plus 3 G1' G2']
```

The composite:
- Consumes the initial state (pc, sh, gas, stack entries used by the block)
- Produces the final state (after all N rules have fired)
- Collects ALL persistent antecedents from the chain
- Internal intermediate facts (e.g., the temporary `stack(s(SH), V)` from DUP) cancel out

### Why this is hard

1. **Symbolic composition requires substitution chaining.** R1's output metavars become R2's input. The composite must track the full binding chain: P1 in R2's antecedent is the SAME P1 produced by R1's consequent, which was computed by `!inc P0 P1`.

2. **Persistent antecedents accumulate.** A block of 50 rules might have 100+ persistent goals (inc, plus, mul, neq). The composite rule has all of them. At runtime, these all need proving. The FFI handles most in O(1), but the sheer count adds overhead.

3. **Code facts are linear but invariant.** Each EVM rule consumes `code(PC, INSTR)` and re-produces it. In the composite, all code facts are consumed and re-produced — they SHOULD cancel. But the preserved-skip optimization already handles this (compile.js detects preserved patterns). The composite would need the same optimization applied to the aggregate.

4. **Existential variables in the chain.** If R5 is `evm/and` and the operands are symbolic, R5 produces a fresh evar. Rules R6+ operate on this evar. The composite must track which slots are evar-producing and thread them through.

5. **Stack effect analysis.** EVM instructions have well-defined stack effects (push, pop, dup, swap). The net stack effect of a block can be pre-computed. But in the general case (non-EVM calculi), there's no simple stack model.

6. **Load-time code dependency.** The composition depends on WHICH code facts exist. For `code(5, 0x50)`, we know opcode 0x50 = POP, so rule `evm/pop` fires next. But this means the composite is **code-specific** — it changes for every contract. We'd need to recompile composites for each contract.

### Implementation spectrum

There's a spectrum from easy to hard:

#### 3a. Lazy block detection (runtime, no pre-composition)

Detect deterministic chains at runtime, but don't pre-compose. Just run them in the iterative loop (Level 1) with reduced bookkeeping. This is Level 1 with an explicit "basic block" concept.

Benefits: clean abstraction, no pre-composition complexity.
Cost: per-step work unchanged.

#### 3b. Rule chaining with pre-computed successors (compile-time)

At compile time, for each rule with a discriminator value, determine which rule COULD fire next based on the produced fingerprint value.

```javascript
// At compile time:
rule.nextDiscriminator = computeNextDiscriminatorValue(rule);
// e.g., evm/push1 at code(5, 0x60) → next PC = 7 → next code(7, INSTR) → next rule

// At runtime:
let m = matches[0];
while (m.rule.nextDiscriminator !== null) {
  apply(m);
  m = lookupByDiscriminator(m.rule.nextDiscriminator);
}
```

This skips `findAllMatches` entirely for deterministic chains. The successor is pre-computed.

**Problem:** The discriminator value depends on the STATE (which code facts exist), not just the rule. We can pre-compute successor chains for a SPECIFIC program (known code facts), but not in general.

**For EVM:** This is feasible. At load time, walk the code facts, determine the instruction at each PC, and build a successor chain. This is essentially building a **threaded code interpreter** — a well-known optimization in VM design.

Estimated savings: ~6.5ms (eliminating findAllMatches for 436 steps).
Implementation complexity: Medium-high (program-specific compilation at load time).

#### 3c. Full symbolic composition (compile-time)

Pre-compose the entire basic block into a single aggregate rule. This is the full optimization described above.

Estimated savings: ~9ms (eliminating findAllMatches + reducing mutateState to one large mutation).
Implementation complexity: Very high (substitution chaining, persistent goal collection, existential threading, preserved detection on composites).

### Performance estimates

| Level | Nodes (tree) | Steps (compute) | Time estimate | Complexity |
|---|---|---|---|---|
| Current | 477 | 477 | 22ms | — |
| Level 1 (iterative) | ~61 | 477 | ~20ms | Low |
| Level 3a (block detection) | ~61 | 477 | ~20ms | Low |
| Level 3b (threaded code) | ~61 | ~61 | ~14ms | Medium-high |
| Level 3c (full composition) | ~61 | ~14 | ~5ms | Very high |

## Connection to Existing Theory

### Threaded code (Bell 1973)

Level 3b is a classic VM optimization. Instead of dispatching each instruction through a lookup table, pre-thread the instructions into a linked list. Each instruction's handler jumps directly to the next handler.

For CALC: instead of dispatching through the strategy stack, pre-link rules by their fingerprint successors. The "threading" happens at load time when the code facts are known.

### Partial evaluation (Futamura 1971, Jones et al. 1993)

Level 3c is the first Futamura projection applied to forward rule chains. Given:
- An interpreter (the forward engine)
- A program (the forward rules + code facts)

Partial evaluation specializes the interpreter to the program, producing a **residual program** (the composite rules) that runs faster.

The analogy:
- "Interpreter" = findAllMatches + mutateState + makeChildCtx
- "Program" = sequence of EVM instructions (code facts)
- "Residual program" = composite state transformation

### Supercompilation (Turchin 1986)

Supercompilation drives a computation forward, generalizing when the process diverges. CALC's structural memoization is the generalization step (MSG). Basic block compilation is the driving step — unfolding rule applications until a branch point.

The homeomorphic embedding check from supercompilation could be used to detect when a basic block is "too complex" (too many accumulated persistent goals) and should be split.

### CHR compilation (Frühwirth 2009)

CHR simpagation rules (kept ∧ removed ⇔ guard | body) are isomorphic to ILL forward rules. CHR compilers (HAL, CCHR, K.U.Leuven CHR) use **occurrence specialization**: each rule's patterns are pre-compiled into specialized matchers that know the rule index.

For basic block compilation, this means: the composite rule can have a specialized matcher that checks all N antecedent patterns in one pass, rather than N separate tryMatch calls.

## Relationship to TODO_0056

TODO_0056 (speculative merge via MSG) targets **branch-level** optimization — reducing redundant subtrees. This TODO targets **step-level** optimization — reducing per-step overhead in deterministic chains.

They're complementary:
- TODO_0056 reduces the tree from 2125 → 477 nodes (structural memo, already done)
- This TODO reduces step cost from 477 → ~61 (representation) or ~14 (computation)
- Combined: 2125 nodes → ~61 steps → ~5ms (from 57ms)

## Recommended Path

**Phase 1: Level 1 (iterative deterministic chains).** Low risk, ~2ms savings, cleaner tree representation, eliminates stack overflow risk for deep programs. ~50 LOC change in `symexec.js`. Do this first.

**Phase 2: Level 3b (threaded code).** Medium effort, ~8ms savings. At load time, build a rule successor graph from the code facts and fingerprint config. Replace `findAllMatches` with direct successor lookup during deterministic chains. ~100 LOC in new module + ~30 LOC in `symexec.js`.

**Phase 3: Level 3c (full composition).** High effort, ~5ms additional savings. Only worth pursuing if profiling shows that per-step mutateState/makeChildCtx cost dominates. This is a research project, not an engineering task.

**Defer: Level 2 (deferred index maintenance).** The savings (~1ms) don't justify the risk of breaking strategy fallback layers. The full stateIndex rebuild is fast enough.

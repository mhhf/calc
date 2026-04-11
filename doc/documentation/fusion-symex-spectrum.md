---
title: "The Fusion–Symex Spectrum"
created: 2026-04-11
modified: 2026-04-11
summary: "Compile-time rule fusion and runtime symbolic execution are the same computation at different granularities. This document describes the continuous spectrum from grade-0 composition through basic block fusion to full exploration, shows where fusion saves work vs where it just moves it, and identifies the frontier."
tags: [forward-chaining, partial-evaluation, cut-elimination, staging, symbolic-execution, supercompilation, Futamura, optimization, architecture]
---

# The Fusion–Symex Spectrum

Compile-time rule fusion (`compose.js`) and runtime symbolic execution (`explore.js`) are **the same computation** — forward rule composition via cut elimination. They differ only in granularity: how many rules are fused before handing the result to the explore engine.

This document describes the continuous spectrum, identifies where each point saves work, and maps the frontier of further fusion.

## 1. The Spectrum

Every pass in the compile pipeline and every step of the symex performs the same fundamental operation: **take two forward rules connected by an intermediate fact, eliminate the fact, produce a fused rule.** This is cut elimination on the forward rule sequent.

```
Producer: Γ₁ -o { M }     Consumer: M ⊗ Γ₂ -o { Δ }
────────────────────────────────────────────────────── cut
              Γ₁ ⊗ Γ₂ -o { Δ }
```

The difference is WHEN and HOW MANY cuts are performed:

```
             ◄─── compile time ────►◄────── runtime ──────►

Grade-0 cut  │  Basic block  │  Chain  │  SROA  │  Symex
(Pass 1-2)   │  fusion (P5)  │  (P5.5) │  (P6)  │  (explore)
             │               │         │        │
Eliminates:  │  Eliminates:  │  Elim:  │  Elim: │  Explores:
grade-0      │  pc threading │  inc→   │  array │  all remaining
intermediates│  within basic │  plus   │  →     │  rule firings
             │  blocks       │  chains │  slots │  (one at a time)
```

Moving left = more fusion at compile time, fewer steps at runtime.
Moving right = less fusion, more runtime steps.

The rightmost point (no compile-time fusion, pure interpretation) is the raw forward engine.
The leftmost theoretical limit (complete fusion) IS the symex — every execution path materialized as a single fused mega-rule.

## 2. Why Fusion and Symex Produce the Same Result

For fixed rules R and initial state S, both fusion-to-completion and symex produce the same set of reachable final states. The proof is trivial: both are sequences of cut steps on the same rule set, differing only in scheduling order. Cut elimination is confluent (Nigam-Miller 2009), so the order doesn't matter.

**Pruning is identical.** Fusion prunes a branch when unification fails (the fused rule's antecedent is unsatisfiable). Symex prunes a branch when matching fails (no rule fires). These are the same check — an intermediate fact that can't be produced means the path is dead. Both discover this and discard the path.

**The number of paths is identical.** For the multisig solc symbolic benchmark: 11 leafs. Whether we fuse all rules or explore step by step, we get 11 final states. The "exponential blowup" from branching doesn't happen because most branches are pruned — the same branches, by the same mechanism, in both approaches.

## 3. Where Each Point on the Spectrum Saves Work

Not all fusion is equally valuable. The key distinction: **does fusion reduce the number of operations, or does it just move them?**

### 3.1 Grade-0 composition (Passes 1-2): saves work

Eliminates compile-time scaffold types (`!_0 step`, `!_0 is_push`). These intermediates exist only to structure the rule definitions — they carry no runtime information. Fusing them away:
- Eliminates intermediate fact creation/consumption at runtime
- Resolves ground arithmetic at compile time (residual resolver)
- Produces per-opcode specialized rules (no runtime bytecode lookup)

**Savings**: O(opcodes × rules) matching steps eliminated. For EVM: ~15 generic rules → ~200 per-PC specialized rules, each doing one step instead of going through `step/make` + opcode dispatch.

### 3.2 Basic block fusion (Pass 5): saves work

Fuses consecutive rules threaded by `pc(GROUND)` into mega-rules. Within a basic block (no branches), this is pure win:
- N opcodes → 1 fused rule
- N-1 fewer matching/undo/state-transition steps at runtime
- Intermediate `pc` values never instantiated

**Savings**: proportional to average basic block length. For EVM contracts: basic blocks average ~5-10 opcodes, so ~5-10× fewer symex steps per basic block.

### 3.3 Chain fusion (Pass 5.5): saves work

Collapses `inc(X,Y) * inc(Y,Z)` → `plus(X,2,Z)`. Eliminates intermediate metavars and replaces N persistent goals with 1 accumulated goal. Resolved at compile time if inputs are ground.

**Savings**: reduces persistent goal count per rule. Moderate impact.

### 3.4 SROA (Pass 6): saves work

Scalarizes array access after McCarthy normalization. Replaces `arr_get`/`arr_set` goals with direct variable bindings. Eliminates the array data structure entirely within fused rules.

**Savings**: eliminates array-access backward chaining at runtime. Significant for stack-heavy EVM opcodes.

### 3.5 Cross-branch fusion: moves work, doesn't save it

Fusing rule A across a JUMPI into two variants (true-branch, false-branch) produces two rules. The symex still tries both. No steps eliminated — the branch exploration is inherent in the problem.

**This is where fusion stops being profitable.** Within a basic block, fusion reduces steps. Across branches, it just pre-attaches the successor to the predecessor without eliminating any exploration.

### 3.6 Summary

| Point on spectrum | Saves work? | Why |
|---|---|---|
| Grade-0 composition | Yes | Eliminates scaffold intermediates |
| Basic block fusion | Yes | Eliminates sequential steps within deterministic chains |
| Chain fusion | Yes | Reduces persistent goal count |
| SROA | Yes | Eliminates array traversal |
| **Cross-branch fusion** | **No** | **Same branches explored, just pre-attached** |
| Full fusion = symex | No | Same computation, same 11 leafs |

The compose pipeline already sits at the optimal boundary: fuse everything that reduces steps (basic blocks), stop at the point where fusion just moves work (branches).

## 4. The Supercompilation Connection

THY_0016 §7 identifies this: **grade-0 composition + explore = partial evaluation + driving = supercompilation** (Turchin 1986, Sørensen-Glück-Jones 1996).

In supercompilation terminology:
- **Partial evaluation** = compile-time fusion (Passes 1-6)
- **Driving** = runtime exploration (explore.js)
- **Generalization** = state abstraction at loop back-edges (not yet implemented)
- **Folding** = memoization of revisited states (not yet implemented)

The compose pipeline does the "partial evaluation" half. The explore engine does the "driving" half. Together they form a supercompiler for forward-chaining linear logic — with resource-awareness that traditional supercompilation lacks.

## 5. The Futamura Projections

(See THY_0016 for the full treatment.)

| Projection | In our system | Result |
|---|---|---|
| 1st: specialize(interpreter, program) | `composeGrade0(evm_rules, bytecode_facts)` | Per-contract specialized rules |
| 2nd: specialize(specializer, interpreter) | `compose.js` with EVM rules loaded | The compiler itself |
| 3rd: specialize(specializer, specializer) | Compose rules composed with themselves | Compiler generator |

The 1st projection is implemented. The 2nd projection is `compose.js` itself — parameterized by the rule set, it IS the compiler from bytecode to specialized rules.

### 5.1 The 3rd projection and Milawa self-verification

The 3rd projection requires **reflection** — expressing the compose pipeline as ILL forward rules that the compose pipeline can operate on. This connects directly to TODO_0008 §14 (Milawa-style self-verification): both need ILL operating on interned representations of ILL objects. See TODO_0187 for the unified reflection infrastructure.

**Shared infrastructure:**
- TODO_0008 §14 interns **proof terms** in the Store → persistent check rules verify proofs → ILL verifying its own backward proofs
- 3rd Futamura interns **forward rules** in the Store → forward compose rules compose other rules → ILL compiling its own forward rules

Both use the same mechanism (forward engine on interned representations) and need the same prerequisite (Store interning of ILL objects, ~50 LOC per object type).

**Compose rules** (hypothetical — `composePair` as ILL):
```ill
!compose_cut:
  rule(R1, Ante1, Conseq1) * rule(R2, Ante2, Conseq2) *
  !has_grade0(Conseq1, P) * !has_grade0(Ante2, P) *
  !unify_cut(Conseq1, Ante2, P, Theta) *
  !apply_merge(Theta, Ante1, Ante2, Conseq1, Conseq2, P, NewAnte, NewConseq)
  -o { rule(composed(R1, R2), NewAnte, NewConseq) }.
```

Once the compose pipeline is expressed as forward rules, the three projections form a tower:
1. Compose rules + EVM rules + bytecode facts → specialized EVM executor
2. Compose rules + EVM rules → EVM compiler (produces specialized rules for any bytecode)
3. Compose rules + compose rules → compiler generator (produces a compiler for any rule set)

The Milawa checker verifies each level: the composed output is correct because the compose-cut rule IS cut elimination, and the check rules verify the cut step. See THY_0016 §2.4 for the grade semiring structure needed for the meta-level.

## 6. Three-Level Staging

THY_0016 §3.2 describes extending the grade semiring to {0, 1, ω}:

| Grade | Binding time | Known when | EVM example |
|---|---|---|---|
| 0 | Deploy-time | Contract deployed | Bytecode, opcode tables |
| 1 | Transaction-time | Specific call | Calldata, msg.sender, msg.value |
| ω | Symbolic | Explored | Storage, stack (post-branch) |

Currently only grade 0 and ω are implemented. Grade 1 would add a **transaction-time specialization pass** between composition and symex — specializing against known calldata (e.g., a specific function selector) to eliminate function dispatch branches before exploration:

```
Parse → Compile → Grade-0 compose → [Grade-1 compose] → Symex (grade-ω explore)
```

This is useful when analyzing a specific function rather than all functions. Not currently implemented.

## 7. Frontier: What Further Fusion Could Do

The compose pipeline is at the optimal point for **within-basic-block** fusion. But there are opportunities for more work that the current pipeline doesn't capture:

### 7.1 Transaction-time specialization (grade-1 PE)

**Impact: moderate. Feasibility: medium.**

When analyzing a specific function (e.g., `transfer()`), the function selector (`msg.data[0:4]`) is known. Grade-1 specialization would resolve the function dispatch JUMPI at compile time, eliminating other functions' branches.

Implementation: extend `composeGrade0` to accept grade-1 facts (calldata fragments), run a second composition pass. The symex then only explores within the selected function.

Note: for the multisig benchmark, most of the 11 leafs come from WITHIN a single function (storage conditions, revert paths), not from function dispatch. So the savings are moderate — fewer initial branches, but the main exploration cost is unchanged.

### 7.2 Loop summarization via inductive generalization

**Impact: potentially huge. Feasibility: hard (research).**

Currently loops unfold step by step in the symex. Each iteration fires the loop body rule, advances the loop counter, checks the exit condition. For N iterations: N symex steps.

Loop summarization would recognize the loop body as a parameterized step and compute a closed form:
```
for (i = 0; i < N; i++) sum += arr[i]
→  sum = fold(+, 0, arr[0..N-1])
```

In rule terms: detect back-edges in the fused rule graph, abstract the loop body into a parameterized rule, find a fixpoint expression. This is the "generalization" step in supercompilation (Turchin's whistle + generalization).

**Challenges**: linear state changes per iteration (stack, memory). Need loop-invariant detection for linear resources. Related to acceleration in model checking (LIRA/Presburger acceleration for counter systems). See TODO_0185.

Prerequisite: loops in the EVM model (back-edges in fused rule graph). Depends on TODO_0163 (supercompilation whistle for loop detection).

### 7.3 State merging at convergence (widening)

**Impact: medium. Feasibility: medium.**

When multiple execution paths reach the same PC with different but "compatible" states, the symex explores the continuation separately for each. State merging would combine them into one abstract state, exploring the continuation only once.

Example: paths A and B both reach PC 42 with identical stack layout but different storage. If the continuation doesn't read storage, the paths can be merged.

This is well-studied: KLEE's state merging, Veritesting (Avgerinos et al. 2014). Would reduce from M paths through the convergence point to 1.

**Challenge for ILL**: linear resources can't be freely merged — merging must respect linearity. Merging `stack_top(5)` with `stack_top(7)` produces `stack_top(X)` with constraint `X ∈ {5, 7}`, which adds constraint tracking. See TODO_0056.

### 7.4 Super-rule native compilation (2nd Futamura, operationalized)

**Impact: medium. Feasibility: straightforward engineering.**

After basic block fusion, each mega-rule is still interpreted by the matching engine (pattern match antecedent, prove persistent goals, instantiate consequent). A further step: compile each mega-rule into a native JS closure:

```js
// Fused rule for PUSH1 0x60; PUSH1 0x40; ADD basic block
function block_0_4(state) {
  const gas = state.remove('gas');
  const newGas = gas - 9;  // 3+3+3 pre-computed
  if (newGas < 0) return null;
  state.add('gas', newGas);
  state.add('pc', 5);
  state.add('stack_top', 0xA0);  // 0x60+0x40 pre-computed
  return true;
}
```

This eliminates matching/unification overhead entirely for fused blocks. The closure directly manipulates the FactSet.

**Caveat**: per-rule closures risk V8 megamorphic IC penalties (see RES_0069 — 59 closure types caused ~25% regression). Must batch into a small number of closure shapes, not per-rule closures.

### 7.5 Automatic BTA (binding-time analysis)

**Impact: low–medium. Feasibility: medium.**

Currently grade-0 annotations are manual. Automatic BTA would infer which predicates can be grade-0 based on groundness analysis: if a predicate's inputs are always ground at rule-compilation time (determined by bytecode content), promote to grade-0 automatically.

This extends the compose pipeline without changing its structure — just widens the set of facts that get composed away.

### 7.6 Cross-contract composition (link-time PE)

**Impact: high for multi-contract analysis. Feasibility: medium.**

When contract A CALLs contract B, and both are pre-specialized: A's CALL rule produces state that B's entry rules consume. Composing A's CALL output with B's entry rules at "link time" fuses the cross-contract boundary.

This is inter-procedural partial evaluation — standard in compiler optimization but novel for linear logic forward chaining. The SELL framework supports it via multi-stratum composition. See TODO_0186. Prerequisite: EVM CALL frame execution (TODO_0053).

## 8. Relationship to Existing Documentation

| Document | Scope |
|---|---|
| **This document** | Unified picture: compile pipeline ↔ symex as a spectrum |
| `grade0-composition.md` | Implementation reference for `compose.js` (passes, API, config) |
| THY_0016 | Theoretical foundation: grades ↔ binding times, Futamura projections |
| THY_0015 | Graded monad theory: grade-0 staging, stratified cut elimination |
| `forward-chaining-engine.md` | Runtime engine architecture (match, strategy, forward, explore) |
| `architecture.md` | Full system architecture (prover layers, engine layers) |

## 9. Key Insight

The compose pipeline and the explore engine are not two separate systems. They are two segments of a single spectrum of forward rule fusion. The pipeline fuses where fusion eliminates intermediate state (deterministic chains). The explore engine handles where fusion just duplicates work (branches). The boundary between them — the end of basic block fusion, the start of branch exploration — is the point where the marginal cost of fusion exceeds the marginal savings.

Moving this boundary is the core optimization lever for forward-chaining symbolic execution in ILL.

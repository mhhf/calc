---
title: "Cross-Stage Specialization: Persistent Facts as Static Input"
created: 2026-04-01
modified: 2026-04-01
summary: "Survey of partial evaluation, supercompilation, and related techniques as they apply to specializing forward rules against compile-time-known persistent facts (e.g. EVM bytecode)."
tags: [partial-evaluation, forward-chaining, evm, optimization, compilation, cut-elimination, multiset-rewriting, supercompilation, staging, backward-chaining]
category: "Forward Chaining"
---

# Cross-Stage Specialization: Persistent Facts as Static Input

## The Problem in CALC Terms

In CALC's EVM model, every forward rule contains persistent prerequisites of the form `!arr_get BC PC OP` — "get the opcode `OP` from bytecode `BC` at position `PC`." These are resolved at runtime by backward chaining into the `arr_get` predicate (which chains into the array prelude, index arithmetic, etc.).

When a specific contract's bytecode is known at compile time, these lookups have ground answers. The `!arr_get` call on a fixed bytecode array `[0x60, 0x80, 0x60, 0x40, ...]` at position `0x00` always returns `0x60` (PUSH1). This fact is not discovered at runtime — it is, in principle, available before any execution begins.

The question: can we pre-resolve these persistent prerequisites during rule composition, producing specialized rules with concrete opcodes hardcoded in?

Concretely, the generic rule:

```ill
evm/add:
  $bytecode BC * pc PC * !arr_get BC PC 0x01 * !inc PC PC' * gas GAS * ...
  -o { ... }.
```

paired with the bytecode fact `bytecode [0x01, 0x02, ...]` could, after specialization for PC=0, produce:

```ill
evm/add_pc0:
  $bytecode [0x01, 0x02, ...] * pc 0x00 * gas GAS * ...
  -o { ... }.
```

with `!arr_get` and `!inc` pre-evaluated away.

This document surveys the theoretical landscape for this operation.

---

## 1. Futamura Projections

### The Three Projections

Futamura (1971/1983) observed that a partial evaluator (PE) operating on a program and its static input produces a specialized residual. The three classic projections:

**First projection:** `PE(interpreter, program) = compiled_program`
Specialize the interpreter with respect to a fixed program (source code as static input). The result is a compiled version of that program — an executable that doesn't carry the interpreter overhead.

**Second projection:** `PE(PE, interpreter) = compiler`
Specialize the partial evaluator itself with respect to the interpreter. The result is a compiler: something that, given any source program, produces a compiled executable.

**Third projection:** `PE(PE, PE) = compiler_compiler`
Specialize the partial evaluator with respect to itself. The result generates compilers from interpreters automatically.

### Mapping to CALC

The EVM forward rules collectively constitute an **interpreter** for EVM bytecode. The execution engine (forward chaining loop in `forward.js`) is the meta-interpreter that runs these rules. A specific contract's bytecode is the **program**.

Applying the first Futamura projection:

- **Static input:** the specific bytecode array (known at "compile time" for CALC's purposes)
- **Dynamic input:** the EVM state (stack, memory, storage, gas, pc) — known only at execution time
- **Result:** a specialized rule set where all `!arr_get BC PC OP` lookups have been resolved, producing concrete dispatch rules specific to that contract

This is exactly the first Futamura projection applied to the CALC rule engine: `PE(evm_rules, specific_bytecode) = contract_compiled_rules`.

### What PE Does Here

The partial evaluator sees:
- `!arr_get BC PC OP` with `BC` ground (the known bytecode) but `PC` free (dynamic)
- It cannot collapse the rule to a single specialized version because `PC` varies
- But for each concrete `(PC, OP)` pair it CAN statically determine the opcode

This is analogous to loop unrolling in the PE literature: the interpreter loop steps are unrolled once per bytecode position. For each position `i` in the bytecode, a specialized rule variant exists. The dispatch condition `!arr_get BC i OP` becomes the constant `OP = bytecode[i]`, hardcoded.

---

## 2. Supercompilation

### Driving and Generalization

Turchin's supercompilation (1970s) goes strictly beyond standard partial evaluation. Where PE classifies inputs as static/dynamic upfront and reduces only static parts, a supercompiler **drives** the computation: it symbolically executes the program, propagating all available information — both known values and structural constraints — and only commits to specializations when it encounters previously-seen configurations (memoization / generalization).

**Driving with partially-known data:** The supercompiler can specialize a program even when only *some* structure of an argument is known — e.g., a list whose elements are unknown but whose length is known, or a tree whose left branch is known. This is more powerful than offline PE's binary static/dynamic partition.

**Generalization:** When the supercompiler encounters a term it has seen before (up to renaming), it folds back to the earlier version rather than diverging. When it encounters a term that embeds a previously seen one but is strictly larger, it applies generalization (widens to a common abstraction) to ensure termination.

### Relation to Persistent-Fact Specialization

In our case, the persistent fact `!arr_get BC PC OP` with `BC` ground and `PC` free is a case where the supercompiler would:

1. Drive into the array lookup with the concrete `BC`
2. Hit a branch: `if PC = 0 then OP = 0x60, if PC = 1 then OP = 0x80, ...`
3. Produce specialized residuals for each `PC` value

This is exactly supercompilation's **case analysis during driving**: it unfolds the branching structure of `arr_get` applied to a specific concrete array.

The key difference from plain PE: supercompilation would propagate the concrete `OP` value into the rest of the rule's body (e.g., confirming that `OP = 0x01` enables `evm/add`), potentially eliminating entire rule branches that are unreachable for this specific contract. Plain offline PE would require binding-time annotations to do this.

**Supercompilation is strictly more powerful** for this use case because it handles term-structure knowledge (the specific bytecode array) without requiring pre-declared binding times. However, it comes at higher implementation complexity and potential non-termination requiring explicit generalization strategies.

---

## 3. Online vs. Offline Partial Evaluation

### The Core Distinction

**Offline PE** (Jones-Gomard-Sestoft 1993, Ch. 4-5):
- Phase 1: **Binding-time analysis (BTA)** — statically classifies every expression as `static` (known at specialization time) or `dynamic` (unknown). The classification is conservative: if something *might* be dynamic, it is classified dynamic.
- Phase 2: **Specialization** — reduces only pre-identified static parts, generates residual code for dynamic parts.
- Advantage: fast, predictable, guaranteed to terminate.
- Disadvantage: imprecise — BTA may classify something as dynamic even though, given this specific input, it could be computed.

**Online PE**:
- No pre-pass. The specializer discovers binding times dynamically as it executes.
- Makes reduce/residualize decisions on the fly, based on current knowledge.
- More precise: finds more redexes than offline PE (it knows exactly which values are available at the current program point).
- More expensive: performs the analysis and reduction simultaneously.

### Which Model Fits Cross-Stage Persistent Fact Specialization?

This is a hybrid case that maps cleanly to **offline PE on a two-level annotation**:

- `BC` (bytecode): **static** — known at contract-compile time
- `PC` (program counter): **dynamic** — not known until execution
- `OP` (opcode): **static given BC and PC at a specific position, but static only after case-split on PC**

The "after case-split" part is the wrinkle. Classical offline PE annotates `PC` as dynamic. But if we're willing to do **polyvariant specialization** (one specialized version per `PC` value), then for each fixed `(BC, PC_val)` pair, `OP` becomes static.

This is precisely the **online PE** pattern: the specializer sees `!arr_get BC PC OP` with `BC` ground, observes that `PC` is free, and can choose to:
1. (Monovariant) Leave the lookup dynamic → no specialization
2. (Polyvariant) Split on each concrete `PC` value → one specialized rule per bytecode position

**Conclusion:** Cross-stage persistent-fact specialization on `BC` with case-splitting on `PC` is **online PE** (or equivalently, polyvariant offline PE with a maximally fine-grained BTA). The `@abstract` annotation in CALC's current `simplify` mechanism is an offline-PE-style declaration.

---

## 4. The EDB/IDB Distinction in Deductive Databases

### Parallel in Database Theory

In deductive databases (Datalog/Prolog-style), the **Extensional Database (EDB)** contains ground base facts, and the **Intensional Database (IDB)** contains rules. Partial evaluation against known EDB facts is a classical technique: given a ground EDB, specialise the IDB rules to produce rules that directly reference the EDB values rather than looking them up.

This is called **magic sets** (Bancilhon et al., 1986) or **demand-driven partial evaluation** in the Datalog literature. Magic sets transformation pre-specializes recursive predicates for specific query patterns; when the base EDB is fully ground, the result is flat residual rules with no recursive lookup.

In CALC's terms:
- `bytecode [0x60, 0x80, ...]` is EDB (a ground persistent fact)
- `arr_get` and related predicates are IDB rules
- Specializing `evm/add` against the EDB bytecode fact is exactly EDB-driven IDB specialization

The magic sets analogy is tight: rather than asking "for all bytecodes, what does ADD do?", we ask "for this specific bytecode, what does ADD do at each position?".

---

## 5. The Code Explosion Problem

### The Tradeoff

Specializing for a 1000-byte contract yields:
- Up to 1000 PC-specific dispatch rules (one per bytecode position)
- Each rule has the opcode hardcoded — no `!arr_get` lookup
- But most positions are not valid opcode starts (PUSH1 consumes 2 bytes; position 1 is data, not an opcode)

In practice: a 1000-byte contract has at most ~500-600 actual opcode positions after accounting for PUSH data bytes. Still, this is 500-600 rules vs ~140 generic rules.

### Standard PE Mitigations

**Monovariant specialization:** Produce exactly one specialized version per predicate, regardless of how many distinct static argument patterns appear. Safe from explosion. Low precision: if `PC` is always dynamic, `!arr_get BC PC OP` gets no specialization at all.

**Polyvariant specialization:** Produce one version per distinct static argument pattern seen during specialization. Potentially exponential in the number of static inputs; controlled by **memoization** (never specialize the same pattern twice). For the EVM case: one version per `(BC, PC)` pair where `BC` is the fixed bytecode and `PC` ranges over valid opcode positions. This is the natural choice.

**Generalization:** When the number of versions exceeds a threshold, or when a pattern is recognized as a permutation of a previous one, merge versions via widening. Used in supercompilation to ensure termination. For the EVM case: since bytecode is finite, no generalization is needed — the fixpoint is guaranteed to be finite (bounded by `|bytecode|` versions).

**Demand-driven specialization:** Only specialize for `PC` values that are actually reachable in the execution — i.e., jump targets. The EVM's jump semantics require `JUMPDEST` markers; static analysis can identify all valid JUMPDEST positions, reducing the specialization fan-out to only reachable positions.

### Concrete Numbers for the EVM Case

A typical Solidity-compiled contract: ~200-500 bytecode positions. The fan-out is bounded and linear in contract size. Compare:
- **Generic rules:** ~140 opcode rules, each requiring backward chaining of `!arr_get BC PC OP` at runtime (~5-10 backward-chaining steps via `arr_get/cons`, `arr_get/head`, arithmetic)
- **Specialized rules:** ~200-500 rules, zero backward chaining for dispatch

Whether specialization is actually faster depends on the relative cost of:
- Matching cost: more specific rules have smaller matching domains (more guards pre-evaluated away)
- Indexing cost: more rules require larger discriminant-tree or fingerprint structures
- Backward-chaining cost: current engine pays this for every `!arr_get` call at runtime

Based on the existing benchmark data in CALC (RES_0099, `tools/bench-compare.js`), backward chaining is a significant fraction of EVM execution time. Eliminating it via specialization is likely a net win for contract-specific workloads.

---

## 6. Simplify vs. Cross-Stage Specialization: Are They the Same?

### What `simplify` Does (RES_0099)

`simplify(target_rules, expansion_rules)` performs **cut on linear types**:
- Expansion rule: `A₁ * ... * Aₙ -o { M * B₁ * ... }` (introduces abstract linear type M)
- Target rule: `M * C₁ * ... -o { D₁ * ... }` (consumes M)
- Result: A₁ * ... * Aₙ * C₁ * ... -o { B₁ * ... * D₁ * ... }` (M eliminated)

The cut is on a **linear resource** — M is consumed and produced exactly once.

### What Cross-Stage Specialization Does

Cross-stage specialization performs **substitution on persistent (bang) facts**:
- Ground fact: `!arr_get [0x01, 0x02, ...] 0x00 0x01` is derivable from the bytecode
- Rule: `... * !arr_get BC PC 0x01 * ...` with `BC` bound to the specific bytecode
- Result: For `PC = 0x00`, the `!arr_get` check is eliminated; `0x01` is substituted for `OP`

The eliminated object is a **persistent resource** (`!P`) — it is not consumed. The operation is not cut on a linear type but resolution (unification + substitution) of a persistent goal.

### Key Structural Difference

| | `simplify` | Cross-Stage Specialization |
|---|---|---|
| Eliminated object | Linear resource (grade-1, consumed once) | Persistent fact (grade-0 / bang, not consumed) |
| Operation | Cut on linear type | Goal resolution / substitution |
| Proof theory | Multiplicative cut in ILL | Bang-left + dereliction in ILL, or SLD-resolution |
| Variables | Metavariables unified across the cut | PC unified to a concrete value; OP determined |
| Result | One composed rule per (producer, consumer) pair | Multiple specialized rules per (rule, PC-value) pair |
| Termination | Guaranteed if type graph is a DAG | Guaranteed if bytecode is finite |

These are **different operations** at different grades. `simplify` is linear cut; cross-stage specialization is persistent-goal pre-resolution.

However, they share a common **proof-theoretic character**: both eliminate intermediate proof obligations at compile time rather than deferring them to runtime. `simplify` eliminates linear resources; cross-stage specialization eliminates persistent lookups. Both produce strictly smaller residual proof search at runtime.

### Are They the Same at Different Grades?

There is a suggestive analogy: if one thinks of the persistent fact `!arr_get BC PC OP` as a "grade-0 resource" in a graded/QTT sense (RES_0101), then:

- Grade-1 (linear) cut: `simplify`
- Grade-0 (persistent) cut: cross-stage specialization

Under a graded semantics (semiring `{0, 1, ω}`), both are instances of "cut on a formula of grade `g`" where `g` determines whether the formula is consumed or duplicated. At grade 0, the cut formula is present in both the premise and conclusion (not consumed). This is dereliction: `!A ⊢ A, !A`.

So: **yes, they are the same operation at different grades**, if one has a graded treatment of the bang modality. In practice, the algorithms differ because grade-0 facts admit value substitution (you can compute `OP` from `BC` and `PC`), whereas grade-1 linear cut only rearranges resources without computing values.

---

## 7. Existing Systems with Contract-Specific Compilation

### Monad's Native Compiler (2024-2025)

Monad's EVM implementation uses a JIT compiler that:
- Tracks contracts by cumulative gas consumed
- For "hot" contracts, compiles bytecode to native x86-64
- **Specializes each EVM instruction to its operand locations**: AND can emit a single `vpand` when both operands are in AVX registers
- Caches compiled native code; falls back to interpreter for cold contracts

This is the first Futamura projection applied industrially: the EVM interpreter is specialized per contract bytecode, yielding a compiled form. The specialization is at the machine-code level (operand locations), not at the rule-matching level, but the principle is identical.

The dispatch structure mirrors what CALC's specialization would produce: for each bytecode position, a specialized handler with no dispatch overhead.

### weval (Fallin, PLDI 2025)

weval ("WebAssembly [partial] evaluator") implements offline PE for WebAssembly interpreters:
- Annotates interpreter variables as static or dynamic
- Uses the program counter as the "context" (static dimension)
- Unrolls the interpreter loop, producing one specialized basic-block per bytecode instruction
- Achieved 2.17× speedup on SpiderMonkey, 1.84× on Lua

This is exactly the first Futamura projection in practice, with the bytecode as static input. The key insight (identical to CALC's case): **the program counter is the dimension along which specialization unfolds**. For each `PC` value, a specialized handler is emitted.

weval's approach is **offline PE**: the user annotates `PC` as static and the bytecode as the static context. The specializer then unrolls the loop. This is the same as what CALC would do with a binding-time annotation marking `BC` as static in the `!arr_get` predicate.

### hevm and Symbolic Execution

hevm (RES_0004) uses a different approach: it does not specialize rules but instead performs symbolic execution with an SMT solver for constraint solving. The `!arr_get BC PC OP` lookup becomes a constraint over symbolic `PC`, solved by the SMT backend. This trades rule specialization for constraint propagation — more general (handles symbolic PC) but slower for concrete execution.

---

## 8. Mechanism Options for CALC

Four distinct implementation strategies, ordered by depth of integration:

### Option A: Ground-Fact Pre-Resolution (Shallow)

Before compiling rules, evaluate all `!P` goals where `P` is derivable from the initial persistent state. For each rule, attempt to resolve persistent prerequisites against the known ground facts.

- If `!arr_get BC PC OP` is ground for specific `(BC, PC)` pairs: substitute the ground `OP` into the rule and produce a specialized clone
- No change to the rule compilation pipeline (`compile.js`)
- New phase: `preResolve(rules, groundFacts)` before `compileRule()`

Analogous to **offline PE with a maximally polyvariant BTA**: one specialized rule per distinct ground substitution pattern.

### Option B: Interpreted-Phase PE (Medium)

Run a limited backward-chaining pass at compile time (a mini-interpreter over the persistent facts), evaluating all `!P` subgoals that can be resolved against ground facts. Substitute results back into rules.

This is closer to **online PE**: the specializer discovers which subgoals are ground-resolvable dynamically, without pre-declared binding times.

Handles chained lookups: `!arr_get BC PC OP`, then `!inc PC PC'`, etc. Can propagate the resolved `OP` value further if subsequent `!P` goals depend on it.

### Option C: `simplify`-Style Persistent Cut (Deeper)

Extend the `simplify` mechanism from linear cut to persistent cut:

- Treat `!arr_get BC PC OP` as a "persistent resource" produced by the bytecode initialization
- Model the pre-resolution as cut on `!P` (not `P`): the bang connective's `!L` rule allows the proof to use the fact multiple times
- The composed rule has the persistent prerequisite replaced by its ground value

This requires extending the existing multicategory composition (RES_0099) to handle bang-guarded prerequisites. The proof theory is sound (it is just the `!L` rule of ILL), but the implementation must be careful about:
- Multiple rules sharing the same `!arr_get` premise (fan-in)
- The fact that `!P` is not consumed, so the "elimination" is really substitution, not removal

### Option D: Full Supercompilation (Deep)

Implement a true driving/generalization loop over the rule set:
- Start with a specific bytecode fact as static context
- Drive the rules: symbolically execute, propagating ground values
- When a rule's persistent prerequisite is fully resolved, substitute and produce a specialized variant
- When a recursive pattern is detected, generalize (widen) to prevent divergence

The most powerful option. For the EVM case, it degenerates to options A/B since the recursion depth is bounded (array lookup is non-recursive for a fixed array). Overkill for the CALC use case, but the correct theoretical framework.

---

## 9. Summary of Theoretical Positions

| Concept | Theoretical Name | CALC Instance |
|---|---|---|
| `simplify(evm_rules, bytecode_facts)` | First Futamura projection | PE(EVM interpreter, specific bytecode) |
| Resolving `!arr_get BC PC OP` at compile time | Offline PE (polyvariant) / EDB specialization | Grade-0 cut / persistent substitution |
| `simplify` (linear cut on intermediate types) | Multiplicative cut in ILL / multicategory composition | Grade-1 cut |
| Difference between `simplify` and persistent-fact specialization | Cut at grade 1 vs grade 0 | Different grades of the same proof-theoretic operation |
| Code explosion with 500 specialized rules | Polyvariant specialization fan-out | Bounded by `|bytecode|` — always finite |
| Preventing divergence | Memoization + generalization (supercompilation) / BTA (PE) | Not needed for finite bytecode |
| Monad's JIT, weval | First Futamura projection in practice | Same principle, different substrate |

---

## References

- Futamura, Y. (1971/1983). "Partial Computation of Programs." *RIMS Symposia* / *Springer LNCS 147*.
- Jones, N.D., Gomard, C.K., Sestoft, P. (1993). *Partial Evaluation and Automatic Program Generation*. Prentice-Hall. ([Online](https://www.itu.dk/people/sestoft/pebook/))
- Turchin, V.F. (1986). "The Concept of a Supercompiler." *ACM TOPLAS*, 8(3):292-325. ([PDF](https://mazdaywik.github.io/direct-link/The%20Concept%20of%20a%20Supercompiler.pdf))
- Glück, R. and Sørensen, M.H. (1996). "Introduction to Supercompilation." *Partial Evaluation*, Springer LNCS 1110.
- Sørensen, M.H., Glück, R., Jones, N.D. (1996). "A Positive Supercompiler." *Journal of Functional Programming*, 6(6):811-838.
- Bolingbroke, M. and Peyton Jones, S. (2010). "Supercompilation by Evaluation." *Haskell Symposium*. ([PDF](https://www.researchgate.net/publication/221562973))
- Sumii, E. and Kobayashi, N. (2001). "A Hybrid Approach to Online and Offline Partial Evaluation." *Higher-Order and Symbolic Computation*, 14(2-3):101-142.
- Gallagher, J.P. (1993). "Tutorial on Specialisation of Logic Programs." *PEPM 1993*.
- Küngas, P. and Matskin, M. (2004). "Partial Deduction for Linear Logic." *DALT 2004*, LNCS 3476. (Referenced in RES_0099.)
- Lloyd, J.W. and Shepherdson, J.C. (1991). "Partial Evaluation in Logic Programming." *JLP*, 11(3-4):217-242.
- Bancilhon, F., Maier, D., Sagiv, Y., Ullman, J. (1986). "Magic Sets and Other Strange Ways to Implement Logic Programs." *PODS 1986*.
- Fallin, C. (2025). "Partial Evaluation, Whole-Program Compilation." *PLDI 2025*. ([PDF](https://cfallin.org/pubs/pldi2025_weval.pdf))
- Monad. "JIT Compilation." *Monad Developer Documentation*. ([Link](https://monad-docs-lb3l7tky7-monad-xyz.vercel.app/monad-arch/execution/native-compilation))
- Meseguer, J. and Montanari, U. (1990). "Petri Nets Are Monoids." *Information and Computation*, 88(2):105-155.

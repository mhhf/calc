---
title: Running Programs Before They Run
part: 5
partTitle: The Frontier
chapter: 20
summary: Grade-0 resources exist only at compile time — the cut rule eliminates them before execution, fusing producer and consumer rules into one, and that is partial evaluation as proof theory.
---

Chapter 17 showed how sorts carve a population into named groups before the
scheduler ever sees a token.
This chapter goes further back: some computation happens before the program
starts at all — during the loading step that turns source text into rules.

## A shared ingredient nobody eats

Imagine two chefs on an assembly line.

- Chef A takes raw apples, produces apple-paste.
- Chef B takes apple-paste, produces pie.

Nobody ever *serves* apple-paste.
It is a private intermediate that connects the two chefs.
If you want to write the full recipe in one step you just write:
raw apples → pie, and apple-paste never appears on any plate.

That is cut elimination.
The shared formula between two sequents is called the **cut formula**.
Eliminating it means merging the two derivations into one.

## Grade-0: a compile-time intermediate

In CALC a formula marked `!_0` (bang-at-grade-zero) is the logic's way of
saying: "this fact only needs to exist during rule loading — never at
runtime."

Think of `!_0 B` as a promise:

> "Rule 1 will produce B.  Rule 2 will consume it.  Nobody else needs it.
> Please fuse them now."

At runtime the fact B never enters any state.
It is cut away before `settle` takes its first step.

## The cut rule

The cut rule says: if you can prove $\Gamma_1 \vdash B$ and you can prove
$B, \Gamma_2 \vdash C$, you can derive $\Gamma_1, \Gamma_2 \vdash C$
directly.
The intermediate $B$ is gone.

Try the three-step version yourself.

```{prove}
goal: a -o b, b -o c, a |- c
title: A chain composes into one step
hint: Apply the first implication to consume a and produce b, then apply the second to consume b and produce c.
id: ch20-chain
rules: loli_l, id
```

In the widget you watched `b` appear briefly as a hypothesis and then
disappear into `c`.
That is exactly what the compiler does with grade-0 facts — the only
difference is that it happens before execution, not during.

## Two rules and a grade-0 intermediate

Here is what two forward rules connected by a grade-0 intermediate look like
in the calculus, and what the compiler produces from them.

```{mermaid}
flowchart LR
  subgraph before["Before loading"]
    R1["Rule 1\nΓ₁ ⊢ {!₀ B}"]
    B["!₀ B\n(grade-0 fact)"]
    R2["Rule 2\n!₀ B ⊗ Γ₂ ⊢ {Δ}"]
    R1 -->|produces| B
    B -->|consumed by| R2
  end
  subgraph after["After loading (fused)"]
    RF["Fused rule\nΓ₁ ⊗ Γ₂ ⊢ {Δ}"]
  end
  before -->|"compose.js\n(cut elimination)"| after
```

The compiler runs `compose.js`, finds every producer–consumer pair linked by a
grade-0 formula, and calls `composePair` — one cut step per pair.
What comes out is a single rule.
The intermediate fact was scaffolding; the scaffold is gone.

## Why this is partial evaluation

Partial evaluation (PE) is the idea of running the parts of a program you
already know, leaving only the parts that depend on unknown inputs.

Grade-0 cut is exactly this:
- The grade-0 formulas encode everything fixed at load time (opcode tables,
  constant tables, sort sizes).
- The cut step evaluates the fixed parts.
- What remains is a rule whose antecedent asks only for runtime resources
  (gas, stack, memory).

The first **Futamura projection** says: specializing an interpreter against a
fixed program produces a compiled version of that program.
In CALC that is not engineered separately — it falls out of cut admissibility.
The loading step IS the specializer; the composed rules ARE the compiled
program.
Correctness is not a separate theorem; it is the definition of cut.

```{prove}
goal: !(a -o b), !(b -o c), a |- c
title: Reusable rules compose at any grade
hint: The bangs mean the implications can be used more than once — but here one use each is enough.
id: ch20-bang-chain
rules: dereliction, loli_l, id
```

The `!` in this widget plays the role of grade-0 in the engine: the rules
themselves are static, shared, not consumed.
The proof thread walks the chain just as `compose.js` walks the rule pairs.

## Chain fusion

When rules form a longer chain — A produces B, B produces C, C produces D —
the compiler follows the chain greedily, fusing step by step.
The result is one rule: A produces D.
No intermediate fact is ever created.

This is basic-block fusion in a compiler, derived from the cut rule.

Concretely: in the EVM model, a sequence of five arithmetic opcodes shares a
program-counter threading predicate `pc(N)`.
After fusion those five rules collapse into one.
At runtime there is one match, one firing, and no intermediate `pc` facts.

## SROA: splitting aggregates

A second optimization, **Scalar Replacement of Aggregates (SROA)**, goes in
the opposite direction of fusion.

Suppose a rule carries an array fact `stack( acons(A, acons(B, empty)) )`.
Every access to the array has to traverse the list structure.
SROA replaces this single aggregate resource with individual scalar resources
`slot_0(A) * slot_1(B)`.
Each slot is a separate linear fact; array access becomes direct match.

The justification is the same: SROA is cut elimination on the array-access
predicates.
McCarthy's select/store axioms are the rules; SROA is the compiler solving
them at load time when the indices are ground.

## The fusion–symex spectrum

Compile-time fusion and runtime symbolic execution are **the same
computation** scheduled at different times.

Fusing two rules via cut produces one rule.
Running those two rules in the symex engine fires them one after the other.
Both produce the same final state.
The difference is only granularity: how many cut steps happen before `settle`
starts, versus how many happen as `settle` fires rules.

Moving work left (to load time) reduces runtime steps but requires the
information to be available at load time.
Moving work right (to runtime) handles unknowns but costs one match per step.
Every point on the spectrum is correct; the question is which is faster for a
given program.

## Supercompilation

Combining grade-0 cut (partial evaluation) with exhaustive exploration
(`explore()`) gives **supercompilation** for linear logic.
Partial evaluation fuses the static parts; driving symbolically executes the
dynamic parts along every branch, detecting cycles and memoizing repeated
configurations.
CALC's `explore()` is the driving machine; the compose pipeline is the PE
phase; together they form the first resource-aware supercompiler — one where
every branch respects linear consumption.

## Quiz

```{quiz, id=ch20-q1}
Q: A fact marked `!_0` appears in a running till program's state. Is that possible?
- [ ] Yes — grade-0 facts are just very fast to look up.
- [ ] Yes — they are consumed on the first step and then gone.
- [x] No — grade-0 facts are eliminated by the compiler before execution starts.
explanation: Grade-0 means "compile-time only." The cut step that eliminates a grade-0 intermediate runs during loading. No grade-0 formula ever enters a runtime state.
```

```{quiz, id=ch20-q2}
Q: The first Futamura projection says specializing an interpreter against a program gives what?
- [ ] A proof of correctness for the program.
- [x] A compiled version of the program — specialized rules with fixed parts already evaluated.
- [ ] A new interpreter for a different language.
explanation: The first projection is: specialize(interpreter, program) = compiled-program. In CALC this is grade-0 cut elimination: load the bytecode as grade-0 facts, compose against the interpreter rules, get per-opcode rules with no runtime bytecode lookup.
```

```{quiz, id=ch20-q3}
Q: What happens to the intermediate fact `B` when two rules are fused via cut elimination?
- [ ] It becomes a persistent fact shared by all consumers.
- [ ] It is stored in the state and matched at runtime.
- [x] It disappears entirely — at compile time, leaving no runtime trace.
explanation: Cut elimination removes the cut formula. The intermediate B was compile-time scaffolding connecting producer to consumer. After fusion the fused rule has B in neither its antecedent nor consequent.
```

## What you learned

- A resource marked `!_0` is a **compile-time intermediate**: it connects two
  rules at load time and is eliminated before any runtime state is created.
- The **cut rule** fuses a producer and a consumer by removing their shared
  formula.
  `compose.js` runs this for every grade-0 pair during loading.
- This is **partial evaluation** as proof theory — the first Futamura
  projection, correct by cut admissibility, not by a separate argument.
- **Chain fusion** collapses $A \to B \to C$ pipelines.
  **SROA** splits aggregate facts into scalars.
  Both are instances of compile-time cut.
- Compile-time fusion and runtime exploration sit on a **spectrum** — both
  sequences of cut steps, differing only in when they run.
- **Supercompilation** = grade-0 composition + exhaustive exploration.

## Going deeper

- [[theory/0016_partial-evaluation-as-cut-elimination|THY_0016: Partial Evaluation as Cut Elimination]] — the full Futamura derivation and the grade × quantifier framework for compile-time tabling.
- [[theory/0017_resource-aware-supercompilation|THY_0017: Resource-Aware Supercompilation]] — how CALC's `explore()` maps to driving, generalization, and folding.
- [[documentation/grade0-composition|Grade-0 Composition Pipeline]] — the seven-pass `compose.js` pipeline in detail.
- [[documentation/fusion-symex-spectrum|The Fusion–Symex Spectrum]] — where each point on the compile/runtime spectrum saves work.

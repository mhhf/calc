---
title: "Data as Terms"
part: 2
partTitle: Logic that Runs
chapter: 9
summary: How CALC encodes numbers as constructor terms, why predicates like plus and inc are backward-chaining logic programs, and how the engine answers persistent goals by running those programs.
---

## Where does data come from?

Chapter 6 showed how the engine searches for proofs by applying rules.
This chapter asks a different question: when a forward rule checks a condition like
$!\text{inc}\ N\ M$, what exactly is it checking — and how does the engine answer it?

The answer is a small logic program.
Data — numbers, lists, memory states — is encoded as **constructor terms**.
Facts about data — "the successor of 3 is 4", "2 plus 3 equals 5" — are
**propositions** proved by **backward-chaining clauses** that pattern-match on those constructors.

## Numbers are constructors

CALC uses a **binary number** encoding.
A number is a tree built from three constructors:

| Constructor | Meaning | ASCII |
|---|---|---|
| `e` | end of bits (zero) | `e` |
| `i X` | prepend a 1-bit (LSB) to X | `i` |
| `o X` | prepend a 0-bit (LSB) to X | `o` |

Bits are stored **least-significant first**.
The value of a term is $\text{val}(e) = 0$,
$\text{val}(i\ X) = 1 + 2 \cdot \text{val}(X)$,
$\text{val}(o\ X) = 2 \cdot \text{val}(X)$.

Six numbers written out:

| Number | Term | Read the bits |
|---|---|---|
| 0 | `e` | empty |
| 1 | `i e` | 1 |
| 2 | `o (i e)` | 0, 1 |
| 3 | `i (i e)` | 1, 1 |
| 5 | `i (o (i e))` | 1, 0, 1 |
| 6 | `o (i (i e))` | 0, 1, 1 |

These are just **terms** — inert data, like nodes in a tree.
Nothing happens to them until a clause or forward rule pattern-matches on them.

## Backward clauses: logic programs over terms

The file `calculus/ill/programs/bin.ill` defines predicates over these terms.
Here are the clauses for `inc` (increment):

```
inc: (n: bin) -> (result: bin) -> type.

inc/z2: inc e (i e).
inc/z1: inc (o X) (i X).
inc/s:  inc (i X) (o Y)
          <- inc X Y.
```

Read each clause as a **case**:
- `inc/z2`: the successor of 0 is 1. ($e \mapsto i\ e$)
- `inc/z1`: if the last bit is 0 (term starts with `o`), flip it to 1. ($o\ X \mapsto i\ X$)
- `inc/s`: if the last bit is 1, flip it to 0 and **carry** into the rest. ($i\ X \mapsto o\ Y$ where $Y = X + 1$)

The `<-` arrow introduces premises (sub-goals).
`inc/s` is recursive: to increment $i\ X$, first increment $X$ to get $Y$, then yield $o\ Y$.

## A derivation by hand

Let us prove $!\,\text{inc}\ (i\ e)\ (o\ (i\ e))$, i.e., the successor of 1 is 2.

The engine unifies the goal $\text{inc}\ (i\ e)\ R$ against the clause heads:
- `inc/z2` has head `inc e (i e)` — no match (`e ≠ i e`).
- `inc/z1` has head `inc (o X) (i X)` — no match (`o X ≠ i e`).
- `inc/s` has head `inc (i X) (o Y)` — **matches** with $X = e$.

Now the premise becomes $\text{inc}\ e\ Y$:
- `inc/z2` has head `inc e (i e)` — **matches** with $Y = i\ e$.

Substituting back: $R = o\ (i\ e)$, i.e., 2.

$$
\dfrac{
  \dfrac{}{\text{inc}\ e\ (i\ e)} \quad \text{inc/z2}
}{
  \text{inc}\ (i\ e)\ (o\ (i\ e))
} \quad \text{inc/s, } X{=}e,\, Y{=}i\,e
$$

Every `!inc` goal in a forward rule triggers exactly this pattern-matching search.

## Terms, Resources, and Propositions — for numbers

Chapter 2 introduced the three categories.
Numbers illustrate them concretely:

| What | Category | Why |
|---|---|---|
| `i (i e)` (the value 3) | **Term** | It IS the number 3 — inert constructor |
| `num_res (i e)` | **Resource** | You POSSESS a counter at 1 — consumed and produced |
| `!inc (i e) (o (i e))` | **Proposition** | You KNOW that $\text{succ}(1) = 2$ — proved on demand |

The test: *"Can I write down what this object IS?"*
A term passes — `i (i e)` is exactly what the number 3 is.
A resource fails — a counter at 1 is something you hold, not something you describe by structure.
A proposition fails too — $\text{succ}(1) = 2$ is something you know, derived from the term structure.

## Exercises

### Applying a single rule

A forward rule `tick: num_res N -o { exists M. !inc N M * num_res M }` is morally like
the backward clause `inc/s`: a persistent fact (the rule body) applied to a linear resource.

At the logic level, `!-formulas` behave as reusable rules.
Let `a` and `b` be atoms standing for two counter states.
Apply the "rule" `a -o b` once to transform `a` into `b`.

```{prove}
goal: !(a -o b), a |- b
title: Apply a rule once
hint: Use dereliction to get the loli, then loli_l to consume a.
id: ch9-apply-rule
rules: dereliction, loli_l
```

### A two-step derivation

The `inc/s` clause calls itself recursively — two clause steps to compute
$\text{succ}(1) = 2$.
The same shape appears in chained rule applications.

```{prove}
goal: !(a -o b), !(b -o c), a |- c
title: Two-step chain
hint: Derelict both bang-formulas, then apply loli_l twice in sequence.
id: ch9-chain
rules: dereliction, loli_l
```

### A rule that produces a pair

The `tick` rule produces a pair: the evidence `!inc N M` and the new counter `num_res M`.
At the logic level, a rule producing two outputs looks like `a -o b * c`.

```{prove}
goal: !(a -o b * c), a |- b * c
title: Rule with two outputs
hint: Derelict the bang, apply loli_l to consume a, then id closes each component.
id: ch9-pair-output
rules: dereliction, loli_l, id
```

## Watch the counter run

The program below imports the binary arithmetic library and defines
a single-resource counter.
The `tick` rule calls `!inc` — the engine backward-chains into `bin.ill`
to find the successor term, then produces it as the new counter value.

```{exec ill}
file: doc/book/programs/counting.ill
query: expect_go_count
maxSteps: 6
title: Binary counter stepping 0 → 1 → 2 → 3 → …
```

Look at the `produced` column in each step.
The `!inc(0, 1)` fact is the proved proposition — evidence the engine
derived from the `inc` clauses.
The `num_res(1)` fact is the new resource — the counter value, encoded as a hash
of the constructor term `i e`.

## The FFI principle

Running `inc` by pattern-matching clauses is correct but slow for large numbers.
CALC therefore provides a **foreign function interface** (FFI) that computes the
same answer natively in JavaScript.

The contract: every FFI predicate has backward clause definitions.
The clauses are the **semantics** — they define what is true.
The FFI is pure **optimization** — faster on concrete numerals, but gives the
same result.
Turn the FFI off and clause resolution takes over, a bit slower, identical answers.

This is why the counting widget shows clean steps even though no bytecode runs:
the clause version and the FFI version are interchangeable.

## Quiz

```{quiz, id=ch9-q1}
Q: What is the binary constructor term for the number 3?
- [ ] `o (o e)`
- [x] `i (i e)`
- [ ] `i (o e)`
- [ ] `e e`
explanation: Bits are least-significant first. 3 in binary is 11. LSB=1 gives `i`, next bit=1 gives another `i`, then `e` ends the chain. So 3 = i(i(e)).

Q: The goal `!inc N M` inside a forward rule is a:
- [ ] Term — it is an inert constructor
- [ ] Resource — it is consumed when the rule fires
- [x] Proposition — it is proved by backward chaining into inc clauses
- [ ] A type declaration
explanation: `!` marks a persistent premise. The engine proves it by backward chaining (pattern-matching the inc clauses). It is not consumed — it stays in the state as evidence.

Q: What does the `<-` arrow mean in an `inc` clause?
- [ ] A linear implication (loli) — the premise is consumed
- [x] A backward premise — the engine must prove the sub-goal to fire the clause
- [ ] A resource production step
- [ ] A type annotation
explanation: In backward clauses, `<-` introduces sub-goals. To apply `inc/s`, the engine must first prove `inc X Y` — a recursive call. This is Prolog-style backward chaining, not a linear rule.

Q: The number 6 = o(i(i(e))). Why does the encoding start with `o`?
- [x] The least-significant bit of 6 is 0, represented by `o`
- [ ] `o` means "odd"
- [ ] The `o` constructor doubles the number
- [ ] It is an arbitrary choice with no numeric meaning
explanation: Bits are stored LSB-first. 6 in binary is 110, LSB=0. The `o` constructor prepends a 0-bit: val(o X) = 2·val(X). So o(i(i(e))) = 2·val(i(i(e))) = 2·3 = 6.
```

## What you learned

- **Constructor terms** encode data without computation.
  Numbers are trees: `e` (zero), `i X` (2X+1), `o X` (2X), bits least-significant first.
- **Backward clauses** are pattern-matching cases over constructors.
  They define predicates like `inc` and `plus` by structural recursion.
- **Propositions** (`!inc N M`) are proved on demand by backward chaining into these clauses.
  They are not consumed — they are evidence placed in the state.
- **Resources** (`num_res N`) are linear: consumed once, produced once.
  They hold the current value as a term argument.
- **FFI is optimization**, not semantics.
  The clauses define what is true; the FFI just answers faster on concrete values.

## Going deeper

- [[documentation/term-resource-proposition]] — full decision guide: Term vs. Resource vs. Proposition with EVM-domain examples.
- [[documentation/numeric-tower]] — how binary terms and rational literals coexist, equational theories, and the cross-tag matching that makes mixed arithmetic work.
- [[documentation/backward-prover]] — the four-layer backward prover (L1–L4) that the engine invokes when solving `!inc` goals.

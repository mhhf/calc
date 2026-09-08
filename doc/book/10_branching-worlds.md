---
title: "Branching Worlds"
part: 2
partTitle: Logic that Runs
chapter: 10
summary: When data is symbolic, a rule that tests it cannot pick a side — oplus splits the state into both worlds, and exhaustive exploration follows every branch.
---

Chapter 6 showed how the backward prover searches for a proof by focusing and inverting rules.
This chapter turns to a different kind of search: **running a program when the data is unknown**.

## The problem with unknowns

Consider a rule for a coin-toss machine:

```
toss: flip -o { heads + tails }.
```

The resource `flip` is consumed; the machine produces either `heads` or `tails`.
If you run this with a concrete token, you get one outcome.
But what if the outcome depends on a **symbolic value** — something that will only be concrete at runtime?

A guard like `!eq Cond 0` fails when `Cond` is symbolic: the FFI cannot evaluate it.
Execution halts prematurely.

The correct object for "the system will decide, but we do not yet know which" is `+` (oplus) — exactly the internal-choice connective from chapter 4.
No guard needed.
The oplus records both possibilities and leaves the resolution to the explorer.

---

## Two execution modes

When a rule fires and produces `A + B`, a forward engine faces a fork.
CALC supports two modes:

**Committed-choice (exec):** Pick one branch and keep going.
Fast. Deterministic. Produces a single final state.

**Exhaustive exploration (explore / symex):** Take both branches.
Build a **tree** of executions. Every leaf is one complete path through the program.

The widgets in this chapter let you see both.

---

## Exec: one committed path

Here is the coin-flip machine as a tiny ILL program.

```{exec ill}
% Coin-flip machine.
flip: type.
heads: type.
tails: type.
prize: type.
bust: type.

toss: flip -o { heads + tails }.
win:  heads -o { prize }.
lose: tails -o { bust }.

#expect_go flip => prize .
```

Step through the execution.
You will see: `toss` fires and commits to `heads`; then `win` fires and produces `prize`.
The `tails` branch is never visited.

This is committed-choice: when the engine sees `heads + tails`, it picks `heads` and moves on.
The other world simply does not exist in this run.

---

## Symex: all paths at once

The proof-tree below runs the **same program** under exhaustive exploration.
Instead of committing, the engine forks at the `toss` step and follows both branches simultaneously.

```{proof ill symex}
#import(programs/toy-branch.ill)
```

Two leaves appear:

| Leaf | Path | Final state |
|------|------|-------------|
| 1 | `toss → win` | `prize` |
| 2 | `toss → lose` | `bust` |

Every possible execution is present.
No world is missed.

---

## The proof obligation

Why is oplus the right connective here?
Because the **consumer** (the next rule) must be prepared for both outcomes.
Recall the `oplus_l` rule from chapter 4:

```{rule oplus_l}
```

Both premises share the same remaining context $\Delta$.
This is not duplication — the two branches are **alternatives**: exactly one will actually hold at runtime.
Linear resources are not copied; they are split across mutually exclusive worlds.

```{exercise, title=Handle both sides}
You receive `heads + tails` and must re-deliver them in the opposite order: `tails + heads`.
Prove it in the widget below — you must case-split and handle each branch.
```

```{prove}
goal: heads + tails |- tails + heads
title: Two worlds, reordered
hint: Apply oplus_l to split on heads or tails. In the heads branch, use oplus_r2 and id. In the tails branch, use oplus_r1 and id.
id: ch10-case-split
rules: oplus_l, oplus_r1, oplus_r2, id
```

```{solution}
Apply `oplus_l`: two subgoals appear, one per incoming branch.
In the `heads` branch: you have `heads |- tails + heads`. Apply `oplus_r2` to select the right side; close with `id`.
In the `tails` branch: you have `tails |- tails + heads`. Apply `oplus_r1` to select the left side; close with `id`.
```

---

## Scaling up: the multisig contract

A symbolic EVM execution makes this concrete.

The multisig contract checks whether a proposal has enough signatures, then either transfers funds or reverts.
The bytecode uses comparison opcodes (`EQ`, `GT`, `ISZERO`) whose results depend on symbolic storage values.
Each comparison is modeled as a rule that produces `(result_true * !path_cond_true) + (result_false * !path_cond_false)`.

The explorer exhaustively follows every branch at every `JUMPI` instruction.
Infeasible branches — those with contradictory path conditions — terminate early and are pruned.
Feasible branches run to `STOP` or `REVERT`.

The `{proof ill symex}` block below runs the full symbolic execution.
Use the **Skeleton** toggle to see the branching shape; click a leaf to inspect its trace.

```{proof ill symex}
#import(programs/multisig_nocall_solc_symbolic.ill)
```

**31 feasible leaves.** Each leaf is a distinct execution path through the contract.
The tree has 1987 nodes and 8733 total rule applications.
All of it is driven by the same exhaustive forward engine — no special EVM logic.

---

## Path conditions accumulate

When the `+` rule fires, each branch inherits a **persistent fact** recording which side was taken.
For example:

```
(!neq C 0 * take_branch) + (!eq C 0 * skip_branch)
```

Later rules can consult `!neq C 0` to guard execution.
On a ground value like `C = 5`, the branch where `!eq 5 0` is asserted is immediately inconsistent — the FFI can detect it and mark that leaf infeasible.
This is how exhaustive exploration stays efficient for ground programs.

---

```{quiz, id=ch10-q1}
Q: In `exec` mode, when a rule produces `A + B`, what happens?
- [x] The engine picks one branch (committed choice) and continues with it.
- [ ] The engine halts and asks the user to choose.
- [ ] Both branches are explored simultaneously.
- [ ] The engine backtracks until only one branch remains provable.
explanation: Exec uses committed choice — it selects one branch (typically the first available) and proceeds. The other branch is simply not explored.

Q: In symbolic execution (symex), who "decides" which branch of `A + B` to take?
- [ ] The prover (it picks the branch it can prove).
- [ ] The environment (an external input resolves the choice).
- [x] Nobody — both branches are explored as separate worlds.
explanation: Symex is don't-know nondeterminism: no agent decides. The engine forks and follows every possibility. This is the key difference from both committed-choice (exec) and external choice (&, where the consumer decides).

Q: In the sequent rule for `oplus_l`, both branches share the same context $\Delta$. Why is this not a violation of linearity?
- [ ] The linear resources are copied into each branch.
- [ ] Only one branch uses $\Delta$; the other discards it.
- [x] The branches are alternatives — exactly one holds at runtime, so $\Delta$ is consumed once.
- [ ] $\Delta$ is persistent, so it may be used any number of times.
explanation: Oplus branches are mutually exclusive alternatives. At runtime, one branch is actual and consumes $\Delta$ linearly. The shared context in the rule reflects that we do not yet know which branch will be taken — not that both will run simultaneously.

Q: What is the difference between `A & B` (with) and `A + B` (oplus) in the context of symbolic execution?
- [ ] They are equivalent — both lead to case splits.
- [x] With (&) is external choice (the consumer picks); oplus (+) is internal choice (the system commits — or we explore both).
- [ ] Oplus is used for persistent facts; with is used for linear resources.
- [ ] With always requires a guard; oplus does not.
explanation: & means the consumer has a choice between A and B — for example, a loli guard that requires evidence before choosing. + means the system has already decided (or the decision is deferred to the explorer). In symex, + triggers a fork; & defers until a guard is satisfied.
```

---

## What you learned

- When a rule fires with a **symbolic value**, oplus (`+`) records both possibilities without evaluating the unknown.
- **Exec** follows one committed path: fast and deterministic, but misses branches.
- **Symex** follows every path: it builds an exhaustive tree of executions, one leaf per outcome.
- The `oplus_l` rule gives case analysis with a **shared context** — branches are alternatives, not parallel copies.
- Path conditions accumulate as persistent facts; infeasible branches are pruned when a contradiction is detected.
- The multisig contract explores **31 feasible execution paths** entirely within the forward engine, with no special EVM logic.

---

## Going deeper

- [[theory/0004_symbolic-branching|Symbolic Branching in ILL Forward Chaining]] — the theoretical analysis: why oplus is correct, why & is wrong for comparisons, the DNF analogy, and how this relates to CHR∨.
- [[documentation/forward-chaining-engine|Forward Chaining Engine]] — the three-layer architecture (generic core, family layer, ILL layer) that drives both exec and explore.
- [[documentation/calc-vs-hevm|CALC vs hevm]] — how this approach compares to hevm-style symbolic execution: the role of path conditions, infeasible-branch pruning, and what the linear-logic encoding buys over a traditional SMT-based approach.

---
title: "Rules as Machines"
part: 2
partTitle: Logic that Runs
chapter: 7
summary: How forward rules become rewriting machines that fire step by step, consuming and producing resources until no rule can fire.
---

## From searching to running

Chapter 6 showed how the prover searches *backward* through rule trees, backtracking when a branch fails.
This chapter flips the direction: rules become **machines that run forward**, consuming inputs and producing outputs one step at a time.

The two modes are genuinely different.
Backward search finds proofs; forward execution runs programs.
You will use both — Chapter 8 shows how they connect — but for now, think of forward execution as a step-by-step process with no undo.

## The state is a multiset

The engine tracks a **state**: a multiset of facts (also called resources or tokens).
A multiset is like a bag — order does not matter, but multiplicity does.

| State | Meaning |
|---|---|
| `{ coin, coin, key }` | two coins and one key |
| `{ coin, coin }` | two coins (no key) |
| `{ coffee }` | one cup of coffee |

Every fact in the state is a **linear resource**: it exists exactly once.
You cannot duplicate it or ignore it; you can only consume it.

## A forward rule fires

A forward rule looks like this:

```{calc}
coin * coin -o { coffee }
```

Read it: "if the state contains two coins, consume them and produce one coffee."

The **braces** `{ coffee }` mark the output as a computation — Chapter 8 explains the monad behind them.
For now just read `{ ... }` as "produces these resources."

The full program declaration adds a name:

```
vend: coin * coin -o { coffee }.
```

Every forward program also needs **type declarations** so the engine knows which atoms are tokens:

```
coin: type.
coffee: type.
vend: coin * coin -o { coffee }.
```

When the engine sees two `coin` facts in the state, `vend` **fires**: both coins are consumed and one `coffee` is produced.
That single fire is one step.

## Your first machine

The widget below starts with two coins in the state.
Click **Step** to fire one rule and watch the state change.
After one step the machine is quiet — no rule can fire on `coffee`.

```{exec ill}
source: |
  coin: type.
  coffee: type.
  vend: coin * coin -o { coffee }.
  #expect_go coin * coin => coffee .
maxSteps: 5
title: The coin-coffee machine
```

The display shows:
- **consumed** — facts removed from the state
- **produced** — facts added to the state
- **state** — what remains after the step

## A chain of rules

Rules compose.
The output of one rule becomes the input of the next.

Here is a two-rule carpentry program:

```
log: type.
plank: type.
table: type.

chop: log -o { plank * plank }.
join: plank * plank -o { table }.
```

Starting from one `log`:
1. `chop` fires — consumes `log`, produces two `plank`
2. `join` fires — consumes two `plank`, produces one `table`

Step through it and watch the intermediate state.

```{exec ill}
source: |
  log: type.
  plank: type.
  table: type.
  chop: log -o { plank * plank }.
  join: plank * plank -o { table }.
  #expect_go log => table .
maxSteps: 5
title: Chop and join — a two-step chain
```

Notice that the engine never "remembered" what it was trying to prove.
It just matched the available facts against rule antecedents, fired the first match, and repeated.

## Committed choice: one path, no regrets

When several rules could fire, the engine picks one and **never goes back**.
This is called **committed choice**.

It is the opposite of the backward prover in Chapter 6, which backtracks whenever a branch fails.
The forward engine trades completeness for speed: one fixed execution path, no search tree.

```{exercise, title=Two rules, two coins}
Suppose the state is `{ coin, coin }` and the program has two rules:

```
vend: coin * coin -o { coffee }.
save: coin -o { piggy }.
```

Which rule fires first?
What is the final state?
```

```{solution}
`vend` fires first — it matches both coins at once.
After firing, the state is `{ coffee }` and `save` has nothing to match.
The final state is `{ coffee }`.

The engine picked `vend` because it was declared first and matched.
Committed choice means it never reconsidered to try `save`.
```

## Quiescence: when the machine stops

The engine keeps firing until **no rule can fire**.
That state is called **quiescent**.

Quiescence happens for one of two reasons:

1. The state is empty.
2. No rule's antecedent matches what is in the state.

In the carpentry example the machine stops at `{ table }` because neither `chop` nor `join` can match a `table`.
The machine has done all the work it can.

## Keeping a resource: the `$` prefix

Sometimes a rule needs a resource but must not destroy it.
Mark it with `$` to say "consume and re-produce identically":

```
key: type.
door: type.
open: type.

unlock: $key * door -o { open }.
```

`$key` means the key is *used but returned*.
The rule consumes `key` internally, does its work, and puts `key` back into the state unchanged.
The door, however, is gone — it was consumed without `$`.

```{exec ill}
source: |
  key: type.
  door: type.
  open: type.
  unlock: $key * door -o { open }.
  #expect_go key * door => open * key .
maxSteps: 5
title: Preserved resource — the key survives
```

Step through and confirm that `key` appears in the final state alongside `open`, even though the rule consumed it.
The `$` sugar desugars to consuming and re-producing the fact; the engine sees it as preserved and skips it in the diff display.

## Quiz

```{quiz, id=ch7-q1}
Q: Start with one `log`. The program has two rules: `chop: log -o { plank * plank }.` and `join: plank * plank -o { table }.`. What is the quiescent state?
- [ ] `{ log }`
- [ ] `{ plank, plank }`
- [x] `{ table }`
- [ ] `{ plank }`
explanation: chop fires first (log → plank * plank), then join fires (plank * plank → table). The machine stops at { table } because no rule matches a single table.

Q: What does committed choice mean in the forward engine?
- [ ] The engine tries every possible rule order and merges the results.
- [x] The engine picks one applicable rule and never backtracks.
- [ ] The engine backtracks whenever a branch fails, like backward search.
- [ ] The engine fires all applicable rules simultaneously.
explanation: Committed choice means the engine selects the first matching rule and executes it without any backtracking. This makes forward execution fast but deterministic along one path.

Q: In the rule `unlock: $key * door -o { open }.`, what happens to `key` after firing?
- [x] It is consumed and then re-produced — it stays in the state.
- [ ] It is consumed and destroyed.
- [ ] It is copied into two keys.
- [ ] It is moved to the persistent zone and never touched again.
explanation: The $ prefix marks a resource as preserved — consumed by the rule and identically re-produced in the output. The door is consumed without $, so it disappears. The key survives.
```

## What you learned

- The **state** is a multiset of linear resources, each existing exactly once.
- A **forward rule** `name: A * B -o { C * D }.` fires when its antecedent matches the state, consuming the matched facts and producing the consequent.
- Rules **chain** naturally: the output of one rule becomes the input of the next.
- **Committed choice** means the engine picks one firing and never backtracks — execution is fast and deterministic along one path.
- **Quiescence** is when no rule can fire; the machine has finished.
- The **`$P` prefix** marks a resource as preserved — consumed and identically re-produced, so it stays in the state after the rule fires.
- The braces `{ ... }` in the consequent are Chapter 8's subject: the lax monad that separates the forward and backward worlds.
- The CALC forward engine is a variant of Constraint Handling Rules (CHR): linear antecedents are CHR's removed heads, persistent antecedents are kept heads, and committed-choice execution corresponds to CHR's simpagation semantics — see [[def/0002_chr-rule-types]].

## Going deeper

- [[documentation/forward-chaining-engine]] — the full three-layer architecture (generic core, LNL family, ILL layer) with matching pipeline and strategy stack diagrams.
- [[def/0002_chr-rule-types]] — the three CHR rule types (simplification, propagation, simpagation) and how CALC forward rules correspond to simpagation.
- [[documentation/architecture]] — how the forward engine fits alongside the backward prover in the wider CALC system.

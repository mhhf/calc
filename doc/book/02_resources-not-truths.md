---
title: Resources, Not Truths
part: 1
partTitle: Proofs as Trees
chapter: 2
summary: Linear logic treats hypotheses as resources consumed exactly once — not facts you can reuse forever.
---

## The vending machine problem

You put one coin in a vending machine. You press the button. You get one coffee. You no longer have the coin.

Classical logic does not model this. In classical logic, if you *know* that you have a coin, that knowledge stays true after you spend it. You could "buy" coffee forever from a single coin because the fact `coin` never disappears.

Linear logic fixes this. Here, `coin` is a **resource** you possess, not a truth you know. Once you spend it, it is gone.

This single idea — hypotheses are consumed, not remembered — is the heart of linear logic.

## Hypotheses vanish when used

In an ordinary sequent $P \vdash Q$, the hypothesis $P$ is a fact. You could use it ten times. You could ignore it. Nothing is tracked.

In a linear sequent, every hypothesis on the left must be used **exactly once**. No more, no less.

Two immediate consequences:

**You cannot copy a resource.** The sequent $P \vdash P \otimes P$ says: "from one $P$, produce two $P$s." Under resource accounting that is impossible. One coin does not become two.

**You cannot discard a resource.** The sequent $P, Q \vdash P$ says: "given $P$ and $Q$, prove $P$." But what happened to $Q$? You threw it away. Under use-exactly-once, that is not allowed.

```{quiz, id=ch2-q1}
Q: Which of these sequents do you expect to hold under linear logic?
- [ ] `P |- P * P`
- [x] `P |- P`
- [ ] `P, Q |- P`
- [x] `P, Q |- Q * P`
explanation: `P |- P` uses one resource once — fine. `P, Q |- Q * P` uses both P and Q exactly once (tensor collects them both). `P |- P * P` would duplicate P. `P, Q |- P` would discard Q. Both duplicating and discarding are forbidden.
```

## Every resource must be accounted for

The tensor connective $A \otimes B$ (written `A * B`) means "I have $A$ **and** $B$, both at once." Proving `A * B` from two hypotheses costs one hypothesis for each side.

This is why `P, Q |- Q * P` is provable: you spend $P$ on the right-hand $P$, and you spend $Q$ on the right-hand $Q$. Both resources are used once, on both sides. Nothing is wasted, nothing is copied.

Try it:

```{prove}
goal: P, Q |- Q * P
title: Tensor uses both resources
hint: Split the goal into two sub-goals with tensor_r. Each sub-goal will need exactly one hypothesis.
id: ch2-tensor-swap
rules: id, tensor_r, tensor_l
```

Notice that the order on the left does not matter — the left side of a linear sequent is a **multiset**, not a sequence.

## A resource is just itself

The simplest provable sequent is $P \vdash P$: one resource, used once.

```{prove}
goal: coin |- coin
title: A coin is a coin
hint: The hypothesis and the goal are identical. One rule closes this immediately.
id: ch2-coin-id
rules: id
```

The `id` rule (identity) closes a goal when the hypothesis and the conclusion are the same atom. It corresponds to: "I have a coin; therefore I have a coin." No duplication, no waste.

## Three kinds of things

Working with linear logic, you will encounter three different kinds of objects. Keeping them distinct prevents a lot of confusion.

**Terms** are objects — what something *is*. The number `5`, the expression `write(addr, val, mem)`, the atom `coin`. Terms are inert data, like nouns. You can build terms from other terms with constructors.

**Resources** are things you *possess*, exactly once. `coin`, `gas N`, `storage key val`. Resources are linear facts: consumed when used, produced when created. They live on the left of a sequent as hypotheses you must spend.

**Propositions** are things you *know*, persistently. `!plus 3 4 7` (three plus four equals seven). Propositions are marked with `!` (pronounced "bang") and can be used any number of times because knowing a fact does not consume it.

The quick test: *"Can I say what this object IS?"* → Term. *"Do I POSSESS it?"* → Resource. *"Do I KNOW it?"* → Proposition.

In the vending machine: `coin` is a resource (you possess it, then you spend it). The price "1 coin per coffee" is a proposition (a standing rule, always available). The atom `coffee` you receive is a resource (you now possess it).

```{rule id}
```

```{rule tensor_r}
```

## What you cannot do

Let us make the failing intuitions concrete.

**Duplication is impossible.** $P \vdash P \otimes P$ would require producing two resources from one. Try as you might in the prover — there is no rule that copies a linear hypothesis. (The `!` modality, coming in a later chapter, is the *only* controlled way to do this.)

**Discarding is impossible.** $P, Q \vdash P$ would leave $Q$ unaccounted for. Every proof must discharge every linear hypothesis on the left. If you cannot use $Q$, you cannot have it.

These two restrictions together are what makes linear logic a faithful model of physical resources, bank balances, and computational state.

## Exercises

```{exercise, title=Swap the pair}
The tensor connective is commutative: if you have $A \otimes B$ you can rearrange it to $B \otimes A$. Prove this below. You will need to first *split* the pair on the left, then *rebuild* it in the opposite order on the right.
```

```{prove}
goal: P * Q |- Q * P
title: Tensor is commutative
hint: Use tensor_l to split P * Q into two separate hypotheses, then tensor_r to recombine them in the new order.
id: ch2-tensor-comm
rules: id, tensor_r, tensor_l
```

```{solution}
Apply `tensor_l` to the hypothesis `P * Q` — this gives you `P` and `Q` as two separate resources. Then apply `tensor_r` to split the goal `Q * P` into two sub-goals: prove `Q` (use the `Q` hypothesis with `id`) and prove `P` (use the `P` hypothesis with `id`).
```

## What you learned

- In linear logic, every hypothesis is a **resource** consumed exactly once.
- You cannot **copy** a resource: $P \nvdash P \otimes P$.
- You cannot **discard** a resource: $P, Q \nvdash P$.
- Tensor ($\otimes$) requires using resources for *both* sides of the pair — nothing is shared, nothing is wasted.
- Three kinds of objects: **Terms** (what something IS), **Resources** (what you POSSESS), **Propositions** (what you KNOW, marked `!`).

## Going deeper

- [[documentation/term-resource-proposition|Terms, Resources, and Propositions]] — the full three-tier design principle with EVM examples.
- [[theory/0002_motivation|CALC Motivation and Vision]] — why resource-sensitive logic matters for accounting and financial modeling.

---
title: "Choices: with, oplus, and the Impossible Zero"
part: 1
partTitle: Proofs as Trees
chapter: 4
summary: The additive connectives — external choice &, internal choice +, and the impossible resource zero — and how proof rules encode who gets to choose.
---

In chapter 3 you met the multiplicative connectives — tensor (`*`), loli (`-o`), and one (`I`) — which control how resources combine and flow.
This chapter introduces a second family: the **additive** connectives, which model **choice**.

## A tale of two menus

Imagine a vending machine. You insert a coin.

In one design, **you** press a button and get coffee or tea — your choice.
In another design, the machine decides what comes out; you just have to deal with it.

Linear logic captures both patterns as connectives:

- `A & B` (**with**, external choice): the **consumer** picks — A or B, but only one.
- `A + B` (**oplus**, internal choice): the **producer** picks — A or B, and the consumer handles whichever arrives.

This distinction is one of the most important ideas in linear logic.
It shapes symbolic execution, game semantics, and everything that follows.

---

## External choice: `&`

`A & B` means: "I can give you A, or I can give you B — you decide which one you want."

The provider must be ready to supply **either** branch.
The consumer picks at most one.

### The right rule: proving `A & B`

To prove `A & B` from resources $\Delta$, you must show you can prove **both** A and **both** B, using the **same** resources each time — because the consumer might ask for either.

```{rule with_r}
```

Both premises share the same $\Gamma; \Delta$.
This is the key difference from tensor ($A \otimes B$), where the resources are **split** between the two branches.

### The left rules: using `A & B`

When you **have** `A & B` as a hypothesis, you can project out one side.
You do not get to use both — that would be tensor.

```{rule with_l1}
```

```{rule with_l2}
```

### Try it: pick a side

You have both `P` and `Q` bundled as `P & Q`.
Extract just `P`:

```{prove}
goal: P & Q |- P
title: Project left
hint: Apply with_l1 to select the left branch of the hypothesis.
id: ch4-with-left
rules: with_l1, with_l2, id
```

Now extract the right side:

```{prove}
goal: P & Q |- Q
title: Project right
hint: Apply with_l2 this time.
id: ch4-with-right
rules: with_l1, with_l2, id
```

---

## `&` is not `*`

Here is a common trap.

`P & Q |- P` holds — you project out P, discarding Q.
But `P * Q |- P` does **not** hold — you have consumed both P and Q to get the pair, and Q would be left over with nowhere to go.

Linear logic is exact: every resource must be accounted for.
`&` gives you a choice of one; `*` gives you both simultaneously.

```{exercise, title=Spot the difference}
Why can you prove `P & Q |- P` but not `P * Q |- P`?
```

```{solution}
`P & Q` is a menu: you pick one item and the other is never produced.
`P * Q` is a pair: both are handed to you simultaneously, and both must be consumed.
Dropping Q would violate linearity.
```

---

## Internal choice: `+`

`A + B` (pronounced "A oplus B") means: "You will receive A, or you will receive B — the system decides."

As the consumer, you do not know which.
You must be ready to handle **both** possibilities.

### The right rules: producing `A + B`

The producer commits to one branch.
Two rules, one per branch:

```{rule oplus_r1}
```

```{rule oplus_r2}
```

You pick which side you will deliver.
The consumer cannot object.

### The left rule: consuming `A + B`

When `A + B` arrives as a hypothesis, you case-split.
You must handle both cases with the **same** goal and the **same** remaining resources.

```{rule oplus_l}
```

This is the proof obligation: "No matter which branch arrived, we can still reach C."

### Try it: deliver a choice

You have resource `P`. Deliver it tagged as the left branch of `P + Q`:

```{prove}
goal: P |- P + Q
title: Inject left
hint: Apply oplus_r1 — you are the producer, so you pick the left side.
id: ch4-oplus-left
rules: oplus_r1, id
```

### Try it: swap branches

`P + Q` arrives, but you need to produce `Q + P`.
You must handle both cases:

```{prove}
goal: P + Q |- Q + P
title: Commutativity of +
hint: Apply oplus_l to case-split. In the P case, use oplus_r2. In the Q case, use oplus_r1.
id: ch4-oplus-comm
rules: oplus_l, oplus_r1, oplus_r2, id
```

---

## Distribution: `*` over `+`

Tensor distributes over oplus — the producer's choice can be made after splitting a pair.

This sequent says: "I have P paired with either Q or R; I can produce either (P together with Q) or (P together with R)."

```{prove}
goal: P * (Q + R) |- (P * Q) + (P * R)
title: Distribution
hint: Start with tensor_l to unpack the pair. Then case-split with oplus_l. In each branch, pick the matching oplus side with oplus_r1 or oplus_r2, then reassemble with tensor_r.
id: ch4-dist
rules: tensor_l, oplus_l, oplus_r1, oplus_r2, tensor_r, id
```

---

## The impossible resource: `zero`

`zero` is the additive false — a resource that can never be produced.
If you somehow **have** `zero` as a hypothesis, something has gone wrong, and you can prove anything at all.

```{rule zero_l}
```

No premises. If you hold the impossible, every goal is reachable.

```{prove}
goal: zero |- P
title: Ex falso
hint: Apply zero_l. No further steps needed — it closes the goal immediately.
id: ch4-zero
rules: zero_l
```

`zero` never appears on the right of a valid sequent (there is no `zero_r`).
You cannot manufacture the impossible from scratch.

---

```{quiz, id=ch4-q1}
Q: You have a vending machine that offers `coffee & tea`. Who decides what you get?
- [x] You (the consumer) decide.
- [ ] The machine (the producer) decides.
- [ ] Both coffee and tea are dispensed.
explanation: `&` is external choice — the consumer picks one branch. The machine must be ready for either, but only one is delivered.

Q: You receive `alarm + error` from a system. You need to handle it and produce `done`. What rule do you apply first?
- [ ] oplus_r1, to pick the alarm branch.
- [x] oplus_l, to case-split on both possibilities.
- [ ] with_l1, to project out alarm.
explanation: `+` on the left requires oplus_l — you must prove `done` in both the alarm case and the error case, because you do not know which arrived.

Q: Which of these sequents is NOT provable in ILL?
- [ ] `P & Q |- P`
- [x] `P * Q |- P`
- [ ] `zero |- P`
explanation: `P * Q |- P` fails because Q is left over with no consumer. Linear resources cannot be discarded unless an explicit rule permits it.
```

---

## What you learned

- `A & B` (with) is **external choice**: the consumer picks one branch, and the provider must prove both sides with the same resources.
- `A + B` (oplus) is **internal choice**: the producer picks which branch to deliver, and the consumer must handle both cases.
- `zero` is the impossible resource: possessing it lets you prove anything (zero_l), but you can never produce it.
- `P & Q |- P` holds; `P * Q |- P` does not — the difference is whether resources are shared or consumed.
- Tensor distributes over oplus: `P * (Q + R) |- (P * Q) + (P * R)`.

---

## Going deeper

- [[def/0005_internal-vs-external-choice|Internal vs External Choice (full definition)]]
- [[def/0027_rule-with_r|with_r rule]]
- [[def/0030_rule-oplus_r1|oplus_r1 rule]]
- [[def/0032_rule-oplus_l|oplus_l rule]]
- [[def/0039_rule-zero_l|zero_l rule]]

---
title: "Pairs and Machines: tensor, loli, one"
part: 1
partTitle: Proofs as Trees
chapter: 3
summary: The multiplicative connectives — tensor pairs resources, loli consumes input to produce output, and one is the empty resource.
---

In the last chapter you saw that every hypothesis in a linear sequent is a resource, consumed exactly once — no copying, no discarding.
Now we want to name the connectives that let you **combine** and **transform** resources.

## Tensor: having both at once

Imagine a vending machine that needs two coins to dispense a drink.
You must feed it both coins simultaneously — not one, then maybe the other.
Linear logic captures "both at once" with the **tensor** connective, written `*` (or $\otimes$).

$P \otimes Q$ means: you possess $P$ **and** you possess $Q$, and both are consumed when you use them.

### Building a pair: tensor\_r

To prove `P * Q` on the right, you need to **split** your linear context into two groups:
one group proves `P`, the other proves `Q`.
Neither group can borrow from the other — resources flow to exactly one premise.

```{rule tensor_r}
```

The rule reads: if context $\Delta$ proves $A$, and a **separate** context $\Delta'$ proves $B$, then together they prove $A \otimes B$.
The key word is *separate*. This is different from classical logic, where you could copy hypotheses freely.

```{prove}
goal: P, Q |- P * Q
title: Pack a pair
hint: The prover will split P to the left premise and Q to the right premise automatically.
id: ch3-tensor-pack
rules: tensor_r, id
```

### Unpacking a pair: tensor\_l

To **use** a pair `P * Q` on the left, you unpack it into two separate hypotheses.

```{rule tensor_l}
```

This says: a hypothesis `A * B` is exactly as good as having `A` and `B` separately.
Once unpacked, each part must be used exactly once.

Now try a classic: tensor is **commutative**.
A pair `P * Q` should be interchangeable with `Q * P`.
The proof strategy: unpack first, then repack with the halves swapped.

```{exercise, title=Tensor is commutative}
Prove `P * Q |- Q * P`. First apply `tensor_l` to split the pair into `P` and `Q`. Then apply `tensor_r` — be ready: the prover will ask which hypothesis goes to which side.
```

```{prove}
goal: P * Q |- Q * P
title: Swap the pair
hint: Apply tensor_l to unpack, then tensor_r to repack with sides swapped.
id: ch3-tensor-comm
rules: tensor_l, tensor_r, id
```

```{solution}
Apply `tensor_l`: the hypothesis `P * Q` splits into hypotheses `P` and `Q`.
Now apply `tensor_r`: the context splits — send `Q` to the left premise, `P` to the right.
Each sub-goal closes by `id`.
```

## Loli: the linear machine

A vending machine is a **transformer**: put a coin in, get a snack out.
The coin is consumed — you do not get it back.
Linear implication `A -o B` (written $A \multimap B$) is exactly this machine:
feed it one `A` and it produces one `B`, consuming the input.

### Building a machine: loli\_r

To prove `A -o B` on the right, you **assume** $A$ as a new linear hypothesis and prove $B$.
That hypothesis must be used exactly once in the proof.

```{rule loli_r}
```

The simplest machine: give it `P`, get back `P`.

```{prove}
goal: |- P -o P
title: The identity machine
hint: Apply loli_r to add P as a hypothesis, then close with id.
id: ch3-loli-id
rules: loli_r, id
```

### Using a machine: loli\_l

To **use** a machine `A -o B` on the left, you must **provide the input**.
Like tensor_r, this rule splits the context: one part proves the input `A`, the other uses the output `B`.

```{rule loli_l}
```

Read it aloud: "I have a machine $A \multimap B$ and enough resources to feed it $A$.
After running it, I get $B$ and can continue to prove $C$."

This is the proper form of **modus ponens** for linear logic.

```{prove}
goal: P, P -o Q |- Q
title: Modus ponens
hint: Apply loli_l. The left premise needs to prove P (close with id), the right gets Q (close with id).
id: ch3-loli-mp
rules: loli_l, id
```

### Packaging a machine

You can prove a tensor-to-tensor swap as a single machine:

```{prove}
goal: |- (P * Q) -o (Q * P)
title: Swap machine
hint: Apply loli_r to assume P * Q, then tensor_l, then tensor_r with halves swapped.
id: ch3-swap-machine
rules: loli_r, tensor_l, tensor_r, id
```

## Currying: one machine or two?

Suppose a machine needs **two** inputs to produce one output.
You can model this two ways:

- `(P * Q) -o R` — feed a pair all at once.
- `P -o (Q -o R)` — feed `P` first, get back a waiting machine, then feed `Q`.

The second style is called **currying**.
In linear logic these are **interderivable**: having either lets you build the other.

```{prove}
goal: (P * Q) -o R |- P -o (Q -o R)
title: Currying
hint: Apply loli_r twice to assume P then Q. Then apply loli_l to fire the (P*Q)-oR machine — you must provide P*Q, which you build with tensor_r from your two assumptions.
id: ch3-curry
rules: loli_r, loli_l, tensor_r, id
```

## One: the empty resource

What is the tensor identity? A resource so trivial it adds nothing: `I` (written $\mathbf{1}$).
Possessing `I` is possessing nothing extra — it is the empty bundle.

### Producing it: one\_r

```{rule one_r}
```

The rule has **no premises** and requires the linear context to be empty.
You produce $\mathbf{1}$ when you have nothing left to use.

```{prove}
goal: |- I
title: The empty resource
hint: The linear context is already empty; apply one_r directly.
id: ch3-one-r
rules: one_r
```

### Discarding it: one\_l

```{rule one_l}
```

If you hold `I` as a hypothesis, you may discard it — it contributes nothing to the proof.
The remaining context still proves `C`.

## Exercises

```{prove}
goal: I, P |- P
title: Discard the empty resource
hint: Apply one_l to remove the I, leaving P |- P, which closes by id.
id: ch3-one-discard
rules: one_l, id
```

```{quiz, id=ch3-q1}
Q: When applying `tensor_r` to prove `P * Q`, what happens to the linear hypotheses?
- [x] They are split between the two premises — each hypothesis goes to exactly one.
- [ ] They are copied so both premises have access to all of them.
- [ ] They are all sent to the left premise; the right premise gets none.
- [ ] The rule requires the context to be empty before applying.
explanation: Tensor_r splits the linear context. Each linear hypothesis goes to exactly one of the two sub-goals. This is the defining feature of the multiplicative conjunction in linear logic.

Q: What does `A -o B` mean as a resource?
- [x] A machine that consumes one A to produce one B.
- [ ] A choice between A and B.
- [ ] A and B both available for free.
- [ ] B is provable without using A.
explanation: Linear implication A -o B is a one-shot transformer. The input A is consumed when the machine fires; it cannot be reused.

Q: Why does `one_r` require an empty linear context?
- [x] Because I represents no resources, and producing it must consume nothing.
- [ ] It is just a convention — the context could contain anything.
- [ ] You need to provide a proof of I from the hypotheses.
- [ ] The rule is only applicable at the root of the proof tree.
explanation: I is the unit of tensor — it carries zero information. Proving I when you still hold unused linear resources would silently discard them, which linear logic forbids.
```

## What you learned

- `*` (tensor, $\otimes$) means **both at once**. To build one you split your context; to use one you unpack it.
- `-o` (loli, $\multimap$) is a **linear machine**: it consumes its input exactly once. To build one you assume the input; to fire one you split the context to provide the input.
- `I` (one, $\mathbf{1}$) is the **empty resource**: provable from nothing, discardable when held.
- Context splitting in `tensor_r` and `loli_l` is the heart of linearity — no hypothesis is shared between branches.
- Currying `(P * Q) -o R` into `P -o (Q -o R)` works in linear logic, just as in functional programming.

## Going deeper

- [[def/rule-tensor_r|tensor_r rule reference]]
- [[def/rule-loli_r|loli_r rule reference]]
- [[def/rule-one_r|one_r rule reference]]
- [[documentation/backward-prover|How the backward prover searches for proofs]]

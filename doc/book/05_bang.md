---
title: "Reuse: the Exponential !"
part: 1
partTitle: Proofs as Trees
chapter: 5
summary: The bang connective !P gives unlimited reuse — dereliction, absorption, copy, and promotion explained step by step.
---

In chapter 4 you met the additive connectives: `&` (with) lets you offer a choice between two branches, and `+` (oplus) delivers one of two alternatives chosen by the producer.
Neither allows a resource to be used more than once. This chapter introduces the connective that does.

## A recipe is not an ingredient

Imagine you are baking bread. You have two things:

- a **bag of flour** — a physical ingredient, consumed when you bake.
- a **recipe card** — knowledge, consulted as many times as you like.

The flour disappears when you use it. The recipe does not. You can bake again tomorrow with the same card.

Linear logic captures this distinction with the **bang** connective, written `!`.

- `flour` — a linear resource, used exactly once.
- `!recipe` — a reusable resource, readable without limit.

## Two zones in the sequent

Every CALC sequent has two hypothesis zones separated by a semicolon:

$$G \;;\; \Delta \vdash C$$

| Zone | Position | Rule |
|---|---|---|
| **Cartesian** $G$ | left of `;` | can be copied and discarded freely |
| **Linear** $\Delta$ | right of `;` before $\vdash$ | consumed exactly once |

The bang `!` is the bridge between them. The four rules below each handle one aspect of that bridge.

## Rule 1 — Dereliction: use one copy now

**Dereliction** lets you spend one use of `!P` as if it were plain `P`.

```{rule dereliction}
```

You consulted the recipe once. The card is not destroyed, but you used one reading of it for this proof step.

Try it — the simplest bang proof uses only dereliction:

```{prove}
goal: !P |- P
title: One use of a reusable resource
hint: Apply dereliction to turn !P into P, then close with id.
id: ch5-dereliction
rules: dereliction, id
```

## Rule 2 — Absorption: file it in the archive

When `!P` arrives in the linear zone, **absorption** moves it into the cartesian zone.

```{rule absorption}
```

Think of this as filing the recipe card into a reference archive. Once it is in the cartesian zone, the copy and promotion rules can act on it.

## Rule 3 — Copy: pull a fresh instance

**Copy** reaches into the cartesian zone and places a fresh linear copy of `A` where the proof needs it.

```{rule copy}
```

Absorption followed by copy lets you use `!P` as many times as you need. Here is a proof that draws two copies:

```{prove}
goal: !P, !P |- P * P
title: Two copies of the same resource
hint: Absorb both bangs into the cartesian zone, then copy each one for the two tensor branches.
id: ch5-copy
rules: absorption, copy, tensor_r, id
```

Two *different* reusable resources at the same time:

```{prove}
goal: !P, !Q |- P * Q
title: Two distinct reusable resources
hint: Absorb both into cartesian, copy each once, then close with tensor_r.
id: ch5-two
rules: absorption, copy, tensor_r, id
```

## Rule 4 — Promotion: certify something as reusable

The first three rules *consume* a bang. **Promotion** *produces* one.

```{rule promotion}
```

To prove `!A`, the linear zone must be empty — every hypothesis must already be in the cartesian zone. You cannot stamp a consumable ingredient as reusable. Only pure knowledge (derivable from $G$ alone) can be promoted to `!A`.

This is why flour cannot become a recipe: flour gets used up, so it lives only in $\Delta$, and promotion is closed to it.

## Putting it together: a reusable function

`!(P -o Q)` means "I know forever how to turn P into Q."

```{prove}
goal: !(P -o Q), P |- Q
title: A persistent function applied once
hint: Absorb !(P -o Q) into cartesian, copy it out, then use loli_l on P.
id: ch5-loli
rules: absorption, copy, loli_l, dereliction, id
```

You can chain several reusable steps into a pipeline:

```{prove}
goal: !(a -o b), !(b -o c), a |- c
title: Reusable two-step pipeline
hint: Absorb and copy the first loli; fire it on a to obtain b. Absorb and copy the second loli; fire it on b to obtain c.
id: ch5-pipeline
rules: absorption, copy, loli_l, dereliction, id
```

Note: the interactive prover searches a restricted bang fragment. Full contraction proofs such as `Q, !P |- Q` are easiest to verify by hand.

## Quiz

```{quiz, id=ch5-q1}
Q: Which zone allows you to copy and discard hypotheses freely?
- [x] the cartesian zone ($G$, left of the semicolon)
- [ ] the linear zone ($\Delta$, right of the semicolon)
- [ ] the succedent (right of $\vdash$)
explanation: Cartesian hypotheses can be used any number of times — that is exactly what makes !P reusable once it is absorbed there.

Q: What does dereliction do to `!P`?
- [x] converts one use of `!P` into plain `P` in the linear zone
- [ ] moves `!P` from the linear zone to the cartesian zone
- [ ] manufactures `!P` from a proof of `P`
- [ ] produces two copies of `P`
explanation: Dereliction (!D) extracts a single linear use from a bang. The bang is consumed for proof-search purposes; plain P is now available.

Q: Which rule requires the linear zone to be *empty* before it fires?
- [ ] dereliction
- [ ] absorption
- [ ] copy
- [x] promotion
explanation: Promotion (!R) is only available when the linear zone is empty. You cannot promote a consumable resource — only purely cartesian context can certify unlimited reuse.
```

## What you learned

- `!P` is an **unlimited license** for `P` — it can be used any number of times.
- **Dereliction** uses one copy now; **absorption** files `!P` into the cartesian zone; **copy** pulls a fresh instance out; **promotion** certifies that `A` is universally reusable.
- CALC sequents are two-zone: $G \;;\; \Delta \vdash C$. The cartesian zone $G$ allows copying; the linear zone $\Delta$ does not.

## Going deeper

In Part III you will meet the **graded bang** $!_k A$ — a counted resource delivering exactly $k$ copies. Under the hood, CALC already represents `!A` as `bang(grade, A)` where the grade carries this count ($\infty$ for the plain `!`).

- [[def/rule-dereliction|Dereliction (!D)]] — formal rule definition
- [[def/rule-absorption|Absorption (!L)]] — formal rule definition
- [[def/rule-copy|Copy (contraction)]] — formal rule definition
- [[def/rule-promotion|Promotion (!R)]] — formal rule definition

---
title: "How the Machine Proves: Polarity and Focusing"
part: 1
partTitle: Proofs as Trees
chapter: 6
summary: Why naive proof search explodes, how polarity tames it, and how Andreoli's focusing algorithm structures the search into safe eager steps and committed choices.
---

## The search space problem

In earlier chapters you built proofs by picking rules yourself.
The machine must do the same — but without a human to guide it.
The question is: in what order should it try the rules?

Consider the goal $P \otimes Q \vdash Q \otimes P$.
Several rules could apply first: `tensor_l` (split the left side), or `tensor_r` (split the right side — but which resources go left and which go right?).
If you guess wrong, you backtrack and try again.
With many connectives the combinations explode.

The key insight: **some rules are always safe to apply and some are real choices**.
Separating them is what makes proof search tractable.

## Invertible rules: safe, eager steps

A rule is **invertible** if applying it never destroys provability.
If the goal is provable before you apply the rule, it is still provable after.
You can apply invertible rules immediately, in any order, and never regret it.

Two classic examples:

```{rule loli_r}
```

```{rule with_r}
```

$\multimap$-right (`loli_r`) is invertible: to prove $A \multimap B$ on the right, you always move $A$ to the left and prove $B$.
There is no other way; applying the rule loses nothing.

$\&$-right (`with_r`) is also invertible: to prove $A \mathbin{\&} B$ you must prove both branches, and both inherit the full context.
Again there is no choice to make.

Other invertible rules: `tensor_l` (decompose $\otimes$ on the left), `oplus_l` (case-split $\oplus$ on the left), `one_l` (discard $I$ on the left), `dereliction` (use $!P$ once).

## Non-invertible rules: the real choices

A rule is **non-invertible** if applying it can destroy provability.
These are the genuine branch points in proof search.

```{rule tensor_r}
```

`tensor_r` requires splitting the linear context between two premises.
If you send $P$ to the left branch and $Q$ to the right, but the proof needed it the other way, you are stuck.
You must backtrack and try a different split.

Other non-invertible rules: `oplus_r1` / `oplus_r2` (pick a branch of $\oplus$), `loli_l` (apply a linear implication — consumes it and commits to a subgoal).

## Polarity: reading off invertibility

Where does invertibility come from?
It follows a simple pattern called **polarity**.

Every connective is either **positive** or **negative**:

| Connective | Symbol | Polarity |
|---|---|---|
| tensor | $\otimes$ | positive |
| one | $I$ | positive |
| oplus | $\oplus$ | positive |
| bang | $!$ | positive |
| loli | $\multimap$ | negative |
| with | $\mathbin{\&}$ | negative |
| forall | $\forall$ | negative |

The rule of thumb:
- A **negative** connective on the **right** of $\vdash$ → the rule is **invertible** (`loli_r`, `with_r`, `forall_r`).
- A **positive** connective on the **left** of $\vdash$ → the rule is **invertible** (`tensor_l`, `oplus_l`, `one_l`).
- Flip the side → not invertible (negative on the left, positive on the right).

Polarity is computed once from the `.rules` file and stored in the calculus object.
No prover code knows which connectives exist; it just queries the polarity table.

## Focusing: two phases, no wasted work

**Andreoli's focusing algorithm** uses polarity to structure proof search into two alternating phases:

**Phase 1 — Inversion.** Apply every invertible rule eagerly, in any order.
This phase terminates: each step strictly reduces the goal.
No choice, no backtracking.

**Phase 2 — Focus.** When no invertible rule applies, **choose one formula** to focus on and decompose it fully — applying non-invertible rules to it until you either close the goal or reach a formula that is invertible (then blur back to Phase 1).

The key property: within one focus phase you commit to ONE formula and one decomposition path.
This cuts the search tree dramatically compared to trying every rule at every step.

In the widget, switching to **focused mode** makes this two-phase structure visible.
You will see `Focus_L` (focus on a left formula) or `Focus_R` (focus on the succedent) actions.

## Exercises

### Swapping a tensor (unfocused)

Prove that tensor is commutative.
In default mode you pick rules directly — try `tensor_l` first, then `tensor_r`.

```{prove}
goal: P * Q |- Q * P
title: Swap a tensor (unfocused)
hint: Apply tensor_l first to get P and Q as separate hypotheses, then use tensor_r to reassemble them in the opposite order.
id: ch6-swap-unfocused
```

### The same goal, focused mode

Now prove the same sequent with `mode: focused`.
You will first see `Focus_L` — click it to commit to the $P \otimes Q$ hypothesis.
The inversion phase then handles the rest automatically.
Compare the two trees: the focused version groups steps into clear phases.

```{prove}
goal: P * Q |- Q * P
title: Swap a tensor (focused)
mode: focused
hint: Start with Focus_L on P * Q. After focusing and decomposing you enter inversion, which picks up tensor_r and closes both branches.
id: ch6-swap-focused
```

### Distributing a linear implication

This sequent needs two invertible phases (one for the outer `&`, one for each `loli_r` branch) and then a focus phase to apply `loli_l`.
Take it step by step.

```{prove}
goal: P -o (Q & R) |- (P -o Q) & (P -o R)
title: Distributing loli over with
hint: Both succedent branches are loli — apply with_r first, then loli_r on each branch. That consumes the hypothesis; use loli_l on P -o (Q & R) to continue.
id: ch6-dist-loli
```

## Quiz

```{quiz, id=ch6-q1}
Q: Which of the following rules is **invertible**?
- [x] `loli_r` — to prove $A \multimap B$, always move $A$ left and prove $B$
- [ ] `tensor_r` — must split the linear context; wrong split = dead end
- [ ] `oplus_r1` — commits to the left branch; might need the right branch instead
- [x] `with_r` — must prove both $A$ and $B$; both branches get the full context
explanation: A rule is invertible when applying it never destroys provability. loli_r and with_r are both invertible — they introduce exactly the proof obligation you were already facing, without any destructive choice.

Q: In Andreoli's focusing algorithm, what happens during the **inversion phase**?
- [ ] You choose one formula and decompose it fully.
- [x] You apply all invertible rules eagerly until none remain.
- [ ] You backtrack to the last focus choice.
- [ ] You split the linear context between two premises.
explanation: The inversion phase applies every invertible rule it can find, in any order. No backtracking is needed because invertible rules preserve provability.

Q: A positive connective on the **right** of $\vdash$ is:
- [ ] invertible — safe to apply eagerly
- [x] non-invertible — a real choice that may require backtracking
- [ ] always false (zero)
- [ ] handled in the inversion phase
explanation: Positive connectives invert on the LEFT (positive_l is safe). On the right they are non-invertible: tensor_r must split the context, oplus_r1/r2 must pick a branch. These are the choices that drive the focus phase.
```

## What you learned

- **Invertible rules** are safe to apply eagerly: applying them never loses provability.
  They define the **inversion phase** of proof search — no choices, no backtracking.
- **Non-invertible rules** are real decisions: wrong choices require backtracking.
  They drive the **focus phase** — commit to one formula, decompose fully.
- **Polarity** determines invertibility: negative connectives invert on the right; positive connectives invert on the left.
- **Andreoli's focusing** alternates these two phases, turning an exponential search space into a structured procedure.
- The **Auto-complete** button in the prover widget runs the full L1–L4 focused search — the same algorithm, automated. See [[documentation/backward-prover]] for the four-layer architecture behind it.

## Going deeper

- [[documentation/backward-prover]] — the full four-layer architecture (L1 kernel, L2 generic, L3 focused, L4 strategy) with data-flow diagrams.
- [[documentation/architecture]] — how the backward prover fits into the wider CALC system alongside the forward engine.

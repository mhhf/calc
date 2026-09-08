---
title: What Is a Proof?
part: 1
partTitle: Proofs as Trees
chapter: 1
summary: Sequents, inference rules, and your first proof tree — built by clicking.
---

## A claim and its evidence

Suppose a friend says "I can get coffee from this machine." That is a claim.
You ask: "How?" Their answer — "I put in a coin, the machine gives coffee" —
is evidence. Claim plus evidence is a **judgment**: something you believe *and*
can justify step by step.

In logic we write judgments precisely. The simplest kind says:

> *Given these assumptions, I can derive this conclusion.*

We call that a **sequent**.

## Sequents

A sequent looks like this:

$$\Gamma \vdash C$$

The symbol $\vdash$ (called the **turnstile**) splits the sequent in two:

- **Left side** ($\Gamma$): your **hypotheses** — the resources you start with.
- **Right side** ($C$): the **conclusion** — what you want to prove.

Read it aloud as: *"From $\Gamma$, I can conclude $C$."*

A concrete example: $P \vdash P$ says "from hypothesis $P$, conclude $P$."
That sounds obvious — you already have it. But even obvious claims need a rule
to justify them.

You can have several hypotheses, separated by commas:

$$P,\, Q \vdash R$$

That says: "starting with both $P$ and $Q$, derive $R$."

## Inference rules

A **judgment** becomes a **proof** when you justify every step. Each step is
justified by an **inference rule**. An inference rule has three parts:

1. **Premises** (above the line): sequents you must already have proved.
2. **A horizontal bar** (the separator between what you need and what you get).
3. **Conclusion** (below the line): the sequent the rule establishes.

A name to the right of the bar lets you refer to the rule by name.

$$\cfrac{\text{premise}_1 \qquad \text{premise}_2}{\text{conclusion}} \;\text{RuleName}$$

When there are **zero premises** above the line, the rule is an **axiom** — it
needs no further justification. Axioms are the leaves where proof trees end.

## The identity axiom

The simplest rule in linear logic is an axiom. It says:

> *If $A$ is your only hypothesis, you can conclude $A$.*

```{rule id}
```

This rule is named **Id** (short for *identity*). There are no premises above
the bar — just a single sequent below. It fires the moment the goal matches
the hypothesis exactly.

See [[def/0022_rule-id|Id — the identity axiom]] for the formal definition.

Try it now. The widget below shows the sequent $P \vdash P$. Click it, pick
the only available rule, and watch the branch close.

```{prove}
goal: P |- P
title: Your first proof
hint: There is exactly one rule that closes a goal where the same atom appears on both sides. Click the sequent and look for it.
id: ch1-id
rules: id
```

Congratulations — you just built a proof. One rule, one step, done.

## Proof trees

Most goals need more than one step. You apply a rule to the current goal.
That rule may produce **subgoals** (the premises), which you then prove in
turn. Repeat until every open branch ends in an axiom.

The result is a **proof tree**:

- The **root** is your original goal.
- Each **internal node** is one rule application.
- The **leaves** are axiom applications — zero premises, nothing left to do.

You can read a proof tree two ways:

- **Bottom-up** (how you *search*): start from the goal, apply rules, reduce
  to simpler subgoals. This is how the prover widget works — you click the
  current goal and choose a rule.
- **Top-down** (how you *check*): start from the axioms and apply rules until
  you reconstruct the original goal. This is how a proof *verifier* works.

Both views describe the same object — the tree is the proof.

## A teaser: modus ponens

Here is a two-step proof. The goal has two hypotheses:

- $P$ — you have $P$.
- $P \multimap Q$ — a "linear implication": if you spend $P$, you get $Q$.

The conclusion is $Q$.

The connective $\multimap$ (written `-o` in CALC) is called **lollipop**.
Chapter 3 explains it in full. For now, just notice: one rule can take apart
$P \multimap Q$ by *consuming* both $P$ and $P \multimap Q$ at the same time,
leaving $Q$ to prove.

```{prove}
goal: P, P -o Q |- Q
title: Modus ponens
hint: Apply the rule for the left side of -o. It splits the goal into two subgoals — prove P (closed by Id) and Q from Q (also closed by Id).
id: ch1-mp
rules: id, loli_l
```

One rule application split the goal into two leaves. Both closed by Id.
The finished proof tree has three nodes total: one for `loli_l`, two for `Id`.

That is modus ponens — the oldest argument form in logic — expressed as a
three-node proof tree.

## Check your understanding

```{quiz, id=ch1-q1}
Q: In an inference rule, what sits **above** the horizontal bar?
- [x] the premises — sequents that must already be proved
- [ ] the conclusion — the sequent the rule establishes
- [ ] the rule name

Q: Which of the following best describes an **axiom**?
- [x] an inference rule with zero premises
- [ ] an inference rule with exactly one premise
- [ ] a sequent with an empty left side

Q: In the sequent $P, Q \vdash R$, what are the hypotheses?
- [x] $P$ and $Q$
- [ ] $R$ only
- [ ] $P$, $Q$, and $R$
explanation: Everything to the left of $\vdash$ is a hypothesis. Everything to the right is the conclusion.

Q: You search for a proof **bottom-up**. Where do you start?
- [x] the goal (root), working toward axioms (leaves)
- [ ] the axioms (leaves), working toward the goal (root)
- [ ] the middle of the tree
explanation: Proof search works bottom-up: apply rules to the current goal, generating subgoals, until every branch ends in an axiom.
```

## What you learned

- A **sequent** $\Gamma \vdash C$ states: "from hypotheses $\Gamma$, derive
  conclusion $C$."
- An **inference rule** has premises above a bar and a conclusion below.
  A rule with no premises is an **axiom**.
- A **proof tree** stacks rule applications until every leaf is an axiom.
- The **Id** rule closes any branch where the sole hypothesis equals the goal.
- Proof search works **bottom-up** (goal → subgoals); proof checking works
  **top-down** (axioms → goal).

## Going deeper

- [[def/0022_rule-id|Id — the identity axiom]]: formal rule definition with properties.
- [[documentation/architecture|CALC architecture]]: how the five-layer prover implements proof search.
- [[documentation/parser-pipeline|Parser pipeline]]: how sequent syntax is parsed into proof terms.

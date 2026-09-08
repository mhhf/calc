---
title: "Runs That Carry Their Own Proof"
part: 4
partTitle: Chance
chapter: 18
summary: A random collapse run is not just a log — each draw mints a linear proof token, and the final sequent's tokens are a machine-checkable certificate of the run's probability mass.
---

## A log is not a proof

Chapter 16 showed collapse in action: the engine draws members of a classifier, weights each draw by the declared prior $\rho(c)$, and produces a run.
The run is a sequence of events.

But a sequence can be fabricated.
Someone could hand you a list of draws and claim each was made at the right prior.
How would you check?

A log is a sequence of claims.
A proof is a derivation whose every step is independently re-derivable from the rules.
This chapter is about turning a collapse run into the second thing.

The results here are at the research frontier.
They are proved and pinned with running tests in this repo, but the full papers are still in progress.

## Every draw mints a token

Each time the collapse engine draws a member $c$ of classifier sort $s$, it creates one atom:

$$\texttt{drawn}(c,\, s)$$

This atom enters the sequent as a **linear hypothesis** — a resource in the sense of Chapter 2.
The sequent accumulates these tokens as the run proceeds.
After three draws, the linear zone holds three `drawn` hypotheses.

A `drawn` atom is deliberately **not** a persistent fact.
Persistent facts can be copied and reused; they live in the bang zone.
A token records one specific commitment: *this draw happened, at this member, in this sort*.
It cannot be duplicated, and it must be accounted for.

The program itself can never produce a `drawn` atom.
No rule's consequent is allowed to conclude `drawn`.
Tokens enter derivations only through the collapse checker — a hard boundary in the kernel.

## The mass is the product over the tokens

Here is the central fact of the chapter.

Let $\Theta$ be the multiset of `drawn` tokens in the final sequent of a run.
The run's **probability mass** is:

$$w(\Theta) \;=\; \prod_{(c,\,s)\,\in\,\Theta} \rho(c)$$

The product runs over every token, including repetitions.
If the run drew member $a$ twice and member $b$ once, $\Theta$ contains two copies of $\texttt{drawn}(a, s)$ and one copy of $\texttt{drawn}(b, s)$, and $w(\Theta) = \rho(a)^2 \cdot \rho(b)$.

This is not a separate annotation.
Weight is a function of **which hypotheses are present in the endsequent** — the same linear zone that records every other resource.
The mass is readable directly from the proof state.

This reformulation is called the internalization theorem (THY_0027 §1).
What looks like a side annotation `[Θ]` on a judgment reduces to ordinary context bookkeeping: tokens are just linear hypotheses, cut concatenates contexts, and $w(\Theta_1 \cup \Theta_2) = w(\Theta_1) \cdot w(\Theta_2)$ follows from multiset union.

## certifyCollapse: re-deriving every draw

Now the certificate becomes checkable.
The `certifyCollapse` function takes a finished run — a trace of `@fire` and `@draw` events — and re-derives every step from the program's declared sort system and priors.

For each `@draw` event recording outcome $c$ in sort $s$:

1. Confirm that $c$ is a member of $s$ in the program's sort system.
2. Confirm that $\rho(c)$ matches the declared prior.
3. Mint exactly one `drawn(c, s)` token — no more, no fewer.
4. Check the `@fire` events around it as a kernel-verified proof tree.

If any step fails — wrong member, inflated weight, missing prior, or a fire that does not follow from the rules — the checker rejects the certificate.

The endsequent that `certifyCollapse` produces has the form:

$$\Delta_0,\;\langle\Theta\rangle \;\vdash\; \bigl\{\exists\,\text{skolems.}\; \bigotimes \text{residual}\bigr\}@h$$

where $\Delta_0$ is the initial state, $\langle\Theta\rangle$ is the token multiset, and the right side is the final world inside a monad at horizon $h$.
The certified mass of the run is $\prod_{(c,s)\in\Theta} \rho(c)$, readable from the left side.

A doctored run fails because the kernel finds no valid proof tree connecting $\Delta_0 \cup \langle\Theta\rangle$ to the claimed final state under the rules the program declared.

## No-cloning: randomness is a resource

There is an unexpected structural consequence of the token discipline.

Recall **identity expansion**: to prove $A \vdash A$ for a compound formula, you unfold both sides using the rules and close by identity at atoms.
This works for every ILL connective.
For the weighted existential $\exists_\rho x{:}s.\, A$ it **fails**.

The attempt: to prove $\exists_\rho x{:}s.\, B \vdash \exists_\rho x{:}s.\, B$, open the left side with the $\exists$-left rule (fresh variable $a$), then re-introduce on the right.
Re-introduction via $\exists_\rho$-right consumes a `drawn` token.
The sequent starts with none.
There is no token to spend, so no expansion is possible.

The identity rule at $\exists_\rho$ stays **primitive** — it cannot be derived from simpler pieces.

In plain terms: **a committed draw can be passed along whole, but cannot be deconstructed and re-derived**.
Re-derivation would be a second draw, minting a new token, producing a different endsequent with a different mass.
You cannot clone a flip of the coin.

This is a proof-theoretic no-cloning: the connective that carries randomness is the one where identity expansion breaks down.

A closely related fence: **promotion through a draw is impossible**.
Recall that `!`-right (promotion) requires an empty linear zone.
Draw tokens are linear; their presence in the zone blocks promotion.
You may bang the downstream *consequences* of a draw — the facts that followed from the outcome — but never the luck itself.
The distinction between what you know and what you were lucky to get is enforced structurally, not by convention.

## Certified conditional independence

The token discipline pays a further dividend.

If a run's derivation splits into two sub-forests that share no linear resource — disjoint token zones, disjoint fire provenances, no contested fact — then the joint mass factorizes:

$$\mu(X = x,\; Y = y \mid z) \;=\; c_M \cdot f(x) \cdot g(y)$$

where $f(x)$ is the mass of the $X$-side sub-forest and $g(y)$ the mass of the $Y$-side.
The factorization is **exact** — not an approximation, not an asymptotic statement.
And it is **readable from the certificate**: the token multiset $\Theta$ splits as $\Theta_A \uplus \Theta_B$ along the sub-forests, and the product splits with it.

`calc.certifyCI` decides this criterion (THY_0031).
It builds the program's dependency graph, adds virtual sites for draws being conditioned on and observed facts, and applies a d-separation test.
If the two query variables $X$ and $Y$ are separated given the conditioning context $z$, it certifies $X \perp Y \mid z$.

This is a **soundness-only** result.
There are programs where independence holds yet the static graph is too dense to prove it (parameter cancellation, context-specific rules that never fire).
The checker refuses those cases rather than guessing.
But when it issues a certificate, the factorization above holds exactly in $\mathbb{Q}_{\geq 0}$.

The criterion is also pinned: `tests/engine/will-ci.test.js` contains seven programs with hand-verified masses and exact engine-computed totals, one for each shape of dependence and independence the criterion needs to handle correctly.

## What you learned

- Each collapse draw mints one `drawn(c, s)` linear token; the final sequent's token multiset is the run's entire draw record.
- The run's probability mass is $\prod_{(c,s)\in\Theta}\rho(c)$ — a function of the endsequent, not a separate annotation.
- `certifyCollapse` re-derives every draw from the program's sort system and priors; doctored runs are rejected because no valid proof tree can be completed.
- Identity expansion fails at $\exists_\rho$: you cannot re-derive a draw from scratch, only pass it along — proof-theoretic no-cloning.
- Promotion through a draw is impossible: tokens are linear, and `!`-right requires an empty linear zone.
- `calc.certifyCI` certifies exact conditional independence from derivation structure (soundness only; completeness fails for classical reasons).

## Going deeper

- [[theory/0027_trace-judgment-cut-admissibility|THY_0027: Cut admissibility for the trace judgment]] — the full proof that cut reduction preserves the token multiset exactly, including the ghost-draw discipline and the no-promotion theorem.
- [[theory/0028_grade-certificates-single-counting|THY_0028: Single-counting and the syntactic independence discipline]] — when the bias product in the posterior is the correctly-factored Bayesian update, and when the certificate reveals double-counting that the numbers alone cannot.
- [[theory/0031_run-certificate-conditional-independence|THY_0031: Certified conditional independence on dynamic derivation forests]] — the d-separation theorem for probabilistic forward-chaining runs, with mass-child sites, allocation forks, and the executable criterion.

```{quiz, id=ch18-q1}
Q: A collapse run produces three draw events with members $a$, $b$, $a$ (drawing $a$ twice). How many `drawn` tokens appear in the final sequent?
- [ ] 2 — duplicate members collapse to a single token each
- [x] 3 — each draw event mints exactly one token, including repeated members
- [ ] 1 — all tokens are merged into a single total weight

explanation: Tokens are linear hypotheses in a multiset, not a set. Repeated draws produce repeated tokens. The mass $\rho(a)^2 \cdot \rho(b)$ correctly reflects both draws of $a$ because there are two tokens for $a$ in $\Theta$.
```

```{quiz, id=ch18-q2}
Q: Why does identity expansion fail at the weighted existential $\exists_\rho x{:}s.\, B$?
- [ ] $\exists_\rho$ is a negative connective, and identity applies only to positive connectives.
- [ ] The sort system does not define identity rules for classifier sorts.
- [x] Re-introducing the witness on the right consumes a `drawn` token that the sequent does not contain without making a new draw.

explanation: Expanding $\exists_\rho x{:}s.\,B \vdash \exists_\rho x{:}s.\,B$ requires the $\exists_\rho$-right rule, which consumes a `drawn(c, s)` token. No such token exists at the start of the derivation, so no expansion is possible. The identity rule at $\exists_\rho$ stays primitive — a proof-theoretic no-cloning result.
```

```{quiz, id=ch18-q3}
Q: A program rule concludes `!`-right on a formula $A$. The current linear zone contains a `drawn(c, s)` token. What happens?
- [x] Promotion fails — `!`-right requires an empty linear zone, and `drawn` tokens are linear.
- [ ] The token is automatically moved to the persistent zone during promotion.
- [ ] Promotion succeeds, and the token is erased from the result.

explanation: `bang_r` (promotion) requires the entire linear zone to be empty. `drawn` tokens are linear hypotheses; their presence blocks promotion. You may bang facts derived from a draw's outcome, but not the draw token itself.
```

```{quiz, id=ch18-q4}
Q: `calc.certifyCI` reports $X \perp Y \mid z$ for a program. What exactly is guaranteed?
- [ ] Independence holds in every individual sample run, not just on average.
- [ ] All programs with a similar structure are also independent.
- [x] The unnormalized joint mass satisfies $\mu(X=x, Y=y, C_z) = c_M \cdot f(x) \cdot g(y)$ exactly for all values $x$, $y$.

explanation: `certifyCI` is a soundness-only criterion. When it certifies independence, the exact $\mathbb{Q}_{\geq 0}$ factorization holds for this program and this conditioning context. When it is silent or refuses, nothing is claimed — the program may still be independent by parameter cancellation that the static graph cannot see.
```

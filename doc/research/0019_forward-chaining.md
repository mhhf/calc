---
title: "Forward Chaining in Linear Logic"
created: 2026-02-18
modified: 2026-02-18
summary: Theory of how forward chaining in linear logic drives computation, the role of each connective, and the CLF/Celf/Ceptre framework.
tags: [linear-logic, forward-chaining, theory, clf, multiset-rewriting]
category: "Forward Chaining"
---

# Forward Chaining in Linear Logic

## 1. Linear Logic as a Logic of State

Classical logic treats hypotheses as permanent truths — they can be duplicated (contraction) and discarded (weakening) freely. Girard's linear logic (1987) removes these structural rules, turning hypotheses into **resources** consumed exactly once.

This makes logical deduction into **state manipulation**:

| Classical | Linear |
|---|---|
| `at(robot, A)` is always true | `at(robot, A)` is a resource |
| Movement needs frame axioms | `at(robot, A) ⊸ at(robot, B)` consumes old, produces new |
| Database only grows | State shrinks and grows |

A program state is a **multiset of linear propositions**. Rules are linear implications that consume some propositions and produce others. Computation is proof search.

## 2. The Connectives and Their Computational Roles

### Multiplicatives

**Tensor (`A ⊗ B`)** — "I have both A and B simultaneously." The join operator: a rule's antecedent `A ⊗ B ⊗ C` means "I need all three resources." A rule's consequent `D ⊗ E` means "I produce both." Distributes into the state as separate facts.

**Linear implication (`A ⊸ B`, "lollipop")** — "Consuming A produces B." The fundamental state transition. As a fact in the state, a loli is a **latent rule** / **continuation** — it waits for its trigger to appear, then fires, consuming both itself and the trigger.

**One (`1`)** — "No resource." The tensor unit. Trivially available, consumes nothing.

### Additives

**With (`A & B`)** — **External choice** (consumer decides). Offers both A and B; the environment chooses which to take. In backward chaining: the prover chooses. In a forward engine: both branches must be explored since we don't know which the environment will pick.

**Plus (`A ⊕ B`)** — **Internal choice** (producer decides). The system/rule has already decided to produce either A or B. In forward chaining: also forks, but semantically the branching represents a **system-determined** decision (e.g., a comparison yielding true/false). Both branches are explored because the result depends on symbolic values.

The semantic difference matters: `&` = "I offer you a choice," `⊕` = "the system made a choice, handle both cases." For decidable conditions (arithmetic comparisons in EVM), `⊕` is correct — the system decided, not the consumer.

### Exponentials

**Bang (`!A`)** — "A is available without limit." Recovers classical structural rules for specific formulas. `!A` can be duplicated and discarded freely.

In forward chaining, `!A` is a **persistent fact** — never consumed when used. This is how backward chaining integrates: persistent definitions (arithmetic, type relations) are `!`-marked and can be **proved** (via backward chaining or FFI) without being consumed from the state.

The distinction between persistent and linear is the engine's most important structural property:
- **Linear facts** = mutable state (consumed and produced by rules)
- **Persistent facts** = immutable knowledge (proved but never consumed)

## 3. Forward Chaining as Multiset Rewriting

Forward chaining in linear logic is isomorphic to **multiset rewriting** (Cervesato & Scedrov, 2009). A state is a multiset of atomic propositions. A rule `A₁ ⊗ ... ⊗ Aₙ ⊸ B₁ ⊗ ... ⊗ Bₘ` rewrites by removing `{A₁,...,Aₙ}` and adding `{B₁,...,Bₘ}`.

This also connects to **Petri nets** (places = propositions, tokens = counts, transitions = rules) and to **CHR** (Constraint Handling Rules), where simpagation rules `H₁ \ H₂ ⟺ G | B` map directly:
- Kept head `H₁` = persistent antecedent (`!A`)
- Removed head `H₂` = linear antecedent
- Guard `G` = backward proving / FFI
- Body `B` = consequent

### The Execution Model

```
State := initial multiset of (linear + persistent) propositions
repeat:
    find a rule R whose antecedent matches a subset of State
    if none found → QUIESCENCE (done)
    consume R's matched linear resources from State
    prove R's persistent antecedents (backward chaining / FFI)
    add R's consequent to State
    (persistent resources remain; linear resources are consumed)
```

Key differences from classical forward chaining (Datalog, production systems):
1. **State shrinks as well as grows** — resources are consumed
2. **No monotonicity** — new facts can make old rules inapplicable
3. **Termination by quiescence**, not saturation
4. **Same rule can fire repeatedly** on fresh resources

### Committed Choice

Forward chaining uses **committed choice**: once a rule fires, there is no backtracking. This is the operational meaning of "synchronous" in CLF — choices are irrevocable. Non-determinism in rule selection leads to different execution traces. For exhaustive analysis (symbolic execution), all traces must be explored — this is what creates the execution tree.

## 4. The Lax Monad: Bridging Forward and Backward

### The CLF Framework

CLF (Watkins, Cervesato, Pfenning, Walker, 2002-2004) integrates forward and backward chaining via the **lax monad** `{A}`:

```
Outside monad:  Backward chaining (goal-directed, backtracking)
Inside monad:   Forward chaining (data-driven, committed choice)
```

Entering `{A}` switches the proof search from backward to forward mode. The forward engine runs until quiescence, then returns. The monad encapsulates the synchronous connectives (`⊗`, `1`, `!`, `∃`) — these are the connectives that appear in forward-chaining consequents.

### Why CLF Restricts What Can Appear Inside the Monad

CLF allows `{C}` where C may contain: atoms, `⊗`, `1`, `!`, `∃`. Notably **excluded** are: `⊸` (loli), `&` (with), `⊤` (top).

This restriction is deliberate. Lolis inside monads create **dormant rules** that need a separate firing mechanism — they cannot be simply added to the state as atomic facts. The monadic `let` binding `{A} ⊗ (A ⊸ {B}) ⊸ {B}` already provides sequencing between forward computations, making nested lolis within the monad redundant from a sequencing perspective.

More precisely: the monad's operational semantics require committed choice and atomic rule application. A loli in the consequent would need to be "remembered" and "fired later" — this is a separate scheduling mechanism that CLF avoids in order to keep the monadic semantics clean. Celf's implementation confirms this: monadic decomposition only handles atoms, tensor, bang, one, and existentials.

### LolliMon: The Bridge

LolliMon (Lopez, Pfenning, Polakow, Watkins, 2005) is the operational bridge between Lolli (backward-only linear logic programming) and CLF. It demonstrated that the monadic separation cleanly enables both modes, with encodings of pi-calculus, call-by-need lambda calculus, and saturating algorithms.

### Ceptre: Stages as Structured Quiescence

Ceptre (Martens, 2015) simplifies CLF for interactive systems (games, narrative). All rules are forward chaining (the monad is implicit). **Stages** provide control structure: each stage is a named set of rules that runs to quiescence, then stage transitions fire. This is Ceptre's key innovation — programming with quiescence as a control primitive.

## 5. Focusing and Forward Chaining

Andreoli's focusing discipline (1992) eliminates redundant choices in proof search. Connectives split into:

- **Asynchronous** (negative polarity): `⊸`, `&`, `⊤` — right-introduction is invertible (apply eagerly)
- **Synchronous** (positive polarity): `⊗`, `1`, `!`, `⊕`, `∃` — right-introduction requires a choice

Proof search alternates between **inversion** (apply invertible rules eagerly) and **focus** (choose a formula, decompose it synchronously until blur).

Chaudhuri and Pfenning (2006) showed that the choice of polarity for atoms determines forward vs backward chaining:
- **Positive atoms** → forward chaining (facts derived bottom-up)
- **Negative atoms** → backward chaining (goals decomposed top-down)
- **Mixed** → combinations of both

This provides a structural explanation for forward/backward chaining: they are two polarities of the same focused proof search framework.

## 6. Lolis as Continuations in Forward Chaining

When a loli `A ⊸ B` appears as a fact in the linear state, it acts as a **one-shot continuation**: it waits for `A` to become available, then fires, consuming both itself and `A`, producing `B`.

Key distinction:
- `!(A ⊸ B)` = **persistent rule** (fires whenever A available, never consumed) — the standard forward rule
- `A ⊸ B` = **linear continuation** (fires once, consumed) — a callback / event handler

In a theoretically clean system, loli continuations should fire through the same matching mechanism as regular rules — they are just rules in the state. The trigger `A` is matched against available facts; if matched, the loli and the trigger are consumed and the body `B` is produced.

When the trigger contains a persistent guard (e.g., `!P ⊸ {Q}`), firing requires **proving** `P` (via backward chaining or FFI), not just finding `!P` in the state. This is where the theory meets the implementation challenge.

## 7. The Correspondence

| Linear Logic | Computation |
|---|---|
| Multiset of linear propositions | Program state |
| `A ⊸ B` (persistent rule) | State transition |
| `A ⊸ B` (linear fact) | Continuation / callback |
| `A ⊗ B` | Simultaneous resources |
| `!A` | Persistent / reusable fact |
| `A & B` | External choice (environment decides) |
| `A ⊕ B` | Internal choice (system decides) |
| `1` | No resource / no-op |
| Proof search | Execution |
| Quiescence | Termination |
| Focusing | Execution strategy |
| Forward chaining | Data-driven execution |
| Backward chaining | Goal-directed proving |

## References

- Girard, J.-Y. (1987). "Linear Logic." *Theoretical Computer Science*, 50(1):1-102.
- Andreoli, J.-M. (1992). "Logic Programming with Focusing Proofs in Linear Logic." *J. Logic and Computation*, 2(3):297-347.
- Miller, D. (2004). "An Overview of Linear Logic Programming." Cambridge University Press.
- Watkins, K. et al. (2004). "CLF: A Dependent Logical Framework for Concurrent Computations."
- Lopez, P. et al. (2005). "Monadic Concurrent Linear Logic Programming." *PPDP 2005*.
- Chaudhuri, K. and Pfenning, F. (2006). "A Logical Characterization of Forward and Backward Chaining." *IJCAR 2006*.
- Schack-Nielsen, A. and Schurmann, C. (2008). "Celf — A Logical Framework for Deductive and Concurrent Systems." *IJCAR 2008*.
- Simmons, R. J. and Pfenning, F. (2008). "Linear Logical Algorithms." *ICALP 2008*.
- Cervesato, I. and Scedrov, A. (2009). "Relating State-Based and Process-Based Concurrency through Linear Logic." *Information and Computation*.
- Martens, C. (2015). "Programming Interactive Worlds with Linear Logic." Ph.D. thesis, CMU.

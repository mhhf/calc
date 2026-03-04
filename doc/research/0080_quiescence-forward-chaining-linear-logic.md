---
title: "Quiescence in Forward-Chaining Linear Logic Systems"
created: 2026-03-03
modified: 2026-03-04
summary: "Survey of quiescence definitions across CLF, LolliMon, SLS, Ceptre, CHR, and Datalog — distinguishing quiescence from saturation, and analyzing whether dormant lolis must be drained."
tags: [quiescence, forward-chaining, linear-logic, clf, lollimon, chr, Ceptre, saturation, loli, theory]
category: "Forward Chaining"
---

# Quiescence in Forward-Chaining Linear Logic Systems

## 1. The Core Distinction: Quiescence vs Saturation

Two termination concepts appear across the literature. They coincide in purely persistent (Datalog-like) settings but diverge when linear resources are present.

**Quiescence:** The state where no rule can fire. The system has reached a fixpoint of *applicability* — not of knowledge. A quiescent state may contain unconsumed linear resources (including lolis). Nothing more can happen given the current state.

**Saturation:** The state where no *new* facts can be derived. The system has reached a fixpoint of the immediate consequence operator T_P. Saturation is the standard termination condition for Datalog and persistent forward chaining. In a monotone setting (facts only grow), saturation implies quiescence.

Simmons and Pfenning (PEPM 2009) make this precise: "saturation is a more appropriate term in the absence of linear propositions." With linear propositions, saturation is not well-defined (facts can be consumed, so the state is not monotone) and quiescence is the correct termination criterion.

## 2. CLF: Quiescence Inside the Monad

### 2.1 Definition

In CLF (Watkins, Cervesato, Pfenning, Walker 2002-2004), forward chaining occurs exclusively inside the lax monad `{S}`. Quiescence means: no more forward-chaining rules can fire on the current linear context. At quiescence, the monadic computation returns, yielding the final state back to the backward-chaining caller.

The CLF papers describe this operationally: the system starts with a linear context representing the initial state, applies forward rules using committed choice, and reaches quiescence when no rules match. Celf's `#exec` directive runs to quiescence (or a step limit).

### 2.2 No Lolis Inside the Monad

CLF restricts the monadic type grammar:

```
Asynchronous types:   A, B ::= P | A -o B | A & B | T | {S}
Synchronous types:    S    ::= P | S1 * S2 | 1 | !A | exists x.S
```

Loli (`-o`), with (`&`), and top (`T`) are **excluded from synchronous types**. They cannot appear inside the monad `{S}`. This means CLF states (inside the monad) consist only of atoms, tensored atoms, banged atoms, and existentially quantified terms. No linear implications can be "dormant" in the state.

**Why CLF excludes loli from the monad:**
1. Lolis create "dormant rules" needing separate scheduling — the monad's let-binding `let {p} = e in E` provides sequencing, making nested lolis redundant for sequencing.
2. Definitional equality (identifying computations that differ only in independent step order) breaks when lolis create future-state-dependent ordering constraints.
3. Type checking decidability relies on keeping commuting conversions confined.

### 2.3 Consequence for Quiescence

Because CLF states contain no lolis, quiescence is simply "no compiled rule's antecedent matches the current state." There is no question of "draining dormant lolis" — they cannot exist in the state.

## 3. LolliMon: Quiescence and Saturation

### 3.1 Two Termination Criteria

LolliMon (Lopez, Pfenning, Polakow, Watkins, PPDP 2005) distinguishes quiescence from saturation explicitly:

- **Quiescence:** no further forward steps are possible. The system cannot fire any rule.
- **Saturation:** forward steps may be possible, but they produce no new information. The state is observationally unchanged.

LolliMon always uses saturation to decide when to stop forward chaining. This is observationally equivalent to quiescence except in one case: a concurrent execution might loop forever under quiescence (repeatedly returning to the same state) while terminating under saturation (detecting that no new facts appeared).

### 3.2 The Monadic State

LolliMon inherits CLF's restriction: inside forward-chaining mode, the state is a multiset of atoms (linear and persistent). No lolis appear in the monadic state. The question of dormant lolis does not arise.

### 3.3 Saturation Checking

LolliMon implements saturation checking via term indexing (discrimination tree). When no new atoms are derived after a round of rule applications, saturation is declared. The LolliMon README notes: "Saturation checking for open terms is experimental, and a bit unstable."

## 4. Simmons' SLS: Quiescence as Fixpoint

### 4.1 Linear Logical Algorithms (ICALP 2008)

Simmons and Pfenning define forward-chaining linear logic programs where the state consists of persistent and ephemeral (linear) atomic propositions. The execution model is:

1. Match a rule's antecedent against state atoms
2. Consume matched linear atoms
3. Produce consequent atoms
4. Repeat until no rule matches

Quiescence = no rule matches = the main loop terminates. The state at quiescence is the "final state" or "result" of the computation.

### 4.2 Cost Semantics

The paper defines a formal cost semantics based on "prefix firings" — the abstract running time is the total number of prefix firings from initial state to quiescence. This assumes quiescence is reachable (the program terminates).

### 4.3 Approximation (PEPM 2009)

The key paper for the quiescence/saturation distinction. Simmons and Pfenning show that replacing linear predicates with persistent ones yields a conservative approximation: if the approximate (persistent-only) program reaches saturation, one can "read off" a conservative approximation of all behaviors of the original linear program. Saturation of the approximation bounds the behaviors of the linear original.

### 4.4 States Are Multisets of Atoms

Like CLF, SLS states contain only atomic propositions (linear or persistent). Rules are the program — they are not "in the state." Lolis do not appear as facts in the state. Quiescence is simply "no rule head matches."

## 5. Ceptre: Stages and Quiescence

### 5.1 Definition

Ceptre (Martens 2015) defines quiescence at the stage level: "A stage is over when it is quiescent: no more rules apply to the current program state."

### 5.2 The `qui` Predicate

Ceptre has a special `qui` predicate denoting quiescence of a stage. Stage transition rules have the form: upon quiescence, replace one stage resource with another. This makes quiescence a first-class programming construct.

### 5.3 All-Forward Design

Ceptre drops the monad entirely — all rules are forward-chaining. The state is a multiset of atomic predicates. No lolis appear in the state. Quiescence is "no rule in the current stage can fire."

### 5.4 Non-Termination

Ceptre acknowledges that some stages may never reach quiescence. In the Blocks World example: "we will never reach quiescence" because no goal condition is specified. Interactive stages run indefinitely until a human or external event intervenes.

## 6. CHR: Saturation with Propagation History

### 6.1 CHR Rule Types

CHR has three rule types:
- **Simplification** (`H <=> B`): remove H, add B. Analogous to linear rule.
- **Propagation** (`H ==> B`): keep H, add B. Analogous to persistent rule.
- **Simpagation** (`H1 \ H2 <=> B`): keep H1, remove H2, add B. The general form.

### 6.2 Termination Condition

CHR computation terminates when no more transitions are applicable (successful derivation) or the underlying solver proves unsatisfiability (failed derivation). Both are "final states."

### 6.3 Propagation History

Propagation rules pose a termination challenge: since they keep their heads, the same rule could fire on the same constraints repeatedly, causing trivial non-termination. CHR solves this with a **propagation history** — a set recording which (rule, constraint-tuple) combinations have already fired. A propagation rule is only applied once per unique constraint combination.

This is CHR's analog of saturation: propagation rules fire exhaustively (once per combination), then stop. The propagation history ensures termination of propagation while achieving a fixed point.

### 6.4 Refined Operational Semantics

The refined operational semantics (Duck, Stuckey, de la Banda, Holzbaur, ICLP 2004) makes the execution order deterministic. It processes constraints as "active" — each newly added constraint searches for matching rules in order. The propagation history prevents re-firing.

### 6.5 CHR and Linear Logic

In the CHR-to-linear-logic translation (Betz & Fruhwirth 2005-2013):
- Linear consumption replaces the propagation history for simplification rules
- Propagation rules map to `!H -o !H * B` (H persists via bang)
- The propagation history has no direct linear logic analog — linear consumption makes it unnecessary for simplification, and for propagation, bang semantics handle it

## 7. Datalog: Saturation as Least Fixed Point

Datalog's termination is the cleanest case. Forward chaining computes the immediate consequence operator T_P repeatedly: start with input I, compute T_P(I), T_P(T_P(I)), etc., until T_P^n(I) = T_P^{n+1}(I). The final result is the least fixed point — the minimal model.

Saturation = least fixed point = no new facts derivable. This is guaranteed to terminate for finite domains because the set of derivable facts is finite and T_P is monotone.

## 8. The Key Question: Must Dormant Lolis Be Drained?

### 8.1 The Question Restated

If a forward-chaining linear logic state contains dormant lolis `A -o B` (where A is not currently available in the state), is the state quiescent? Or must these lolis be "drained" (forced to fire, or declared unfireable) before declaring quiescence?

### 8.2 CLF/LolliMon/SLS/Ceptre: Question Does Not Arise

In all the standard systems (CLF, LolliMon, SLS, Ceptre), lolis do **not** appear as facts in the forward-chaining state. The state contains only atomic propositions. Rules are the program, separate from the state. Therefore the question of "dormant lolis in state" simply does not arise in the standard theory.

### 8.3 CALC's Unique Position

CALC extends CLF by allowing loli-in-monad (see THY_0001). A rule consequent can produce `!G -o {B}`, which lands in the state as a linear implication waiting for its trigger. This creates a situation not addressed by any existing system.

### 8.4 Analysis: Quiescence Is Correct Without Draining

A state containing a dormant loli `!G -o {B}` where `G` is not provable IS quiescent. The reasoning:

**From proof theory:** The loli `!G -o B` in the linear context represents a resource. It can only be eliminated via loli-left when `!G` is available. If `!G` cannot be proved (no FFI, no clause, not in state), the loli-left rule is simply not applicable. The state is a valid multiset that happens to contain an unconsumed implication. This is no different from a state containing an unused atom — it is a "leftover resource."

**From operational semantics:** Quiescence means "no rule fires." The matching pipeline checks:
1. All compiled forward rules: none match
2. All loli continuations in state: none can fire (triggers not available)

If both return nothing, the state is quiescent. The dormant loli is simply an unconsumed linear resource at quiescence.

**From the CHR perspective:** A dormant loli is analogous to a constraint in the CHR store that no rule head matches. CHR considers such states final (successful derivation). The constraint remains in the store as part of the answer.

**From the multiset rewriting perspective:** The state `{p, q, (!r -o s)}` where `r` is not provable is a valid multiset. The only applicable rewrite would consume the loli and `!r`, but `!r` is not available. No rewrite applies. The state is a terminal configuration.

### 8.5 When Draining Would Be Wrong

Forcibly "draining" lolis at quiescence would be semantically incorrect:

1. **No trigger available:** If `!G` in `!G -o B` cannot be proved, firing the loli would require fabricating a proof of `G`. This violates soundness.

2. **Linear resources are not obligations:** A linear resource `A -o B` is a capability ("if A appears, produce B"), not an obligation ("B must be produced"). Having an unfired capability at quiescence is perfectly valid — it means the condition never arose.

3. **Garbage collection is not draining:** One might want to *discard* unfired lolis at quiescence for cleanliness (weakening). But discarding is not the same as firing. In linear logic, weakening is only valid for `!`-marked (persistent) resources, not for linear ones. Discarding a linear loli would violate linearity. The loli must simply remain in the final state as an unconsumed resource.

### 8.6 The Correct Interpretation

At quiescence, dormant lolis in the state are **residual resources** — capabilities that were produced but never triggered. The final state correctly includes them. A consumer of the final state can observe them (e.g., for analysis, warnings, or further processing).

In CALC's symexec, a leaf node with dormant lolis represents a valid execution outcome: the computation terminated, and these conditional continuations were never activated. The leaf state `{pc 63, sh 0, !eq X Y -o {stack 0 1}}` means: "execution reached PC 63 with stack height 0, and the equality guard was never triggered."

## 9. Summary Table

| System | State contents | Termination criterion | Lolis in state? | Draining required? |
|---|---|---|---|---|
| **CLF** | Atoms, tensor, bang, exists | Quiescence (no rule fires) | No (forbidden by grammar) | N/A |
| **LolliMon** | Atoms (linear + persistent) | Saturation (no new facts) | No (monadic state is atoms) | N/A |
| **SLS** | Atoms (ephemeral + persistent) | Quiescence (no rule fires) | No (rules are program) | N/A |
| **Ceptre** | Atomic predicates | Quiescence per stage | No (all-forward, atoms only) | N/A |
| **CHR** | Constraints (atoms) | No rule applicable + propagation history | No (rules are program) | N/A |
| **Datalog** | Persistent atoms | Saturation (least fixed point) | No (persistent only) | N/A |
| **CALC** | Atoms + lolis + bang atoms | Quiescence (no rule or loli fires) | **Yes** (loli-in-monad extension) | **No** (dormant lolis are residual resources) |

## References

### CLF / Celf / LolliMon
- Watkins, Cervesato, Pfenning, Walker. [A Concurrent Logical Framework I](http://www.cs.cmu.edu/~fp/papers/CMU-CS-02-101.pdf). CMU-CS-02-101 (2002).
- Watkins et al. [CLF: A Dependent Logical Framework for Concurrent Computations](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). (2004).
- Lopez, Pfenning, Polakow, Watkins. [Monadic Concurrent Linear Logic Programming](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf). PPDP 2005.
- Schack-Nielsen, Schurmann. [Celf](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28). IJCAR 2008.

### SLS / Linear Logical Algorithms
- Simmons, Pfenning. [Linear Logical Algorithms](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf). ICALP 2008.
- Simmons, Pfenning. [Linear Logical Approximations](https://www.cs.cmu.edu/~fp/papers/pepm09.pdf). PEPM 2009.
- Simmons. [Substructural Logical Specifications](https://www.cs.cmu.edu/~rwh/students/simmons.pdf). PhD thesis, CMU-CS-12-142 (2012).

### Ceptre
- Martens. [Ceptre: A Language for Modeling Generative Interactive Systems](https://www.cs.cmu.edu/~cmartens/ceptre.pdf). AIIDE 2015.
- Martens. [Programming Interactive Worlds with Linear Logic](https://www.cs.cmu.edu/~cmartens/thesis/). PhD thesis, CMU (2015).

### CHR
- Duck, Stuckey, de la Banda, Holzbaur. [The Refined Operational Semantics of CHR](https://www.comp.nus.edu.sg/~gregory/papers/iclp2004a.pdf). ICLP 2004.
- Betz, Fruhwirth. A Linear-Logic Semantics for CHR. CP 2005.
- Betz, Fruhwirth. [CHR with Disjunction](https://arxiv.org/abs/1009.2900). ACM TOCL 14(1) (2013).

### Focusing / Polarity
- Chaudhuri, Pfenning, Price. [Forward and Backward Chaining in the Inverse Method](https://www.cs.cmu.edu/~fp/papers/ijcar06.pdf). IJCAR 2006.

### Datalog
- Pfenning. [Lecture Notes on Datalog](https://www.cs.cmu.edu/~fp/courses/15317-f17/lectures/18-datalog.pdf). 15-317 (2017).

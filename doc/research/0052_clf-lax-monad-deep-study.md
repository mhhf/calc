---
title: "The CLF Lax Monad {A}: Deep Study"
created: 2026-02-23
modified: 2026-02-23
summary: "Comprehensive study of the CLF lax monad — original papers, LolliMon, focusing/polarity, SLS, proof-theoretic status, adjoint logic relationship, Ceptre simplification, and implications for CALC's extensions."
tags: [clf, lax-monad, forward-chaining, backward-chaining, focusing, lollimon, adjoint-logic, ceptre, moggi, curry-howard]
category: "Related Paradigms"
---

# The CLF Lax Monad {A}: Deep Study

## 1. The Original CLF Papers

### 1.1 Core References

- Watkins, Cervesato, Pfenning, Walker. "A Concurrent Logical Framework I: Judgments and Properties." CMU-CS-02-101 (2002). The technical report with full metatheory.
- Watkins, Cervesato, Pfenning, Walker. "A Concurrent Logical Framework: The Propositional Fragment." TYPES 2003, LNCS 3085 (2004). The published conference paper.
- Watkins, Cervesato, Pfenning, Walker. "CLF: A Dependent Logical Framework for Concurrent Computations." (2004). The dependent-type extension.

### 1.2 What is {A}?

The monadic type `{S}` is the central innovation of CLF. It acts as a coercion from **synchronous types** into **asynchronous types**.

**Type grammar (propositional fragment):**

```
Asynchronous types:   A, B ::= P | A -o B | A & B | T | {S}
Synchronous types:    S    ::= P | S1 * S2 | 1 | !A | exists x.S
```

The asynchronous types are: atoms `P`, linear implication `A -o B`, additive product `A & B`, additive truth `T`, and the monadic type `{S}`. The synchronous types are: atoms `P`, tensor `S1 * S2`, unit `1`, bang `!A`, and existential `exists x.S`.

The monad `{S}` is the **only** bridge from synchronous to asynchronous. No synchronous type can appear at the top level except wrapped in `{...}`.

### 1.3 Proof Terms: Three Syntactic Categories

CLF distinguishes three classes of proof terms, corresponding to the type stratification:

| Category | Types | Terms | Role |
|---|---|---|---|
| **Normal terms** N | Asynchronous (A) | lambda, pair, unit, `{E}` | Values / backward-chaining results |
| **Monadic terms** M | Synchronous (S) | tensor pair, `*`, `!N`, `<>` | Data constructors inside monad |
| **Expressions** E | Monadic computation | `let {p} = R in E`, `M` | Computations (eliminations + return) |

The expression form `let {p} = R in E` is the monadic elimination: it deconstructs a value of type `{S}`, binding the synchronous pattern `p`, then continues with expression `E`. A monadic computation is a sequence of let-bindings ending in a monadic term.

### 1.4 Introduction and Elimination

**Monad introduction** (`{}I`): if `E` is a well-typed expression of synchronous type `S`, then `{E}` is a normal term of type `{S}`.

**Monad elimination** (`{}E`): the let-binding `let {p} = R in E`. This is where all concurrency lives. The crucial insight: independent let-bindings can be **reordered** without changing meaning.

### 1.5 Definitional Equality: True Concurrency

The key metatheoretic property: CLF's definitional equality identifies monadic expressions that differ only in the order of independent let-bindings. Two expressions `E1` and `E2` are definitionally equal if they differ only by permuting independent let-steps.

This is what makes CLF a framework for **concurrent** computation: the order of independent steps is irrelevant. The definitional equality captures "true concurrency" as opposed to interleaving semantics.

Restricting synchronous types to the monad is what makes this definitional equality tractable. If synchronous types (tensor, bang, existential) could appear outside the monad, the commuting conversions for their let-eliminators would infect the entire type theory, destroying the decidability of type checking.

### 1.6 Why These Specific Connectives?

**Inside the monad (synchronous):** `tensor`, `1`, `!`, `exists`. These are the "positive" / "synchronous" connectives of linear logic — their right rules require a choice. They represent data production: creating pairs, persisting facts, introducing witnesses.

**Outside the monad (asynchronous):** `-o`, `&`, `T`. These are the "negative" / "asynchronous" connectives — their right rules are invertible (no choice needed). They represent computation structure: functions, records, trivial goals.

**Excluded from the monad:** `-o` (loli), `&` (with), `T` (top). These are asynchronous — they belong outside. Putting them inside would require commuting conversions that break the clean monadic structure.

## 2. LolliMon: The Monad Bridges Forward and Backward

### 2.1 Overview

LolliMon = Lolli + Monad. Lopez, Pfenning, Polakow, Watkins (PPDP 2005).

Lolli is a backward-chaining linear logic programming language (the linear logic analog of lambda-Prolog). LolliMon extends it with CLF's synchronous connectives restricted to the monad.

### 2.2 The Two Modes

**Outside the monad (backward chaining):**
- Goal-directed proof search
- Backtracking on failure
- Uniform proofs (Miller et al.)
- Connectives: `-o`, `&`, `T`, atoms, and goals of the form `{S}`

**Inside the monad (forward chaining):**
- Data-driven multiset rewriting
- Committed choice (no backtracking)
- Connectives: `tensor`, `1`, `!`, atoms
- Runs until quiescence (no more rules fire)

### 2.3 The Bridge Mechanism

When backward-chaining proof search encounters a goal of type `{S}`, it switches to forward-chaining mode. The forward engine:

1. Takes the current linear context as the initial multiset state
2. Applies forward rules (clauses whose heads are monadic) using committed choice
3. Runs until quiescence
4. Returns the resulting state as the proof of `{S}`

When a forward rule's body references a non-monadic goal, backward chaining is invoked to prove it. This is how the two modes interleave.

### 2.4 Operational Semantics

A LolliMon program consists of two kinds of clauses:

- **Backward clauses:** `A :- G1, ..., Gn` where A is an atom and Gi are goals. Standard Lolli backward chaining.
- **Forward clauses (monadic):** `{S} :- G1, ..., Gn` where S is synchronous. When the goal `{S}` is encountered, the engine switches to forward mode.

Inside forward mode, the state is a multiset of atoms. Rules are applied by:
1. Matching a rule's antecedent against state atoms
2. Proving any persistent antecedents (via backward chaining)
3. Consuming matched linear atoms
4. Adding the rule's consequent atoms to the state

### 2.5 Committed Choice and Saturation

Forward chaining uses committed choice: once a rule fires, there is no backtracking. This is essential for modeling concurrent computation — the system commits to interleaving choices.

Quiescence (saturation of the linear state) terminates forward mode. The final state is returned to the backward-chaining caller.

### 2.6 Key Example: Pi-Calculus Encoding

LolliMon can encode the pi-calculus:
- Channels are linear resources
- Send/receive are forward rules consuming/producing channel resources
- Process composition is the tensor of channel states
- The monad captures the "concurrent execution" aspect

## 3. Focusing, Polarity, and the Monad

### 3.1 Chaudhuri, Pfenning, Price (IJCAR 2006, JAR 2008)

Paper: "A Logical Characterization of Forward and Backward Chaining in the Inverse Method."

### 3.2 The Core Insight

In Andreoli's focused proof search, connectives have fixed polarity:
- **Positive (synchronous):** `tensor`, `oplus`, `1`, `0`, `!`, `exists` — right-intro requires a choice
- **Negative (asynchronous):** `-o`, `&`, `T`, `bot`, `?`, `forall` — right-intro is invertible

But **atoms have no fixed polarity**. The choice of polarity for atoms is a parameter of the focused system. Chaudhuri and Pfenning showed:

- **Positive atoms** produce forward chaining behavior: facts are derived bottom-up, accumulated in the database. This corresponds to hyperresolution.
- **Negative atoms** produce backward chaining behavior: goals are decomposed top-down. This corresponds to SLD resolution.
- **Mixed polarity** produces combinations of both.

### 3.3 The Structural Explanation

This is not just an operational observation — it is a **structural** (proof-theoretic) characterization. Forward and backward chaining are two polarities of the same focused proof search framework. The choice is not about the search procedure; it is about the logic itself.

In a focused proof:
- A negative atom on the right (as a goal) forces immediate identity or decomposition — backward chaining.
- A positive atom on the right triggers the focus phase — the system must choose premises that derive this atom, building the proof bottom-up — forward chaining.

### 3.4 Relationship to CLF's Monad

The monadic separation in CLF corresponds exactly to the polarity separation in focusing:
- **Outside the monad** = negative polarity = backward chaining = asynchronous phase
- **Inside the monad** = positive polarity = forward chaining = synchronous (focus) phase

The monad `{S}` is the **polarity shift** from negative to positive. Entering the monad switches from the asynchronous (inversion) phase to the synchronous (focus) phase of proof search.

This provides the deep proof-theoretic justification for CLF's design: the monad is not an ad-hoc operational trick, but the natural polarity shift in focused linear logic.

### 3.5 Implications for Mixed Systems

A system could assign atoms different polarities independently. Some atoms could be forward-chained (positive) while others are backward-chained (negative). This is more general than CLF's all-or-nothing monadic separation, but harder to implement and reason about.

CALC's persistent antecedents (proved via backward chaining inside forward rules) are exactly this: persistent predicates are effectively negative atoms (proved backward) even while the overall computation is forward-chaining.

## 4. Rob Simmons' Thesis and SLS

### 4.1 Overview

Robert J. Simmons. "Substructural Logical Specifications." PhD thesis, CMU-CS-12-142 (2012). Advised by Frank Pfenning.

### 4.2 SLS: Ordered Linear Lax Logic

SLS (Substructural Logical Specifications) is a logical framework defined as a fragment of **ordered linear lax logic**. It extends CLF in one direction (ordered hypotheses) and restricts it in another (propositional, no dependent types). The key contribution is a methodology for relating different styles of programming language specification.

### 4.3 The Persistent vs. Ephemeral Distinction

Simmons, building on his joint work with Pfenning (ICALP 2008, "Linear Logical Algorithms"), formalizes the distinction:

- **Persistent propositions** (`!A`): Available indefinitely. Can be used any number of times. Never consumed. Written with a `!` or placed in a persistent (cartesian) context.
- **Ephemeral propositions** (linear): Available once. Consumed on use. The standard linear context.

In forward chaining, this becomes:
- **Persistent facts** = the immutable knowledge base (types, axioms, arithmetic truths)
- **Ephemeral facts** = the mutable state (resources, tokens, program counter)

The ICALP 2008 paper introduced underlining notation: `a` (underlined) for ephemeral atoms, `a` for persistent atoms. Different atoms can have different persistence, unlike CLF where `!` is explicit.

### 4.4 Focusing in SLS

Simmons synthesizes Andreoli's focusing with Watkins' hereditary substitution technique ("structural focalization"). The key result: for any logic describable in the framework, focused derivations form a complete proof search strategy.

For forward chaining specifically:
- The inversion (asynchronous) phase decomposes goals eagerly
- The focus (synchronous) phase selects a rule and applies it
- Polarity of atoms determines forward vs. backward behavior (per Chaudhuri-Pfenning)

### 4.5 Relationship to CLF

SLS is complementary to CLF:
- CLF provides dependent types but only linear + lax modalities
- SLS adds ordered hypotheses (useful for stack-like structures) but drops dependent types
- Both use the lax monad for the forward/backward bridge
- SLS provides four methodologies (structural focalization, SLS framework itself, logical correspondence, linear logical approximation) that could be applied to CLF-based systems

### 4.6 Linear Logical Algorithms (Simmons & Pfenning, ICALP 2008)

This paper established forward-chaining linear logic programming as a serious algorithmic tool. Key contributions:
- A cost semantics for complexity analysis of linear logic programs
- Demonstrations of MST, Dijkstra, and other graph algorithms encoded as linear logic programs
- The persistent/ephemeral distinction as the basis for algorithm specification

## 5. Proof-Theoretic Status of the Lax Monad

### 5.1 Origin: Propositional Lax Logic (Fairtlough & Mendler, 1997)

Propositional Lax Logic (PLL) is an intuitionistic modal logic featuring a single modal operator circle (`O`) that has aspects of both possibility and necessity.

**Axioms of PLL** (extending intuitionistic propositional logic):
- `A -> OA` (unit / return)
- `O(A -> B) -> (OA -> OB)` (functoriality / strength)
- `OOA -> OA` (join / multiplication)

These are exactly the **monad laws** in logical form. PLL is the internal logic of a category with a strong monad.

**Models:** Two-frame Kripke models (W, R_imp, R_circ) where R_circ is a subrelation of R_imp. The worlds include "fallible" worlds (where all formulas hold), modeling computational failure/divergence.

### 5.2 Pfenning-Davies Judgmental Reconstruction (2001)

Pfenning and Davies reconstruct modal logic judgmentally, introducing separate judgment forms:

- `A true` — A is true (standard)
- `A valid` — A is true in all worlds (necessity)
- `A lax` — A is "laxly true" (achievable through computation)

The lax modality gets two rules:

**Lax introduction:**
```
    A lax
  ---------  OI
   OA true
```

**Lax elimination:**
```
  OA true    [A true |- C lax]
  ----------------------------  OE
          C lax
```

The elimination rule is notable: from a lax truth `OA`, one can only conclude `C lax` (another lax truth), not `C true`. The monad is "sticky" — once you enter lax truth, you cannot escape to plain truth.

This corresponds to the computational interpretation: once a computation has effects, the result is permanently effectful.

### 5.3 Curry-Howard Correspondence

The lax monad corresponds via Curry-Howard to **Moggi's computational monad** (1989, 1991).

| Logic | Type Theory | Category Theory |
|---|---|---|
| `OA` (lax truth) | `T A` (computation type) | `T(A)` (monad applied to A) |
| `A -> OA` (unit) | `return : A -> T A` | `eta : Id -> T` (unit) |
| `OOA -> OA` (join) | `join : T(T A) -> T A` | `mu : T^2 -> T` (multiplication) |
| OE rule | `let x <- m in e` (bind) | Kleisli extension |

Moggi's insight: **computational effects** (state, IO, exceptions, nondeterminism, continuations) can all be modeled by strong monads. The type `T A` means "a computation that, when executed, may perform effects and produces a value of type A."

CLF specializes this to: `{S}` means "a concurrent computation that, when executed via forward chaining, produces resources of type S."

### 5.4 Category-Theoretic Structure

The lax monad `{A}` in CLF corresponds to:
- A **strong monad** T on the category of types
- **Monadic strength** captures the interaction with the linear context
- The Kleisli category of T is the category of "computations" (forward-chaining processes)

More precisely, in the linear setting:
- The **monoidal** structure of tensor gives concurrent composition
- The monad provides **sequencing** (let-binding)
- The definitional equality (permuting independent lets) makes this a **commutative** (or symmetric) monad in the concurrent fragment

### 5.5 The Lax Monad in Recent Work (2024-2026)

Kavvos, Pfenning, et al. (CSL 2026): "Lax Modal Lambda Calculi" introduces a hierarchy of four typed lambda calculi corresponding to sublogics of PLL:

| Calculus | Axioms | Models | Term constructs |
|---|---|---|---|
| lambda_SL | S only | Strong functors | `letmap` only |
| lambda_SRL | S + R | Strong pointed functors | `letmap` + `return` |
| lambda_SJL | S + J | Strong semimonads | `letmap` + `let` (bind) |
| lambda_ML | S + R + J | Strong monads (full PLL) | `return` + `let` |

Where: S = functoriality `O(A->B) -> OA -> OB`, R = unit `A -> OA`, J = join `OOA -> OA`.

This work normalizes by evaluation (NbE) using proof-relevant possible-world semantics. It confirms that the lax modality admits weaker-than-monad structures (functors, pointed functors, semimonads).

**Relevance to CALC:** CALC's forward engine uses the full monad (lambda_ML): `return` is monadic introduction, `let` is sequential composition. But the hierarchy suggests that weaker fragments could be useful for restricted forward-chaining modes.

## 6. Adjoint Logic and the Lax Monad

### 6.1 The Adjunction Behind the Lax Monad

Following Reed (2009), Pruiksma, Chargin, Pfenning, Reed (2018), and Licata, Shulman (2016):

The lax modality arises from an adjunction between two **modes**:
- Mode `U` (unrestricted / truth)
- Mode `X` (lax / computation)

With an adjunction `F : U -> X` (left adjoint, downshift) and `U : X -> U` (right adjoint, upshift):

```
F |- U        (F is left adjoint to U)

Lax monad:  O A  =  U(F(A))  =  upshift(downshift(A))
```

The monad `UF` on mode U is exactly the lax modality.

### 6.2 Comparison with Other Modal Operators

| Operator | Adjunction | Monad/Comonad | Modes |
|---|---|---|---|
| `!A` (bang) | `F -| U` between cartesian and linear | Comonad `FU` on linear | U > L |
| `OA` (lax) | `F -| U` between truth and lax | Monad `UF` on truth | U > X |
| `box A` (necessity) | `F -| U` between truth and validity | Comonad `FU` on truth | V > U |

### 6.3 Shift Operators in Adjoint Logic

In adjoint logic (Pruiksma et al. 2018), the general shift operators are:

- `upshift^k_m A_k` — lift A from mode k to mode m (right adjoint = U)
- `downshift^m_k A_m` — project A from mode m to mode k (left adjoint = F)

The lax monad is `upshift^X_U (downshift^X_U A_U)`. This is one specific instantiation of the general adjoint framework.

### 6.4 How This Subsumes CLF

CLF's type theory can be embedded in adjoint logic with two modes:
- Mode `U` (asynchronous = backward chaining)
- Mode `X` (synchronous = forward chaining)

The monadic type `{S}` = `upshift^X_U S_X`. Entering the monad = applying `downshift^X_U` to get into mode X. Exiting = applying `upshift^X_U` to return to mode U.

This gives a cleaner account of the synchronous/asynchronous split: it is not an ad-hoc syntactic restriction but falls out of the mode theory.

### 6.5 The Fibrational Framework (Licata, Shulman, Riley, 2017)

The most general setting. The logic is parametrized by a 2-category of modes. Each mode is a category, each mode morphism is an adjunction, and mode 2-morphisms are morphisms of adjunctions.

This framework covers: LNL, S4, lax logic, session types, bunched implications, ordered logic, and adjoint logic itself — all as special cases of different mode theories. Cut and identity are admissible generically.

## 7. Ceptre's Simplification of CLF

### 7.1 What Ceptre Keeps

Chris Martens' Ceptre (PhD thesis, CMU, 2015) simplifies CLF for interactive systems:

- Forward-chaining linear rules (multiset rewriting)
- Simple types (no dependent types, no Sigma/Pi)
- Committed choice per step
- Stages: named rule sets that run to quiescence, with explicit stage transitions

### 7.2 What Ceptre Drops

- **The monad itself.** All rules are forward chaining. There is no backward-chaining mode and no monadic boundary.
- **Backward chaining.** No goal-directed search. All computation is forward.
- **Dependent types.** Simple first-order types only.
- **Additives.** No `&` or `oplus` in the surface language.
- **Existentials.** No explicit existential quantification (implicit via metavariables).

### 7.3 What Is Lost

**Backward chaining integration.** In CLF/Celf/LolliMon, backward chaining proves persistent goals and computes with functions. Ceptre cannot do this — all "computation" must be encoded as forward rules, which is awkward for arithmetic, type checking, and other inherently goal-directed tasks.

**The monadic discipline.** The monad provides a clean separation between effectful (state-changing) and pure (deterministic) computation. Without it, all computation is effectful. There is no way to express "compute this value without changing state" versus "transition the state."

**Additives.** No way to express nondeterministic or disjunctive outcomes within a single rule. Each rule deterministically rewrites.

**Expressiveness for algorithms.** Simmons & Pfenning (2008) showed that many graph algorithms need backward chaining for auxiliary computation (e.g., comparing distances in Dijkstra). Ceptre cannot express these naturally.

### 7.4 What Is Gained

**Simplicity.** Ceptre is dramatically simpler to implement and understand. One mode, one search strategy, explicit control via stages.

**Stages as quiescence programming.** Stages are Ceptre's genuinely novel contribution. They structure computation as: run stage A to quiescence, then fire transition rules to determine the next stage. This provides a form of control flow that CLF lacks.

**Interactivity.** Ceptre supports interactive execution (human chooses among applicable rules) and random execution (for simulation/testing). These are natural for game mechanics and narrative generation.

## 8. Practical Considerations for CALC

### 8.1 CALC's Violations of CLF's Restrictions

CALC extends CLF in three ways documented in THY_0001:

**Lolis inside the monad (guarded continuations).** CLF forbids `-o` inside `{S}`. CALC allows it:
```
evm/iszero: ... -o { ... * (!eq V 0 -o { stack SH 1 }) }
```

The loli `!eq V 0 -o { stack SH 1 }` is a conditional continuation: "if eq(V,0) is provable, produce stack(SH,1)." This is the loli-left rule applied to facts in the state.

**Additives (`oplus`) inside the monad.** CLF excludes additives. CALC uses `oplus` for symbolic branching:
```
evm/eq: ... -o { (stack SH 0 * !neq X Y) + (stack SH 1 * !eq X Y) }
```

**Exhaustive exploration.** CLF uses committed choice (don't-care nondeterminism). CALC's symexec explores all paths (don't-know nondeterminism).

### 8.2 Theoretical Trade-offs of Lolis Inside the Monad

**What breaks:**
1. **Definitional equality.** CLF's concurrent definitional equality identifies computations differing only in independent step order. Lolis create "dormant rules" — their firing depends on future state, so their position in the let-sequence matters. The simple permutation equality breaks.
2. **Monadic let sufficiency.** CLF's design principle is that `{A} tensor (A -o {B}) -o {B}` provides sequencing. Lolis-in-monad need a different mechanism: state-matching + backward proving.
3. **Decidability of type checking.** With lolis inside, commuting conversions become more complex.

**What is preserved:**
1. **Soundness.** Each loli firing is a valid loli-left application. The extension is sound provided lolis compete equally with compiled rules (this was a bug in CALC, fixed in TODO_0041).
2. **Linearity.** A loli `!A -o B` in the state is linear — fires once, consumed. It cannot become persistent (`!(A -o B)`) because bang-right requires an empty linear context.
3. **Operational semantics.** The execution model is still: at each step, select any fireable rule or fireable loli, apply it. The matching pipeline is unified.

**CALC's justification:** conditional production within a single rule's consequent. The pattern `!guard -o { body }` means "if guard holds, produce body." Monadic let cannot express this: it would require factoring every conditional rule into multiple rules with explicit state tokens.

### 8.3 Theoretical Trade-offs of Additives Inside the Monad

The inclusion of `oplus` in forward consequents corresponds to CHR-with-disjunction (Betz & Fruhwirth 2013). Their soundness theorem transfers: every CALC forward derivation corresponds to a valid ILL derivation.

`oplus`-left is invertible — case-split eagerly. This is the standard treatment. In the forward engine, `expandItem` forks into alternatives, creating branches in the execution tree.

### 8.4 Alternatives to the Monadic Approach

**Pure focusing (no monad).** Use polarity assignment to atoms (Chaudhuri-Pfenning) instead of a monadic boundary. Forward-chained atoms get positive polarity, backward-chained atoms get negative polarity. This is more flexible but requires per-atom polarity decisions and loses the clean mode separation.

**Adjoint logic modes.** Use the mode theory of adjoint logic with a forward mode and a backward mode. The shift operators replace the monad. This is more general (can have multiple forward modes, graded resource tracking) but more complex.

**Stages only (Ceptre approach).** Drop the monad entirely, make everything forward-chaining, use stages for control. Simpler but loses backward chaining and is less expressive for algorithms.

**CHR with constraint store.** Use CHR's constraint handling approach: a constraint store with propagation/simplification rules. Guards replace backward chaining. This is close to what CALC already does but has different theoretical foundations (logical semantics via Betz-Fruhwirth rather than type-theoretic semantics via CLF).

### 8.5 The Relationship to CALC's Architecture

| CLF concept | CALC implementation | Notes |
|---|---|---|
| Monad `{S}` | `expandItem` in forward.js | Monadic decomposition |
| Monadic let | Sequential rule application | Implicit in the main loop |
| Backward chaining | `prove.js` + FFI | Level 2 of persistent proving |
| Forward chaining | `forward.js` main loop | Committed choice per step |
| Quiescence | `run()` termination | No more rules fire |
| Synchronous types | Atoms, tensor, bang in consequents | Plus `oplus` and `loli` (extensions) |
| Asynchronous types | Rule antecedents, `-o` structure | Backward proving for persistent ante |
| Definitional equality | Not implemented | Not needed for forward-only |
| Polarity of atoms | All atoms are positive (forward) | Persistent atoms proved backward via Level 2 |

## 9. Open Questions and Future Directions

### 9.1 Can CALC's Extensions Be Formalized Within Adjoint Logic?

The mode theory approach suggests: add a mode `G` (guarded) below mode `X` (forward), where the downshift `X -> G` creates a guarded continuation. This would give a type-theoretic account of loli-in-monad.

### 9.2 What Would a Full Dependent-Type CLF Give CALC?

Dependent types (`Pi`, `Sigma`) would enable:
- Type-level specifications of rule correctness
- Metatheoretic reasoning (subject reduction proofs as types)
- More precise persistent predicates (indexed by term values)

But they bring significant implementation complexity (type checking, capture-avoiding substitution, kind system).

### 9.3 Existentials in Forward Consequents

CLF allows `exists` inside `{S}`. CALC doesn't yet use explicit existentials in forward rules, but symbolic metavariables serve the same role. Making existentials explicit would:
- Connect to Skolemization (eigenvariable introduction)
- Enable the loli-freeze pattern with proper quantifier scoping
- Clarify the semantics of fresh symbolic values in symexec

### 9.4 Semi-Naive Evaluation for Linear Logic

No published work addresses Datalog-style semi-naive evaluation when facts can be consumed. CALC sidesteps this with indexing (strategy stack). For very large state spaces, incremental matching matters. This remains an open research problem.

## References

### CLF / Celf

- Watkins, Cervesato, Pfenning, Walker. [A Concurrent Logical Framework I: Judgments and Properties](http://www.cs.cmu.edu/~fp/papers/CMU-CS-02-101.pdf). CMU-CS-02-101 (2002).
- Watkins, Cervesato, Pfenning, Walker. [A Concurrent Logical Framework: The Propositional Fragment](https://www.cs.cmu.edu/~iliano/papers/types03.pdf). TYPES 2003 (2004).
- Watkins, Cervesato, Pfenning, Walker. [CLF: A Dependent Logical Framework for Concurrent Computations](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). (2004).
- Schack-Nielsen, Schurmann. [Celf: A Logical Framework for Deductive and Concurrent Systems](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28). IJCAR 2008.

### LolliMon

- Lopez, Pfenning, Polakow, Watkins. [Monadic Concurrent Linear Logic Programming](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf). PPDP 2005.
- [LolliMon GitHub Repository](https://github.com/clf/lollimon).

### Focusing and Polarity

- Andreoli. Logic Programming with Focusing Proofs in Linear Logic. JLC 2(3):297-347 (1992).
- Chaudhuri, Pfenning, Price. [A Logical Characterization of Forward and Backward Chaining in the Inverse Method](https://www.cs.cmu.edu/~fp/papers/ijcar06.pdf). IJCAR 2006.
- Liang, Miller. [Focusing and Polarization in Linear, Intuitionistic, and Classical Logics](https://www.lix.polytechnique.fr/~dale/papers/tcs09.pdf). TCS 410(46):4747-4768 (2009).

### Simmons / SLS

- Simmons, Pfenning. [Linear Logical Algorithms](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf). ICALP 2008.
- Simmons. [Substructural Logical Specifications](https://www.cs.cmu.edu/~rwh/students/simmons.pdf). PhD thesis, CMU-CS-12-142 (2012).

### Lax Logic and Monads

- Fairtlough, Mendler. [Propositional Lax Logic](https://www.uni-bamberg.de/fileadmin/uni/fakultaeten/wiai_professuren/grundlagen_informatik/papersMM/pll.pdf). Information and Computation 137(1):1-33 (1997).
- Pfenning, Davies. [A Judgmental Reconstruction of Modal Logic](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/judgmental-reconstruction-of-modal-logic/975027BB7F07B59619913EAD4CEE52F4). MSCS 11(4):511-540 (2001).
- Moggi. [Notions of Computation and Monads](https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf). Information and Computation 93(1):55-92 (1991).
- Kavvos et al. [Lax Modal Lambda Calculi](https://arxiv.org/abs/2512.10779). CSL 2026.

### Adjoint Logic

- Reed. A Judgmental Deconstruction of Modal Logic. (2009).
- Licata, Shulman. [Adjoint Logic with a 2-Category of Modes](https://dlicata.wescreates.wesleyan.edu/pubs/ls15adjoint/ls15adjoint.pdf). LFCS 2016.
- Licata, Shulman, Riley. [A Fibrational Framework for Substructural and Modal Logics](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.25). FSCD 2017.
- Pruiksma, Chargin, Pfenning, Reed. [Adjoint Logic](https://ncatlab.org/nlab/files/PCPR18-AdjointLogic.pdf). (2018).

### Ceptre

- Martens. [Ceptre: A Language for Modeling Generative Interactive Systems](https://www.cs.cmu.edu/~cmartens/ceptre.pdf). (2015).
- Martens. [Programming Interactive Worlds with Linear Logic](https://www.cs.cmu.edu/~cmartens/thesis/). PhD thesis, CMU (2015).

### Indexed Lax Logic

- Garg. [From Indexed Lax Logic to Intuitionistic Logic](https://people.mpi-sws.org/~dg/papers/cmu-cs-07-167.pdf). CMU-CS-07-167 (2007).

### Pfenning Lecture Notes

- Pfenning. [Lecture Notes on Monadic Logic Programming](https://www.cs.cmu.edu/~fp/courses/15816-s12/lectures/20-monad.pdf). 15-816: Linear Logic (2012).

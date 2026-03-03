---
title: "muMALL, Cyclic Proofs, Tabling, and Their Interrelationships"
created: 2026-03-02
modified: 2026-03-02
summary: "Deep survey of muMALL (linear logic with fixed points), cyclic proofs, tabling, exponential encodings, session types, two-level logic, and whether fixed points can subsume Ceptre stages"
tags: [muMALL, linear-logic, fixed-points, cyclic-proofs, proof-theory, focusing, coinduction, induction, session-types, tabling, exponentials, cut-elimination, Ceptre, model-checking, proof-search]
category: "Proof Theory"
---

## 1. muMALL: Linear Logic with Least and Greatest Fixed Points

### 1.1 Motivation

MALL (multiplicative-additive linear logic) with first-order quantifiers and equality is expressive but **weak**: it cannot capture unbounded (infinite) behavior. The standard fix in full linear logic is adding exponentials (!, ?). Baelde and Miller (LPAR 2007, TOCL 2012) take a different path: add **least fixed point** (mu) and **greatest fixed point** (nu) operators directly.

The resulting logic is called **muMALL** (also written mu-MALL or muMALL=).

### 1.2 Syntax

Extend MALL formulas with:
- **mu B x** = least fixed point of body B binding variable x
- **nu B x** = greatest fixed point of body B binding variable x

Bodies B must be **monotone** (the bound variable appears only positively). Since the logic uses negation-normal form, this is syntactic: no negation of the bound variable.

Standard encodings:
- **Natural numbers**: `nat = mu X. (1 oplus X)` -- zero is left injection (1), successor is right injection (recursive X)
- **Lists of A**: `list A = mu X. (1 oplus (A tensor X))`
- **Streams of A**: `stream A = nu X. (A tensor X)` -- coinductive infinite sequences
- **Binary trees**: `tree A = mu X. (A oplus (X tensor X))`

### 1.3 Inference Rules

The proof system has four key rules organized into two groups:

**Unfolding rules** (structural, always applicable):
- **muR** (mu-right / fold): to prove `mu B`, prove `B[mu B / X]` -- unfold the definition once
- **nuL** (nu-left / unfold): from `nu B` on the left, get `B[nu B / X]`

**Induction/coinduction rules** (the power rules):
- **muL** (mu-left / induction): from `mu B` on the left, prove a property holds for all unfoldings. Uses an invariant S such that B[S/X] entails S. This is structural induction.
- **nuR** (nu-right / coinduction): to prove `nu B` on the right, exhibit a coinvariant S such that S entails B[S/X]. This is coinduction.

The induction rule (muL) uses a higher-order variable S representing the invariant. The coinduction rule (nuR) uses S as the coinvariant.

Crucially, the **unfolding rules are derivable** from induction/coinduction, so the core system needs only the (co)induction rules. But for proof search, having both is essential.

### 1.4 Proof-Theoretic Properties

**Cut elimination**: muMALL satisfies cut elimination (implies consistency).

**Weak normalization**: Cut-free proofs have a weak normal form.

**Focusing** (the key result for automation): Baelde and Miller prove a **complete focused proof system** for muMALL. The polarity assignment is:
- **mu is positive** (like tensor, oplus, 1) -- invertible on the LEFT, focusable on the RIGHT
- **nu is negative** (like with, loli, par) -- invertible on the RIGHT, focusable on the LEFT

This means: least fixed points define **data types** (integers, lists, trees) which are positive/synchronous. Greatest fixed points define **codata types** (streams, processes) which are negative/asynchronous.

The focused proof system provides a strong normal form that **directly enables proof search automation**.

### 1.5 The Manighetti-Miller Hierarchy

Manighetti and Miller use muMALL as a **unified framework for computational logic**. By restricting the nesting depth of fixed points, they recover a hierarchy:

| Level | Fixed-point restriction | Captures |
|-------|------------------------|----------|
| 0 | No fixed points (pure MALL=) | Unification problems |
| 1 | Stratified least fixed points | Horn-clause logic programming |
| 2 | Alternating mu/nu | Model checking problems |
| 3 | Nested fixed points with arithmetic | Linearized Peano arithmetic |

At level 1, proof search in muMALL is essentially Prolog. At level 2, it is essentially model checking (mu-calculus style). The proof search interpretation can compute **general recursive functions**, and several situations where provability in Peano Arithmetic can be replaced by provability in muMALL.


## 2. Cyclic Proofs

### 2.1 What They Are

A **cyclic proof** (also called circular proof) is a proof represented as a finite directed graph rather than a finite tree. Some leaves point back to ancestors, forming cycles. The cycle represents an implicit (co)inductive argument: "we can keep going forever, but we already know this works because we've seen this sequent before."

Formally, a **pre-proof** is any such graph. Not every pre-proof is valid -- you need a **global trace condition** (or **thread condition**) to ensure soundness.

### 2.2 The Global Trace Condition

For every **infinite path** through the proof graph (obtained by unrolling the cycles), there must exist a **progressing trace**: a sequence of formulas tracked along the path where some inductively-defined predicate decreases infinitely often. This ensures that the argument is well-founded despite the apparent circularity.

More precisely: a trace follows formulas through inference rules. A **progress point** occurs when a case-split decomposes an inductive definition. Soundness requires that every infinite path has at least one trace with infinitely many progress points.

### 2.3 Brotherston-Simpson Conjecture

Brotherston and Simpson (LICS 2007) introduced two proof systems for first-order logic with inductive definitions:
- **LKID**: explicit induction (Martin-Lof style induction rules)
- **CLKIDomega**: cyclic proofs with the global trace condition

They proved LKID embeds into CLKIDomega and conjectured the reverse (equivalence).

**The conjecture is FALSE in classical logic.** Berardi and Tatsuta (2017) found a counterexample: the **2-Hydra** statement. 2-Hydra describes a game on pairs of natural numbers with shrinking rules. The statement "all pairs eventually reach a winning state" is:
- Provable in CLKIDomega (cyclic proofs)
- NOT provable in LKID (explicit induction)

This means **cyclic proofs are strictly stronger than explicit induction** in the classical case. The cyclic system does not need to commit to an induction formula in advance -- it can discover it dynamically during proof construction.

**In the intuitionistic case**: Berardi and Tatsuta showed equivalence holds under arithmetic (2017), but the general case remains open.

### 2.4 Connection to muMALL

Baelde, Doumane, and Saurin developed **three proof systems** for muMALL:
- **muMALLind**: finitary proofs with explicit (co)induction rules
- **muMALLinfty**: non-wellfounded (infinitary) proofs
- **muMALLomega**: circular proofs with the global trace condition

They proved **cut elimination for all three** and showed relationships between them. Every finitary proof embeds into a circular proof. Circular proofs in muMALL have a thread validity condition analogous to Brotherston-Simpson.

### 2.5 Doumane's Results on Decidability

Doumane proved that the **validity condition for circular proofs in muMALL is PSPACE-complete**. The decision procedure reduces to the **emptiness problem for Buchi automata**. This is important for implementation: given a finite cyclic pre-proof, you can effectively check whether it constitutes a valid proof.

A **local validity condition** (Baelde et al., CSL 2018) was also developed, based on labeling formulas. This local criterion:
- Is strictly stronger than the global thread condition
- Contains all circular embeddings of finitary muMALL proofs
- Is checkable compositionally (important for programming language design)


## 3. Tabling and Its Relation to Coinduction/Fixed Points

### 3.1 XSB Prolog and SLG Resolution

**Tabling** (memoization of logic programming goals) is the key technique in XSB Prolog. SLG resolution extends SLD resolution with:
- A **table** storing computed answers for subgoals
- **Suspension** of variant calls (instead of infinite recursion)
- **Resumption** with answers from the table

The key properties tabling provides:
- **Termination** for programs with the bounded term-depth property
- **Optimal complexity** for Datalog-style queries
- **Well-founded semantics** for negation (via delay and simplification)

### 3.2 Tabling as Fixed-Point Computation

Tabling computes **least fixed points** bottom-up. Given a set of rules, tabling:
1. Starts with known facts (axioms)
2. Applies rules to derive new facts
3. Adds derived facts to the table
4. Repeats until no new facts are derivable (fixed point)

This is exactly Datalog-style bottom-up evaluation, and corresponds to computing the **least model** of the program.

### 3.3 Coinductive Logic Programming (co-LP)

Standard Prolog/tabling computes **least** fixed points. For **greatest** fixed points, you need **coinductive logic programming** (co-LP), introduced by Gupta et al.:

- **co-SLD resolution**: extends SLD with coinductive hypotheses. When a goal calls a variant of itself, instead of looping, it **succeeds** (the loop is evidence of a coinductive witness).
- **Semantics**: co-LP programs have greatest fixed point semantics rather than least fixed point.

The integration with tabling:
- A loop over an **inductive** predicate: tabling treats it as **failure** (no finite proof)
- A loop over a **coinductive** predicate: tabling treats it as **success** (coinductive witness)

This is exactly the proof-theoretic distinction: mu (induction) vs nu (coinduction).

### 3.4 Bedwyr: The Bridge

**Bedwyr** (Baelde, Miller, et al.) is a model checker that implements proof search in a logic with inductive and coinductive definitions. It uses **tabling** to handle loops:
- Loop on inductive predicate = failure (no infinite descent)
- Loop on coinductive predicate = success (coinductive witness found)

Bedwyr directly implements the proof search semantics of (a fragment of) muMALL, making the tabling/fixed-point connection concrete.


## 4. muMALL vs Exponentials: Encoding ! and ?

### 4.1 The Encodings

Baelde and Miller showed that exponentials can be encoded as fixed points:

```
!'A  :=  nu X. (A & (1 & (X tensor X)))
?'A  :=  mu X. (A oplus (bot oplus (X par X)))
```

Simplified (from the Proof Theory Blog presentation):
```
!'A  =  nu X. (1 & A & (X tensor X))
?'A  =  mu X. (bot oplus A oplus (X par X))
```

The intuition:
- **!'A** (bang): you can **use A** (dereliction via &A), you can **ignore it** (weakening via &1), and you can **duplicate it** (contraction via tensor X X). The nu means "you can do this forever" -- the resource is persistent.
- **?'A** (why-not): dual of bang. The mu captures the finite nature of consumption.

### 4.2 Deriving Exponential Rules

All standard exponential rules are derivable for these encodings:
- **Dereliction** (!A |- A): from the &A component
- **Weakening** (!A |- ): from the &1 component
- **Contraction** (!A |- !A tensor !A): from the tensor X X component + coinduction
- **Promotion** (under suitable conditions): requires coinduction (nu)

The crucial point: **contraction uses coinduction**. The ability to copy !A indefinitely is modeled by the greatest fixed point -- you can always unfold once more.

### 4.3 Forward Soundness, Not Faithfulness

**Proposition (Baelde)**: If muLL proves Gamma(!,?), then muMALL proves Gamma(!',?').

The encoding is **forward-sound**: anything provable with exponentials is provable with the fixed-point encoding.

**But the encoding is NOT faithful.** The fixed-point encodings are **canonical** (Knaster-Tarski extremality), while genuine exponentials are **not**:

- ?'A satisfies an induction principle: `?'A |- E_A(Y) |- Y` where E_A(Y) characterizes "Y is a ?-exponential of A"
- Genuine ?A does **not** satisfy this: `?A |- E_A(Y) |- Y` is NOT provable in LL

This means the fixed-point encodings are **strictly stronger** than exponentials. They prove more things. The exponentials ! and ? are "just one possible" fixed-point solution, while mu/nu give you the **extreme** (least/greatest) solutions.

### 4.4 Implications

1. **muMALL subsumes full linear logic** in terms of provability (forward direction)
2. **muMALL is strictly more expressive** -- it can state and prove extremal properties that LL with exponentials cannot
3. For **implementation**, this means: if you implement muMALL, you get exponential behavior "for free" via the encoding, plus additional power
4. **Open problem**: construct semantic countermodels showing the exact gap between !' and genuine !


## 5. muMALL and Session Types

### 5.1 The Propositions-as-Types Correspondence

Caires and Pfenning (CONCUR 2010) established that **intuitionistic linear logic propositions are session types**:
- Propositions = types of communication channels
- Proofs = concurrent processes
- Cut reduction = process computation (message passing)

This works for basic ILL. But to express **recursive protocols** (servers, streams, interactive loops), you need fixed points.

### 5.2 Fixed Points as Recursive Session Types

Adding mu and nu to the correspondence:

| Logic | Session Type | Example |
|-------|-------------|---------|
| mu X. (1 oplus X) | Finite counter: send zero or increment | Natural number protocol |
| nu X. (A tensor X) | Infinite stream: keep sending A values | Stream protocol |
| mu X. (A & (B oplus X)) | Finite interaction: respond to queries or terminate | Database query session |
| nu X. (A oplus (B & X)) | Infinite server: offer services forever | Server protocol |

**mu** (least fixed point) = **inductive/finite session types** -- the protocol must eventually terminate.
**nu** (greatest fixed point) = **coinductive/infinite session types** -- the protocol can run forever.

### 5.3 Circular Proofs as Processes (Derakhshan, Pfenning)

Derakhshan and Pfenning (LMCS 2022) established:
- Circular proofs in subsingleton logic with fixed points correspond to **mutually recursive session-typed processes**
- The **local validity condition** ensures **strong progress**: every configuration either terminates, takes a step, or attempts external communication within finitely many steps
- Process definitions can be checked **compositionally** -- each definition is validated against only the type signatures of other processes

The polarity of fixed points determines communication direction:
- **mu (positive)**: process sends an unfolding message rightward
- **nu (negative)**: process sends an unfolding message leftward

### 5.4 Non-Divergence and Productivity

Toninho and Pfenning studied **corecursion and non-divergence** in session-typed processes. The typing discipline prevents divergence (infinite unobservable reduction) while allowing productive infinite behavior (streams, servers).

This connects directly to the validity condition for circular proofs: a valid circular proof = a non-divergent recursive process.


## 6. Induction in/about Linear Logic: Two-Level Logic

### 6.1 The Problem

How do you **prove properties about** linear logic programs? You cannot use the object logic (the linear logic you're programming in) to state meta-theorems. You need a **meta-logic**.

### 6.2 Abella and the Two-Level Approach

**Abella** (Gacek, Miller, Nadathur) implements a **two-level logic**:

**Level 1 (Specification logic)**: Hereditary Harrop formulas (a fragment of intuitionistic logic). This is where you write your linear logic program as a specification. It supports lambda-tree syntax (higher-order abstract syntax with binders).

**Level 2 (Reasoning logic)**: An intuitionistic logic called G with:
- **Inductive definitions** (least fixed points) -- for structural induction over derivations
- **Coinductive definitions** (greatest fixed points) -- for bisimulation arguments
- The **nabla** quantifier -- for reasoning about fresh names/binders
- **Nominal constants** -- for generic reasoning about bound variables

The key insight: derivations in the specification logic are represented as **inductive definitions** in the reasoning logic. You prove properties about programs by doing induction over their derivation trees.

### 6.3 Bedwyr as Automated Fragment

**Bedwyr** is the automated fragment of this approach -- it does model checking (decidable properties) using tabling. Abella handles the full inductive/coinductive reasoning interactively.

The architecture:
```
Specification (hereditary Harrop / linear logic program)
    |
    v
Encoding as inductive definition in G
    |
    v
Proof by induction/coinduction in G (Abella, interactive)
   or
Model checking via tabling (Bedwyr, automated)
```

### 6.4 Connection to muMALL

The two-level approach is philosophically orthogonal but practically complementary to muMALL:
- **muMALL**: adds fixed points to the **object** logic (you reason within linear logic itself)
- **Two-level logic**: adds fixed points to a **meta** logic (you reason about linear logic from outside)

For CALC, both perspectives are relevant:
- muMALL-style fixed points could be added to the object calculus for recursive types
- Two-level reasoning could be used to prove meta-theorems about CALC programs


## 7. Can muMALL Subsume Ceptre Stages?

### 7.1 What Ceptre Stages Are

Ceptre (Martens, 2015) is a linear logic programming language with **stages**:
- A **stage** is a named collection of forward-chaining rules
- Rules fire until **quiescence**: no rule is applicable to the current state
- When a stage reaches quiescence, control transfers to the next stage
- Stages can be composed sequentially, and can be recursive

Stages give programmers the ability to **program with quiescence** -- expressing sequencing that pure linear logic forward chaining cannot.

### 7.2 What Stages Provide

1. **Phase separation**: different rule sets active at different times
2. **Quiescence detection**: "all rules of this phase have fired to completion"
3. **Sequential composition**: "do phase A, then phase B"
4. **Iteration**: "repeat phase A until some condition"

### 7.3 The Fixed-Point Encoding Argument

**Greatest fixed points (nu) can encode persistent resources** (via the bang encoding). This gives the "always available" aspect.

**Least fixed points (mu) can encode finite iteration.** A stage that runs to quiescence and then transitions is:
```
stage A then B  ~  mu X. (run_rules_A; if quiescent then B else X)
```

More precisely, the quiescence check is a **negation-as-failure** test: "no rule applies." In muMALL terms, this is related to the duality of mu/nu:
- A stage's rules firing = unfolding a least fixed point
- Quiescence = reaching the base case of the induction
- The stage transition = the next step after the base case

### 7.4 What Fixed Points Can and Cannot Replace

**CAN replace:**
- Sequential composition of stages (mu encoding of finite phases)
- Iterative stages (mu for bounded iteration, nu for unbounded)
- Phase-dependent behavior (different fixed-point bodies for different phases)

**CANNOT directly replace (without additional machinery):**
- **Quiescence detection as a primitive**: In pure muMALL, you cannot test "no rule is applicable." This requires negation-as-failure or a closed-world assumption, which is **outside** muMALL's proof theory. Ceptre's stages hard-code quiescence detection at the meta-level.
- **Dynamic rule activation**: Stages select which rules are active. In muMALL, all rules are always available. You would need to encode rule activation as state predicates (a `phase` token that guards each rule), which is the standard encoding but adds overhead and loses the clean separation.

### 7.5 The Standard Encoding

The well-known encoding of stages in linear logic (used by CLF/Celf):
```
phase_A -o (rule1 & rule2 & ... & done)
done -o phase_B
```

With fixed points, this becomes cleaner:
```
run_A = mu X. (apply_some_rule_A tensor X) oplus transition_to_B
```

The `oplus` gives internal choice: either apply another rule (continue the stage) or transition. The `mu` ensures this terminates (finite phase). For infinite servers, use `nu` instead.

### 7.6 Assessment

muMALL fixed points **partially subsume** Ceptre stages:
- The **sequential composition** and **iteration** aspects are cleanly captured
- The **quiescence detection** aspect requires an encoding (phase tokens + guards) that works pragmatically but is not as clean as Ceptre's built-in mechanism
- For CALC specifically: the existing forward engine already has a main loop with quiescence detection built in. Adding mu/nu would give recursive types and infinite behavior, but the staging mechanism would likely remain at the meta-level (engine control flow) rather than the object level (logic)


## 8. Expressiveness Comparison: What Subsumes What

```
Pure MALL    <  muMALL  >=  Full LL (via exponential encoding)
                  |
                  |-- subsumes Horn clause LP (level 1)
                  |-- subsumes model checking / mu-calculus (level 2)
                  |-- encodes Peano arithmetic fragments (level 3)
                  |
                  v
          muLL = muMALL + genuine exponentials
          (strictly stronger due to non-canonical exponentials)
```

### Key Subsumption Results

| System A | System B | Relationship |
|----------|----------|-------------|
| muMALL | Full LL | muMALL proves everything LL proves (forward sound), but is strictly stronger |
| muMALL | Horn LP | Horn LP = level-1 fragment of muMALL |
| muMALL | mu-calculus model checking | Captured at level 2 |
| Cyclic proofs | Explicit induction | Cyclic strictly stronger (classically); equivalent under arithmetic (intuitionistically) |
| muMALL circular | muMALL finitary | Circular subsumes finitary |
| Tabling (XSB) | Least fixed points | Tabling computes LFPs; co-LP computes GFPs |
| muMALL | Ceptre stages | Partial: captures recursion/iteration but not quiescence-as-primitive |
| muMALL + session types | Recursive session types | Full correspondence via Curry-Howard |

### Implementation Feasibility for CALC

Adding mu/nu to CALC would involve:
1. **Syntax**: two new connectives (mu, nu) with monotone bodies -- fits the existing connective framework
2. **Focusing**: mu is positive (like tensor/oplus), nu is negative (like with/loli) -- fits existing polarity system
3. **Forward engine**: inductive types (mu) = finite iteration (already handled); coinductive types (nu) = potentially infinite behavior (needs productivity checking or depth bounds)
4. **Proof search**: the focused proof system tells you exactly when to unfold vs. apply (co)induction -- compatible with CALC's Andreoli focusing
5. **Cyclic proofs**: would require extending the proof tree representation to allow back-edges, plus a validity checker (PSPACE for the thread condition, linear for the local condition)
6. **Tabling**: the forward engine already does memoization via FactSet. Tabling for backward chaining (prove.js) would be the natural extension


## References

- Baelde, Miller. "Least and Greatest Fixed Points in Linear Logic." LPAR 2007, TOCL 2012.
- Baelde, Doumane, Saurin. "Infinitary Proof Theory: the Multiplicative Additive Case." CSL 2016.
- Baelde, Doumane, Saurin. "Local Validity for Circular Proofs in Linear Logic with Fixed Points." CSL 2018.
- Brotherston, Simpson. "Complete Sequent Calculi for Induction and Infinite Descent." LICS 2007.
- Berardi, Tatsuta. "Classical System of Martin-Lof's Inductive Definitions Is Not Equivalent to Cyclic Proof System." FoSSaCS 2017.
- Derakhshan, Pfenning. "Circular Proofs as Session-Typed Processes: A Local Validity Condition." LMCS 2022.
- Manighetti, Miller. "Computational Logic Based on Linear Logic and Fixed Points." 2022.
- Baelde, Miller, Snow. "Focused Inductive Theorem Proving." IJCAR 2010.
- Caires, Pfenning. "Session Types as Intuitionistic Linear Propositions." CONCUR 2010.
- Martens. "Ceptre: A Language for Modeling Generative Interactive Systems." AIIDE 2015.
- Gupta et al. "Coinductive Logic Programming." ICLP 2007.
- Gacek, Miller, Nadathur. "The Abella Interactive Theorem Prover." IJCAR 2008.
- "Exponentials vs Fixed Points in Linear Logic." Proof Theory Blog, 2024.

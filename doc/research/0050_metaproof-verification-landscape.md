---
title: "Metaproof & Verification Landscape for Linear Logic Forward Chaining"
created: 2026-02-23
modified: 2026-02-23
summary: "Comprehensive survey of techniques for state property verification and metaproofs over linear logic execution trees"
tags: [metaproofs, verification, Petri-nets, model-checking, invariants, CEGAR, CHR, session-types]
category: "Related Paradigms"
---

# Metaproof & Verification Landscape

Survey of eight verification paradigms applicable to a linear logic forward-chaining system with exhaustive execution trees, content-addressed hashing, persistent/linear facts, and additive branching.

---

## 1. Petri Net Invariant Checking / Place Invariants

### The Correspondence

Linear logic formulas map to Petri net markings: each linear fact is a token in a place, each forward rule is a transition. This was established by three foundational works:

- **Girard** showed provability in propositional linear logic directly encodes Petri net reachability.
- **Engberg & Winskel (1990)** — "Petri Nets as Models of Linear Logic", CAAP'90, LNCS 431, pp. 147-161. They gave a systematic correspondence between individual Petri nets, linear logic theories, and linear categories (commutative quantales). They showed individual Petri nets form models of intuitionistic linear logic and explored completeness.
- **Kanovich (1995)** — "Petri Nets, Horn Programs, Linear Logic, and Vector Games", Annals of Pure and Applied Logic 75(1-2), pp. 107-135. Proved the !-Horn fragment of MELL is equivalent to Petri net reachability. Horn programming in linear logic is NP-complete. Any non-deterministic concurrent computation can be simulated within each of these formalisms.

### P-Invariants and T-Invariants

Given a Petri net with incidence matrix **C** (rows = places, columns = transitions):

- **P-invariant**: nontrivial integer vector **y** such that **y** . **C** = **0**. Meaning: the weighted sum of tokens across places in the support of **y** is constant for all reachable markings. This is the Petri net analog of a *conservation law*.
- **T-invariant**: nontrivial integer vector **x** such that **C** . **x** = **0**. Meaning: the firing sequence represented by **x** returns the net to its original marking. Identifies cyclic behavior / functional modules.

### Computation

P-invariants are computed by solving the homogeneous system **y** . **C** = **0** over the integers. The standard algorithm is due to **Farkas/Martinez-Silva** (an adaptation of Fourier-Motzkin elimination for non-negative integer solutions). Minimal-support P-invariants enumerate all "independent" conservation laws. Complexity: polynomial in the size of the net for finding one invariant; exponential in the worst case for enumerating all minimal invariants.

Key references:
- **Martinez & Silva (1982)** — "A Simple and Fast Algorithm to Obtain All Invariants of a Generalised Petri Net", European Workshop on Applications and Theory of Petri Nets.
- **Colom & Silva (1991)** — Decomposition-based P-invariant computation.
- **Desel (1998)** — "Basic Linear Algebraic Techniques for Place/Transition Nets" — tutorial on the incidence matrix approach.

### Application to CALC

CALC's forward rules are transitions. Linear facts are tokens. The incidence matrix is derivable from rule descriptors (each descriptor specifies consumed and produced formulas). For a rule consuming `{A, B}` and producing `{C}`:
- Column entry for A: -1, B: -1, C: +1.

**Persistent facts (banged)** correspond to *read arcs* (test arcs) in Petri nets — they enable a transition without being consumed. P-invariants over the linear fragment automatically yield conservation laws. The oplus (disjunction) branching creates a *free-choice* Petri net structure where different branches correspond to different conflict sets.

**Concrete opportunity**: Build the incidence matrix from `calc.forwardRules` descriptors, solve the linear system, and automatically discover all conservation laws without user annotation.

---

## 2. Model Checking over Multiset Rewriting Systems

### MSR Formalism (Cervesato & Scedrov)

- **Cervesato, Durgin, Lincoln, Mitchell, Scedrov (1999)** — "A Meta-Notation for Protocol Analysis", CSFW'99. Defined MSR (Multiset Rewriting with existentials) based on the first-order Horn fragment of linear logic with existential quantification. Used to formalize the Dolev-Yao model of security protocols.
- **Cervesato & Scedrov (2009)** — "Relating State-Based and Process-Based Concurrency through Linear Logic", Information and Computation 207(10). Extended MSR language omega, showing process-algebraic and state-based views unify through linear logic.

### Decidability Results

- **Durgin, Lincoln, Mitchell, Scedrov (2004)** — "Multiset Rewriting and the Complexity of Bounded Security Protocols", Journal of Computer Security 12(2), pp. 247-311.
  - **Unbounded roles + unbounded nonces**: secrecy is **undecidable** (even with bounded message size/encryption depth).
  - **Bounded nonces, unbounded roles**: **DEXPTIME-complete**.
  - **Bounded nonces + bounded roles**: **NP-complete**.

### WSTS Framework

- **Finkel & Schnoebelen (2001)** — "Well-Structured Transition Systems Everywhere!", TCS 256, pp. 63-92. Showed that systems with a well-quasi-ordering (WQO) on states compatible with transitions have decidable coverability, termination, and boundedness. Petri nets are the canonical example. Two algorithmic families: backward set-saturation (computing upward-closed predecessors) and forward tree-saturation (Karp-Miller trees).

### Petri Net Reachability Complexity

- **Mayr (1981)** — decidability of Petri net reachability (STOC'81).
- **Czerwinski, Lasota, Lazic, Leroux, Mazowiecki (2019)** — "The Reachability Problem for Petri Nets is Not Elementary", STOC'19, JACM 2021. Proved a non-elementary lower bound (tower of exponentials). Best upper bound: Ackermannian (Leroux & Schmitz, LICS'19).
- **Coverability** remains EXPSPACE-complete (Rackoff 1978) — much more tractable.

### Application to CALC

CALC's state space (multisets of content-addressed hashes) forms a WSTS under multiset inclusion ordering. This immediately gives:
- **Coverability** is decidable: "can a state containing formula X ever be reached?" — EXPSPACE.
- **Boundedness** is decidable: "is the number of tokens bounded across all reachable states?"
- **Reachability** is decidable but non-elementary: "can exact state S be reached?"

For practical verification, coverability (safety properties) is the right target — checking "can the system reach a state with property P?" is cheaper than exact reachability.

---

## 3. CLF/Celf Metaproofs and Twelf Totality

### CLF and Celf

- **Watkins, Cervesato, Pfenning, Walker (2002)** — defined CLF (Concurrent LF), extending LF with linear types and a monad for concurrency.
- **Schack-Nielsen & Schürmann (2008)** — "Celf — A Logical Framework for Deductive and Concurrent Systems", IJCAR'08, LNCS 5195. Celf implements CLF with two search modes: backward goal-directed for asynchronous types, and forward committed-choice multiset rewriting for synchronous types.

**Current limitation**: Celf lacks Twelf's metatheoretic capabilities (mode checking, termination checking, coverage checking). These were left to future work and remain unimplemented.

### Twelf's Approach to Totality

- **Pfenning & Schürmann (1999)** — "System Description: Twelf — A Meta-Logical Framework for Deductive Systems", CADE'99.
- **Schürmann & Pfenning (2003)** — "A Coverage Checking Algorithm for LF", TPHOLs'03. Verifies that a relation covers all possible inputs.

Twelf proves metatheorems via three checks:
1. **Mode checking** — verifies input/output modes of relations (which arguments are given, which are produced).
2. **Coverage checking** — ensures every possible input pattern has a matching case.
3. **Totality checking** (via `%total`) — combines mode + coverage + termination to prove a relation is total (a function).

The methodology: encode your object logic as an LF signature, state metatheorems as totality assertions over relations, let Twelf mechanically verify them.

### Application to CALC

Twelf's totality-checking methodology suggests an approach: encode CALC rules as an LF signature, express properties (conservation, progress) as relations, and check totality. However, Twelf handles intuitionistic logic natively — encoding linear logic requires additional machinery (the LLF extension, or CLF). Since Celf lacks metatheoretic checking, the practical path would be:

- **Short term**: Implement CALC-specific versions of coverage and mode checking for forward rules (ensure every rule descriptor is well-formed, every premise is satisfiable).
- **Long term**: When/if Celf gains metatheoretic checking, export CALC programs to CLF for verified metaproofs.

---

## 4. Ceptre's Approach to Property Checking

### Ceptre Language

- **Martens (2015)** — "Ceptre: A Language for Modeling Generative Interactive Systems", AIIDE'15.
- **Martens (2015)** — PhD Thesis: "Programming Interactive Worlds with Linear Logic", CMU-CS-15-132.

Ceptre is a forward-chaining linear logic programming language for games and interactive narratives. It uses stages (phases with quiescence-based termination) and supports both interactive and generative modes.

### Invariant Checking (Thesis Chapter 6)

Martens defines two kinds of invariants over linear logic program states:

1. **Consumptive invariants**: properties about what is *absent* from a state after a rule fires. If a rule consumes resource A, a consumptive invariant asserts A will not persist improperly.

2. **Generative invariants**: properties about what is *present* after a rule fires. If a rule produces resource B, a generative invariant asserts B appears with correct multiplicity.

The key result: **decidability of invariant checking for the propositional fragment**. For ground (propositional) linear logic programs, checking whether an invariant holds across all reachable states is decidable, because the state space (multisets over a finite set of propositions) under the forward rules forms a WSTS (connecting back to Finkel-Schnoebelen).

### Practical Mechanisms

Ceptre does NOT have a built-in invariant checker in the implementation. The thesis provides the theoretical framework and decidability proofs, but the actual Ceptre tool focuses on execution and exploration. Property checking is done by:
- Exhaustive exploration of all traces (when finite).
- Manual inspection of generated traces.
- The theoretical framework for automation exists but is unimplemented.

### Application to CALC

CALC's symexec already provides exhaustive exploration. Ceptre's invariant framework maps directly:
- Consumptive invariants = "no rule creates token X from nothing" (like Petri net P-invariants).
- Generative invariants = "rule R always produces token Y when it fires".
- The propositional decidability result applies when CALC programs use ground (no metavariable) rules — which covers many practical programs like EVM execution.

---

## 5. CHR Program Analysis

### Key Researchers

- **Frühwirth** — creator of CHR, author of the definitive book.
- **Abdennadher** — confluence and operational equivalence.
- **Sneyers, Schrijvers, De Koninck** — survey and complexity results.

### Confluence Checking

- **Abdennadher, Frühwirth, Meuss (1999)** — "Confluence and Semantics of Constraint Simplification Rules", Constraints 4(2). Gave a sufficient and necessary condition for confluence of terminating CHR programs based on *critical pair analysis* (adapted from term rewriting theory). A terminating CHR program is confluent iff all critical pairs are joinable.
- **Abdennadher & Frühwirth (1998)** — "On Completion of Constraint Handling Rules", CP'98. Showed how to transform non-confluent programs into confluent ones by adding rules (completion procedure, analogous to Knuth-Bendix completion for term rewriting).
- **Duck, Stuckey, Sulzmann (2007)** — "Observable Confluence for Constraint Handling Rules", ICLP'07. Confluence checker based on the refined operational semantics.

**Algorithm**: Enumerate all pairs of rules that could fire on overlapping multisets. For each overlap (critical pair), check whether the two results can be joined by further rule applications. If all critical pairs are joinable, the program is confluent.

### Termination Analysis

- **Frühwirth (2000)** — proved termination by ranking functions over constraint stores.
- **Sneyers, Schrijvers, De Koninck (2008)** — Abstract CHR machines that decouple counting rule applications from finding ranking functions.

### Operational Equivalence

- **Abdennadher & Frühwirth (1999)** — "Operational Equivalence of CHR Programs and Constraints". Gave a decidable, sufficient and necessary syntactic condition for operational equivalence of well-behaved (confluent and terminating) CHR programs. For programs sharing only one user-defined constraint, the condition is both sufficient and necessary.

### Survey

- **Sneyers, Van Weert, Schrijvers, De Koninck (2010)** — "As Time Goes By: Constraint Handling Rules — A Survey of CHR Research from 1998 to 2007", TPLP 10(1). Covers 180+ publications. Includes complexity-wise completeness: any algorithm can be efficiently encoded in CHR.

### Monograph

- **Frühwirth (2009)** — *Constraint Handling Rules*, Cambridge University Press. Part II: formal semantics, confluence, termination, operational equivalence, complexity. Part III: applications.

### Application to CALC

CHR's critical pair analysis maps directly to CALC's forward rules. Two CALC rules are in a critical pair when they match overlapping subsets of the linear context. Confluence checking for CALC would:
1. Enumerate rule pairs with overlapping linear patterns.
2. For each overlap, check if applying rule A then rule B yields the same state as B then A.
3. If all pairs joinable: program is confluent (rule order doesn't matter).

This is precisely what CALC's symexec already explores — it builds all orderings. A confluence checker could be a *post-analysis* on the execution tree: if all branches reaching the same multiset of consumed/produced facts lead to identical leaf states, the program is confluent.

**Termination**: CALC's ground programs (no metavariable recursion) over finite initial states always terminate (finite multiset strictly decreasing under each linear consumption). Programs with banged rules that generate new facts need explicit ranking functions.

---

## 6. Bedwyr and Model Checking in Linear Logic

### The System

- **Baelde, Gacek, Miller, Nadathur, Tiu (2007)** — "The Bedwyr System for Model Checking over Syntactic Expressions", CADE'07, LNCS 4603. Bedwyr is an OCaml implementation that generalizes logic programming to model checking over syntactic expressions with binders.

### Underlying Logic: LINC / muMALL

- **LINC** — extension of intuitionistic logic with definitions (fixed points) and the nabla quantifier (for fresh names). Bedwyr implements proof search in LINC.
- **muMALL** — Baelde & Miller (2007/2012): "Least and Greatest Fixed Points in Linear Logic", LPAR'07 (LNCS 4790), expanded in ACM TOCL 13(1), 2012. Extends MALL with least (mu) and greatest (nu) fixed point operators. Key properties: weak normalization, complete focused proof system.

### How Bedwyr Checks Properties

1. **Finite success** = reachability (exists a derivation).
2. **Finite failure** = safety (no derivation exists = property always holds).
3. **Tabling** — memoization to avoid redundant computation and detect loops. Loops over inductive predicates → failure; loops over coinductive predicates → success.
4. **Nabla quantifier** — handles fresh name generation (critical for process calculi, security protocols).

### Related: Abella

- **Gacek, Miller, Nadathur (2012)** — "A Two-Level Logic Approach to Reasoning About Computations", Journal of Automated Reasoning 49(2), pp. 241-273. Abella is a proof assistant using the two-level approach: specifications in lambda-Prolog, reasoning in an intuitionistic logic with induction/coinduction. Not linear, but demonstrates the two-level methodology.

### Application to CALC

muMALL's fixed points provide exactly the connectives needed for expressing invariants over execution trees:
- **mu X. P(X)** = least fixed point = inductively defined set of states (reachable states).
- **nu X. P(X)** = greatest fixed point = coinductively defined property (holds forever along all paths).

For CALC, the focusing discipline of muMALL aligns with existing Andreoli focusing in L3. Adding mu/nu to CALC's formula language would enable:
- Safety: `nu X. (safe(state) & after-step(X))` — "safe at every reachable state".
- Liveness: `mu X. (goal(state) | after-step(X))` — "goal eventually reached".

Bedwyr's tabling strategy is directly applicable: during symexec tree exploration, memoize states; loops detected by content-addressed hash equality → finite failure (inductive) or success (coinductive).

---

## 7. Linear Logic and Resource Invariants

### Nomos: Session-Type Resource Tracking

- **Das, Balzer, Hoffmann, Pfenning (2021)** — "Resource-Aware Session Types for Digital Contracts", CSF'21 (arXiv: 1902.06056, 2019). Nomos is a language for digital contracts with three pillars:
  1. **Shared binary session types** rooted in linear logic — express communication protocols.
  2. **Resource-aware session types** with automatic amortized resource analysis — infer resource bounds.
  3. **Linear type system** — prevent asset duplication or deletion.

- **Das (2021)** — PhD Thesis: "Resource-Aware Session Types for Digital Contracts", CMU-CS-21-112.

### Key Concepts

- **Equi-synchronizing session types**: impose invariant that a process is released back to the same type at which it was acquired. Prevents resource leaks across shared-to-linear transitions.
- **Potential annotations**: types carry numeric "potential" representing available resources. Type checking ensures potential is conserved across communication steps — a *type-level conservation law*.
- **Linear-time type checking**: NomosPro implementation checks resource conservation in linear time.

### Other Resource-Tracking Formalisms

- **Rust ownership system** — affine types (at most once use) enforced by the borrow checker. Not full linear logic but demonstrates practical resource tracking.
- **Linear Haskell** (Bernardy et al., 2018) — "Retrofitting Linear Types", adds linear arrows to Haskell's type system.
- **Substructural type systems** generally (Walker, 2005) — systematic study of type systems dropping weakening/contraction.

### Application to CALC

Nomos's approach suggests a **type-level** verification strategy for CALC:
- Annotate each predicate/formula with a resource weight.
- Type-check each forward rule: sum of input weights = sum of output weights.
- This is precisely the P-invariant computation from Section 1, expressed as a type system rather than linear algebra.

The session-type aspect maps to CALC's loli continuations: a loli `A -o B` is a channel offering to consume A and produce B. Nomos's equi-synchronizing invariant corresponds to ensuring loli contracts maintain resource balance.

**Concrete DSL idea**: Express resource weights as annotations on predicates, let the checker verify conservation automatically:
```
@weight(token, 1)
@weight(transferred, 1)
@invariant sum(token) + sum(transferred) = CONST
```

---

## 8. CEGAR for Linear Logic Execution Trees

### Classic CEGAR

- **Clarke, Grumberg, Jha, Lu, Veith (2003)** — "Counterexample-Guided Abstraction Refinement for Symbolic Model Checking", JACM 50(5). The CEGAR loop: (1) abstract system, (2) model-check abstract system, (3) if counterexample found, check if it's real, (4) if spurious, refine abstraction, repeat.

### CEGAR for Petri Nets / Graph Transformation

- **König & Kozioura (2006)** — "Counterexample-Guided Abstraction Refinement for the Analysis of Graph Transformation Systems", TACAS'06, LNCS 3920. Over-approximate graph transformation systems by Petri nets. Spurious counterexamples arise from merging graph nodes. Refinement: identify merged nodes, split them. Implemented in the **Augur** tool.

- **Blondin, Finkel, Haase (2017)** — "Approaching the Coverability Problem Continuously". Use continuous Petri nets as over-approximations of discrete nets for coverability.

- **Klüppelholz & Baier (2021)** — "Abstraction-Based Incremental Inductive Coverability for Petri Nets". Integrates IC3 with place-merge abstraction: reduce dimensionality by merging places, refine when counterexample is spurious.

### Abstractions for Multiset States

For a system with multiset states (like CALC), natural abstractions include:

1. **Predicate abstraction**: Track boolean predicates over token counts (e.g., "count(A) > 0", "count(A) = count(B)") rather than exact counts.
2. **Place merging**: Collapse multiple formula types into equivalence classes. Merge `token(alice, 5)` and `token(bob, 3)` into `token(*, *)`. Refine when the merge causes a spurious counterexample.
3. **Interval abstraction**: Track token counts as intervals [lo, hi] rather than exact values.
4. **Symmetry reduction**: CALC's content-addressed hashing already canonicalizes formulas. Extend to canonicalize *states* up to symmetry of identical-typed facts.
5. **Counting abstraction**: For parameterized systems, track counts of each fact type rather than individual identities.

### Application to CALC

CALC's execution tree provides the concrete system; CEGAR provides a way to verify properties without exploring the full tree:

1. **Abstract**: Collapse the multiset state space (e.g., merge all `token(addr, amount)` into a single `token_count`).
2. **Model-check**: Check the property (e.g., conservation) on the abstract Petri net — this is a simple linear algebra check on the abstract incidence matrix.
3. **Counterexample check**: If the abstract system violates the property, simulate the counterexample trace on the concrete CALC system.
4. **Refine**: If the trace is spurious (doesn't actually happen in CALC), split the abstracted places.

The content-addressed hash gives a natural refinement lattice: start with tag-level abstraction (all `token` facts are one place), refine to hash-level (each distinct `token(x,y)` is a separate place).

---

## Synthesis: Applicability to CALC

| Technique | Difficulty | Payoff | Prerequisites |
|-----------|-----------|--------|---------------|
| P-invariant computation | Low | High | Incidence matrix from rule descriptors |
| Coverability (WSTS) | Medium | High | Backward reachability algorithm |
| CHR confluence check | Medium | High | Critical pair enumeration on rules |
| Ceptre-style invariant DSL | Medium | Medium | State property language (TODO_0029) |
| Bedwyr-style tabling | Low | Medium | Hash-based memoization in symexec |
| CEGAR abstraction | High | Very High | Abstract domain design, refinement loop |
| Nomos-style resource types | Medium | Medium | Type annotation layer on predicates |
| CLF/Twelf metaproofs | Very High | Very High | Export to external logical framework |

### Recommended Implementation Order

1. **P-invariant discovery** (Section 1) — Purely algebraic, can be computed statically from rule descriptors without any execution. Build incidence matrix from `calc.forwardRules`, solve **y . C = 0**, report all conservation laws.

2. **Confluence checking** (Section 5) — Enumerate critical pairs between forward rules. For rules with overlapping linear patterns, check joinability. Can be integrated with existing symexec by comparing branch-pair outcomes.

3. **Invariant DSL + checker** (Sections 4, 7) — Design a property language inspired by Martens (consumptive/generative invariants) and Nomos (weighted resource sums). Verify by checking initial + preservation on each rule.

4. **Tabling/memoization** (Section 6) — Enhance symexec with state memoization using content-addressed hashes. Detects cycles, prunes redundant exploration. Low implementation cost, high practical benefit.

5. **Coverability queries** (Section 2) — Implement backward reachability analysis. Given target state property, compute minimal predecessor sets. Decidable for ground programs (EXPSPACE, but practical for small state spaces).

6. **CEGAR loop** (Section 8) — Most ambitious. Requires abstract domain design, counterexample validation, refinement. Enables verification of large/infinite state spaces without full exploration.

---

## Full Bibliography

### Petri Nets and Linear Logic
- Engberg, U. & Winskel, G. (1990). "Petri Nets as Models of Linear Logic". CAAP'90, LNCS 431, pp. 147-161.
- Kanovich, M.I. (1995). "Petri Nets, Horn Programs, Linear Logic, and Vector Games". Annals of Pure and Applied Logic 75(1-2), pp. 107-135.
- Martinez, J. & Silva, M. (1982). "A Simple and Fast Algorithm to Obtain All Invariants of a Generalised Petri Net". European Workshop on Petri Nets.
- Desel, J. (1998). "Basic Linear Algebraic Techniques for Place/Transition Nets". Lectures on Petri Nets I, LNCS 1491.

### Multiset Rewriting and Decidability
- Cervesato, I., Durgin, N., Lincoln, P., Mitchell, J., Scedrov, A. (1999). "A Meta-Notation for Protocol Analysis". CSFW'99.
- Durgin, N., Lincoln, P., Mitchell, J., Scedrov, A. (2004). "Multiset Rewriting and the Complexity of Bounded Security Protocols". JCS 12(2), pp. 247-311.
- Cervesato, I. & Scedrov, A. (2009). "Relating State-Based and Process-Based Concurrency through Linear Logic". Inf. Comput. 207(10).
- Finkel, A. & Schnoebelen, P. (2001). "Well-Structured Transition Systems Everywhere!". TCS 256, pp. 63-92.
- Czerwinski, W., Lasota, S., Lazic, R., Leroux, J., Mazowiecki, F. (2019). "The Reachability Problem for Petri Nets Is Not Elementary". STOC'19 / JACM 2021.

### CLF, Celf, and Twelf
- Watkins, K., Cervesato, I., Pfenning, F., Walker, D. (2002). "A Concurrent Logical Framework I". CMU-CS-02-101.
- Schack-Nielsen, A. & Schürmann, C. (2008). "Celf — A Logical Framework for Deductive and Concurrent Systems". IJCAR'08, LNCS 5195.
- Pfenning, F. & Schürmann, C. (1999). "System Description: Twelf — A Meta-Logical Framework". CADE'99.
- Schürmann, C. & Pfenning, F. (2003). "A Coverage Checking Algorithm for LF". TPHOLs'03.

### Ceptre and Linear Logic Programming
- Martens, C. (2015). "Ceptre: A Language for Modeling Generative Interactive Systems". AIIDE'15.
- Martens, C. (2015). "Programming Interactive Worlds with Linear Logic". PhD Thesis, CMU-CS-15-132.

### CHR Analysis
- Abdennadher, S., Frühwirth, T., Meuss, H. (1999). "Confluence and Semantics of Constraint Simplification Rules". Constraints 4(2).
- Abdennadher, S. & Frühwirth, T. (1998). "On Completion of Constraint Handling Rules". CP'98.
- Abdennadher, S. & Frühwirth, T. (1999). "Operational Equivalence of CHR Programs and Constraints". Tech Report.
- Sneyers, J., Van Weert, P., Schrijvers, T., De Koninck, L. (2010). "As Time Goes By: CHR". TPLP 10(1).
- Frühwirth, T. (2009). *Constraint Handling Rules*. Cambridge University Press.

### Bedwyr and Fixed Points
- Baelde, D., Gacek, A., Miller, D., Nadathur, G., Tiu, A. (2007). "The Bedwyr System for Model Checking over Syntactic Expressions". CADE'07, LNCS 4603.
- Baelde, D. & Miller, D. (2007/2012). "Least and Greatest Fixed Points in Linear Logic". LPAR'07 / ACM TOCL 13(1), 2012.
- Gacek, A., Miller, D., Nadathur, G. (2012). "A Two-Level Logic Approach to Reasoning About Computations". JAR 49(2), pp. 241-273.

### Resource Types and Session Types
- Das, A., Balzer, S., Hoffmann, J., Pfenning, F. (2021). "Resource-Aware Session Types for Digital Contracts". CSF'21.
- Das, A. (2021). "Resource-Aware Session Types for Digital Contracts". PhD Thesis, CMU-CS-21-112.

### CEGAR
- Clarke, E., Grumberg, O., Jha, S., Lu, Y., Veith, H. (2003). "Counterexample-Guided Abstraction Refinement for Symbolic Model Checking". JACM 50(5).
- König, B. & Kozioura, V. (2006). "Counterexample-Guided Abstraction Refinement for the Analysis of Graph Transformation Systems". TACAS'06, LNCS 3920.

---
title: "muMALL: Linear Logic with Least and Greatest Fixed Points"
created: 2026-02-12
modified: 2026-02-12
summary: Comprehensive survey of muMALL -- proof theory, cyclic proofs, implementations, session types, and applications to CALC
tags: [research, muMALL, fixed-points, induction, coinduction, cyclic-proofs, session-types, focusing]
status: active
---

# muMALL: Linear Logic with Least and Greatest Fixed Points

---

## 1. What is muMALL?

**muMALL** extends MALL (multiplicative additive linear logic) with least fixed point (mu) and greatest fixed point (nu) operators. Introduced by **David Baelde and Dale Miller** (LPAR 2007), fully developed in Baelde's TOCL 2012 paper.

**Core idea:** MALL cannot capture unbounded behavior. Rather than adding exponentials (!, ?) to handle infinity, muMALL adds fixed point operators. This isolates two independent sources of infinity in linear logic: exponentials and fixed points.

### Formulas

```
A, B ::= X | a | A^bot         -- atoms, variables, negation
       | A tensor B | 1         -- multiplicative conjunction, unit
       | A par B    | bot       -- multiplicative disjunction, unit
       | A oplus B  | 0         -- additive disjunction, false
       | A & B      | top       -- additive conjunction, true
       | mu X. B(X)             -- least fixed point (inductive)
       | nu X. B(X)             -- greatest fixed point (coinductive)
```

Negation distributes: `(mu X. B(X))^bot = nu X. B^bot(X)` -- mu and nu are De Morgan duals.

### Key People

- **David Baelde** (ENS Paris-Saclay) -- primary developer, thesis, TOCL 2012
- **Dale Miller** (Inria / LIX) -- co-author, Abella/Bedwyr architect
- **Amina Doumane** (IRIF Paris) -- circular proofs thesis (2017), Gilles Kahn prize
- **Alexis Saurin** (IRIF Paris) -- infinitary proofs, phase semantics
- **Anupam Das** (Birmingham) -- decision problems, cyclic proof complexity
- **Abhishek De** (IRIF Paris) -- decision problems, phase semantics
- **Farzad Jafarrahmani** (Paris Cite) -- categorical models, muLLP thesis (2023)
- **Frank Pfenning** (CMU) -- circular proofs as session types
- **Farzaneh Derakhshan** (CMU) -- circular proofs as session types

---

## 2. Proof Theory

### 2.1 Proof Rules

muMALL is typically presented with one-sided sequents `|- Gamma`. Rules for fixed points:

**Unfolding (derivable from induction/coinduction):**
```
    |- Gamma, B(mu X. B)             |- Gamma, B(nu X. B)
    --------------------  muR        --------------------  nuR
     |- Gamma, mu X. B                |- Gamma, nu X. B
```

**Induction (mu on the left):**
```
    |- Gamma, B(S)    |- S^bot, mu X.B
    ------------------------------------  muL (Induction)
            |- Gamma, (mu X.B)^bot
```

S is the **invariant** -- any closed formula, NOT necessarily a subformula. This is the deep challenge: the subformula property fails.

**Coinduction (nu on the right):**
```
    |- Gamma, B(S)    |- S, (nu X.B)^bot
    ------------------------------------  nuR (Coinduction)
            |- Gamma, nu X.B
```

S is the **coinvariant**.

### 2.2 Focusing and Polarity

In Andreoli-style focusing:
- **mu is positive** (synchronous): decomposed eagerly on the right, requires invariant on the left
- **nu is negative** (asynchronous): decomposed eagerly on the left, requires coinvariant on the right

This extends ILL's focusing discipline:
- Positive (tensor, oplus, 1, 0, **mu**): invertible on left, focusable on right
- Negative (par, &, bot, top, **nu**): invertible on right, focusable on left

**Baelde's completeness theorem:** The focused system for muMALL is complete w.r.t. the unfocused system.

### 2.3 Cut Elimination

**Theorem (Baelde 2012):** muMALL satisfies weak normalization -- every proof can be transformed into a cut-free proof.

Proved via Girard's **candidates of reducibility** method. The key difficulty: invariants are not subformulas, so the standard subformula-based measure fails. Instead, reducibility candidates are indexed by formulas.

**Consequence:** muMALL is consistent.

### 2.4 The Invariant Problem

The induction/coinduction rules require **guessing** an invariant S that can be any formula. This makes:
1. Proof search undecidable in general
2. Subformula property fails for cut-free proofs
3. Automation requires heuristics or alternative proof systems (cyclic proofs)

This is the central motivation for cyclic proof systems (Section 5).

---

## 3. Encoding Exponentials as Fixed Points

One of Baelde & Miller's key insights: exponentials are **encodable** as fixed points.

### The Encodings

```
!A  =  nu X. A & X        (coinductive: "always available")
?A  =  mu X. A oplus X    (inductive: "finitely demanded")
```

Intuition:
- `!A`: "I can use A as many times as I want" -- a stream that always offers A
- `?A`: "A may be needed finitely many times" -- either use A now or stop

### Deriving Exponential Rules

All standard rules for ! and ? are derivable:
- **Dereliction** (`!A |- A`): unfold nu once, project with &
- **Contraction** (`!A |- !A tensor !A`): unfold nu, coinduction with !A as coinvariant
- **Weakening** (`!A |- 1`): unfold nu, project to & right component
- **Promotion** (`?Gamma |- A` implies `?Gamma |- !A`): uses coinduction crucially

### Separation Result

- Fixed points can simulate exponentials (all exponential rules derivable)
- Exponentials **cannot** simulate fixed point encodings -- there exist muMALL theorems not provable in MALL with exponentials

Fixed points are **strictly more expressive** than exponentials.

---

## 4. Data Type Encodings

### Natural Numbers
```
Nat := mu X. 1 oplus X
```
`1` is zero, `oplus X` is successor. Admits weakening and contraction despite linearity.

### Lists
```
List(A) := mu X. 1 oplus (A tensor X)
```
`1` is nil, `A tensor X` is cons.

### Streams (infinite)
```
Stream(A) := nu X. A tensor X
```
Coinductive: always produces another element. Dual of lists.

### Finite Trees
```
Tree(A) := mu X. A oplus (X tensor X)
```

---

## 5. Cyclic Proofs

### 5.1 Motivation

The invariant problem (Section 2.4) motivates an alternative: **cyclic proofs**. Instead of guessing invariants, allow proof trees with **back-edges** and impose a global correctness condition. The proof structure itself encodes the (co)inductive argument.

### 5.2 Three Proof Systems

| System | Structure | Size | Validity |
|--------|-----------|------|----------|
| **muMALL_ind** | Well-founded trees + explicit (co)induction | Finite | Built-in |
| **muMALL_circ** | Finite graphs with back-edges | Finite repr. | Thread condition |
| **muMALL_inf** | Arbitrary infinite trees | Infinite | Thread condition |

Relationship: **Finitary ⊆ Circular ⊆ Non-wellfounded** (strict in general).

### 5.3 The Global Trace Condition (GTC)

A circular pre-proof has **buds** (leaves) linked to **companions** (interior nodes). A pre-proof is valid iff:

> For every infinite path through the unfolded proof tree, there exists an **infinitely progressing trace** following some tail of the path.

A **trace** follows a formula through rule applications. It **progresses** when passing through an unfolding of a mu-formula (left) or nu-formula (right).

**Soundness:** An infinite path with a progressing trace would induce an infinite decreasing chain of ordinals, contradicting well-foundedness.

### 5.4 Doumane's Results (PhD 2017, Gilles Kahn Prize)

Three main results:

1. **Cut-elimination for muMALL_inf** (with Baelde & Saurin, CSL 2016): Via multicut reductions. Fair sequences of internal/external reductions converge to cut-free proofs. First result for the multiplicative-additive case (Fortier-Santocanale only covered additive).

2. **Focalization for muMALL_inf**: First result for infinitary systems. Focused system complete w.r.t. unfocused, even for non-wellfounded proofs.

3. **Constructive completeness for linear-time mu-calculus**: A valid formula has a finitary proof iff circular proof iff non-wellfounded proof. The circular intermediate makes completeness constructive.

4. **Local validity criterion** (CSL 2018): Compositional alternative to GTC. Checked formula-by-formula via labelling. PSPACE-decidable. Suitable for programming language foundations (enables modular reasoning).

### 5.5 Fortier & Santocanale (CSL 2013)

Added cuts to circular proofs with a **parity-game-inspired guard condition**: on every infinite path, the parity of the outermost fixed point unfolded infinitely often determines validity. Results:
- Soundness in mu-bicomplete categories
- Local termination of cut-elimination
- Fullness w.r.t. mu-bicomplete categories
- **Limitation:** Only the purely additive fragment

### 5.6 The Brotherston-Simpson Conjecture

**Conjecture (2007):** Cyclic proofs derive exactly the same theorems as explicit induction.

| Setting | Result |
|---------|--------|
| FOL + inductive defs | Cyclic **strictly stronger** (Berardi & Tatsuta 2017, 2-Hydra) |
| + arithmetic | Equivalent (Simpson 2017) |
| Intuitionistic + arithmetic | Equivalent (Berardi 2017) |
| muMALL (propositional) | Equivalent (Doumane) |
| Separation logic | Open |

### 5.7 Checking Algorithms

**Standard (Buchi automata):** Construct path automaton P, trace automaton T, check L(P) ⊆ L(T). EXPTIME worst case (Buchi complementation is exponential).

**Complexity (Cohen et al., POPL 2024):** PSPACE-complete in general. Parameterized by vertices (n) and vertex width (w).

**E-Cyclist (Stratulat 2021):** Polynomial-time alternative using multiset path orderings. Checks locally at root-bud paths. 5x speedup over Cyclist's standard checking.

**Size-Change Termination connection:** The trace condition is closely related to SCT (Lee, Jones, Ben-Amram). Size-change graphs correspond to traces. SCT algorithm adaptable for cyclic proof checking.

**Ramsey-based (Das & Girlando, MSCS 2024):** Soundness via Ramsey's theorem instead of automata. Conceptually simpler.

### 5.8 Recent Developments

**Das, De & Saurin (FSTTCS 2023):** muMALL_inf (finitely branching non-wellfounded) is **strictly contained in** muMALL_{omega,inf} (infinitely branching well-founded). Novel infinitary rewriting technique.

**Acclavio, Curzi & Guerrieri (CSL 2024):** Infinitary cut-elimination via finite approximations -- build finite approximations, cut-eliminate each, take limit. Eliminates need for multicut rules and fairness conditions.

---

## 6. Semantics

### Phase Semantics
**De, Jafarrahmani & Saurin (FSTTCS 2022):** Phase semantics for muMALL. Designed muMALL_omega with phase semantics and cut-admissibility. Key finding: muMALL_omega and muMALL_ind have **different provability**.

### Categorical Models
**Ehrhard & Jafarrahmani (LICS 2021):** Categorical models of muLL. Two models:
1. **Sets and relations:** mu and nu coincide
2. **Non-uniform totality spaces:** mu and nu differ; denotational normalization

### Ludics
**Baelde & Doumane (CSL 2015):** muMALL interpreted in Girard's Ludics. Proofs = strategies, formulas = behaviours. Completeness for essentially finite designs.

### Curry-Howard-Lambek
**Jafarrahmani thesis (2023):** muLLP (Polarized LL with fixed points), term syntax, deterministic reduction semantics.

---

## 7. Decision Problems

**Das, De & Saurin (FSCD 2022):**
- **General (non-wellfounded):** Pi^0_1-hard (undecidable, via Minsky machines)
- **Least fixed points only:** Sigma^0_1-complete (via AVASS reachability)
- **Circular validity:** PSPACE-complete (Doumane)

Automated proof search is fundamentally incomplete. Heuristics, bounded search, and interactive guidance are necessary.

---

## 8. Implementations

### 8.1 Bedwyr (Model Checker)

Focused proof search for intuitionistic logic with (co)inductive definitions. OCaml. Uses **tabling** for fixed point computation: loops over inductive predicates = failure, loops over coinductive predicates = success. Direct implementation of Baelde & Miller's results.

Applications: bisimulation checking (pi-calculus), type checking, model checking over syntactic expressions with binders (via nabla quantifier).

### 8.2 Abella (Interactive Theorem Prover)

Two-level logic: specification logic (lambda-Prolog) + reasoning logic G. G has inductive/coinductive **relation** definitions (not propositional fixed points like muMALL, but same Knaster-Tarski foundations). Same research group (Parsifal/INRIA) as muMALL.

Used to formalize LL meta-theory: cut-admissibility, invertibility, generalized identity for sequent calculi (Chaudhuri, Lima, Reis, TCS 2019).

### 8.3 Linc (Logic with Induction and Coinduction)

Prototype proof checker by Tiu, Miller, Momigliano. Fixed points via definitions with stratification. Cut elimination proved. Proof checking only (not search).

### 8.4 Click and coLLecT

Interactive web-based MALL prover. OCaml backend. Exports to Coq, LaTeX, PDF, ASCII. No fixed points yet, but relevant infrastructure. https://click-and-collect.linear-logic.org/

### 8.5 Rast (Session-Typed Language)

Practical language for resource-aware session types with arithmetic refinements (Das & Pfenning, FSCD 2020). SML implementation. Recursive session types, work/span complexity bounds.

### 8.6 Gap

As of 2026, **no production-quality implementation** of full muMALL with both explicit (co)induction AND circular proof support exists. This is an opportunity for CALC.

---

## 9. Connection to Session Types

### 9.1 The Caires-Pfenning Correspondence

| Linear Logic | Session Type | Communication |
|-------------|-------------|---------------|
| A tensor B | Send A, continue as B | Output |
| A lolli B | Receive A, continue as B | Input |
| A & B | Offer choice A or B | External choice |
| A oplus B | Select A or B | Internal choice |
| 1 | Close channel | Termination |
| !A | Shared/persistent channel | Server |

### 9.2 Recursive Session Types via Fixed Points

```
Server := nu X. Request -o (Response tensor X)
  -- coinductive: serves forever

FileTransfer := mu X. (Chunk tensor X) oplus Done
  -- inductive: sends finitely many chunks, then Done

Counter := nu X. (Inc tensor X) & (Get tensor Nat tensor X) & (Stop tensor 1)
  -- coinductive: always available
```

### 9.3 Corecursion and Non-Divergence

**Toninho, Caires & Pfenning (TGC 2014):** Coinductive types ensure productive corecursion. Type safety implies protocol compliance + global progress.

### 9.4 Circular Proofs as Session-Typed Processes

**Derakhshan & Pfenning (LMCS 2022):** Mutually recursive processes = circular proofs. Validity ensures non-divergence. Local decidable criterion, suitable as basis for a programming language.

### 9.5 Structural Recursion

**Lindley & Morris (ICFP 2016), "Talking Bananas":** mu-types = catamorphic (fold-based) protocols, nu-types = anamorphic (unfold-based) protocols. Guarantees termination, deadlock-freedom, livelock-freedom.

### 9.6 Fair Termination

**Ciccone & Padovani (CONCUR 2022):** Conservatively extend muMALL_inf so cut elimination corresponds to **fair termination** -- programs that diverge in principle but terminate under fair scheduling.

**Dagnino & Padovani (PPDP 2024), "sMALL CaPS":** Propositions themselves may be infinite. All derivations valid by construction. Recursive protocols (authentication, coordination, consensus).

---

## 10. Computational Interpretations

### Cyclic Proofs and System T

**Curzi & Das (POPL 2021):**
- Cyclic proofs without contraction = System T (primitive recursive functions)
- Cyclic proofs with contraction = all of Peano arithmetic
- The **contraction rule** is the key dividing line

---

## 11. Relevance to CALC

### 11.1 What Fixed Points Give CALC

**Without fixed points (current ILL):**
- Only finite, bounded computations
- No "repeat until done" or "serve forever"
- Cannot define data types (nat, list, tree) within the logic
- Exponentials (!) are primitive and opaque

**With fixed points (muMALL):**

| Capability | Mechanism | CALC Application |
|-----------|-----------|------------------|
| Inductive data types | mu X. F(X) | Token lists, approval chains, Merkle trees |
| Coinductive processes | nu X. F(X) | Streaming payments, persistent services |
| Exponentials as sugar | !A := nu X. A & X | Simplifies core logic |
| Inductive reasoning | mu-left rule | Prove conservation laws, safety invariants |
| Coinductive reasoning | nu-right rule | Bisimulation, protocol equivalence |
| Recursive protocols | Session type mu/nu | Financial protocol specification |
| Model checking | CTL encoding | State space verification |

### 11.2 Connection to Execution Trees

CALC's execution trees ([[execution-trees-metaproofs]] Section 1) are **finite unfoldings** of fixed points. Currently, forward chaining builds a finite tree and stops at choice points or quiescence. With mu/nu:

- A **terminating** execution tree is an element of `mu X. Leaf(State) oplus Branch(Rule, X, X)` -- inductive, finitely deep
- A **non-terminating** computation (server, stream) is `nu X. Step(Rule, X)` -- coinductive, potentially infinite
- **Cycle detection** in execution = detecting when a cyclic proof structure applies

### 11.3 Connection to Metaproofs

Metaproofs ([[execution-trees-metaproofs]] Section 2) are exactly **induction over fixed point types**:

```
-- Conservation: total supply preserved (induction on reachable states)
Conservation := mu I. (Initial(s) tensor Balanced(s))
                oplus (forall rule. Preserves(rule, I))

-- Safety: bad state unreachable (induction)
Safety(bad) := mu I. (Initial(s) tensor NotBad(s))
               oplus (forall rule. step(s, rule, s') tensor I(s'))

-- Liveness: something good eventually happens (coinduction + induction)
Liveness := nu L. Good oplus (Step tensor L)
```

The key insight: **metaproofs ARE fixed-point proofs**. Adding mu/nu to CALC doesn't just add data types -- it gives a native language for expressing and verifying properties about CALC programs.

### 11.4 CALC-Specific Encodings

```
-- Streaming payments (coinductive)
StreamingPayment := nu X. [Alice] Pay(amount) tensor Delay tensor X

-- Bounded approval chain (inductive)
ApprovalChain := mu X. Approved oplus (RequestApproval tensor X)

-- Token list (inductive)
TokenList := mu X. 1 oplus ([Owner] Token tensor X)

-- Persistent service (exponential via fixed point)
Service(A, B) := nu X. (A -o B) & X
-- equivalent to !(A -o B), but now exponential is derived!

-- Bisimulation: two contracts behave identically
Bisim(C1, C2) := nu R. forall action.
  Step(C1, action) -o Step(C2, action) tensor R

-- Invariant: total token supply constant
TotalPreserved := mu I.
  (Initial tensor SupplyEquals(N))
  oplus (forall rule. I tensor Preserves(rule))
```

### 11.5 Implementation Path for CALC

**Phase 1: Syntax + unfold rules.**
Add `mu X. B(X)` and `nu X. B(X)` to the formula grammar (extend ll.json / the v2 calculus definition). Implement unfolding rules. This alone gives inductive data types and coinductive processes. The focused prover already handles polarity -- mu is positive, nu is negative.

**Phase 2: Bounded model checking.**
Unfold fixed points to depth k. Detect revisited states via content-addressed hashing (CALC already has this!). Practical for finding bugs without full verification.

**Phase 3: Cyclic proof engine.**
Allow proofs with back-edges. Implement the GTC checker -- start with SCT-based polynomial approach (E-Cyclist style), fall back to Buchi for completeness. This avoids invariant-guessing and connects naturally to the manual proof UI (user can close cycles interactively).

**Phase 4: Full (co)induction.**
Interactive mode: user supplies invariants/coinvariants, prover verifies them. Connects to the manual proof interface. For metaproofs: user states conservation law, CALC verifies by induction over rules.

### 11.6 Why Cyclic Proofs over Explicit Induction?

For CALC specifically, cyclic proofs are preferable because:
1. **No invariant guessing** -- the proof structure encodes the (co)inductive argument
2. **Automation-friendly** -- proof search explores cyclic structure naturally, validity is a separate decidable post-check
3. **CALC's content-addressed store** enables cheap cycle detection (state equality is O(1) hash comparison)
4. **Connects to forward chaining** -- cycle detection during forward chaining is the operational analogue of cyclic proof construction
5. **Manual proof UI** -- user can "close a cycle" by pointing to an earlier sequent, which is more intuitive than constructing an invariant formula

---

## 12. References

### Foundational

1. Baelde & Miller. "Least and greatest fixed points in linear logic." LPAR 2007.
   https://www.lix.polytechnique.fr/~dale/papers/lpar07final.pdf
2. Baelde. "Least and greatest fixed points in linear logic." TOCL 2012.
   https://dl.acm.org/doi/abs/10.1145/2071368.2071370
3. Baelde. Habilitation, 2022.
   https://inria.hal.science/hal-03579451/document

### Cyclic and Infinitary Proofs

4. Fortier & Santocanale. "Cuts for circular proofs." CSL 2013.
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2013.248
5. Baelde, Doumane & Saurin. "Infinitary proof theory: the multiplicative additive case." CSL 2016.
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2016.42
6. Doumane. PhD thesis, 2017.
   https://www.irif.fr/~doumane/these.pdf
7. Doumane. "Local validity for circular proofs in muMALL." CSL 2018.
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2018.35
8. Brotherston & Simpson. "Complete sequent calculi for induction and infinite descent." LICS 2007.
9. Acclavio, Curzi & Guerrieri. "Infinitary cut-elimination via finite approximations." CSL 2024.
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2024.8

### Decision Problems

10. Das, De & Saurin. "Decision problems for muMALL." FSCD 2022.
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.20
11. Das, De & Saurin. "Comparing infinitary systems." FSTTCS 2023.
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2023.40
12. Cohen, Jabarin, Popescu, Rowe. "Complexity of checking infinite descent." POPL 2024.
    https://dl.acm.org/doi/abs/10.1145/3632888

### Semantics

13. De, Jafarrahmani & Saurin. "Phase semantics for muMALL." FSTTCS 2022.
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2022.35
14. Ehrhard & Jafarrahmani. "Categorical models of muLL." LICS 2021.
    https://arxiv.org/abs/2011.10209
15. Jafarrahmani. PhD thesis, 2023.
    https://theses.hal.science/tel-04523738
16. Baelde & Doumane. "Fixed points in Ludics." CSL 2015.
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2015.549

### Session Types

17. Caires & Pfenning. "Session types as intuitionistic linear propositions." CONCUR 2010.
18. Caires, Pfenning & Toninho. "Linear logic propositions as session types." MSCS 2016.
19. Toninho, Caires & Pfenning. "Corecursion and non-divergence." TGC 2014.
20. Derakhshan & Pfenning. "Circular proofs as session-typed processes." LMCS 2022.
    https://lmcs.episciences.org/9444/pdf
21. Lindley & Morris. "Talking Bananas: structural recursion for session types." ICFP 2016.
22. Ciccone & Padovani. "Fair termination in the linear pi-calculus." CONCUR 2022.
    https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2022.36
23. Dagnino & Padovani. "sMALL CaPS." PPDP 2024.

### Implementations

24. Baelde, Gacek, Miller, Nadathur, Tiu. "The Bedwyr system." CADE 2007.
25. Gacek. "The Abella interactive theorem prover." IJCAR 2008. https://abella-prover.org/
26. Tiu. "Cut elimination for Linc." Journal of Applied Logic, 2012.
27. Das & Pfenning. "Rast: resource-aware session types." FSCD 2020.

### Computational Interpretations

28. Curzi & Das. "Cyclic proofs, system T, and the power of contraction." POPL 2021.
29. Stratulat. "E-Cyclist." 2021. https://arxiv.org/abs/2109.03235

### Formalizations

30. Xavier & Olarte. "Mechanizing focused linear logic in Coq." ENTCS 2018.
31. Chaudhuri, Lima, Reis. "Formalized meta-theory of sequent calculi for linear logics." TCS 2019.

### Expository

32. Proof Theory Blog. "Exponentials vs fixed points in linear logic." 2024.
    https://prooftheory.blog/2024/06/27/exponentials-vs-fixed-points-in-linear-logic/

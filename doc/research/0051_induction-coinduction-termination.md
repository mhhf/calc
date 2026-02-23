---
title: "Induction, Coinduction, Termination, and Bisimulation for Linear Logic"
created: 2026-02-23
modified: 2026-02-23
summary: "Comprehensive survey of induction/coinduction in linear logic, termination proofs for forward-chaining/rewriting systems, bisimulation, cyclic proofs, and their Curry-Howard content"
tags: [induction, coinduction, cyclic-proofs, termination, bisimulation, muMALL, size-change, rewriting, Curry-Howard]
category: "Proof Theory"
---

# Induction, Coinduction, Termination, and Bisimulation for Linear Logic

Eight interconnected topics surveyed with exact references, step-by-step proof sketches, and applicability to a linear logic forward-chaining system.

---

## 1. Induction and Coinduction in Linear Logic -- Beyond muMALL

### 1.1 muMALL (Baelde & Miller)

**Core system.** muMALL extends MALL with least (mu) and greatest (nu) fixed point operators. See RES_0031 for full details.

- Baelde, D. & Miller, D. "Least and greatest fixed points in linear logic." LPAR 2007, LNCS 4790, pp. 92--106. doi:10.1007/978-3-540-75560-9_9
- Baelde, D. "Least and greatest fixed points in linear logic." ACM TOCL 13(1), Article 2, January 2012. doi:10.1145/2071368.2071370

**Key result:** muMALL satisfies weak normalization (cut elimination) and has a complete focused proof system. The invariant needed for induction can be any formula (not restricted to subformulas), making proof search undecidable in general.

### 1.2 Cyclic Proof Systems for Linear Logic

Three groups have developed cyclic/infinitary proof theory for linear logic with fixed points:

**Fortier & Santocanale (CSL 2013).** Added cuts to a cyclic proof calculus for mu-calculus/linear logic. Soundness and local cut-elimination in mu-bicomplete categories. Limited to the purely additive fragment.
- Fortier, J. & Santocanale, L. "Cuts for circular proofs: semantics and cut-elimination." CSL 2013, LIPIcs 23, pp. 248--262. doi:10.4230/LIPIcs.CSL.2013.248

**Baelde, Doumane & Saurin (CSL 2016).** Extended to the full multiplicative-additive case (muMALL_inf). Proved cut elimination for non-wellfounded proofs via fair multicut reduction sequences and established focalization for infinitary proofs.
- Baelde, D., Doumane, A. & Saurin, A. "Infinitary proof theory: the multiplicative additive case." CSL 2016, LIPIcs 62, pp. 42:1--42:17. doi:10.4230/LIPIcs.CSL.2016.42

**Doumane (PhD 2017, Gilles Kahn Prize).** Unified treatment: finitary proofs (explicit induction) embed into circular proofs embed into non-wellfounded proofs. Constructive completeness for linear-time mu-calculus. Local validity criterion (CSL 2018) is PSPACE-decidable and compositional.
- Doumane, A. "On the infinitary proof theory of logics with fixed points." PhD thesis, Universite Sorbonne Paris Cite, 2017. https://www.irif.fr/~doumane/these.pdf
- Nollet, R., Saurin, A. & Tasson, C. "Local validity for circular proofs in linear logic with fixed points." CSL 2018, LIPIcs 119, pp. 35:1--35:23. doi:10.4230/LIPIcs.CSL.2018.35

**Recent (2023--2024):**
- Das, A., De, A. & Saurin, A. "Comparing infinitary systems for linear logic with fixed points." FSTTCS 2023, LIPIcs. doi:10.4230/LIPIcs.FSTTCS.2023.40
- Acclavio, M., Curzi, G. & Guerrieri, G. "Infinitary cut-elimination via finite approximations." CSL 2024, LIPIcs. doi:10.4230/LIPIcs.CSL.2024.8

### 1.3 Abella -- Induction via Two-Level Logic

Abella is an interactive theorem prover based on a two-level architecture: a *specification logic* (intuitionistic hereditary Harrop formulas, essentially lambda-Prolog) and a *reasoning logic* G with induction, coinduction, the nabla quantifier, and nominal constants.

**How Abella handles induction:** G allows **inductive definitions** of predicates (not propositional mu-formulas as in muMALL, but same Knaster-Tarski foundations). Induction is over the *height* of a derivation in the specification logic. The user invokes `induction on N` to get an inductive hypothesis restricted to smaller derivation heights. This is natural induction, not structural -- it applies uniformly to any specification.

- Gacek, A. "The Abella interactive theorem prover (system description)." IJCAR 2008, LNCS 5195, pp. 154--161. doi:10.1007/978-3-540-71070-7_13
- Gacek, A., Miller, D. & Nadathur, G. "A two-level logic approach to reasoning about computations." J. Automated Reasoning 49(2), pp. 241--273, 2012. doi:10.1007/s10817-011-9218-1
- https://abella-prover.org/

**Applicability to CALC:** Abella's two-level approach is directly relevant -- CALC's forward rules are the "specification logic" and properties about execution (termination, invariants) live in the "reasoning logic." Abella has been used to formalize LL meta-theory including cut-admissibility (Chaudhuri, Lima, Reis, TCS 2019).

### 1.4 Bedwyr -- Coinduction via Tabling

Bedwyr is a model checker that generalizes logic programming with (co)inductive definitions, higher-order abstract syntax, and the nabla quantifier. It implements focused proof search.

**Tabling mechanism:** When proof search encounters a goal already visited on the current branch:
- For an **inductive** predicate: the loop is **failure** (no finite evidence)
- For a **coinductive** predicate: the loop is **success** (the observation is consistent)

This is a direct implementation of the least/greatest fixed point semantics: inductive predicates are the *least* fixed point (only finitely derivable facts are true), coinductive predicates are the *greatest* fixed point (anything not refutable is true).

- Baelde, D., Gacek, A., Miller, D., Nadathur, G. & Tiu, A. "The Bedwyr system for model checking over syntactic expressions." CADE 2007, LNCS 4603, pp. 391--397. doi:10.1007/978-3-540-73595-3_28

**Applicability to CALC:** Bedwyr's tabling strategy maps directly to cycle detection in CALC's forward chaining. When the engine revisits a state (detectable via content-addressed hashing in O(1)), the interpretation depends on whether the property being checked is inductive (fail -- no new derivation) or coinductive (succeed -- stable observation).

### 1.5 Size-Change Termination and Cyclic Proofs

**The size-change principle (SCT)** states: a program terminates on all inputs if every infinite call sequence would cause an infinite descent in some data values (according to size-change graphs).

- Lee, C.S., Jones, N.D. & Ben-Amram, A.M. "The size-change principle for program termination." POPL 2001, pp. 81--92. doi:10.1145/360204.360210

**Key result:** SCT is PSPACE-complete. Despite this, practical algorithms exist.

**Connection to cyclic proofs:** The global trace condition (GTC) for validating cyclic proofs is closely related to SCT. In both cases:
- You have finitely many "size-change graphs" (trace transitions in cyclic proofs)
- Soundness requires that every infinite path exhibits infinite descent
- The decision problem is PSPACE-complete in both cases

Doumane's thesis (2017) explicitly establishes this connection: thread-validity for muMALL circular proofs is PSPACE-complete, and the proof reduces to/from SCT. The size-change graphs of SCT correspond to traces following formulas through proof rules. Infinite descent in data values corresponds to infinite progress through mu-unfoldings.

- Nollet, R., Saurin, A. & Tasson, C. "PSPACE-completeness of a thread criterion for circular proofs in linear logic with least and greatest fixed points." FoSSaCS 2019, LNCS 11425, pp. 319--336. doi:10.1007/978-3-030-29026-9_18

---

## 2. Simple Induction Proofs in Linear Logic

### Can You Do Mathematical Induction in Linear Logic?

**Yes**, via muMALL. Natural numbers are defined as:

```
Nat := mu X. 1 oplus X
```

where `1` is zero and `oplus X` is successor. Despite linearity, `Nat` is a *positive* formula and admits derived weakening and contraction rules (because it is a least fixed point of a positive body). So reasoning about natural numbers in muMALL feels the same as in intuitionistic logic.

### Step-by-Step: "Every natural number is zero or a successor"

We prove: `|- Nat -o (IsZero oplus IsSucc)` where:
- `IsZero := 1` (the number is zero)
- `IsSucc := Nat` (the number is a successor of some nat)

Equivalently in one-sided sequent notation: `|- Nat^bot, (1 oplus Nat)`

**Proof by induction on Nat:**

1. **Set up induction.** Apply the mu-left rule (induction) on `Nat` with invariant `S := 1 oplus Nat` (the conclusion itself).

   We must show two things:
   - (a) `S` is closed under the body of Nat (i.e., `|- (1 oplus S), (1 oplus Nat)` -- substituting S for X in the body `1 oplus X`)
   - (b) `|- S^bot, (1 oplus Nat)` (the invariant implies the conclusion -- trivially here since S = conclusion)

2. **Base case (zero).** The body `1 oplus X` with `X := S` gives the left disjunct `1`.
   - We must show: `|- 1^bot, (1 oplus Nat)`, i.e., the zero case.
   - Choose left disjunct of `1 oplus Nat`: `|- 1^bot, 1`. This closes by identity (`1^bot = bot`, and `|- bot, 1` is the unit axiom).

3. **Inductive case (successor).** The body gives the right disjunct `S`.
   - We must show: `|- S^bot, (1 oplus Nat)`, i.e., `|- (1 oplus Nat)^bot, (1 oplus Nat)`.
   - The inductive hypothesis gives us that the predecessor satisfies `1 oplus Nat`.
   - Choose right disjunct of `1 oplus Nat`: provide `Nat` as witness. This closes because the predecessor is a Nat (from the inductive hypothesis, which gives `S = 1 oplus Nat`, and the right component is `Nat`).

**In focused proof search**, this proof is found automatically by the Tac prover (Baelde, Miller & Snow, IJCAR 2010). The focusing discipline determines when to apply induction (asynchronous phase) and when to make choices (synchronous phase).

- Baelde, D., Miller, D. & Snow, Z. "Focused inductive theorem proving." IJCAR 2010, LNCS 6173, pp. 278--292. doi:10.1007/978-3-642-14203-1_24

### What Makes This Work Despite Linearity?

The key insight from Baelde (TOCL 2012): formulas of the form `mu X. F(X)` where `F` is positive inherit structural properties. Specifically, `Nat = mu X. 1 oplus X` admits:
- **Weakening:** you can discard a Nat (it is "garbage-collectable")
- **Contraction:** you can duplicate a Nat (it can be copied)

This is because `Nat` can be shown equivalent to `!Nat_inner` for an appropriate inner formula. So mathematical induction in muMALL works just like in intuitionistic logic for positive inductive types.

---

## 3. Coinduction Examples

### 3.1 Bisimulation of Two Streams

The simplest coinductive proof: show that two infinite streams are equal.

**Definition.** Streams in muMALL:
```
Stream(A) := nu X. A tensor X
```
A stream is a greatest fixed point: it always produces a head (of type A) and a tail (another stream).

**Example.** Let `ones = 1 :: 1 :: 1 :: ...` and `ones' = 1 :: ones`. We prove `ones ~ ones'` (bisimilar).

**Coinductive proof structure:**

1. **State the goal.** Show `Stream_eq(ones, ones')`, defined coinductively:
   ```
   Stream_eq(s1, s2) := nu R. head(s1) = head(s2) & R(tail(s1), tail(s2))
   ```

2. **Apply coinduction.** Choose coinvariant `S := {(ones, ones')}`. We must show S is a *post-fixed point* (i.e., S implies one step of the body applied to S).

3. **Check one step:**
   - `head(ones) = 1 = head(ones')` -- heads match.
   - `(tail(ones), tail(ones')) = (ones, ones)` -- tails are `(ones, ones)`.
   - But `ones = ones'` by definition (`ones' = 1 :: ones = ones`), so `(ones, ones) in S`.

4. **Conclude by coinduction.** S is a bisimulation (a post-fixed point of the body), so `Stream_eq(ones, ones')` holds.

### 3.2 What is Productivity?

**Productivity** is the coinductive analogue of termination. A corecursive definition is *productive* if it can always produce the next piece of output in finite time.

- **Termination** (induction): every computation reaches a base case in finite steps
- **Productivity** (coinduction): every observation (head, tail) is computable in finite time

**Guardedness** is a syntactic sufficient condition for productivity: every corecursive call must be "guarded" by a constructor. In Coq/Agda, the termination checker enforces guardedness -- corecursive calls must appear under a coinductive constructor (like `::` for streams).

**Example of unproductive definition:**
```
bad := if expensive_computation() then 1 :: bad else bad
```
The second branch calls `bad` without producing any output -- it may loop forever without ever yielding a stream element.

**Example of productive definition:**
```
nats_from(n) := n :: nats_from(n+1)
```
Always produces a head `n` before the corecursive call.

### 3.3 Coinduction in Bedwyr/Abella

In Bedwyr, coinductive model checking is tabling: revisiting a goal on a coinductive predicate succeeds. In Abella, coinduction is explicit: the user provides a coinvariant (the bisimulation relation), and Abella checks that it is a post-fixed point.

- Sangiorgi, D. "Introduction to Bisimulation and Coinduction." Cambridge University Press, 2012. ISBN 978-1-107-00363-7

---

## 4. Termination Proofs for Forward-Chaining Systems

### 4.1 Ranking Functions

A **ranking function** maps computation states to a well-founded domain (typically natural numbers) such that each rule application strictly decreases the rank. If such a function exists, termination is guaranteed.

For CHR (Constraint Handling Rules), which are closely related to linear logic forward rules:
- A ranking maps constraint stores (multisets) to natural numbers
- For each rule with head constraints H and body constraints B: `rank(H) > rank(B)`
- Since natural numbers are well-founded, the rule cannot fire infinitely

- Fruhwirth, T. "Constraint Handling Rules." Cambridge University Press, 2009. ISBN 978-0-521-87776-3
- Sneyers, J., Van Weert, P., Schrijvers, T. & Demoen, B. "As time goes by: Constraint Handling Rules -- a survey of CHR research from 1998 to 2007." Theory and Practice of Logic Programming 10(1), pp. 1--47, 2010. doi:10.1017/S1471068409990123

**Applicability to CALC:** Each forward rule consumes linear facts and produces new ones. A ranking function on multisets of linear facts that strictly decreases per rule application proves termination.

### 4.2 Well-Founded Orderings on Multisets (Dershowitz-Manna)

The **Dershowitz-Manna multiset ordering** lifts any well-founded ordering on elements to a well-founded ordering on finite multisets. Given a well-founded order `>` on a set S, define `>>` on multisets over S:

> M >> N iff M != N and for every x in (N - M), there exists y in (M - N) with y > x.

Intuitively: you can replace elements with *finitely many* smaller elements, and the multiset still decreases.

- Dershowitz, N. & Manna, Z. "Proving termination with multiset orderings." Communications of the ACM 22(8), pp. 465--476, 1979. doi:10.1145/359138.359142

**Key theorem:** If `>` is well-founded on S, then `>>` is well-founded on finite multisets over S. The order type of `>>` is omega^omega when `>` has order type omega, and epsilon_0 for iterated nesting.

**Applicability to CALC:** Linear facts form a multiset. Each forward rule replaces some facts (consumed) with others (produced). If we can assign a weight to each fact type such that consumed > produced in the multiset ordering, termination follows. This is exactly how CHR termination works.

### 4.3 CHR Termination Techniques

CHR is Turing-complete, so termination is undecidable. But several semi-decision procedures exist:

1. **Ranking-based:** Map constraint stores to well-founded domains. Simplification rules: `rank(head) > rank(body)`. Propagation rules: need additional conditions (e.g., token-based history).

2. **Transformational:** Transform CHR to Prolog, apply LP termination provers.
   - Pilozzi, P. & De Schreye, D. "Proving termination of CHR in Prolog: a transformational approach." WST 2007.

3. **Self-sustainability analysis:** Check whether a rule can re-enable itself.
   - Voets, D. et al. "Improved termination analysis of CHR using self-sustainability analysis." ICLP 2012.

### 4.4 Connection to Gas-Bounded EVM Execution

EVM execution terminates because each instruction consumes gas, and gas is a finite resource that strictly decreases. This is a trivial ranking function:

```
rank(state) = state.gas
```

Every instruction decreases gas by at least 1. Since gas is a natural number, termination is guaranteed by well-foundedness of the naturals.

In CALC's EVM model, the same argument applies: each forward rule that models an EVM instruction must consume a `gas(n)` fact and produce `gas(n-k)` for some `k >= 1`. The ranking function `rank = gas value` proves termination.

More generally, **resource-bounded linear logic** (bounded linear logic) controls complexity through explicit resource bounds:
- Girard, J.-Y., Scedrov, A. & Scott, P.J. "Bounded linear logic: a modular approach to polynomial-time computability." Theoretical Computer Science 97(1), pp. 1--66, 1992. doi:10.1016/0304-3975(92)90386-T

### 4.5 Dependency Pairs

The **dependency pair method** (Arts & Giesl) decomposes termination into: (1) identify recursive call structure ("dependency pairs"), (2) find a well-founded ordering on the arguments of recursive calls.

- Arts, T. & Giesl, J. "Termination of term rewriting using dependency pairs." Theoretical Computer Science 236(1--2), pp. 133--178, 2000. doi:10.1016/S0304-3975(99)00207-8

This is the backbone of modern automated termination provers (AProVE, TTT2) and applies to rewriting systems generally.

---

## 5. Bisimulation in Linear Logic

### 5.1 The Deng-Cervesato-Simmons Result

The key result connecting bisimulation and linear logic proof theory:

- Deng, Y., Cervesato, I. & Simmons, R.J. "Relating reasoning methodologies in linear logic and process algebra." Mathematical Structures in Computer Science 26(5), pp. 868--906, 2016. doi:10.1017/S0960129514000218. Also: LINEARITY 2012, pp. 50--60.

**Main theorem:** For a CCS-like calculus obtained from the formula-as-process interpretation of a fragment of linear logic, the *proof-theoretic logical preorder* (definable purely in terms of provability in linear logic) coincides with the *process-theoretic contextual preorder* (defined coinductively as the standard notion from process algebra).

The proof uses a **coinductively defined simulation relation** as a stepping stone: first show logical preorder implies simulation, then simulation implies contextual preorder, then contextual preorder implies logical preorder.

### 5.2 Bisimulation Between Linear Logic Programs

To prove two linear logic programs P1 and P2 are bisimilar:

1. **Define the observation relation.** What constitutes a "step" -- a single forward rule application, producing observable facts.

2. **Construct a bisimulation relation R.** R relates states of P1 to states of P2 such that:
   - If `(s1, s2) in R` and `s1 --rule--> s1'`, then there exists `s2'` with `s2 --rule--> s2'` and `(s1', s2') in R`
   - Symmetrically for steps from s2.

3. **Prove R is a post-fixed point** of the bisimulation functional. This is a coinductive argument.

In muMALL, this can be expressed as:
```
Bisim(P1, P2) := nu R. forall action.
  (Step(P1, action) -o exists P1'. Step(P1', action) tensor R(P1', P2'))
  & (Step(P2, action) -o exists P2'. Step(P2', action) tensor R(P1', P2'))
```

### 5.3 Coinductive Proof Structure

The proof that R is a bisimulation proceeds coinductively:

1. **Coinduction rule:** To prove `Bisim(s1, s2)`, choose coinvariant S (typically R itself or some extension).
2. **Show S is closed:** For each pair `(s1, s2) in S` and each action, exhibit matching transitions and show the resulting pair is again in S.
3. **Conclude:** By the nu-right rule, `Bisim(s1, s2)` holds.

In CALC, bisimulation checking between two execution trees amounts to synchronized traversal: at each branching point, both trees must offer the same choices, and corresponding subtrees must be recursively bisimilar. CALC's content-addressed store makes state equality O(1), which accelerates bisimulation checking.

---

## 6. Do You Need Full Higher-Order Logic for Induction?

### 6.1 First-Order Induction Suffices for Many Properties

For proving properties of forward-chaining programs (like CALC's), **first-order induction over rule application sequences** usually suffices. You do not need second-order quantification or higher-order logic.

What you need:
- **Inductive definitions** of predicates (first-order)
- An **induction principle** for those definitions (first-order schema)
- The ability to reason about **multisets** of facts (first-order with multiset axioms)

Peano Arithmetic (PA) with its first-order induction schema captures:
- All properties expressible as arithmetic predicates
- Termination of primitive recursive programs
- Conservation laws (sums over multisets)

### 6.2 The Omega-Rule

The **omega-rule** states: if you can prove P(0), P(1), P(2), ... (one proof for each natural number), then you can conclude `forall n. P(n)`. This is an *infinitary* rule -- it has infinitely many premises.

The omega-rule is **strictly stronger** than first-order induction: there exist arithmetical truths provable with the omega-rule but not provable in PA with the induction schema. However, for practical programming properties, the omega-rule is rarely needed.

Cut elimination holds for arithmetic with the omega-rule (Schutte, 1977), which is a key tool in ordinal analysis.

### 6.3 Cyclic Proofs as an Alternative to Explicit Induction

**Key question:** Are cyclic proofs equivalent to explicit induction?

| Setting | Result | Reference |
|---------|--------|-----------|
| FOL + inductive definitions (classical) | Cyclic strictly stronger | Berardi & Tatsuta, LICS 2017 |
| FOL + inductive defs + arithmetic (classical) | Equivalent | Simpson, 2017 |
| FOL + inductive defs + arithmetic (intuitionistic) | Equivalent | Berardi & Tatsuta, 2017 |
| muMALL (propositional) | Equivalent | Doumane, 2017 |

- Brotherston, J. & Simpson, A. "Sequent calculi for induction and infinite descent." J. Logic and Computation 21(6), pp. 1177--1216, 2011. doi:10.1093/logcom/exq052
- Berardi, S. & Tatsuta, M. "Equivalence of inductive definitions and cyclic proofs under arithmetic." LICS 2017.
- Berardi, S. & Tatsuta, M. "Explicit induction is not equivalent to cyclic proofs for classical logic with inductive definitions." arXiv:1712.09603, 2017.

**Takeaway for CALC:** Cyclic proofs are at least as powerful as explicit induction, and strictly more powerful without arithmetic. Since CALC already has arithmetic (via FFI for inc, plus, etc.), the two approaches are equivalent in CALC's setting. But cyclic proofs are more automation-friendly because they avoid invariant guessing.

### 6.4 What CALC Actually Needs

For proving properties of CALC's forward-chaining programs:

1. **Termination:** Ranking functions (Section 4) -- first-order, no induction needed.
2. **Safety invariants** ("bad state unreachable"): Induction over rule application steps -- first-order induction schema suffices.
3. **Conservation laws** ("total supply constant"): Induction over multiset transformations -- first-order with multiset axioms.
4. **Liveness** ("eventually reaches good state"): Coinduction or omega-rule -- but for finite state spaces, model checking suffices.
5. **Bisimulation:** Coinduction -- first-order coinductive definitions suffice.

**Full higher-order logic is not needed.** First-order logic with (co)inductive definitions covers all practical cases for CALC.

---

## 7. Practical Systems for Induction over Rewriting Systems

### 7.1 Maude

**Maude** implements rewriting logic. It provides:
- **Model checking:** LTL model checker for finite-state systems (breadth-first search of reachable states).
- **Inductive Theorem Prover (ITP):** Interactive prover using reflection and initial algebra semantics. Induction is over *initial models* of rewriting theories.
- **Maude Termination Tool (MTT):** Transforms Maude modules to TRS form, applies external termination provers (AProVE, TTT2) as backends.

- Clavel, M. et al. "All About Maude -- A High-Performance Logical Framework." Springer, LNCS 4350, 2007. doi:10.1007/978-3-540-71999-1

### 7.2 K Framework

**K** is a rewriting-based framework for defining programming language semantics. Verification is via **reachability logic** (generalization of Hoare logic) and **matching logic** (pattern-based static reasoning).

- Rosu, G. "K: A semantic framework for programming languages and formal analysis tools." Marktoberdorf Summer School 2017.
- Stefanescu, A. et al. "All-path reachability logic." RTA 2014, LNCS 8560.

K has been used to verify real programs in C, Java, JavaScript, and EVM (the KEVM project). Termination is handled by matching logic reachability claims with ranking arguments.

### 7.3 AProVE

**AProVE** is the most powerful automated termination prover for term rewriting. Techniques:
- **Dependency pairs** (Arts & Giesl, 2000): decompose termination into sub-problems
- **Polynomial interpretations:** map terms to polynomials, show decrease
- **Matrix interpretations:** generalize polynomial interpretations with matrix-valued weights
- **Size-change principle:** adapted from Lee, Jones, Ben-Amram

- Giesl, J. et al. "Automated termination proofs with AProVE." RTA 2004, LNCS 3091, pp. 210--220. doi:10.1007/978-3-540-25979-4_15
- Giesl, J. et al. "AProVE 1.2: automatic termination proofs in the dependency pair framework." IJCAR 2006, LNCS 4130, pp. 281--286. doi:10.1007/11814771_24

### 7.4 TTT2

**TTT2** (Tyrolean Termination Tool 2) is another automated termination prover. Uses dependency pairs, polynomial/matrix interpretations, RPO, and the subterm criterion. Repeatedly wins the Termination Competition.

### 7.5 CiME

**CiME** (Calculs, Implementations, Modeles, Experimentations) focuses on completion and termination of equational theories. Uses LPO, RPO, polynomial interpretations. Can certify termination proofs.

### 7.6 Comparison and Applicability to CALC

| Tool | Approach | Strengths | CALC Relevance |
|------|----------|-----------|----------------|
| Maude | Rewriting logic + model checking | Full language semantics | High -- similar multiset rewriting |
| K | Reachability logic | Real language verification | High -- EVM (KEVM) |
| AProVE | Dependency pairs + multiple orderings | Fully automated | Medium -- TRS termination |
| TTT2 | Same as AProVE, different heuristics | Competition winner | Medium |
| CiME | Equational completion | Certification | Low -- less relevant to multiset |

For CALC specifically, the most relevant approach is **Maude-style multiset rewriting termination** combined with **K-style reachability logic** for proving properties of execution.

---

## 8. Curry-Howard for Cyclic Proofs

### 8.1 Kuperberg, Pinault & Pous (POPL 2021)

The paper establishes a Curry-Howard correspondence for cyclic proofs:

- Kuperberg, D., Pinault, L. & Pous, D. "Cyclic proofs, system T, and the power of contraction." Proc. ACM Program. Lang. 5(POPL), Article 1, 2021. doi:10.1145/3434282

**Setting:** A cyclic proof system **C** over regular expression types, inspired by linear logic and non-wellfounded proof theory.

**Key computational interpretation:** Proofs in C correspond to **strongly typed goto programs**. A cyclic proof has back-edges (jumps to earlier points in the derivation), and under Curry-Howard, these are goto instructions. The global trace condition ensures that these goto programs always terminate.

**Main results:**

| System | Functions Captured |
|--------|-------------------|
| C (full, with contraction) | Same as Godel's System T (all provably total functions of PA) |
| C_aff (affine, no contraction) | Exactly primitive recursive functions |

**Theorem (Kuperberg-Pinault-Pous):** Godel's System T and the cyclic proof system C capture the same first-order functions on natural numbers.

**Theorem (affine case):** Without contraction, C captures exactly the primitive recursive functions. This gives an alternative proof of a result by Dal Lago about affine System T.

**The power of contraction:** Contraction (the ability to duplicate hypotheses) is what takes you from primitive recursion to full Peano Arithmetic. Without contraction, you can only do primitive recursion (bounded iteration). With contraction, you can encode unbounded search (minimization).

**Open question:** Whether there exists a direct, uniform translation from C to T in the presence of contraction.

### 8.2 Curzi & Das (LICS 2023)

Follow-up work extending to full fixed point operators:

- Curzi, G. & Das, A. "Computational expressivity of (circular) proofs with fixed points." LICS 2023, IEEE. doi:10.1109/LICS56636.2023.10175772

**Setting:** muLJ (intuitionistic logic with least and greatest fixed points) and its circular extension CmuLJ.

**Main result:** Both muLJ and CmuLJ represent exactly the first-order functions provably total in Pi^1_2-CA_0, a subsystem of second-order arithmetic beyond the "big five" of reverse mathematics. This is one of the strongest theories for which ordinal analysis exists.

### 8.3 Implications for CALC

The Curry-Howard correspondence for cyclic proofs means:
1. **Cyclic proofs ARE programs** -- specifically, typed goto programs. CALC's execution traces (with cycle detection) are already close to this.
2. **The trace condition IS termination** -- checking that a cyclic proof is valid is checking that the corresponding program terminates.
3. **Contraction controls complexity** -- if CALC restricts duplication of linear facts (which it already does by default), execution is primitive recursive. Allowing contraction (via `!`) enables full recursion.
4. **Proof extraction** -- from a cyclic proof of a property about CALC programs, one can extract a witness program (in System T) that demonstrates the property.

---

## Summary Table: All References

| # | Authors | Title | Venue | Year | DOI/URL |
|---|---------|-------|-------|------|---------|
| 1 | Baelde, Miller | Least and greatest fixed points in linear logic | LPAR | 2007 | doi:10.1007/978-3-540-75560-9_9 |
| 2 | Baelde | Least and greatest fixed points in linear logic | TOCL 13(1) | 2012 | doi:10.1145/2071368.2071370 |
| 3 | Fortier, Santocanale | Cuts for circular proofs | CSL | 2013 | doi:10.4230/LIPIcs.CSL.2013.248 |
| 4 | Baelde, Doumane, Saurin | Infinitary proof theory: the mult. add. case | CSL | 2016 | doi:10.4230/LIPIcs.CSL.2016.42 |
| 5 | Doumane | On the infinitary proof theory of logics with fixed points | PhD thesis | 2017 | irif.fr/~doumane/these.pdf |
| 6 | Nollet, Saurin, Tasson | Local validity for circular proofs in LL with FP | CSL | 2018 | doi:10.4230/LIPIcs.CSL.2018.35 |
| 7 | Nollet, Saurin, Tasson | PSPACE-completeness of thread criterion | FoSSaCS | 2019 | doi:10.1007/978-3-030-29026-9_18 |
| 8 | Gacek | The Abella interactive theorem prover | IJCAR | 2008 | doi:10.1007/978-3-540-71070-7_13 |
| 9 | Gacek, Miller, Nadathur | A two-level logic approach | JAR 49(2) | 2012 | doi:10.1007/s10817-011-9218-1 |
| 10 | Baelde, Gacek, Miller, Nadathur, Tiu | The Bedwyr system | CADE | 2007 | doi:10.1007/978-3-540-73595-3_28 |
| 11 | Lee, Jones, Ben-Amram | The size-change principle | POPL | 2001 | doi:10.1145/360204.360210 |
| 12 | Dershowitz, Manna | Proving termination with multiset orderings | CACM 22(8) | 1979 | doi:10.1145/359138.359142 |
| 13 | Fruhwirth | Constraint Handling Rules (book) | CUP | 2009 | ISBN 978-0-521-87776-3 |
| 14 | Sneyers, Van Weert, Schrijvers, Demoen | CHR survey 1998--2007 | TPLP 10(1) | 2010 | doi:10.1017/S1471068409990123 |
| 15 | Arts, Giesl | Termination using dependency pairs | TCS 236 | 2000 | doi:10.1016/S0304-3975(99)00207-8 |
| 16 | Giesl et al. | AProVE | RTA | 2004 | doi:10.1007/978-3-540-25979-4_15 |
| 17 | Brotherston, Simpson | Sequent calculi for induction and infinite descent | JLC 21(6) | 2011 | doi:10.1093/logcom/exq052 |
| 18 | Berardi, Tatsuta | Explicit induction not equiv. to cyclic proofs | arXiv | 2017 | arxiv:1712.09603 |
| 19 | Deng, Cervesato, Simmons | Relating reasoning in LL and process algebra | MSCS 26(5) | 2016 | doi:10.1017/S0960129514000218 |
| 20 | Sangiorgi | Introduction to Bisimulation and Coinduction | CUP | 2012 | ISBN 978-1-107-00363-7 |
| 21 | Kuperberg, Pinault, Pous | Cyclic proofs, system T, contraction | POPL | 2021 | doi:10.1145/3434282 |
| 22 | Curzi, Das | Computational expressivity of circular proofs with FP | LICS | 2023 | doi:10.1109/LICS56636.2023.10175772 |
| 23 | Baelde, Miller, Snow | Focused inductive theorem proving | IJCAR | 2010 | doi:10.1007/978-3-642-14203-1_24 |
| 24 | Girard, Scedrov, Scott | Bounded linear logic | TCS 97(1) | 1992 | doi:10.1016/0304-3975(92)90386-T |
| 25 | Clavel et al. | All About Maude | Springer | 2007 | doi:10.1007/978-3-540-71999-1 |
| 26 | Rosu | K: A semantic framework | Marktoberdorf | 2017 | fsl.cs.illinois.edu |
| 27 | Pilozzi, De Schreye | Proving termination of CHR in Prolog | WST | 2007 | -- |
| 28 | Acclavio, Curzi, Guerrieri | Infinitary cut-elimination via finite approx. | CSL | 2024 | doi:10.4230/LIPIcs.CSL.2024.8 |
| 29 | Das, De, Saurin | Decision problems for muMALL | FSCD | 2022 | doi:10.4230/LIPIcs.FSCD.2022.20 |
| 30 | Das, De, Saurin | Comparing infinitary systems | FSTTCS | 2023 | doi:10.4230/LIPIcs.FSTTCS.2023.40 |

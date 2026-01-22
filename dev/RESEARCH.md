# RESEARCH.md

This document tracks research goals, directions, knowledge base, and resources for reviving and extending the CALC linear logic proof system.

---

## Table of Contents

1. [Overview](#overview)
2. [Research Goals](#research-goals)
3. [Core Topics](#core-topics)
   - [Linear Logic Foundations](#linear-logic-foundations)
   - [Quantitative Type Theory (QTT)](#quantitative-type-theory-qtt)
   - [Graded Modal Types & Granule](#graded-modal-types--granule)
   - [Multimodal Linear Logic](#multimodal-linear-logic)
   - [Focusing & Proof Search](#focusing--proof-search)
   - [Cut Elimination](#cut-elimination)
   - [Substructural Operational Semantics](#substructural-operational-semantics)
4. [Related Systems & Implementations](#related-systems--implementations)
5. [Applications](#applications)
6. [Reading List](#reading-list)
7. [Open Questions](#open-questions)
8. [Research TODOs](#research-todos)

---

## Overview

This repository implements a proof calculus system for linear logic with:
- Dynamic parser generation from a JSON calculus specification
- Automated proof search with forward/backward chaining
- Focus/blur mechanism (based on Andreoli's focusing)
- Multi-format output (ASCII, LaTeX, Isabelle)

The goal is to evolve it into a modern, performant playground for substructural logics with potential applications in accounting/finance and resource-aware systems.

---

## Research Goals

### Meta-Goal: Validating the Intuition

**The core question:** Is there something genuinely significant hidden in linear logic and its extensions that few people see - or am I confused / intellectually masturbating?

**The intuition:** Linear logic, extended with quantitative types (semiring grading) and multimodalities (ownership/location), might be a foundational language for resource-aware systems - a kind of "type theory for economics" or "logic of ownership and exchange."

**Why this matters:** If true, this could unify:
- Accounting/double-entry bookkeeping
- Blockchain/smart contracts
- Capability systems
- Resource management (memory, energy, bandwidth)
- Economic modeling

**How to test this:**
1. Try to encode real examples - is the encoding natural or forced?
2. Can we prove useful properties that would be hard otherwise?
3. Do the extensions compose well, or do they fight each other?
4. Does the formalism reveal insights we wouldn't get otherwise?

**Reflection checkpoints:** Revisit this question regularly. Are we making progress toward clarity, or going in circles?

---

### Meta-Goal: Why Do Gentzen-Style Sequent Calculi Feel Significant?

**The question:** Beyond linear logic specifically, why does the Gentzen-style sequent calculus itself feel like "hidden knowledge"? What is it about this formalism that seems so fundamental?

**Possible reasons to investigate:**

1. **Symmetry and Duality**
   - Sequents make duality explicit: `Γ ⊢ Δ` shows both sides
   - Classical logic's symmetry becomes visible
   - Cut elimination reveals computational content on both sides

2. **Composition and Modularity**
   - Cut rule = composition of proofs
   - Proofs become first-class objects that can be combined
   - This is essentially the "API" of logical reasoning

3. **Resource Awareness Built-In**
   - The context management (what's on left/right) naturally tracks usage
   - Substructural logics fall out by restricting structural rules
   - This might be why it maps so well to computation and economics

4. **Proof Search = Computation**
   - Bottom-up proof search is a form of goal-directed computation
   - Focusing disciplines this into deterministic phases
   - This connects logic to programming in a deep way

5. **Universal Interface**
   - Many different logics can be expressed as sequent calculi
   - The "shape" of sequents is invariant; only rules change
   - Suggests sequents capture something fundamental about inference itself

**Questions to explore:**
- Is there a category-theoretic explanation for why sequents are "right"?
- How do sequent calculi relate to game semantics?
- Why did it take until Gentzen (1935) to discover this representation?
- What would a "more fundamental" representation look like, if one exists?

**Reading to pursue:**
- Girard's "Proofs and Types" - philosophical perspective
- Wadler's "Propositions as Sessions" - sequents and concurrency
- Game semantics literature - sequents as dialogue games

---

### Primary Goals

1. **Understand Gentzen-style calculi deeply** - Use as a sandbox for experimenting with different calculi, cut-elimination, interactive proofs

2. **Understand different semantics of linear logic** - Build deep intuition for all connectives through multiple semantic lenses:
   - **Resource semantics**: I have intuition for most connectives (tensor, lolli, with, plus, bang) but NOT for:
     - **Par (⅋)**: What is the resource interpretation? Why is it the dual of tensor?
     - **Why Not (?)**: Dual of bang, but what does it *mean*?
   - **Game semantics**: Linear logic as dialogue games between Proponent and Opponent
   - **Quantum semantics**: Connections to quantum computation and the !/?-modalities as "classical" control
   - **Coherence spaces / Phase semantics**: Girard's original denotational models
   - **Categorical semantics**: *-autonomous categories, linear/non-linear adjunctions

3. **Extend with quantitative types** - Move from binary linearity (use exactly once) to graded/quantitative linearity (use `n` times, where `n` can be any semiring element including real numbers)

4. **Explore multimodalities** - Understand how multiple modal operators can coexist and interact in linear logic

5. **Build towards practical applications** - Resource-aware accounting system, tracking trades across currencies with provable resource conservation

6. **Blockchain as linear logic ontology** - Explore whether LL + quantitative types + multimodalities can serve as a formal ontology for blockchain systems:
   - Can "ownership modalities" generalize to consensus algorithms?
   - Single authority: `[Alice] A` (Alice has sole control)
   - Multi-signature: `[Alice ∧ Bob] A` (both must agree)
   - Weighted voting: `[Alice:0.3, Bob:0.7] A` with threshold
   - Proof-of-Work: Modality earned through computational work
   - Proof-of-Stake: Modality weighted by staked tokens
   - Can we represent the *rules* of consensus as part of the logic itself?

### Secondary Goals

- Understand HCP (Hypersequent Calculus) and Display Calculi
- Explore connections to session types and concurrent programming

---

## Core Topics

### Linear Logic Foundations

**What is Linear Logic?**
Linear logic (Girard, 1987) is a substructural logic that treats propositions as resources. Unlike classical logic where `A` implies `A ∧ A` (contraction) and `A ∧ B` implies `A` (weakening), linear logic controls these structural rules.

**Key Connectives:**
- `A ⊗ B` (tensor) - multiplicative conjunction: "I have both A and B"
- `A ⅋ B` (par) - multiplicative disjunction
- `A & B` (with) - additive conjunction: "I can choose A or B"
- `A ⊕ B` (plus) - additive disjunction
- `A ⊸ B` (lollipop/lolli) - linear implication: "consuming A produces B"
- `!A` (bang/of course) - exponential: "unlimited copies of A"
- `?A` (why not) - dual exponential

**Polarity:**
- Positive formulas: `⊗`, `⊕`, `!`, atoms (bias toward right rules)
- Negative formulas: `⅋`, `&`, `?`, `⊸` (bias toward left rules)

**Understanding Par (⅋) and Why Not (?) - PRIORITY**

These are the connectives I lack intuition for:

**Par (⅋) - Multiplicative Disjunction:**
- De Morgan dual of tensor: `A ⅋ B = (A⊥ ⊗ B⊥)⊥`
- NOT "I have A or B" (that's ⊕)
- Possible interpretations to explore:
  - "A and B are available but entangled/dependent"
  - "Either A fails or B succeeds (or both)"
  - Game semantics: Opponent chooses, but both branches share resources
  - Session types: Parallel composition of sessions
  - Coherence spaces: Union of webs

**Why Not (?) - Exponential:**
- Dual of bang (!): `?A = (!A⊥)⊥`
- Structural rule: allows weakening/contraction on the LEFT
- Possible interpretations:
  - "Garbage collection" - can discard or duplicate
  - "Non-deterministic choice of how many A's to consume"
  - Classical control / continuations

**The Symmetry Puzzle:**
Classical linear logic is perfectly symmetric (every connective has a dual), but my resource intuition only works for one side. Understanding par/? requires either:
1. Finding a symmetric resource interpretation
2. Understanding why the asymmetry is fundamental
3. Using a different semantics (games, coherence spaces) where symmetry is clear

**Key Resource:**
- Frank Pfenning's course: https://www.cs.cmu.edu/~fp/courses/15836-f23/
- Combined lecture notes (248 pages) covering deductive inference, substructural hypotheses, cut elimination, session types, focusing

### Quantitative Type Theory (QTT)

**Core Idea:**
QTT extends dependent type theory by tracking how many times variables are used. Instead of just "linear" (exactly once), variables are annotated with multiplicities from a semiring.

**Semiring Structure:**
- Addition: models disjunctive usage (branching)
- Multiplication: models sequential composition
- Common semirings: `{0, 1, ω}` (erased/linear/unrestricted), natural numbers, real numbers

**Key Judgment:**
```
Γ ⊢ t : A
```
Where Γ contains multiplicity-annotated variables: `x :_r A` means "x has type A and is used r times"

**Idris 2 Implementation:**
Idris 2 is the first full implementation of QTT. Key insight: multiplicities on binders, not types, making combination with dependent types natural.

**Relevance to CALC:**
Current implementation has binary linearity (tracked via `num` in `linear_ctx`). Extension to QTT would allow:
- `2.123 A * 0.3 A ⊢ 2.423 A` (real-number quantities)
- Precise resource accounting
- Better modeling of partial consumption

**Key Papers:**
- McBride, "I Got Plenty o' Nuttin'" (2016) - original QTT
- Atkey, "Syntax and Semantics of Quantitative Type Theory" (2018)
- Brady, "Idris 2: Quantitative Type Theory in Practice" (ECOOP 2021)

### Graded Modal Types & Granule

**Beyond Simple Linearity:**
Granule extends linear logic with *graded modalities* - indexed families of modalities with algebraic structure.

**Key Syntax:**
```
a [n]  -- boxed value usable n times
twice : (a [c] -> b) [2] -> a [2 * c] -> (b, b)
```

**Three Built-in Modalities in Granule:**
1. **Resource bounds** - counting usage (like BLL)
2. **Security lattices** - information flow (Public/Private)
3. **Effects** - graded possibility for IO

**Coeffect Polymorphism:**
Functions can be polymorphic over grades, enabling generic programming over resource annotations.

**Relevance to CALC:**
Granule's approach is directly applicable to our quantitative extension goal. Their semiring-based grading generalizes naturally to real numbers for accounting.

**Key Papers:**
- Orchard et al., "Quantitative Program Reasoning with Graded Modal Types" (ICFP 2019)
- Vollmer et al., "A Mixed Linear and Graded Logic" (CSL 2025)

**Resources:**
- https://granule-project.github.io/granule.html
- Paper: https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf

### Multimodal Linear Logic

**Motivation:**
Different applications need different modal operators. Security needs "public" vs "private", distributed systems need "local" vs "remote", temporal logic needs "now" vs "later".

**Key Paper (ESORICS 2006):**
Garg, Bauer, Bowers, Pfenning, Reiter: "A Linear Logic of Authorization and Knowledge"
- Modal enrichment of linear logic for security policies
- Consumable authorizations as linear resources
- Cut elimination proven for the enriched logic

**Multimodal Systems:**
- Multiple indexed modalities: `□_i` for different modes
- Structural rules parameterized by mode
- Accessibility relations between modes

**Relevance to CALC:**
Multimodalities could model:
- Different accounts/wallets (each a mode)
- Different currencies (each a mode)
- Trust levels in authorization

**Resources:**
- https://link.springer.com/chapter/10.1007/11863908_19

### Focusing & Proof Search

**Andreoli's Focusing (1992):**
Discipline on proof search that consists of phases:
1. **Inversion phase**: Apply all invertible rules (no backtracking needed)
2. **Focus phase**: Choose a formula and apply non-invertible rules until atomic

**Polarity determines strategy:**
- Negative formulas: rules invertible on the right
- Positive formulas: rules invertible on the left

**Current CALC Implementation:**
`proofstate.js` implements focusing via:
- `getInvertableRule()` - finds formulas for inversion
- `focus()` / `blur()` - manages focused formula
- Polarity tracking in `ll.json`

**Key Papers:**
- Andreoli, "Logic Programming with Focusing Proofs in Linear Logic" (1992)
- Simmons, "Structural Focalization" (CMU thesis)

### Lax Modality (Understanding Required)

**Status:** Need to understand deeply - currently don't have good intuition.

**What is Lax?**
The lax modality `{A}` (also written `○A` or `A lax`) comes from Pfenning-Davies' reconstruction of modal logic via judgmental methodology. It's related to:
- Moggi's computational monad (monadic metalanguage)
- Possibility modality (◇) in modal logic
- "Eventual truth" or "achievable" propositions

**Syntactic Observations (from this codebase):**
```
{A}     -- monadic/lax formula
A lax   -- alternative syntax (internal representation)
Monad_R -- rule for introducing {A}
```

In the proof search (`proofstate.js`), lax triggers forward chaining:
```javascript
if(pt.conclusion.succedent.isLax() || o.mode === "proof") {
  // Enter forward chaining / focusing phase
}
```

**Key Questions to Answer:**
1. What is the categorical/denotational semantics of lax?
2. How does it relate to Haskell's IO monad / computational effects?
3. Why does it trigger forward chaining in proof search?
4. What is the relationship to CLF (Concurrent LF)?
5. How does it interact with linear resources?

**Intuition to Build:**
- Lax as "computation that produces A" vs "proof of A"
- Lax as "A is achievable through some process"
- Lax as demarcation between "logical" and "computational" phases

**Key Papers:**
- Pfenning & Davies, "A Judgmental Reconstruction of Modal Logic" (2001)
- Fairtlough & Mendler, "Propositional Lax Logic" (1997)
- Benton, Bierman, de Paiva, "Computational Types from a Logical Perspective" (1998)

**In CLF/Celf:**
The lax modality `{A}` in CLF means "A is achievable through forward chaining". Inside `{...}`, the system does goal-directed execution (state changes) rather than just proof construction.

---

### Cut Elimination

**Gentzen's Hauptsatz:**
Any sequent provable with the cut rule is provable without it.

**Significance:**
- Consistency: if `⊢ A` and `⊢ ¬A` both provable, cut gives `⊢ ⊥`
- Subformula property: cut-free proofs only use subformulas of the conclusion
- Normalization: corresponds to evaluation in the Curry-Howard view

**In Linear Logic:**
Cut elimination is well-behaved. On proof nets, it's particularly clean - local rewrite rules, linear time complexity.

**Relevance to CALC:**
- Implement cut elimination as a proof transformation
- Verify correctness of proof search by checking cut-freeness
- Study computational content via cut elimination = computation

**Resources:**
- https://www.cs.cmu.edu/~fp/courses/15317-f09/lectures/10-cutelim.pdf
- https://plato.stanford.edu/entries/logic-linear/

### Substructural Operational Semantics

**SSOS (Pfenning & Simmons, LICS 2009):**
Use substructural logic to specify programming language semantics.

**Key Insight:**
Linear logic's resource-awareness naturally models:
- State (linear propositions = current state)
- Concurrency (parallel composition via tensor)
- Communication channels (linear resources)

**Destination-Passing Style:**
Technique for encoding evaluation order via linear destinations.

**Features specifiable in SSOS:**
- Call-by-value, call-by-name, call-by-need
- Mutable store
- Parallelism and communication
- Exceptions and continuations

**Relevance to CALC:**
Long-term goal: use CALC as kernel for SSOS-style language semantics.

**Resources:**
- Pfenning & Simmons, "Substructural Operational Semantics as Ordered Logic Programming" (LICS 2009)
- https://www.cs.cmu.edu/~fp/papers/lics09.pdf

---

## Related Systems & Implementations

### Celf
- **What**: Implementation of CLF (Concurrent LF) type theory
- **Language**: Standard ML
- **Features**: Dependent types, linear types, monadic concurrency
- **Proof Search**: Focusing-based, forward-chaining
- **URL**: https://clf.github.io/celf/

### Ceptre
- **What**: Linear logic programming for narrative generation
- **Author**: Chris Martens (CMU thesis, 2015)
- **Features**: Forward-chaining, rule-based state transitions
- **Use Cases**: Games, interactive fiction, simulations
- **URL**: https://www.cs.cmu.edu/~cmartens/ceptre.pdf

### Granule
- **What**: Quantitative functional programming language
- **Features**: Graded modal types, coeffect polymorphism, Z3 integration
- **Language**: Haskell-like syntax
- **URL**: https://granule-project.github.io/

### Idris 2
- **What**: Dependently typed language with QTT
- **Features**: Multiplicities (0, 1, ω), erasure, linearity
- **URL**: https://www.idris-lang.org/

### Twelf
- **What**: LF implementation for mechanized metatheory
- **Features**: Higher-order abstract syntax, totality checking
- **URL**: http://twelf.org/

### Calculus Toolbox
- **What**: Tool for display calculi
- **Relevance**: Original inspiration for this repo
- **URL**: https://github.com/goodlyrottenapple/calculus-toolbox

---

## Applications

### Accounting & Finance

**Connection to Linear Logic:**
Double-entry bookkeeping has structural similarities to linear logic:
- Every transaction has dual effect (debit/credit) ↔ linear implication
- Resources cannot be created/destroyed ↔ no weakening/contraction
- Balance must be maintained ↔ proof consistency

**Quantitative Extension:**
With real-number quantities:
```
100 USD ⊗ 0.85 EUR/USD ⊢ 85 EUR
```
Currency conversion as linear transformation.

**Potential Features:**
- Provably balanced transactions
- Type-safe multi-currency accounting
- Audit trails as proof terms

### Resource-Aware Systems

- Memory management (like Rust but with proof terms)
- Capability systems (linear capabilities)
- Session types for protocols

---

## Reading List

### Essential (Start Here)

1. **Pfenning's 15-836 Lecture Notes** (248 pages)
   - https://www.cs.cmu.edu/~fp/courses/15836-f23/
   - Comprehensive introduction to substructural logics

2. **Girard's Original Paper** (1987)
   - "Linear Logic" - Theoretical Computer Science
   - The foundational paper

3. **Brady's Idris 2 Paper** (ECOOP 2021)
   - https://arxiv.org/abs/2104.00480
   - Practical QTT implementation

### Deep Dives

4. **Atkey's QTT Paper** (LICS 2018)
   - "Syntax and Semantics of Quantitative Type Theory"
   - Formal foundations of QTT

5. **Granule ICFP Paper** (2019)
   - "Quantitative Program Reasoning with Graded Modal Types"
   - Graded types in practice

6. **Pfenning & Simmons SSOS** (LICS 2009)
   - "Substructural Operational Semantics as Ordered Logic Programming"
   - Semantics via linear logic

7. **Andreoli's Focusing** (1992)
   - "Logic Programming with Focusing Proofs in Linear Logic"
   - Proof search foundation

### Advanced Topics

8. **Garg et al. Multimodal LL** (ESORICS 2006)
   - "A Linear Logic of Authorization and Knowledge"
   - Multimodalities for security

9. **Martens' Thesis** (CMU 2015)
   - "Programming Interactive Worlds with Linear Logic"
   - Ceptre and narrative generation

10. **Ciabattoni et al.** (Studia Logica 2014)
    - "Hypersequent and Display Calculi – a Unified Perspective"
    - Advanced proof systems

### Semantics (Par, Why Not, Quantum)

11. **Girard's Original Paper** (1987)
    - Phase semantics and coherence spaces
    - Original intuitions for all connectives including par

12. **Abramsky & Jagadeesan** (1994)
    - "Games and Full Completeness for Multiplicative Linear Logic"
    - Game semantics makes par intuitive

13. **Hyland & Ong** (2000)
    - "On Full Abstraction for PCF"
    - Game semantics foundations

14. **Mellies** (2009)
    - "Categorical Semantics of Linear Logic"
    - Survey of categorical models

15. **Abramsky & Coecke** (2004)
    - "A Categorical Semantics of Quantum Protocols"
    - Quantum mechanics via compact closed categories (related to linear logic)

### Lax Modality / Monadic Logic

16. **Pfenning & Davies** (2001)
    - "A Judgmental Reconstruction of Modal Logic"
    - Foundation for understanding lax/possibility modality

17. **Benton** (1995)
    - "A Mixed Linear and Non-Linear Logic"
    - LNL models, adjoint decomposition of !

18. **Watkins et al.** (2002)
    - "A Concurrent Logical Framework I: Judgments and Properties"
    - CLF foundation, explains lax/monadic fragment

### Blockchain & Distributed Ledger Systems

**Research Question:**
Can we model blockchain systems (e.g., Ethereum) using:
1. **Quantitative linear types** for fractional resources: `0.2321 BTC`
2. **Multimodalities for ownership/location**: `[Alice] 0.123 BTC`

**Potential Representation:**
```
[Alice] 0.5 BTC ⊗ [Bob] 0.3 ETH ⊢ [Alice] 0.3 ETH ⊗ [Bob] 0.5 BTC
```
This represents an atomic swap: Alice's BTC and Bob's ETH are exchanged.

**Key Modeling Questions:**
- Modes as wallet addresses/accounts
- Quantities as token amounts (fixed-point decimals)
- Transactions as linear implications with ownership transfer
- Smart contracts as parameterized rules

**Ethereum-Specific Considerations:**
- Gas fees as resource consumption
- Contract state as persistent linear context
- ERC-20 tokens as typed quantities
- Multi-signature as conjunctive modes

**Related Work:**
- Session types for smart contracts
- Nomos language (CMU) - linear types for blockchain
- Move language (Libra/Diem) - resource types

**Potential Calculus Rules:**
```
-- Transfer rule (consuming at source, producing at destination)
[A] n X ⊢ [B] n X    -- A sends n units of X to B

-- Atomic swap
[A] m X ⊗ [B] n Y ⊢ [A] n Y ⊗ [B] m X

-- Contract interaction (with gas)
[User] call ⊗ [User] g Gas ⊗ [Contract] state ⊢ [User] result ⊗ [Contract] state'
```

---

## Open Questions

1. **How to extend semiring to real numbers?**
   - What properties must the semiring satisfy?
   - How to handle division? (not semiring operation)
   - Approximation/rounding issues?

2. **Multimodality architecture:**
   - How to specify mode accessibility?
   - Runtime representation of modes?
   - Interaction between modes and quantities?

3. **Blockchain modeling:**
   - How to encode transaction atomicity?
   - Representing "anyone can send to address X"?
   - Modeling time/block ordering?
   - Handling non-determinism in contract execution?

3. **Performance at scale:**
   - Proof search complexity bounds?
   - Incremental proof checking?
   - Parallelization opportunities?

4. **Connections to Rust:**
   - Can we formalize Rust's ownership as linear logic?
   - Mutable borrows as affine types?

---

## Research TODOs

### Phase 0: Critical Understanding Gaps

- [ ] **Study Proof Nets in Depth** (HIGH PRIORITY)
  - [ ] What are proof nets? How do they relate to proof trees?
  - [ ] Understand "bureaucracy" problem in sequent calculus
  - [ ] Study correctness criteria (Danos-Regnier, others)
  - [ ] Understand sequentialization (proof net → sequent proof)
  - [ ] Connection to HCP (relevant to blockchain goals)
  - [ ] Can proof nets extend to modalities? (research frontier)
  - [ ] Viability for multimodal quantitative linear types
  - Key papers:
    - Girard's original proof nets (1987)
    - [Proof Nets for the Multimodal Lambek Calculus](https://www.semanticscholar.org/paper/Proof-Nets-for-the-Multimodal-Lambek-Calculus-Moot-Puite/c5d077d1e9e09fa7bf6a75d7c556838c6f06f7a7)
    - [A linear logic framework for multimodal logics](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/linear-logic-framework-for-multimodal-logics/E94D27CFB82C57E1C2F6E0FC65ECB243)
    - Laurent's introduction to proof nets

- [ ] **Understand Lax modality** - semantically and syntactically
  - [ ] Read Pfenning & Davies "Judgmental Reconstruction of Modal Logic"
  - [ ] Understand relationship to monads and computational effects
  - [ ] Understand why lax triggers forward chaining in proof search
  - [ ] Work through CLF/Celf examples

- [ ] **Understand Par (⅋) deeply**
  - [ ] Work through game semantics interpretation
  - [ ] Study coherence space semantics
  - [ ] Find examples where par is natural (session types?)

- [ ] **Understand Why Not (?) deeply**
  - [ ] Relate to classical control/continuations
  - [ ] Understand structural rule perspective

- [ ] **Explore quantum semantics of linear logic**
  - [ ] Read Abramsky & Coecke on categorical quantum mechanics
  - [ ] Understand !/?-modalities as "classical" control
  - [ ] Explore connections to quantum computing

### Phase 1: Foundations (Understanding)
- [ ] Re-read Pfenning's lecture notes completely
- [ ] Implement basic examples from the notes in current CALC
- [ ] Document exactly what current `ll.json` encodes
- [ ] Trace through proof search on concrete examples

### Phase 2: QTT Extension (Design)
- [ ] Study Idris 2's multiplicity implementation
- [ ] Design semiring-parameterized sequent structure
- [ ] Specify typing rules for quantitative extension
- [ ] Prototype real-number semiring

### Phase 3: Multimodalities (Exploration)
- [ ] Read Garg et al. paper thoroughly
- [ ] Understand mode/world accessibility
- [ ] Design JSON schema for multimodal calculi
- [ ] Implement simple two-mode example

### Phase 4: Applications (Building)
- [ ] Specify simple accounting example
- [ ] Currency conversion as linear transformation
- [ ] Multi-account ledger as multimodal system
- [ ] Transaction validation as proof search

### Phase 5: Blockchain Modeling
- [ ] Research Nomos language (CMU linear types for blockchain)
- [ ] Research Move language (resource types in Diem/Sui)
- [ ] Design ownership modalities for wallet addresses
- [ ] Model ERC-20 transfer as linear rule
- [ ] Implement atomic swap example
- [ ] Explore gas consumption as linear resource

---

## Notes & Scratchpad

*(Space for ongoing research notes)*

### 2026-01-21: Initial Research Survey

Completed initial survey of:
- Current codebase architecture
- Key papers and systems (Celf, Ceptre, Granule, Idris 2)
- Modern developments in QTT and graded types
- Tool alternatives for refactoring

Key insight: The move from binary linearity to quantitative/graded types is well-studied. Granule's approach (semiring-indexed modalities) aligns well with our real-number accounting goal.

The CSL 2025 paper "A Mixed Linear and Graded Logic" by Granule team is very recent and relevant - should prioritize reading.

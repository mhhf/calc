# CALC Research Index

**CALC** (Calculus for Accountable Linear Computations) explores the intersection of proof theory, linear logic, authorization, and financial modeling.

---

## The Central Question

> Can we design a proof calculus where resources are tracked exactly, ownership is explicit, quantities matter, and financial primitives have natural representations?

**Key Discovery:** Double-entry bookkeeping (Pacioli, 1494) is applied linear logic. Accountants have been doing resource-sensitive reasoning for 500+ years. CALC makes this connection formal.

**Three Orthogonal Dimensions of Resource Control:**

| Dimension | Concern | Mechanism |
|-----------|---------|-----------|
| **Structural** | Use pattern | Linear, affine, exponential |
| **Epistemic** | Who owns it? | `[Alice] A`, `[Bob] A` |
| **Quantitative** | How much? | `[]_r A` (graded modalities) |

**The Technical Challenge:** Display calculus elegantly handles structural modalities, but exponentials (!) lack residuals. Multi-type methodology (Greco & Palmigiano) offers a solution.

---

## I. Motivation: Why Linear Logic for Finance?

*Start here to understand the vision.*

### [[accounting-foundations]]
**The 500-Year Connection.** Mathematical foundations of accounting: Pacioli group, Grothendieck group, conservation laws. Plain text accounting systems (Ledger, hledger, Beancount). **Key insight:** PTA has been doing applied linear logic since the Renaissance.

**Tags:** `accounting` `double-entry` `Pacioli-group` `Grothendieck-group` `conservation` `linear-negation`

### [[linear-negation-debt]]
**Debt as Linear Negation.** `A⊥` = obligation to provide A. Settlement: `A ⊗ A⊥ ⊢ 1`. Connects to session type duality—channel endpoints are asset/liability pairs.

**Tags:** `linear-negation` `debt` `obligation` `settlement` `session-types` `game-semantics`

### [[financial-primitives]]
**What We Want to Model.** Financial derivatives in linear logic: options as additive choice (&), futures as deferred obligations, swaps as iterated atomic exchanges, markets as order collections.

**Tags:** `futures` `options` `swaps` `order-books` `auctions` `temporal-modalities` `Peyton-Jones`

---

## II. Key Insights

*The novel research contributions. Read after motivation.*

### [[insights]]
**Research Discoveries.**
1. **Pacioli group as grading structure** (potentially novel)
2. **Ownership as fibration, not mode** — principals form base category, resources are fibers
3. **Debt as channel** — unification of obligations and session types
4. **Coherence = consensus achievability** — compile-time guarantee of agreement
5. **Three-level structure** — structural × epistemic × quantitative modalities

**Tags:** `Pacioli-group` `fibration` `ownership` `session-types` `coherence` `three-level-structure`

---

## III. The Ownership Problem

*Core application domain: who can do what with resources?*

### [[ownership-design]]
**Comprehensive Design.** User-centric model: `[Alice] []_r token`. Transfer, split, merge, atomic swap rules. WITH clause for atomic contract creation with deposit.

**Tags:** `ownership` `user-centric` `transfer` `split` `merge` `atomic-swap` `contracts`

### [[authorization-logic]]
**Garg's Says Modality.** `A says φ` for principal affirmations. Linear vs exponential credentials. Composite principals (`A ∧ B`), speaks-for delegation.

**Tags:** `authorization` `says-modality` `principals` `delegation` `speaks-for` `credentials`

### [[consensus-modalities-mpst]]
**Multi-Party Consent.** How to express `[A ∧ B] φ` (both must agree). MPST's coherence generalizes binary duality. Threshold modalities (k-of-n) need predicates, not modalities.

**Tags:** `consensus` `multi-sig` `threshold` `MPST` `choreography` `coherence`

### [[ownership-as-session-types]]
**Partial Correspondence.** Can `[Alice] A` be expressed as session types? Linearity ✓, transfer ✓, principal identity ✗. They're complementary, not equivalent.

**Tags:** `session-types` `ownership` `Caires-Pfenning` `propositions-as-sessions` `channel-delegation`

---

## IV. Proof-Theoretic Foundations

*The theoretical backbone. Display calculus and beyond.*

### [[proof-calculi-foundations]]
**Hierarchy of Proof Systems.** Natural deduction → sequent calculus → display calculus. Why sequent calculus is "good" (uniform bottom-up reading, cut elimination). Curry-Howard correspondence.

**Tags:** `proof-calculi` `sequent-calculus` `display-calculus` `Curry-Howard` `cut-elimination` `deep-inference`

### [[display-calculus]]
**Belnap's Framework.** The C1-C8 conditions that guarantee cut elimination. Structural connectives and residuation. Why exponentials (!) break the display property.

**Tags:** `display-calculus` `Belnap` `C1-C8` `cut-elimination` `residuation` `proof-nets`

### [[residuation]]
**Galois Connections.** Why `A ⊗ B ⊢ C iff A ⊢ B ⊸ C`. Residuated lattices as the algebraic semantics. Fundamental for display postulates.

**Tags:** `residuation` `Galois-connection` `residuated-lattice` `adjunction` `display-postulates`

### [[exponential-display-problem]]
**The ! Problem.** Why bang lacks a residual and how this breaks display. Benton's LNL decomposition `! = F ∘ G` as the solution.

**Tags:** `exponential` `bang-modality` `display-property` `LNL` `Benton` `adjunction`

### [[logics-overview]]
**What Can Be Displayed?** Survey: CLL, ILL, FILL, FOL, multimodal, QTT, Granule. Research gap: display + graded + multi-type combined.

**Tags:** `CLL` `ILL` `FILL` `multimodal` `QTT` `Granule` `mGL` `research-gap`

---

## V. The Multi-Type Framework

*CALC's chosen approach: multiple formula types with adjunctions.*

### [[multi-type-display-calculus]]
**Greco & Palmigiano.** Framework for handling multiple formula types with adjunctions between them. How CALC implements LNL (persistent_ctx + linear_ctx). Parametric indices for ownership.

**Tags:** `MTDC` `multi-type` `Benton` `LNL` `F-functor` `G-functor` `adjunction`

### [[adjunctions-and-adjoint-logic]]
**Pfenning's Adjoint Logic.** Unit/counit, triangle identities, monads/comonads. Evaluation: use for structural properties, keep principals separate.

**Tags:** `adjunction` `adjoint-logic` `category-theory` `monad` `comonad` `modes`

### [[multimodal-linear-logic]]
**Three Modality Families.** Ownership `[Alice] A`, location `@L A`, graded `[]_r A`. Uses MTDC with parametric indices (not SELL). Orthogonal concerns.

**Tags:** `multimodal` `ownership` `location` `graded` `SELL` `subexponentials` `parametric-indices`

### [[graded-resource-tracking]]
**Quantitative Type Theory.** McBride's QTT, Atkey's fix, Granule, Idris 2. Object-level vs meta-level quantities. Decision: quantities are object-level terms.

**Tags:** `QTT` `quantitative-type-theory` `Granule` `Idris-2` `semiring` `multiplicities`

---

## VI. Related Paradigms

*Connections to session types, ludics, and logic programming.*

### [[nomos]]
**CMU's Session-Typed Contracts.** Nomos language: session types + linear types for smart contracts. Acquire-release prevents re-entrancy. Automatic gas analysis.

**Tags:** `Nomos` `session-types` `smart-contracts` `acquire-release` `AARA` `gas-analysis`

### [[ludics-and-orthogonality]]
**Girard's Post-Linear-Logic.** Ludics (proofs as strategies), Geometry of Interaction, orthogonality as agreement. N-ary extension via coherence.

**Tags:** `Ludics` `Girard` `orthogonality` `Geometry-of-Interaction` `focalization`

### [[clf-celf-ceptre]]
**Forward Chaining.** CLF (Concurrent LF) with lax monad `{A}`. Celf implementation. Ceptre for game mechanics. Lazy resource management.

**Tags:** `CLF` `Celf` `Ceptre` `forward-chaining` `lax-monad` `multiset-rewriting`

### [[bdi-framework]]
**Belief-Desire-Intention Agents.** Bratman's planning theory, Rao-Georgeff BDI logic (BDICTL + CTL*). Key insight: intentions are *linear* (consumed on execution), beliefs are *exponential* (persistent). Connects to Porello-Troquard's resource-sensitive agency and CALC's ownership modalities.

**Tags:** `BDI` `agents` `intentions` `Bratman` `Rao-Georgeff` `AgentSpeak` `linear-agency` `Porello-Troquard`

---

## VII. Implementation Design

*DSL, FFI, prover architecture.*

### [[DSL-approaches]]
**Specifying Sequent Calculi.** Comparison: Haskell embedding (Calculus Toolbox), external DSL (ll.json), typed DSL. Trade-offs in expressivity vs verification.

**Tags:** `DSL` `ll.json` `calculus-toolbox` `Isabelle` `Lean` `Twelf` `parser-generation`

### [[typed-dsl-logical-framework]]
**Logical Frameworks.** LF, CLF, Twelf, Celf influence on CALC's DSL. HOAS, adequacy. Three-file architecture (.calc/.rules/.mde).

**Tags:** `LF` `CLF` `Twelf` `Celf` `HOAS` `typed-DSL` `tree-sitter`

### [[higher-order-linear-types]]
**Can We Have `bar: ltype → ltype`?** Two interpretations: Cartesian HKT (use encoding) vs linear modalities (use indexed wrappers). Ownership IS an ltype → ltype operator.

**Tags:** `higher-kinded-types` `HKT` `type-operators` `linear-modalities` `indexed-wrappers`

### [[ffi-logics]]
**External Computation.** Twelf modes (+/-/*), Agda postulates, CLP constraints. Mode declarations specify information flow. Trust levels.

**Tags:** `FFI` `modes` `oracles` `CLP` `constraint-solving` `trusted-computing-base`

### [[prover-architecture]]
**LCF-Style Design.** Sledgehammer's parallel prover orchestration, Lean4's TacticM monad hierarchy. Trust levels for CALC.

**Tags:** `LCF` `de-Bruijn` `tacticals` `Sledgehammer` `TacticM` `proof-orchestration`

---

## VIII. Performance Engineering

*Making proof search fast.*

### [[content-addressed-formulas]]
**The Foundation.** Merkle-DAG hash consing: O(1) equality, structural sharing, lazy hashing. This enables all other optimizations.

**Tags:** `Merkle-DAG` `hash-consing` `content-addressing` `O(1)-equality` `structural-sharing`

### [[benchmarking]]
**What's Slow?** Current hotspots: mgu (O(n²)), toString comparisons, context hashing. Merkle-DAG impact analysis.

**Tags:** `benchmarking` `complexity-analysis` `profiling` `hotspots`

### Optimization Techniques

These documents detail specific optimizations; all build on content-addressed formulas:

| Document | Technique | Complexity Improvement |
|----------|-----------|----------------------|
| [[near-linear-unification]] | Martelli-Montanari + Union-Find | O(n²) → O(n·α(n)) |
| [[constructor-indexing]] | Index by outermost constructor | O(n) → O(1) lookup |
| [[polynomial-memoization]] | Cache (sequent → result) | Exponential → polynomial |
| [[explicit-substitutions]] | Lazy substitution evaluation | Defer O(n) work |
| [[persistent-data-structures]] | HAMT for sequents | O(n) copy → O(1) |
| [[backward-prover-optimization]] | Focusing, inversion, tabling | Various |

---

## IX. Semantic Foundations

*Deep theory: fibrations, term semantics.*

### [[fibrations-study-plan]]
**Ownership as Fibration.** Base category = principals, fibers = owned resources, reindexing = transfer. Study plan with reading order.

**Tags:** `fibrations` `Grothendieck` `dependent-types` `Lawvere` `reindexing`

### [[resource-term-semantics]]
**What Are Proof Terms?** Terms of `[Alice] coin(BTC, 0.5)` as audit trails carrying provenance.

**Tags:** `proof-terms` `audit-trail` `provenance` `Curry-Howard` `UTXO`

---

## X. Reference

### [[QnA]]
**Accessible Explanations.** Q&A-style treatment of proof theory concepts: structural connectives, display property, residuation, cut efficiency.

**Tags:** `tutorial` `structural-connectives` `display-property` `cut-elimination`

### [[logic_engineering]]
**Designing Logics.** Semantics-first vs syntax-first. Iterative refinement. Checklist for good sequent calculi.

**Tags:** `logic-engineering` `proof-theoretic-semantics` `harmony` `soundness`

### [[bibliography]]
**Citations.** Comprehensive bibliography organized by topic.

---

## Document Relationships

```
                           ┌─────────────────────┐
                           │     MOTIVATION      │
                           │  accounting ← debt  │
                           │         ↓           │
                           │   financial-prims   │
                           └─────────┬───────────┘
                                     │
              ┌──────────────────────┼──────────────────────┐
              ↓                      ↓                      ↓
   ┌──────────────────┐   ┌──────────────────┐   ┌──────────────────┐
   │    OWNERSHIP     │   │   FOUNDATIONS    │   │   RELATED WORK   │
   │  ownership-design│   │  proof-calculi   │   │     nomos        │
   │  authorization   │   │  display-calculus│   │     ludics       │
   │  consensus-mpst  │   │  residuation     │   │   clf-celf       │
   └────────┬─────────┘   │  exponential-!   │   │  bdi-framework   │
            │             └────────┬─────────┘   └──────────────────┘
            │                      │
            └──────────┬───────────┘
                       ↓
            ┌──────────────────────┐
            │   MULTI-TYPE FRMWK   │
            │  mtdc ← adjoint-logic│
            │  multimodal ← graded │
            └──────────┬───────────┘
                       ↓
            ┌──────────────────────┐
            │   IMPLEMENTATION     │
            │  DSL → prover-arch   │
            │  content-addressed   │
            │  ← all optimizations │
            └──────────────────────┘
```

---

## Research Status

### Novel Contributions (see [[insights]])

1. **Pacioli group as grading semiring** — accounting + graded types unification
2. **Ownership as fibration** — categorical semantics for `[P] A`
3. **Coherence = consensus** — compile-time multi-party agreement
4. **Linear BDI** — intentions as linear resources, beliefs as exponential (see [[bdi-framework]])

### Open Problems

| Problem | Status | See Document |
|---------|--------|--------------|
| Threshold modalities (k-of-n) | Predicate, not modality | [[consensus-modalities-mpst]] |
| Temporal modalities for derivatives | Unexplored | [[financial-primitives]] |
| Cyclic proofs for fixpoints | Mentioned, not developed | [[proof-calculi-foundations]] |

### Unexplored Directions

- **Comparative analysis:** CALC vs Move vs Nomos
- **Formal verification of CALC itself** in Lean/Agda
- **Hardware acceleration** for proof search
- **Linear BDI implementation:** Agent execution with linear intentions

---

*Last updated: 2026-02-10*

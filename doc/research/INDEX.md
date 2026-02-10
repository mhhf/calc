# Research Document Index

Cross-reference and summary of all research documents in dev/research/.

---

## Foundations

### [proof-calculi-foundations.md](proof-calculi-foundations.md)
Hierarchy of proof formalisms: natural deduction, sequent calculus, display calculus. Explains why sequent calculus is "good" (uniform bottom-up reading, cut elimination). Covers Curry-Howard correspondence and extends to linear logic.

**Sections:** [Logic vs Type Theory](#logic-vs-type-theory-whats-the-difference) · [Curry-Howard](#the-curry-howard-correspondence) · [Why Sequent Calculus is Good](#why-is-sequent-calculus-good) · [Why Display is Harder](#why-is-display-calculus-harder-than-sequent-calculus) · [Graded Modalities Gap](#why-dont-graded-modalities-have-display-calculi-yet) · [Hierarchy](#the-hierarchy-of-proof-systems) · [Deep Inference](#deep-inference) · [Cyclic Proofs](#cyclic-proofs) · [Proof Nets](#proof-nets)

**Tags:** `proof-calculi` `natural-deduction` `sequent-calculus` `display-calculus` `Curry-Howard` `Curry-Howard-Lambek` `cut-elimination` `subformula-property` `deep-inference` `cyclic-proofs` `proof-nets` `Gentzen` `hypersequent` `nested-sequent`

### [display-calculus.md](display-calculus.md)
Belnap's display calculus and the C1-C8 conditions that guarantee cut elimination. Explains why exponentials lack residuals (the ! problem) and how Greco & Palmigiano solve this via multi-type methodology.

**Sections:** [Executive Summary](#executive-summary) · [What is Display Calculus?](#what-is-display-calculus) · [Display Property](#the-display-property) · [Belnap's Conditions C1-C8](#belnaps-conditions-for-cut-elimination) · [Structural Connectives](#structural-connectives-and-residuation) · [Alternative Proof Calculi](#alternative-proof-calculi) · [Comparison Matrix](#comparison-matrix) · [Current Implementation Analysis](#analysis-of-current-implementation) · [Recommendations](#recommendations)

**Tags:** `display-calculus` `Belnap` `C1-C8` `cut-elimination` `structural-connectives` `residuation` `proof-nets` `deep-inference` `hypersequent` `nested-sequent` `labelled-sequent` `focused-proof-search` `calculus-toolbox`

### [residuation.md](residuation.md)
Comprehensive treatment of residuated lattices, Galois connections, and their connection to proof theory. Explains why `A ⊗ B ⊢ C iff A ⊢ B ⊸ C` and why this is fundamental for display postulates.

**Sections:** [What is Residuation?](#what-is-residuation) · [Galois Connections](#galois-connections) · [Residuated Lattices](#residuated-lattices) · [Connection to Display](#connection-to-display-calculus) · [Linear Logic](#residuation-in-linear-logic) · [Why ! Lacks Residual](#why-exponentials-lack-residuals)

**Tags:** `residuation` `Galois-connection` `residuated-lattice` `adjunction` `tensor-lolli` `display-postulates` `algebraic-semantics` `ordered-algebra` `intuitionistic-logic`

### [exponential-display-problem.md](exponential-display-problem.md)
Why the bang modality (!) doesn't have a residual and how this breaks the display property. Details Benton's LNL decomposition `! = F ∘ G` as the solution.

**Sections:** [Display Property Requirement](#the-display-property-requirement) · [What ! Would Need](#what-a-display-postulate-would-need) · [Impossibility Proof](#the-impossibility-proof) · [Why No f Can Exist](#why-no-such-f-can-exist) · [Can We Add Connectives?](#can-we-introduce-a-new-connective) · [Multi-Type Solution](#the-solution-multi-type-systems)

**Tags:** `exponential` `bang-modality` `display-property` `residual` `LNL` `Benton` `adjunction` `multi-type` `promotion-rule` `contraction`

### [logics-overview.md](logics-overview.md)
Survey of which logics can be expressed via display calculus: CLL, ILL, FILL, FOL, multimodal, QTT, Granule. Identifies research gap combining display + graded + multi-type.

**Sections:** [Summary Table](#summary-table) · [CLL](#1-classical-linear-logic-cll) · [ILL](#2-intuitionistic-linear-logic-ill) · [FILL](#3-full-intuitionistic-linear-logic-fill) · [FOL](#4-first-order-logic-fol) · [Multimodal](#5-multimodal-logic) · [QTT](#6-quantitative-type-theory-qtt) · [Granule](#7-graded-modal-types-granule) · [mGL](#8-mixed-linear-and-graded-logic-mgl) · [Conclusions](#conclusions-for-your-project)

**Tags:** `CLL` `ILL` `FILL` `BiILL` `FOL` `multimodal` `QTT` `Granule` `mGL` `hypersequent` `display-calculus` `Restall` `Greco-Palmigiano` `research-gap`

---

## Multi-Type and Modal Extensions

### [multi-type-display-calculus.md](multi-type-display-calculus.md)
Greco & Palmigiano's framework for handling multiple formula types with adjunctions between them. The approach CALC uses for LNL (persistent_ctx + linear_ctx). Covers parametric indices for ownership modalities.

**Sections:** [Executive Summary](#executive-summary) · [CALC's Implementation](#calcs-current-implementation) · [Benton's LNL](#bentons-lnl-model) · [F and G Functors](#the-f-and-g-functors) · [MTDC Theory](#multi-type-display-calculus-theory) · [Calculus-Toolbox-2](#calculus-toolbox-2-approach) · [Analysis](#analysis-can-special-rules-be-generalized) · [Alternatives](#alternatives-for-generalization)

**Tags:** `MTDC` `multi-type` `Benton` `LNL` `persistent_ctx` `linear_ctx` `F-functor` `G-functor` `adjunction` `calculus-toolbox-2` `labelled-sequents` `adjoint-logic` `cyclic-proofs`

### [adjunctions-and-adjoint-logic.md](adjunctions-and-adjoint-logic.md)
Comprehensive treatment of categorical adjunctions and Pfenning's adjoint logic. Covers unit/counit, triangle identities, monads/comonads, LNL decomposition. Evaluates adjoint logic as CALC's foundation and concludes: use for structural properties, keep principals separate.

**Sections:** [Categorical Adjunctions](#categorical-adjunctions) · [Key Examples](#key-examples-of-adjunctions) · [Monads/Comonads](#adjunctions-monads-and-comonads) · [Proof-Theoretic View](#proof-theoretic-view) · [Adjoint Logic](#adjoint-logic) · [What It Unifies](#what-adjoint-logic-unifies) · [Fibrational Framework](#the-fibrational-framework) · [Graded Adjoint Logic](#graded-adjoint-logic) · [Relevance to CALC](#relevance-to-calc)

**Tags:** `adjunction` `adjoint-logic` `category-theory` `functors` `unit` `counit` `monad` `comonad` `LNL` `Benton` `Pfenning` `modes` `structural-properties` `weakening` `contraction` `upshift` `downshift` `fibration` `graded-types`

### [multimodal-linear-logic.md](multimodal-linear-logic.md)
Design for CALC's multimodal system: ownership `[Alice] A`, location `@L A`, graded `[]_{r} A`. Uses MTDC with parametric indices (not SELL). Three orthogonal modality families.

**Sections:** [Core Question](#1-the-core-question) · [Three Modality Families](#2-three-families-of-modalities) · [Modalities vs Parameters](#3-modalities-vs-parameters-expressiveness-comparison) · [Interaction](#4-how-modalities-interact) · [Combining Modalities](#5-combining-modalities) · [Negation](#6-negation-of-modalities) · [MTDC Evaluation](#7-multi-type-display-calculus-evaluation) · [Implementation](#8-implementation-design)

**Tags:** `multimodal` `ownership` `location` `graded` `SELL` `subexponentials` `parametric-indices` `MTDC` `composite-principals` `transfer` `settlement` `mmll.family`

### [graded-resource-tracking.md](graded-resource-tracking.md)
Quantitative Type Theory (QTT) and graded modal types. Covers McBride's original, Atkey's fix, Granule, Idris 2. Object-level vs meta-level quantities. Key decision: quantities are object-level terms with lazy storage.

**Sections:** [What is QTT?](#what-is-qtt) · [Semiring Structure](#the-semiring-structure) · [Typing Rules](#typing-rules) · [QTT vs Granule](#qtt-vs-granule) · [Object vs Meta-Level](#object-level-vs-meta-level-quantities) · [QTT vs MTDC](#qtt-vs-multi-type-display-calculus) · [Implementations](#implementations) · [Relevance to CALC](#relevance-to-calc)

**Tags:** `QTT` `quantitative-type-theory` `graded-types` `semiring` `Granule` `Idris-2` `McBride` `Atkey` `multiplicities` `erasure` `zero-one-many` `object-level` `modalities` `graded-comonads`

---

## Authorization and Ownership

### [authorization-logic.md](authorization-logic.md)
Garg's `A says φ` modality for principal affirmations. Linear vs exponential credentials. Composite principals (`A ∧ B`), speaks-for delegation. See `dev/ownership-authorization-plan.md` for implementation plan.

**Sections:** [Executive Summary](#executive-summary) · [The Says Modality](#the-says-modality) · [Linear Authorization](#garg-et-als-linear-authorization-logic) · [BL Family](#the-bl-family-of-authorization-logics) · [Key Concepts](#key-authorization-concepts) · [Composite Principals](#composite-principals-and-thresholds) · [Related Systems](#related-systems)

**Tags:** `authorization` `says-modality` `principals` `delegation` `speaks-for` `controls` `composite-principals` `multi-sig` `threshold` `credentials` `linear-credentials` `ABLP` `BL-family` `Garg` `Pfenning`

### [ownership-design.md](ownership-design.md)
Comprehensive design for digital asset ownership. User-centric model: `[Alice] []_r token`. Transfer, split, merge, atomic swap rules. WITH clause for atomic contract creation with deposit.

**Sections:** [The Problem](#the-problem) · [Design Space](#design-space) · [Core Question](#the-core-question) · [User-Centric Ownership](#user-centric-ownership) · [Fresh Names](#fresh-names-and-resource-creation) · [Contracts and State](#contracts-and-internal-state) · [Minimal Core](#the-minimal-core) · [Worked Examples](#worked-examples) · [Remaining Challenges](#remaining-challenges)

**Tags:** `ownership` `user-centric` `coin` `transfer` `split` `merge` `atomic-swap` `WITH-clause` `fresh-names` `minting` `contracts` `deposit` `escrow` `AMM` `Move` `conservation`

### [ownership-as-session-types.md](ownership-as-session-types.md)
Explores whether `[Alice] A` can be expressed as session types. Partial correspondence: linearity ✓, transfer ✓, principal identity ✗. Recommends keeping them complementary.

**Sections:** [Core Question](#the-core-question) · [Two Correspondences](#background-two-correspondences) · [Attempting Correspondence](#attempting-the-correspondence) · [What ST Captures](#what-session-types-do-capture) · [What ST Doesn't](#what-session-types-dont-capture) · [Synthesis Approaches](#possible-synthesis-three-approaches) · [MPST Connection](#connection-to-mpst-and-global-types) · [Conclusions](#conclusions)

**Tags:** `session-types` `ownership` `Caires-Pfenning` `Wadler` `propositions-as-sessions` `adjoint-logic` `modes` `channel-delegation` `MPST` `multiparty` `principal-identity`

### [consensus-modalities-mpst.md](consensus-modalities-mpst.md)
How to express `[A ∧ B] φ` (both must consent). MPST's coherence generalizes binary duality. Threshold modalities explode combinatorially — use predicate not modality.

**Sections:** [Core Question](#the-core-question) · [Composite Principals](#background-composite-principals-in-authorization-logic) · [MPST Overview](#multiparty-session-types-mpst-overview) · [Additive Choice](#additive-choice-with-multiple-principals-who-chooses) · [Consensus Gap](#the-gap-consensus-in-mpst) · [Threshold Modalities](#threshold-modalities-2-of-3-1-of-4-etc) · [Coherence/Orthogonality](#coherence-and-orthogonality) · [Ludics](#ludics-as-theoretical-foundation) · [Recommendations](#recommendations-for-calc)

**Tags:** `consensus` `composite-principals` `multi-sig` `threshold` `MPST` `multiparty-session-types` `choreography` `coherence` `orthogonality` `ludics` `agreement` `voting`

---

## Session Types and Concurrency

### [nomos.md](nomos.md)
CMU's Nomos language: session types + linear types for smart contracts. Acquire-release discipline prevents re-entrancy. Automatic gas analysis. Connection to adjoint logic via `/\` and `\/`.

**Sections:** [Propositions-as-Sessions](#the-propositions-as-sessions-correspondence) · [Session Type Syntax](#session-type-syntax) · [Re-entrancy Prevention](#re-entrancy-prevention-acquire-release-discipline) · [Asset Tracking](#asset-tracking-with-linear-types) · [AARA Gas Analysis](#resource-aware-types-automatic-gas-analysis) · [Deadlock Freedom](#deadlock-freedom) · [Adjoint Logic](#adjoint-logic-foundation) · [Rast](#rast-resource-aware-session-types)

**Tags:** `Nomos` `session-types` `smart-contracts` `acquire-release` `re-entrancy` `DAO-hack` `linear-types` `AARA` `gas-analysis` `Caires-Pfenning` `propositions-as-sessions` `adjoint-logic` `Move` `Rast`

### [ludics-and-orthogonality.md](ludics-and-orthogonality.md)
Girard's post-linear-logic work: Ludics (proofs as interactive strategies), Geometry of Interaction (proofs as operators), Transcendental Syntax. Orthogonality as agreement model. N-ary extension via MCP coherence.

**Sections:** [Girard's Trajectory](#girards-research-trajectory) · [Geometry of Interaction](#geometry-of-interaction) · [Ludics Core](#ludics-core-concepts) · [Orthogonality](#orthogonality-and-behaviours) · [Consensus](#orthogonality-as-agreementconsensus) · [N-ary Gap](#the-n-ary-orthogonality-gap) · [Transcendental Syntax](#transcendental-syntax) · [Relevance to CALC](#relevance-to-calc)

**Tags:** `Ludics` `Girard` `orthogonality` `behaviours` `designs` `focalization` `polarity` `Geometry-of-Interaction` `GoI` `Transcendental-Syntax` `coherence` `MCP` `consensus` `game-semantics`

---

## Forward Chaining and Logic Programming

### [clf-celf-ceptre.md](clf-celf-ceptre.md)
CLF (Concurrent LF): linear LF with lax monad `{A}` for forward chaining. Celf implementation. Ceptre for game mechanics. Lazy resource management via input/output contexts.

**Sections:** [CLF Overview](#1-clf-concurrent-logical-framework) · [Celf Implementation](#2-celf-implementation-of-clf) · [Ceptre for Games](#3-ceptre-linear-logic-for-gamesinteractivity) · [LolliMon Bridge](#4-lollimon-bridge-between-lolli-and-clf) · [What CALC Needs](#5-what-calc-v2-needs) · [Implementation Roadmap](#6-implementation-roadmap)

**Tags:** `CLF` `Celf` `Ceptre` `forward-chaining` `lax-monad` `quiescence` `stages` `multiset-rewriting` `linear-logic-programming` `game-mechanics`

### [ffi-logics.md](ffi-logics.md)
FFI integration patterns: Twelf modes (+/-/*), Agda postulates, CLP constraint solvers. Mode declarations specify information flow. Trust levels for external computations.

**Sections:** [The Problem](#the-problem) · [Existing Systems](#approaches-in-existing-systems) · [Mode Declarations](#mode-declarations) · [Constraint Logic Programming](#constraint-logic-programming) · [Proof Assistants & FFI](#proof-assistants-and-ffi) · [Oracle Predicates](#oracle-predicates) · [Design for CALC](#design-for-calc) · [Security](#security-considerations)

**Tags:** `FFI` `modes` `oracles` `CLP` `constraint-solving` `Prolog` `Twelf` `Agda` `postulates` `trusted-computing-base` `verification`

### [prover-architecture.md](prover-architecture.md)
LCF-style architecture, Sledgehammer's parallel prover orchestration, Lean4's TacticM monad hierarchy. Trust levels for CALC. Current implementation analysis.

**Sections:** [LCF and de Bruijn](#lcf-architecture-and-de-bruijn-criterion) · [Lazy Resource Management](#lazy-resource-management-for-linear-logic) · [Tacticals](#tacticals-and-composition) · [Sledgehammer](#sledgehammer-parallel-prover-orchestration) · [Monad Hierarchies](#monad-hierarchies) · [Architecture Options](#architecture-options-for-calc) · [CALC Implementation](#calcs-current-implementation)

**Tags:** `LCF` `de-Bruijn` `trusted-kernel` `tacticals` `Sledgehammer` `relevance-filter` `MePo` `MaSh` `TacticM` `Ltac2` `proof-orchestration` `trust-levels` `focusing` `Hodas-Miller`

---

## Financial Modeling

### [accounting-foundations.md](accounting-foundations.md)
Mathematical foundations of accounting: Pacioli group, Grothendieck group, graph theory, linear algebra. Plain text accounting systems (Ledger, hledger, Beancount). Deep connection to linear logic. Key insight: PTA has been doing applied linear logic for 500+ years.

**Sections:** [Pacioli Group](#the-pacioli-group) · [Grothendieck Group](#the-grothendieck-group) · [Graph-Theoretic View](#graph-theoretic-view) · [Linear Algebra](#linear-algebra-formulation) · [Plain Text Accounting](#plain-text-accounting-systems) · [Connection to Linear Logic](#connection-to-linear-logic) · [Connection to CALC](#connection-to-calc) · [Open Questions](#open-questions)

**Tags:** `accounting` `double-entry` `Pacioli-group` `Grothendieck-group` `K-theory` `graph-theory` `linear-algebra` `incidence-matrix` `plain-text-accounting` `Ledger` `hledger` `Beancount` `conservation` `linear-negation` `debt` `liabilities` `category-theory`

### [linear-negation-debt.md](linear-negation-debt.md)
Debt as linear negation: `A⊥` = obligation to provide A. Settlement: `A ⊗ A⊥ ⊢ 1`. Connects to session type duality — channel endpoints are asset/liability.

**Sections:** [Overview](#overview) · [Formal Properties](#the-formal-properties) · [Interpretations of A⊥](#interpretations-of-a) · [Debt Interpretation](#the-debt-interpretation) · [Application to CALC](#application-to-calc) · [Connection to Accounting](#connection-to-accounting) · [Classical vs Intuitionistic](#classical-vs-intuitionistic-linear-logic) · [Game-Semantic Perspective](#game-semantic-perspective)

**Tags:** `linear-negation` `debt` `obligation` `settlement` `involution` `De-Morgan` `session-types` `game-semantics` `CLL` `ILL` `asset-liability` `Girard` `orthogonality`

### [financial-primitives.md](financial-primitives.md)
Modeling financial derivatives and market mechanisms in linear logic. Options as additive choice (&), futures as deferred obligations, swaps as iterated atomic swaps, markets as order collections.

**Sections:** [Overview](#overview) · [Futures Contracts](#1-futures-contracts) · [Options](#2-options) · [Swaps](#3-swaps-interest-rate-currency-etc) · [Leverage](#4-leverage) · [Markets/Order Books](#5-markets--order-books) · [Auctions](#6-auctions) · [Summary](#summary-what-maps-naturally) · [Features CALC Needs](#what-additional-features-calc-needs) · [Peyton-Jones Combinators](#the-peyton-jones-combinators)

**Tags:** `financial-primitives` `futures` `options` `swaps` `leverage` `order-books` `auctions` `temporal-modalities` `Peyton-Jones` `contract-DSL` `oracles` `additive-choice` `LexiFi` `ACTUS`

---

## DSL and Implementation

### [DSL-approaches.md](DSL-approaches.md)
Comparison of approaches for specifying sequent calculi: Haskell embedding (Calculus Toolbox), external DSL (ll.json), typed DSL. Trade-offs in expressivity vs verification.

**Sections:** [Current ll.json Approach](#current-approach-lljson) · [Calculus-Toolbox-2 DSL](#calculus-toolbox-2-dsl) · [Isabelle/HOL](#isabellehol) · [Lean 4](#lean-4) · [Twelf/LF](#twelflf) · [Agda](#agda) · [YAML/TOML DSL](#yamltoml-based-dsl) · [Granule-style](#granule-style) · [Comparison Matrix](#comparison-matrix) · [Recommendations](#recommendations)

**Tags:** `DSL` `ll.json` `calculus-toolbox` `Isabelle` `Lean` `Twelf` `LF` `Agda` `YAML` `Granule` `quantitative-types` `proof-search` `parser-generation`

### [typed-dsl-logical-framework.md](typed-dsl-logical-framework.md)
Logical frameworks (LF, CLF, Twelf, Celf) and their influence on CALC's DSL design. Covers HOAS, adequacy, Extended Celf syntax. Three-file architecture (.calc/.rules/.mde).

**Sections:** [Executive Summary](#executive-summary) · [Logical Frameworks](#logical-frameworks) · [optimism-mde DSL](#the-optimism-mde-dsl) · [Design Decisions](#design-decisions) · [References](#references)

**Tags:** `LF` `CLF` `Twelf` `Celf` `HOAS` `adequacy` `typed-DSL` `tree-sitter` `annotations` `three-file-architecture` `calculus-toolbox-2`

### [higher-order-linear-types.md](higher-order-linear-types.md)
Can we have `bar: ltype -> ltype`? Two interpretations: (A) Cartesian HKT (use encoding), (B) Linear modalities (use indexed wrappers). Ownership IS an ltype → ltype operator.

**Sections:** [Executive Summary](#executive-summary) · [Quick Answer](#quick-answer) · [Three-Level Hierarchy](#1-the-three-level-hierarchy) · [Built-in Type Operators](#2-built-in-type-operators) · [Approaches to HKT](#3-approaches-to-higher-kinded-linear-types) · [Second-Order Linear Logic](#4-second-order-linear-logic) · [What CALC Has](#5-what-calc-currently-has) · [Recommendations](#6-recommendations-for-calc) · [Linear Modalities](#7-linear-modalities-interpretation-b)

**Tags:** `higher-kinded-types` `HKT` `type-operators` `linear-modalities` `System-Fω` `System-F°` `LF` `CLF` `Celf` `indexed-wrappers` `subexponentials` `ownership-modality` `second-order`

### [content-addressed-formulas.md](content-addressed-formulas.md)
Merkle-DAG hash consing for formulas. O(1) equality, structural sharing, lazy hashing. Detailed complexity analysis showing n× speedup on all hot-path operations.

**Sections:** [Problem Statement](#problem-statement) · [Current Analysis](#current-implementation-analysis) · [Merkle-DAG Approach](#chosen-approach-merkle-dag-hash-consing) · [Hash Function Selection](#hash-function-selection) · [Implementation](#merkle-dag-hash-consing-implementation) · [Memory Management](#memory-management-strategies) · [Substitution](#substitution-in-merkle-dag-store) · [Complexity Analysis](#complexity-analysis)

**Tags:** `Merkle-DAG` `hash-consing` `content-addressing` `rapidhash` `structural-sharing` `interning` `O(1)-equality` `GC` `arena-allocation`

---

## Optimization

### [benchmarking.md](benchmarking.md)
Comprehensive benchmarking strategy: micro-benchmarks, proof search benchmarks, GC analysis. Current hotspots: mgu (O(n²)), toString comparisons, context hashing. Merkle-DAG impact analysis.

**Sections:** [Primitive Operations](#part-1-primitive-operations-catalog) · [Call Graph Analysis](#part-2-call-graph-analysis) · [Complexity Summary](#part-3-complexity-summary)

**Tags:** `benchmarking` `complexity-analysis` `profiling` `hotspots` `mgu` `substitution` `hash-consing` `GC` `performance`

### [polynomial-memoization.md](polynomial-memoization.md)
Memoization for proof search: cache (sequent → proof result). Polynomial complexity for repeated subproofs via subformula property.

**Sections:** [Exponential Problem](#1-the-problem-exponential-proof-search) · [Subformula Property](#2-the-subformula-property-bounding-the-search-space) · [Polynomial Bound](#3-from-subformula-property-to-polynomial-bound) · [Memoization Principle](#4-memoization-computing-each-sequent-once) · [Merkle-DAG Implementation](#5-implementing-memoization-with-merkle-dag) · [Before/After Example](#6-concrete-example-before-and-after-memoization) · [Complexity Analysis](#8-complexity-analysis)

**Tags:** `memoization` `subformula-property` `polynomial-time` `proof-search` `caching` `hash-consing` `cut-elimination` `hit-rate` `orthologic` `exponential-blowup`

### [constructor-indexing.md](constructor-indexing.md)
O(1) identity rule lookup via indexing formulas by outermost constructor. Speeds up the common case of failing identity checks.

**Sections:** [The Problem](#1-the-problem-identity-rule-is-the-hot-path) · [Key Insight](#2-the-key-insight-unification-prerequisites) · [Index Design](#3-constructor-index-design) · [Fast Lookup](#4-fast-identity-lookup) · [Merkle-DAG Integration](#6-integration-with-merkle-dag) · [Implementation](#7-complete-implementation) · [Performance Analysis](#8-performance-analysis)

**Tags:** `optimization` `identity-rule` `constructor-indexing` `term-indexing` `hash-lookup` `unification` `proof-search` `Merkle-DAG`

### [near-linear-unification.md](near-linear-unification.md)
Martelli-Montanari algorithm for near-linear unification. Current O(n²) due to toString comparisons; with Union-Find becomes O(n α(n)).

**Sections:** [Current Analysis](#1-current-implementation-analysis) · [Martelli-Montanari](#2-the-martelli-montanari-algorithm) · [Union-Find](#3-union-find-data-structure) · [Near-Linear Algorithm](#4-near-linear-unification-with-union-find) · [CALC Implementation](#5-detailed-implementation-for-calc) · [Before/After](#6-comparison-before-and-after) · [Merkle-DAG Integration](#7-integration-with-merkle-dag)

**Tags:** `unification` `Martelli-Montanari` `Union-Find` `path-compression` `union-by-rank` `O(n·α(n))` `inverse-Ackermann` `occurs-check` `mgu` `hash-equality`

### [explicit-substitutions.md](explicit-substitutions.md)
Lazy substitution evaluation: defer application until needed. Analogous pattern to lazy primitive storage.

**Sections:** [Problem: Eager Substitution](#1-the-problem-eager-substitution-is-expensive) · [Core Concept](#2-explicit-substitutions-core-concept) · [Closures Implementation](#3-implementation-closures) · [Sequent with Closures](#4-sequent-with-closures) · [Strategic Forcing](#5-when-to-force-strategic-forcing) · [Merkle-DAG Integration](#7-integration-with-merkle-dag) · [Complexity Analysis](#8-complexity-analysis) · [Recommendation](#10-recommendation)

**Tags:** `explicit-substitutions` `lazy-evaluation` `closures` `environment` `forcing` `deferred-computation` `optimization` `lambda-sigma`

### [persistent-data-structures.md](persistent-data-structures.md)
HAMT (Hash Array Mapped Trie) for O(1) sequent "copying" via structural sharing. Eliminates O(m·n) copy cost. Free backtracking.

**Sections:** [The Problem](#1-the-problem-copying-is-expensive) · [Core Concept](#2-persistent-data-structures-core-concept) · [HAMT](#3-hamt-hash-array-mapped-trie) · [Proof Search](#4-application-to-proof-search) · [Complexity Comparison](#5-complexity-comparison) · [Merkle-DAG Integration](#6-integration-with-merkle-dag) · [Implementation](#7-implementation-options)

**Tags:** `HAMT` `persistent-data-structures` `structural-sharing` `path-copying` `immutable` `Immutable.js` `COW` `backtracking` `bitmap` `popcount` `Bagwell`

### [backward-prover-optimization.md](backward-prover-optimization.md)
Strategies for backward chaining prover: focusing, inversion, identity checks. Current implementation analysis.

**Sections:** [Bottleneck Analysis](#current-bottleneck-analysis) · [Simultaneous Substitution](#1-simultaneous-substitution-highest-impact) · [Union-Find](#2-union-find-unification) · [Triangular Substitution](#3-triangular-substitution) · [Tabling](#4-tablingmemoization) · [Explicit Substitutions](#6-explicit-substitutions-λσ-calculus) · [E-graphs](#7-e-graphs--congruence-closure)

**Tags:** `optimization` `unification` `substitution` `union-find` `triangular-substitution` `tabling` `memoization` `hash-consing` `e-graphs` `de-Bruijn` `proof-search`

---

## Semantic Foundations

### [fibrations-study-plan.md](fibrations-study-plan.md)
Study plan for fibrations as ownership semantics. Base category = principals, fibers = owned resources, reindexing = transfer. Lawvere correspondence: fibrations ≈ dependent types.

**Sections:** [Why Fibrations for CALC?](#why-fibrations-for-calc) · [Prerequisites](#prerequisites-what-you-need-first) · [Intuition First](#the-intuition-first) · [Study Path](#study-path) · [Reading Order](#reading-order-summary) · [Concepts Checklist](#key-concepts-checklist) · [Applies to CALC](#how-this-applies-to-calc)

**Tags:** `fibrations` `Grothendieck` `categorical-semantics` `dependent-types` `Lawvere` `ownership` `reindexing` `base-category` `fibers` `cartesian-morphisms` `Jacobs` `Vistoli` `study-plan`

### [resource-term-semantics.md](resource-term-semantics.md)
What are proof terms of `[Alice] coin(BTC, 0.5)`? Audit trail interpretation: terms carry provenance (where resource came from). CAU calculus reference.

**Sections:** [The Question](#the-question) · [Perspectives](#perspectives-on-term-semantics) · [Audit Trails](#terms-as-receipts--audit-trails) · [Linear Logic](#linear-logic-perspective) · [Terms in CALC](#what-terms-could-be-in-calc) · [Blockchain Connection](#connection-to-blockchain) · [Open Questions](#open-questions)

**Tags:** `proof-terms` `audit-trail` `provenance` `CAU` `realizability` `UTXO` `trail-annotation` `Curry-Howard` `game-semantics` `coherence-spaces`

### [insights.md](insights.md)
Key research discoveries: Pacioli group as grading structure, ownership as fibration (not mode), debt as channel, three-level structure (structural × epistemic × quantitative).

**Sections:** [Pacioli Group as Grading](#1-pacioli-group-as-grading-ring--potentially-novel) · [Ownership as Fibration](#2-ownership-as-fibration-not-mode) · [Debt as Channel](#3-debt-as-channel--unification-of-debt-and-session-types) · [MPST for Authorization](#4-mpst-methodology-for-authorization) · [Coherence = Consensus](#5-coherence--consensus-achievability--compile-time-guarantee) · [Three-Level Structure](#7-the-three-level-structure--big-picture)

**Tags:** `Pacioli-group` `graded-types` `fibration` `ownership` `debt` `session-types` `MPST` `coherence` `consensus` `three-level-structure` `modes` `principals` `research-contributions`

---

## Meta and Reference

### [QnA.md](QnA.md)
Accessible Q&A-style explanations of proof theory concepts: structural connectives, display property, residuation, cut efficiency, context-sensitivity, fixpoints. Cross-references dedicated documents for deeper treatment.

**Sections:** [Structural Connectives](#1-are-structural-connectives-limited) · [Residuation](#2-what-is-residuation) · [Exponentials Displayed](#3-exponentials-in-linear-logic-properly-displayed) · [Display Property](#4-what-is-the-display-property) · [Decomposition Failures](#5-decomposition-failures) · [Cut Efficiency](#6-cut-and-efficiency) · [Context-Sensitivity](#7-context-sensitivity) · [Fixpoints](#8-fixpoints-and-cyclic-proofs) · [Non-Determinism](#9-non-determinism) · [Structural vs Logical](#12-what-makes-a-connective-structural-vs-logical) · [Why ! Lacks Residuals](#13-why-doesnt-bang-have-residuals-detailed-explanation)

**Tags:** `QnA` `tutorial` `structural-connectives` `display-property` `residuation` `cut-elimination` `Boolos` `context-sensitivity` `fixpoints` `cyclic-proofs` `classical-logic` `non-determinism` `adjoint-decomposition`

### [logic_engineering.md](logic_engineering.md)
Two approaches to logic design: semantics-first vs syntax-first. Iterative refinement. Practical guidance for designing sequent calculi.

**Sections:** [Central Question](#the-central-question) · [Two Approaches](#two-approaches) · [Proof-Theoretic Semantics](#proof-theoretic-semantics) · [Model-Theoretic Semantics](#model-theoretic-semantics) · [Iterate!](#the-practical-answer-iterate) · [Checklist](#checklist-for-a-good-sequent-calculus) · [Tools for Display](#tools-for-display)

**Tags:** `logic-engineering` `semantics-first` `syntax-first` `proof-theoretic-semantics` `model-theoretic` `Tarski` `Gentzen` `harmony` `cut-elimination` `soundness` `completeness` `residuation` `adjoint-decomposition`

### [bibliography.md](bibliography.md)
Comprehensive bibliography with citations, URLs, tags. Organized by topic: display calculus, authorization, session types, etc.

**Sections:** [Foundational Papers](#foundational-papers) · [Display Calculus & Multi-Type](#display-calculus--multi-type-systems) · [Curry-Howard](#curry-howard--type-theory) · [Graded Types](#quantitative--graded-types) · [Authorization](#authorization-logic--security) · [Session Types](#session-types--process-calculi) · [Logic Programming](#logic-programming--ffi) · [Interactive Proving](#interactive-proving--prover-orchestration)

---

## Notes on Specific Documents

### Study Plans

| Document | Status |
|----------|--------|
| fibrations-study-plan.md | Complete study guide with reading order; study not yet executed |

### Acknowledged Open Problems

| Document | Open Problem |
|----------|--------------|
| consensus-modalities-mpst.md | Threshold modalities (k-of-n) lack compact modal representation — use predicates instead |

---

## Document Relationships

```
┌─────────────────────────────────────────────────────────────┐
│                    FOUNDATIONS                               │
│  proof-calculi-foundations ← display-calculus ← residuation │
│                              ↓                               │
│               exponential-display-problem                    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                  MULTI-TYPE FRAMEWORK                        │
│    multi-type-display-calculus ← adjunctions-and-adjoint-logic │
│              ↓                                               │
│    multimodal-linear-logic ← graded-resource-tracking        │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                 AUTHORIZATION & OWNERSHIP                    │
│    authorization-logic → ownership-design                    │
│              ↓                    ↓                          │
│    ownership-as-session-types  consensus-modalities-mpst    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                   FINANCIAL MODELING                         │
│         accounting-foundations ← linear-negation-debt        │
│                      ↓                                       │
│              financial-primitives                            │
└─────────────────────────────────────────────────────────────┘
```

---

*Last updated: 2026-02-10 (documents cleaned)*

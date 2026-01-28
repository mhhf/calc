# TODO

Outstanding tasks for the CALC project.

---

## Active Tasks

### Research: Multi-Type Display Calculus in CALC ✅
**Priority:** HIGH — COMPLETE

Our `persistent_ctx` + `linear_ctx` IS multi-type display calculus (Benton's LNL).
Research confirmed this and analyzed generalization options.

- [x] **Confirm LNL Structure** (See: dev/research/multi-type-display-calculus.md)
  - [x] Verified: persistent_ctx = Cartesian type (set, contraction/weakening OK)
  - [x] Verified: linear_ctx = Linear type (multiset, exact resource tracking)
  - [x] Verified: Bang_L is the F functor (prover.js:308-316)
  - [x] Verified: G functor is implicit (persistent_ctx propagated to all premises)

- [x] **Can Special Rules Be Generalized?**
  - [x] Researched calculus-toolbox-2: uses DSL with explicit type parameters
  - [x] Researched Greco & Palmigiano: properness + multi-type methodology
  - [x] Researched Pfenning's adjoint logic: generalizes to preorder of modes
  - [x] **Conclusion: Three options identified** (see research doc)

- [x] **Recommendation: Keep It Simple (YAGNI)**
  - [x] Current implementation is CORRECT—not a hack
  - [x] Bang_L special case IS the F functor properly implemented
  - [x] Generalize only when we need a second calculus
  - [x] Even mature tools (calculus-toolbox-2) have type-specific handling

**Key Finding:** CALC already implements multi-type DC correctly!

---

### Core/Calculus Separation (Revised)
**Priority:** MEDIUM

Two completely separate provers, minimal interaction for now.

**GenericProver** (lib/core/prover.js):
- Just tries all rules (including structural rules)
- NO explicit split enumeration (structural rules handle it implicitly)
- Supports ordered logic, linear logic, etc. - no assumptions
- Loop detection needed (A,B => B,A => A,B)
- Can verify proof trees from specialized provers

**ILLProver** (lib/provers/ill/):
- Current focused prover, unchanged
- Produces proof trees that GenericProver can verify
- No oracle/FFI for now - just two separate implementations

- [ ] Implement GenericProver (dumb rule enumeration)
- [ ] Add loop detection / visited state tracking
- [ ] Keep ILLProver as-is
- [ ] Add `verify(proofTree)` method to GenericProver

---

### Code Investigation
**Priority:** MEDIUM

Understand what's logic-specific vs generic in current code.

- [ ] **substitute.js:10 - Formula_Forall check**
  - Purpose: Avoid substituting bound variables in ∀
  - Is this strictly necessary? Where is it used?
  - Can it be made generic (any "binder" rule)?

- [ ] **calc.js:214 - Structure_Term_Formula check**
  - Purpose: Marks nodes as "term type" for rendering
  - Can be generalized: look for rules with Formula child type?

- [ ] **compare.js:23-27 - Commented references**
  - Were Structure_Term_Formula / Structure_Focused_Term_Formula comparisons
  - Investigate git history - why were they added/removed?
  - Probably debug/experimental code

- [ ] **sequent.js - hardcoded structure names**
  - Why config is better: allows different calculi with different structure names
  - But maybe YAGNI - keep hardcoded until we have second calculus

---

### Clean Up & Polish (completed)
- [x] Clean up ll.json - mark what's used vs unused clearly

---

## Completed

### Multi-Type Display Calculus Research ✅
- [x] Confirmed CALC implements Benton's LNL (persistent_ctx + linear_ctx)
- [x] Bang_L is the F functor (Lin → Cart bridge)
- [x] G functor implicit via persistent_ctx propagation
- [x] Researched Greco & Palmigiano, calculus-toolbox-2, Pfenning's adjoint logic
- [x] Recommendation: Keep current implementation (YAGNI)
- [x] Created: dev/research/multi-type-display-calculus.md

### Display Calculus Verification ✅
- [x] Implement C1-C8 checker in JavaScript (via /health UI)
- [x] Document the hybrid architecture (display rules + focused search)
- [x] Document which conditions pass/fail for ll.json
- [x] Decide: stay with ILL fragment (no ⅋, +, ?)

### UI Revival ✅
- [x] Get basic rendering working (SolidJS + Vite)
- [x] Add interactive rule application
- [x] Classical proof tree view
- [x] Structured (Lamport-style) proof view
- [x] ASCII proof tree view
- [x] JSON export view
- [x] Clickable rule labels with detail dialog
- [x] Show abstract rule, substitution (MGU), instantiated premises

### Interactive Proof Enhancements ✅
- [x] Show rule premises when selecting a rule
- [x] Display abstract rule pattern
- [x] Show sigma (substitution) applied by rule
- [x] Context split dialog for Tensor_R etc.

### Calculus Health Check UI ✅
- [x] Create /health route with educational C1-C8 explanation
- [x] Show overall cut elimination status
- [x] Expandable condition cards with full explanations
- [x] Architecture section explaining hybrid (display + focused)

### Research Documentation ✅
- [x] Logics overview: which logics can be displayed (dev/research/logics-overview.md)
- [x] Proof calculi foundations (dev/research/proof-calculi-foundations.md)
- [x] Display calculus deep research (dev/research/display-calculus.md)
- [x] Q&A on proof theory (dev/research/QnA.md)
- [x] Logic engineering guide (dev/research/logic_engineering.md)
- [x] Residuation knowledge base (dev/research/residuation.md)
- [x] Exponential display problem (dev/research/exponential-display-problem.md)
- [x] QTT overview (dev/research/QTT.md)
- [x] DSL approaches comparison (dev/research/DSL-approaches.md)
- [x] Interactive proving & prover orchestration (dev/research/interactive_proving.md)

### Interactive Proving Research ✅
- [x] LCF architecture (trusted kernel + untrusted tactics)
- [x] de Bruijn criterion vs LCF architecture comparison
- [x] Isabelle tacticals (THEN, ORELSE, REPEAT, etc.)
- [x] Isabelle Sledgehammer (parallel provers, relevance filtering, proof reconstruction)
- [x] Lean4 TacticM monad hierarchy (CoreM → MetaM → TermElabM → TacticM)
- [x] Coq Ltac2 (Hindley-Milner types, effects model, backtracking)
- [x] CoqHammer (ATP integration, proof reconstruction)
- [x] Twelf logic programming (mode checking, totality checking, coverage)
- [x] Prover orchestration patterns (parallel race, tacticals, translation+reconstruction)
- [x] Relation to CALC: FocusedProver ≈ untrusted tactics, mgu.js ≈ MetaM, Sequent ≈ LNL

### Key Papers Studied ✅
- [x] Pfenning's 15-836 Substructural Logics course notes
- [x] Wadler's "Propositions as Types" (Curry-Howard)
- [x] Granule ICFP 2019 (Graded Modal Types)
- [x] Benton's LNL (Linear/Non-Linear) Logic
- [x] Greco & Palmigiano's "Linear Logic Properly Displayed"

---

## Backlog

### Display Calculus Completeness
**Priority:** DEPRIORITIZED (decided to stay with ILL fragment)

- [ ] ~~Add Par (⅋) - multiplicative disjunction (dual of ⊗)~~
- [ ] ~~Add Plus (+) - additive disjunction (dual of &)~~
- [ ] ~~Add Why-not (?) - dual exponential (dual of !)~~
- [ ] ~~Add units: ⊥ (bottom), 0 (zero), ⊤ (top), 1 (one)~~

Decision: Stay with intuitionistic linear logic (ILL) fragment. Full classical linear logic duals not needed for current goals.

### Architecture (Core/Calculus Separation)
**Priority:** MEDIUM

- [ ] Identify code that is "Gentzen machinery" vs "Linear Logic specific"
- [ ] Design clean interface between core engine and calculus plugins
- [ ] Extract core into `lib/core/` directory
- [ ] Support compile-time and runtime calculus loading

### Code Quality
**Priority:** LOW

- [ ] Add ESLint configuration
- [ ] Add TypeScript (gradual)
- [ ] Set up CI with GitHub Actions

### Parser
**Priority:** LOW

- [ ] Document current Jison grammar
- [ ] Evaluate Chevrotain migration
- [ ] Benchmark parser performance

### Research
**Priority:** MEDIUM — DONE

- [x] Read Pfenning's 15-836 notes - DONE (see ANKI.md)
- [x] Study Granule ICFP 2019 paper - DONE (see QTT.md)
- [x] Research Nomos language (blockchain + linear types) - DONE (see nomos.md)
- [x] Research FFI for logics (mode-checked trusted computation) - DONE (see ffi-logics.md)

### Logic Engineering (How to Design Sequent Calculi)
**Priority:** HIGH — DONE

This is a main research goal — understanding how to come up with correct and good sequent calculi.

- [x] **Syntax vs Semantics: Which comes first?**
  - [x] Study proof-theoretic semantics (meaning from rules)
  - [x] Study model-theoretic semantics (meaning from truth)
  - [x] Understand the iteration between syntax and semantics
  - See: logic_engineering.md
- [x] **Checklist for a "good" sequent calculus**
  - [x] Cut elimination (must have)
  - [x] Subformula property (should have)
  - [x] No global side conditions (nice to have)
  - [x] Modularity (adding connectives doesn't break things)
  - See: logic_engineering.md, QnA.md

### Foundational Understanding
**Priority:** HIGH — MOSTLY DONE

- [x] **Study Curry-Howard correspondence in depth**
  - [x] Read Wadler's "Propositions as Types" paper
  - [x] Understand the three levels: syntax, structure, dynamics
  - [x] Work through Curry-Howard-Lambek (category theory connection)
  - [x] Understand why classical logic → continuations/control operators
  - See: proof-calculi-foundations.md, ANKI.md
- [x] **Understand proof calculi hierarchy**
  - [x] Natural deduction vs sequent calculus trade-offs
  - [x] Why sequent calculus is good for proof search
  - [x] Display calculus requirements (residuation, 8 conditions)
  - [x] When logics lack sequent calculi (fixpoints, context-sensitivity)
  - See: QnA.md, proof-calculi-foundations.md
- [x] **Study cut elimination deeply**
  - [x] Why cut elimination = consistency
  - [x] Why subformula property enables proof search
  - [x] Proof size explosion (Boolos's example)
  - See: QnA.md

### Residuation & Exponentials (for !_r display calculus)
**Priority:** HIGH — MOSTLY DONE

- [x] **Study residuation in depth**
  - [x] Work through examples in residuated lattices
  - [x] Understand Galois connections as requirement for residuation
  - [x] Why ! is a comonad, not residuated
  - [x] Examples of non-residuated connectives and why
  - See: residuation.md, exponential-display-problem.md
- [x] **Study adjoint decomposition for exponentials**
  - [x] Read Benton's LNL (Linear/Non-Linear) paper
  - [x] Understand multi-type display calculus approach
  - [x] How ! = F ∘ G (composition of adjoints)
  - [x] Study Greco & Palmigiano's "Linear Logic Properly Displayed"
  - See: exponential-display-problem.md, ANKI.md
- [x] **Study left/right decomposition patterns**
  - [x] What makes a "good" sequent rule?
  - [x] When do you need hypersequents/labels?
  - [x] Understand "local" vs "global" conditions in rules
  - [x] Which connectives fail decomposition (modalities, fixpoints)
  - See: QnA.md, proof-calculi-foundations.md
- [x] **Study non-determinism and confluence**
  - [x] Why classical cut-elimination is non-deterministic
  - [x] How polarization/focusing restores determinism
  - [ ] Cyclic proofs for fixpoints — TODO: deeper study
  - See: QnA.md

### Categorical & Algebraic Foundations
**Priority:** MEDIUM — PARTIALLY DONE

Concepts needed to understand display calculus deeply.

- [x] **Comonads** (in the sense of "! is a comonad")
  - [x] Definition: counit and comultiplication
  - [x] Why comonads are different from residuated operations
  - [ ] Coalgebras over comonads — deeper study needed
  - See: exponential-display-problem.md, QnA.md
- [x] **Adjoint decomposition** (! = F ∘ G)
  - [x] Adjunctions vs residuations
  - [x] How adjoints between TYPES give well-behaved rules
  - [x] Benton's LNL logic as canonical example
  - See: ANKI.md, exponential-display-problem.md
- [x] **Multi-type display calculus**
  - [x] Multiple types of formulas/structures
  - [x] Bridge connectives between types
  - [x] How this solves the exponential problem
  - See: exponential-display-problem.md, logics-overview.md
- [x] **Galois connections**
  - [x] Formal definition (f ⊣ g)
  - [x] Relationship to residuation
  - [x] Why they're required for display postulates
  - See: residuation.md, QnA.md
- [x] **Labelled sequents**
  - [x] How labels solve context-sensitivity
  - [x] Labels as explicit worlds (Kripke-style)
  - [x] Relationship to display calculus
  - See: QnA.md, proof-calculi-foundations.md
- [x] **Hypersequents**
  - [x] Definition: multiset of sequents
  - [x] How they solve S5 modal logic
  - [x] Comparison with display calculus
  - See: QnA.md, ANKI.md
- [x] **Global side conditions**
  - [x] What they're used for (modal logic, exponentials, eigenvariables)
  - [x] Why they're problematic for cut elimination
  - [x] Alternative formulations that avoid them
  - See: QnA.md

### Extensions
**Priority:** LOW (future)

- [ ] Design semiring-parameterized quantities
- [ ] Design ownership modalities
- [ ] Prototype real-number arithmetic

### Documentation
**Priority:** LOW

- [ ] Write significance hypothesis document (dev/HYPOTHESIS.md)
- [ ] Design minimal litmus test example (token transfer encoding)

---

## Deprioritized

### Study Proof Nets
**Priority:** VERY LOW

Proof nets are hard for multimodalities. Keep as long-term research interest only.

- [ ] Understand proof nets vs proof trees
- [ ] Study the "bureaucracy" problem they solve
- [ ] Understand correctness criteria

### Display proofs as PDF/HTML
**Priority:** VERY LOW

Already have HTML UI with multiple views. PDF export can wait.

### Isabelle Export
**Priority:** ULTRA LOW

- [ ] Consider Isabelle export for formal verification of cut elimination
- [ ] Research Isabelle/Isar proof format
- [ ] Would provide machine-checked guarantee but not needed for current goals

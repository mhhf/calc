---
title: TODO
created: 2026-02-10
modified: 2026-02-13
summary: Outstanding development tasks
tags: [planning, tasks]
status: active
---

# TODO

Outstanding tasks for the CALC project.

---

## HIGHEST Priority

### Prover Lasagne Implementation
**Priority:** HIGHEST
**Status:** Design complete — ready for implementation
**See:** doc/dev/prooverlasagne.md

Implement the 5-layer prover architecture:
- [ ] L1: Kernel (proof checker / verifier)
- [ ] L2: Generic prover (exhaustive search, backtracking)
- [ ] L3: Focused discipline (polarity, inversion phases)
- [ ] L4: Strategy layer (manual, auto, forward, symexec)
- [ ] Clean up browser.js duplication (extract shared builders)
- [ ] Run full test suite, rebuild bundle

### UI Refactor (L5 Thinning)
**Priority:** HIGHEST — do immediately after prover API
**Status:** Blocked by prover lasagne implementation

`proofLogicV2.ts` (854 lines) is NOT the "thin wrapper" it should be. It contains:
- Hardcoded rule schemas (`buildAbstractRuleStrings`)
- Its own `ProofTreeNode` type with `delta_in`/`delta_out`
- Focus handling logic (`applyFocusAction`, `collapseFocusSteps`)
- Category assignment (`getRuleCategory`)
- Serialization/export (115 lines)
- Debug utilities on `window.calcDebug`

After the prover API is clean (L1-L4), refactor L5:
- [ ] Move rule schemas to L4a (manual strategy)
- [ ] Move focus handling to L3
- [ ] Move proof tree types to L2
- [ ] Make proofLogicV2.ts a pure view adapter (~200 lines)
- [ ] Remove `window.calcDebug` hacks

---

## HIGH Priority

### Lax Monad `{A}` — Backward/Forward Integration
**Priority:** HIGH
**Status:** needs-research

CLF/Celf/LolliMon integrate forward and backward chaining via the lax monad `{A}`:
entering the monad switches from backward (L2/L3) to forward (L4c), exiting at quiescence.

- [ ] Study CLF, Celf, LolliMon lax monad semantics in depth
- [ ] Design how `{A}` integrates with the prover lasagne layers
- [ ] Prototype forward↔backward mode switch
- [ ] Understand relationship to Ceptre stages

**See:** doc/dev/prooverlasagne.md §3.6.1

---

### Analysis Layer / Metaproofs
**Priority:** HIGH
**Status:** needs-research

Execution tree analysis, invariant checking, property verification.

- [ ] Study Twelf/Abella approaches to metaproofs over linear logic
- [ ] Design analysis layer that sits above L4
- [ ] Property DSL for expressing invariants

**See:** doc/research/execution-trees-metaproofs.md

---

### Dual Representation Elimination
**Priority:** MEDIUM
**Status:** needs-benchmarks

`seq.contexts.linear` array vs `delta` multiset costs ~25% runtime. Need benchmarks before changing.

- [ ] Profile actual overhead with `CALC_PROFILE=1`
- [ ] Benchmark array vs multiset on real proof searches
- [ ] Decide whether to unify

---

### Multimodal Linear Logic Implementation
**Priority:** HIGH
**Status:** Design converging — ready for formalization after prerequisites

Design and implement multimodal linear logic with:
- Ownership modality: `[Alice] A` (possession/box)
- Authorization modality: `⟨Alice⟩ A` (affirmation/diamond)
- Graded modality: `[]_{100} token` (quantities)

**Key decisions (from research):**
- Use **MTDC with parametric indices** (not SELL — SELL requires fixed index sets)
- User-centric ownership: `[Alice] []_{10} eth` (not contract-centric)
- Fresh name generation for token/contract identity
- `WITH` clause for atomic contract creation with deposit
- Rules are persistent implications `!(P ⊸ Q)` — forward-chaining
- **Graded quantities are object-level** — enables split/merge rules in logic

**Minimal core:**
- Connectives: `⊗`, `⊸`, `!`, `[P]`, `⟨P⟩`, `[]_r`
- Operations: mint, transfer, contract creation (WITH)
- Engine: forward-chaining rule application (Celf-style)

**Implementation tasks:**
- [ ] Extend parser for `[P]`, `⟨P⟩`, `[]_r` modalities
- [ ] Implement fresh name generation
- [ ] Implement `WITH` clause for atomic deposit
- [ ] Forward-chaining engine for rule application
- [ ] Worked examples: token, transfer, atomic swap, AMM

**Proofs needed:**
- Cut-elimination (via MTDC Belnap conditions)
- Conservation (total supply preserved)
- No counterfeiting (freshness property)

**See:** doc/research/multimodal-linear-logic.md, doc/research/ownership-design.md


### Pacioli Grading Semiring
**Priority:** HIGH

Can the Pacioli group P be a well-behaved grading semiring for graded linear logic?

- [ ] Define multiplication: [a//b] · [c//d] = ???
- [ ] Verify semiring laws
- [ ] Define □_{[x//y]} A in the logic
- [ ] What does grade polymorphism mean for T-accounts?

---

### Fibration Semantics for Ownership
**Priority:** HIGH

What is the precise fibration structure for ownership?

- [ ] Base category: Principals with speaks-for morphisms?
- [ ] Fibers: SMC of resources? Linear categories?
- [ ] Transfer as reindexing: what properties?
- [ ] Connection to dependent linear types?

---

### Debt as Session Protocol
**Priority:** HIGH

Define debt relationships as session types:

- [ ] debt_type = &{ pay: ..., renegotiate: ..., default: ... }
- [ ] Settlement as channel closure
- [ ] Default handling via exception types?
- [ ] Multi-party debt (syndicated loans)?

---

### MPST-Based Authorization Design
**Priority:** HIGH

Apply MPST methodology to CALC:

- [ ] Define atomic swap as global type
- [ ] Implement projection algorithm
- [ ] Prove deadlock freedom for swap
- [ ] Generate local rules automatically

---

### Execution Trees (Proofs Despite Choice)
**Priority:** HIGH
**Status:** Research complete — ready for implementation

Build execution trees by branching at additive choice (&) points instead of stopping.

**Problem:** Forward chaining stops at `A & B` because consumer picks branch.
**Solution:** Explore BOTH branches, build tree of all possible executions.

**Key concepts (from Ceptre):**
- Stages run until **quiescence** (no rules fire)
- Can run **interactive** (human picks) or **random** (engine picks)
- Generate **trace graphs** of execution paths

**Implementation tasks:**
- [ ] Detect choice (with) in rule consequent
- [ ] Fork state at branch points, explore both
- [ ] Build recursive Tree structure with branch metadata
- [ ] GraphViz dot output for visualization
- [ ] Extract all leaf states for analysis

**Applications:**
- Model checking: verify property on all reachable states
- Test generation: find paths to specific states
- Game tree analysis: explore all player choices

**See:** doc/research/execution-trees-metaproofs.md

---

### Metaproofs (Properties of Linear Logic Programs)
**Priority:** HIGH
**Status:** Research complete — design needed

Prove properties **about** CALC programs: conservation, safety, termination.

**Key metaproperties:**
- **Conservation:** `∀ exec. total_supply(initial) = total_supply(final)`
- **No counterfeiting:** Tokens only from mint or initial state
- **Safety:** Bad states never reachable
- **Progress:** System can always make a move
- **Termination:** Forward chaining always reaches quiescence

**Proof techniques:**
1. **Reachability analysis** — Build exec tree, check all leaves
2. **Inductive invariants** — Show `I(initial) ∧ ∀rule. I(pre) → I(post)`
3. **External formalization** — Export to Twelf/Abella for high assurance

**Implementation tasks:**
- [ ] State property DSL (language to express invariants)
- [ ] Invariant checker (initial + preservation verification)
- [ ] Reachability queries ("can state S be reached?")
- [ ] Counter-example generation (trace to violating state)

**Depends on:** Execution trees (for reachability)

**See:** doc/research/execution-trees-metaproofs.md

---

### Induction and Coinduction (Fixed Points)
**Priority:** HIGH
**Status:** Research complete — longer-term

Handle unbounded/infinite behavior: recursive contracts, streaming payments.

**μMALL approach** (Baelde & Miller):
- Add least (μ) and greatest (ν) fixed points to MALL
- Cut-elimination holds
- Complete focused proof system
- Undecidable in general (Π⁰₁-hard)

**Cyclic proofs approach:**
- Allow proofs with back-edges
- Global progress condition for validity
- Trades invariant complexity for proof structure

**Applications:**
- Recursive contract definitions: `νX. (pay ⊗ delay ⊗ X)`
- Termination proofs for bounded execution (induction on gas)
- Bisimulation for contract equivalence

**Implementation tasks:**
- [ ] Cycle detection in forward chaining
- [ ] Bounded exploration with depth limit
- [ ] Fixed point syntax (μ, ν connectives)
- [ ] Progress checking for cyclic proofs

**Depends on:** Execution trees, basic metaproofs

**See:** doc/research/execution-trees-metaproofs.md

---

## MEDIUM Priority

### Advanced Optimizations
**Priority:** MEDIUM
**Status:** Content-addressing complete, profiling infrastructure in place

Deferred optimizations documented in **doc/research/prover-optimization.md**.

Use `CALC_PROFILE=1` to identify bottlenecks before implementing:
- Constructor Index (O(1) identity lookup)
- Proof Memoization (polynomial complexity)
- Near-Linear Unification (Martelli-Montanari)
- Explicit Substitutions (lazy evaluation)
- Persistent Data Structures
- Arena Allocation (for Zig port)

---

### Conditional execution
**Priority:** MEDIUM

if a condition is reached (time is up, price is hit, etc) we need to triger a transition. how to model it?

see financial-primitives

### Price Oracles
**Priority:** MEDIUM

- internal price oracles
- external price oracles

see financial-primitives

### Explicit time
**Priority:** MEDIUM
Some things - like future or option contracts need explicit time - since they are expiering. We need to research how to model that well with calc

see financial-primitives.md

### Proper Multi-Type Display Calculus for ILL
**Priority:** HIGH (after DSL refactor)

**Problem discovered (2026-02-02):**
The current `lnl.family` implements Benton's LNL model, which is valid for ILL but is NOT a "proper" multi-type display calculus (Greco & Palmigiano style). Key issues:

1. **Sequents not type-uniform**: `Γ_cart ; Δ_lin ⊢ C_lin` mixes types
2. **No residuation**: Cannot fully "display" formulas within each mode
3. **Cut elimination**: Proven for LNL specifically, NOT via Belnap's generic metatheorem

**Why this matters:**
- Generic cut elimination would allow extending with multimodalities
- Proper MTDC has modular cut-elim: add connectives without re-proving
- Current design requires per-logic cut-elim proofs for extensions

**Goal:**
Create a NEW calculus (e.g., `lnl-proper.family`) that IS a proper MTDC:
- Type-uniform sequents: `X ⊢_Lin Y` and `X ⊢_Cart Y` separately
- Residuation display postulates within each mode
- Bridge connectives (F, G) crossing types
- Verify Belnap's adapted C1-C8 conditions hold
- Generic cut elimination via metatheorem

**Constraint:** Minimal intrusion to core implementation — new calculus file, not rewrite.

**Research needed:**
- [ ] Study Greco & Palmigiano "Linear Logic Properly Displayed" in detail
- [ ] Understand adapted Belnap conditions for multi-type
- [ ] Design type-uniform sequent structure
- [ ] Verify generic cut-elim applies

**See:** doc/research/multi-type-display-calculus.md, doc/research/display-calculus.md

---

### Generalize Multi-Type Display Calculus
**Priority:** MEDIUM (after proper MTDC)

CALC implements Benton's LNL via persistent_ctx + linear_ctx. For multimodalities, graded types, and agents, we need a generic multi-type framework.

**Current State:**
- LNL hardcoded (persistent_ctx, linear_ctx, Bang_L special handling)
- Works correctly for ILL — this is our case study
- NOT proper MTDC — see above task

**Goal:**
- Generalize to support arbitrary types and bridge rules
- Keep LNL as instantiation proving the framework works
- Enable: ownership modalities, consensus algorithms, graded types

**Consensus modalities to support (not just simple ownership):**
- Single authority: `[Alice] A`
- Multi-signature: `[Alice ∧ Bob] A`
- k-of-n threshold: `[2-of-{A,B,C}] A`
- Weighted voting: `[Alice:0.3, Bob:0.7] A`
- Proof of Work: `[PoW(nonce, difficulty)] A`
- Proof of Stake: `[Stake(Alice, amount)] A`

**Options evaluated (see research doc):**
1. **Multi-type DC** (Greco & Palmigiano) — PRIMARY CHOICE
2. **Labelled sequents** — backup if MTDC insufficient
3. **Pfenning's adjoint logic** — good fit, modes as partial order

**Advanced systems evaluated:**
- Deep Inference: LOW relevance (structural flexibility, not our need)
- Cyclic Proofs: MEDIUM-HIGH for future (if we need recursive contracts/fixpoints)
- Proof Nets: LOW (bad for multimodal logics)

See: doc/research/multi-type-display-calculus.md

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

### Partial Settlement with Arithmetic FFI
**Priority:** MEDIUM

From linear-negation-debt research:
- [ ] Partial settlement with arithmetic FFI

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

### Ceptre Stages (Structured Quiescence)
**Priority:** LOW
**Prerequisite:** Lax monad and forward chaining

Stages are Ceptre's mechanism for structured multi-phase computation.

**Concept:**
```ceptre
stage combat = {
  attack : enemy * weapon -o damaged_enemy.
  defeat : damaged_enemy -o victory.
}

stage exploration = {
  move : at Player Room -o at Player Room2.
}

% Stage transitions
combat * victory -o exploration.
```

**Semantics:**
- Each stage runs until quiescence (no rules apply)
- Stage transitions fire when quiescence reached
- Enables turn-based games, multi-phase protocols

**Research needed:**
- [ ] Study Ceptre stage semantics in detail
- [ ] Design stage syntax for .calc/.rules
- [ ] Implement stage engine with transitions
- [ ] Add `#interactive` mode (human chooses rules)

**See:** doc/research/clf-celf-ceptre.md, Chris Martens' thesis

---

### CLF Dependent Types (Π, ∃)
**Priority:** LOW
**Prerequisite:** Lax monad and forward chaining

For full LF/LLF/CLF compatibility, need dependent types.

**Connectives needed:**
- Dependent function `Π x:A. B` (types depending on terms)
- Existential `∃ x:A. B` (witness-providing)
- Top `⊤` (additive truth, trivially provable)

**How to extend:**
```celf
% In ill.calc
pi : (A : type) -> (A -> formula) -> formula
  @ascii "Pi _ : _ . _"
  @latex "\\Pi #1 : #2. #3".

exists : (A : type) -> (A -> formula) -> formula
  @ascii "exists _ : _ . _"
  @latex "\\exists #1 : #2. #3"
  @polarity positive.

top : formula
  @ascii "T"
  @latex "\\top"
  @polarity negative.
```

**Why this is hard:**
- Requires type-checking terms, not just formulas
- Substitution becomes capture-avoiding
- Need kind system (type : kind)

**See:** doc/research/clf-celf-ceptre.md, CLF paper (Watkins et al.)

---

### Cyclic Proofs for Fixpoints
**Priority:** LOW

- [ ] Cyclic proofs for fixpoints — deeper study needed

### Coalgebras over Comonads
**Priority:** LOW

- [ ] Coalgebras over comonads — deeper study needed

### Extensions
**Priority:** LOW (future)

- [ ] Design semiring-parameterized quantities
- [ ] Design ownership modalities
- [ ] Prototype real-number arithmetic

### Documentation System (Executable Markdown)
**Priority:** MEDIUM
**Status:** Partially implemented in `src/ui/lib/markdown.ts`

Implement executable code blocks in markdown for research docs.

**Hybrid rendering approach:**
- Server-side: graphviz, katex, calc (static output)
- Client-side: mermaid, proof trees (interactive)

**Remaining work:**
- [ ] Add client-side mermaid rendering
- [ ] Add interactive proof tree viewer
- [ ] Generate backlinks from wiki-links
- [ ] Add tags-based filtering

---

### Documentation (Legacy)
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

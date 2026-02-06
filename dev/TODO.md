# TODO

Outstanding tasks for the CALC project. See DONE.md for completed items.

---

## HIGH Priority

### Higher Order Linear Types:
Priority: HIGH

I'm curious about linear types that can wrap linear types.
Right now we only have the posibility of doing:

```
bla: type.
omg: bla.
omg2: bla.

foo: bla -> ltype.
```

but i'd like something like:

```
bar: ltype -> ltype
```

We would need to research that in depth if its possible and how easy and 'far away' it is from the constructive LL we already implemented.


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

## MEDIUM Priority

### Advanced Optimizations
**Priority:** MEDIUM
**Status:** Content-addressing complete, profiling infrastructure in place

Deferred optimizations documented in **dev/optimization_strategies.md**.

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

research BDI framework and logic - behaviour desire intention and how it might fit into our system, create a research document for bdi

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

**See:** dev/research/multi-type-display-calculus.md, dev/research/display-calculus.md

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

See: dev/research/multi-type-display-calculus.md (revised)

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

**See:** dev/research/clf-celf-ceptre.md, Chris Martens' thesis

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

**See:** dev/research/clf-celf-ceptre.md, CLF paper (Watkins et al.)

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

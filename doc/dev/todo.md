---
title: TODO
created: 2026-02-10
modified: 2026-02-13
summary: Outstanding development tasks
tags: [planning, tasks]
status: active
---

# TODO

## Architecture & Engine

### Lax Monad `{A}` — Backward/Forward Integration
**Priority:** HIGH | **Status:** needs-research

CLF/Celf/LolliMon integrate forward and backward chaining via the lax monad `{A}`:
entering the monad switches from backward (L2/L3) to forward (L4c), exiting at quiescence.

- [ ] Study CLF, Celf, LolliMon lax monad semantics in depth
- [ ] Design how `{A}` integrates with the prover lasagne layers
- [ ] Prototype forward↔backward mode switch
- [ ] Understand relationship to Ceptre stages

### Execution Trees
**Priority:** HIGH | **Status:** research complete — ready for implementation

Branch at additive choice (&) points instead of stopping. Explore all possible executions.

- [ ] Detect choice (with) in rule consequent
- [ ] Fork state at branch points, explore both
- [ ] Build recursive Tree structure with branch metadata
- [ ] GraphViz dot output for visualization
- [ ] Extract all leaf states for analysis

**See:** doc/research/execution-trees-metaproofs.md

### Metaproofs
**Priority:** HIGH | **Status:** research complete — design needed | **Depends on:** execution trees

Prove properties about CALC programs: conservation, safety, termination.

- [ ] State property DSL (language to express invariants)
- [ ] Invariant checker (initial + preservation verification)
- [ ] Reachability queries ("can state S be reached?")
- [ ] Counter-example generation (trace to violating state)

**See:** doc/research/execution-trees-metaproofs.md

### Induction and Coinduction (Fixed Points)
**Priority:** MEDIUM | **Status:** research complete — longer-term | **Depends on:** execution trees, metaproofs

Handle unbounded/infinite behavior: recursive contracts, streaming payments.

- [ ] Cycle detection in forward chaining
- [ ] Bounded exploration with depth limit
- [ ] Fixed point syntax (μ, ν connectives)
- [ ] Progress checking for cyclic proofs

**See:** doc/research/execution-trees-metaproofs.md, doc/research/muMALL-fixed-points.md

### Ceptre Stages
**Priority:** LOW | **Depends on:** lax monad

Named rule subsets running to quiescence with inter-stage transitions.

- [ ] Study Ceptre stage semantics
- [ ] Design stage syntax for .calc/.rules
- [ ] Implement stage engine with transitions

**See:** doc/research/clf-celf-ceptre.md

### CLF Dependent Types (Π, ∃)
**Priority:** LOW | **Depends on:** lax monad

For full LF/LLF/CLF compatibility. Requires type-checking terms (not just formulas), capture-avoiding substitution, kind system.

---

## Multimodal Logic

### Proper Multi-Type Display Calculus for ILL
**Priority:** HIGH

Current `lnl.family` implements Benton's LNL — valid for ILL but NOT a proper MTDC (Greco & Palmigiano). Key issues: sequents not type-uniform, no residuation, cut-elim not via Belnap metatheorem.

- [ ] Study Greco & Palmigiano "Linear Logic Properly Displayed"
- [ ] Design type-uniform sequent structure
- [ ] Verify generic cut-elim applies
- [ ] Implement as `lnl-proper.family` (new file, not rewrite)

**See:** doc/research/multi-type-display-calculus.md

### Generalize MTDC
**Priority:** MEDIUM | **Depends on:** proper MTDC

Generalize beyond LNL to support arbitrary types and bridge rules. Enable ownership modalities, consensus algorithms, graded types.

**See:** doc/research/multi-type-display-calculus.md

### Multimodal Implementation
**Priority:** HIGH | **Status:** design converging

Ownership `[Alice] A`, authorization `⟨Alice⟩ A`, graded `[]_r token`.

**Key decisions:** MTDC with parametric indices (not SELL), user-centric ownership, quantities are object-level terms.

- [ ] Extend parser for `[P]`, `⟨P⟩`, `[]_r` modalities
- [ ] Implement fresh name generation
- [ ] Implement `WITH` clause for atomic deposit
- [ ] Forward-chaining engine for rule application
- [ ] Worked examples: token, transfer, atomic swap, AMM

**See:** doc/research/multimodal-linear-logic.md, doc/research/ownership-design.md

---

## Research (Theoretical)

### Pacioli Grading Semiring
**Priority:** MEDIUM

Can the Pacioli group be a well-behaved grading semiring for graded linear logic?

- [ ] Define multiplication: `[a//b] · [c//d] = ???`
- [ ] Verify semiring laws
- [ ] Define `□_{[x//y]} A` in the logic

### Fibration Semantics for Ownership
**Priority:** MEDIUM

Base category = principals with speaks-for morphisms, fibers = resources, transfer = reindexing.

- [ ] Define base category and fiber structure
- [ ] Connection to dependent linear types

### Debt as Session Protocol
**Priority:** MEDIUM

- [ ] `debt_type = &{ pay, renegotiate, default }`
- [ ] Settlement as channel closure
- [ ] Multi-party debt (syndicated loans)

### MPST-Based Authorization
**Priority:** MEDIUM

- [ ] Define atomic swap as global type
- [ ] Implement projection algorithm
- [ ] Prove deadlock freedom

### Financial Primitives
**Priority:** MEDIUM

- [ ] Conditional execution (triggers on state conditions)
- [ ] Price oracles (internal / external)
- [ ] Explicit time for expiring contracts (futures, options)
- [ ] Partial settlement with arithmetic FFI

**See:** doc/research/financial-primitives.md

---

## Performance

### Dual Representation Elimination
**Priority:** MEDIUM | **Status:** needs benchmarks

`seq.contexts.linear` array vs `delta` multiset — profile actual overhead before changing.

- [ ] Profile with `CALC_PROFILE=1`
- [ ] Benchmark array vs multiset on real proof searches

### Constructor Indexing
**Priority:** MEDIUM

O(1) identity for ground formulas via tag-based index. Highest-impact single optimization.

**See:** doc/dev/constructor-indexing.md, doc/research/prover-optimization.md

### Symexec: Incremental buildStateIndex & hashState
**Priority:** MEDIUM | **Status:** profiled — ready for implementation

After strategy stack optimization (181ms → 14ms), remaining costs are evenly split:
buildStateIndex 29%, hashState 23%, applyMatch 24%, tryMatch 21%.
Both buildStateIndex and hashState rebuild from scratch every node (~178 facts).
Incremental update via consumed/produced delta could eliminate most of this cost.

### Symexec: Non-Opcode Rule Strategy
**Priority:** LOW

4 non-opcode helper rules (concatMemory/z, concatMemory/s, calldatacopy/z, calldatacopy/s)
cause 24% tryMatch waste — they're tried at every node but only match when their specific
trigger predicates (`concatMemory`, `calldatacopy`) are present. The predicate layer already
filters them, but they still get tried at nodes where predicates are present but values don't
match. Could add a more specific strategy layer or just accept the small waste.

---

## Tooling

### Documentation System
**Priority:** MEDIUM | **Status:** partially implemented

- [ ] Interactive proof tree viewer in markdown
- [ ] Generate backlinks from wiki-links
- [ ] Tags-based filtering

### Code Quality
**Priority:** LOW

- [ ] ESLint configuration
- [ ] Gradual TypeScript adoption
- [ ] CI with GitHub Actions

---

## Deprioritized

- **Display Calculus Completeness** — decided to stay with ILL fragment (no par, plus, why-not)
- **Proof Nets** — hard for multimodalities, low relevance
- **PDF/HTML proof export** — already have HTML UI
- **Isabelle Export** — formal verification of cut-elim, not needed now
- **Coalgebras over comonads** — deeper study needed, no urgency

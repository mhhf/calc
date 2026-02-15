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
**Priority:** HIGH | **Status:** DONE (symexec.js)

Implemented in `lib/prover/strategy/symexec.js`:

- [x] Detect choice (with) in rule consequent — `expandItem()`, `expandConsequentChoices()`
- [x] Fork state at branch points, explore both — `explore()` with mutation+undo
- [x] Build recursive Tree structure with branch metadata — `{ type, state, children, rule, choice }`
- [x] GraphViz dot output for visualization — `toDot()`
- [x] Extract all leaf states for analysis — `getAllLeaves()`, `countLeaves()`, `maxDepth()`
- [x] Cycle detection (back-edge via commutative XOR hash)
- [x] Depth bounding (maxDepth option)

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
**Priority:** MEDIUM | **Status:** partially implemented | **Depends on:** execution trees, metaproofs

Handle unbounded/infinite behavior: recursive contracts, streaming payments.

- [x] Cycle detection in forward chaining — back-edge detection via commutative XOR hash in `explore()`
- [x] Bounded exploration with depth limit — `maxDepth` option in `explore()`
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
**Priority:** MEDIUM | **Status:** DONE (181ms → 14ms → 8.4ms → 4.7ms → 3.8ms)

Implemented: ExploreContext (incremental index + XOR hash), mutation+undo, strategy stack.
Latest: index mutation+undo eliminates cloneIndex (46µs per 173-entry codeByPC spread × 6 clones),
mutable pathVisited Set eliminates new Set() copies.
**See:** doc/documentation/symexec-optimizations.md

### Audit: Precompute Everything Possible at Compile Time
**Priority:** VERY HIGH | **Status:** DONE (audit complete, .calc/.rules fully precomputed)

**Completed:**
- [x] `compileRule()` in forward.js precomputes `linearMeta` and `persistentOutputVars` (.ill data)
- [x] `ill.json` precomputes `parserTables`, `rendererFormats`, `ruleSpecMeta`, `connectivesByType`
- [x] Browser hydration skips all table derivation from constructors/rules
- [x] `findAllMatches` spread eliminated — reusable `_indexedState` object (12.6% speedup)

**Audit result: .calc/.rules/.family data is fully precomputed.** Everything derivable
from the calculus definition is now serialized in ill.json at build time. Browser hydration
only creates closures (parser, renderer, AST constructors, makePremises). The Node path
also uses precomputed metadata when available (ruleSpecMeta).

**Remaining runtime computation is on .ill program data (not precomputable to JSON):**
- `compileRule()` — walks .ill formula hashes (Store.get) to extract structure
- `buildRuleIndex`/`buildOpcodeIndex` — groups compiled rules by trigger predicates
- `buildStateIndex`/`hashState` — indexes execution state (changes every step)
- `buildIndex` (backward) — indexes clauses/types for proof search
- `freshenTerm`/`freshenClause` — renames variables per proof step

**Low-priority Store-level opportunities:**
- [ ] `isMetavar`/`isVar` do `Store.get(h)` per call — could maintain a `Set<hash>` of known metavars populated at `Store.put` time. Saves one Map lookup per unify/match step.
- [ ] `freshenTerm`/`freshenClause` walk full clause trees. Could precompute variable position maps per clause at load time so freshening only visits variable positions.

### Symexec: 178-Match-Call Exhaustive Scans
**Priority:** VERY HIGH | **Status:** DONE (1,661 → 605 match() calls)

**Root cause:** Bug in tryMatch candidate lookup. When `pred` was known (e.g. 'calldatasize')
but `index[pred]` was undefined (0 facts), the code fell through to scanning ALL linear facts
(`Object.keys(state.linear)` → 178 match calls). Fix: `candidates = index[pred] || []`.

**Findings:**
- [x] `evm/calldatasize` caused 64% of match() calls (6 tries × 178 facts = 1,068 calls)
- [x] Rule was opcode-indexed (opcode 0x36), correctly selected by opcode layer
- [x] But `calldatasize(_Size)` fact was missing from state → scanned ALL 178 facts
- [x] Fix: known predicate with 0 indexed facts → empty candidates (not full scan)
- [x] Next biggest: jumpi_neq/jumpi_eq at ~14 match/try — legitimate work (2×stack patterns)

### Symexec: Prove Memo Cache
**Priority:** VERY HIGH | **Status:** DONE (direct FFI bypass — 153 prove() calls → 0)

Solved by `tryFFIDirect()` in forward.js: persistent antecedents with FFI (inc, plus, neq,
mul, etc.) are dispatched directly from tryMatch, bypassing the full prove() machinery.
Added `neq` FFI for O(1) BigInt inequality. FFI failure is definitive (break immediately).

- [x] Direct FFI dispatch without prove overhead — `tryFFIDirect()` in forward.js
- [x] neq FFI added — `arithmetic.neq`, mode `+ +`
- [x] Result: 153 prove() calls → 0 per 63-node tree (19% symexec speedup)

### Forward Optimization Stages 6-9
**Priority:** MEDIUM | **Status:** design complete, research in progress

**See:** doc/dev/forward-optimization-roadmap.md

- [ ] **Stage 6: De Bruijn indexed theta** — compile-time slot assignment, O(1) metavar lookup
  - Research complete: doc/research/de-bruijn-indexed-matching.md
  - Undo stack needed for intra-rule pattern failure reset
  - Enables Stage 7
- [ ] **Stage 7: Delta optimization + compiled substitution** — depends on Stage 6
  - Delta bypass: extract changed args directly instead of full match()
  - Compiled consequent: Store.put chain instead of applyFlat traversal
- [ ] **Stage 9: Discrimination tree indexing** — for 100+ rules
  - Research complete: doc/research/term-indexing.md
  - Compiled pattern matching (Maranget) as alternative: doc/research/compiled-pattern-matching.md
  - Recommendation: fingerprints <100 rules, discrimination trees 100-500, code trees 500+
- [ ] **Stage 5: Theta format unification** — superseded if Stage 6 adopted globally

**Research items (from de Bruijn analysis):**
- [ ] Compile-time first-occurrence vs subsequent-occurrence distinction (WAM get_variable/get_value)
- [ ] Compiled match functions (per-rule specialized matchers, beyond generic match())
- [ ] Interaction between deferral order and first/subsequent classification

**Research items (from forward chaining networks):**
- [ ] TREAT-style dirty rule tracking — only re-evaluate rules whose trigger predicates changed
- [ ] CHR join ordering — match most selective antecedent first (beyond current deferral)
- [ ] LEAPS delta-driven activation — maintain activation queue instead of scanning all rules
- [ ] Tabled forward chaining — cache symexec subtrees for recurring states

**Research items (from incremental matching):**
- [ ] Delta predicate tracking in `findAllMatches` (~30 LOC, helps at any scale)
- [ ] Full semi-naive evaluation at 100K+ facts (positive + negative delta for linear logic)
- [ ] Provenance tracking for non-monotonic semi-naive (which facts contributed to each match)
- [ ] Relational e-matching for multi-antecedent rules (leapfrog trie join at 100K+ facts)

**See also:** doc/research/forward-chaining-networks.md, doc/research/incremental-matching.md

### Symexec: Non-Opcode Rule Strategy
**Priority:** LOW | **Status:** investigated — minimal impact

4 non-opcode helper rules (concatMemory/z, concatMemory/s, calldatacopy/z, calldatacopy/s)
go to predicate layer. In practice these contribute 0 match() calls because their trigger
predicates (concatMemory, calldatacopy) are never present in the multisig benchmark state.
Only relevant when those EVM instructions are actually used.

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

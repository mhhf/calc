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
**Priority:** MEDIUM | **Status:** DONE (181ms → 14ms → 8.4ms → 4.7ms)

Implemented: ExploreContext (incremental index + XOR hash), mutation+undo, strategy stack.

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
**Priority:** VERY HIGH | **Status:** needs-research

6 of 63 nodes account for 64% of all `match()` calls (1,068 of 1,661). Each tries
matching a rule against ALL 178 linear facts and finds nothing. These rules pass the
predicate filter (trigger predicates exist in state) but fail matching every fact.

Need to investigate:
- [ ] Which specific rules cause the exhaustive scans? (rule name, antecedent structure)
- [ ] Why do they pass the predicate filter but fail matching? (predicates present but wrong argument structure?)
- [ ] Would first-argument indexing (like backward prover's `getFirstArgCtor`) prune candidates?
- [ ] Are these non-opcode rules that fall through to predicate layer? (concatMemory, calldatacopy?)
- [ ] Can the strategy stack add a layer that prevents these scans?

Context: `findAllMatches` → `tryMatch(rule, state)` → for each linear pattern, looks up
`index[pred]` to get candidate facts, then calls `match(pattern, fact)` for each. When the
index bucket is large (e.g., all 178 facts have the same predicate? or fallback to all?),
we scan everything.

### Symexec: Prove Memo Cache
**Priority:** VERY HIGH | **Status:** needs-research

`prove()` (backward chaining) is called 153 times across 63 nodes (2.4/node), taking
54% of findAllMatches time. Most calls are arithmetic FFI: `inc(binlit, _PC')`,
`plus(binlit, binlit, _GAS')`, `neq(X, Y)`.

Need to investigate:
- [ ] How many prove calls have identical goal hashes? (same inc/plus with same binlit inputs)
- [ ] Are goals fully ground after substitution? (if so, result is deterministic → cacheable)
- [ ] What does the prove call tree look like? (depth, branching, FFI vs clause resolution)
- [ ] Would a simple `Map<goalHash, theta>` cache work? (concerns: freshening, variable scoping)
- [ ] How big would the cache get? (per-explore vs global lifetime)
- [ ] Can we avoid prove entirely for FFI-only goals? (direct FFI dispatch without prove overhead)

Context: tryMatch calls `backward.prove(goal, clauses, types, { maxDepth: 50 })` for each
persistent antecedent pattern after substitution. Prove does: freshenTerm, getCandidates,
unify, recurse on premises. For `inc(binlit(117), _PC')`, it freshens `inc` clause, unifies,
then calls FFI `plus` to compute the result.

### Symexec: Non-Opcode Rule Strategy
**Priority:** LOW

4 non-opcode helper rules (concatMemory/z, concatMemory/s, calldatacopy/z, calldatacopy/s)
cause tryMatch waste — they're tried at nodes where predicates are present but values don't
match. The predicate layer filters by trigger predicate existence but not by argument values.

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

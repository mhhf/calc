---
title: TODO
created: 2026-02-10
modified: 2026-02-17
summary: Outstanding development tasks
tags: [planning, tasks]
status: active
---

# TODO

## Currently Working On: Unsound Loli Decomposition in Forward Engine

**See also:** `doc/research/forward-chaining.md` (theory), `doc/documentation/forward-chaining-engine.md` (implementation)

### The Problem

Our EVM rules use **guarded loli continuations** inside ⊕ forks to model conditional branching:

```ill
evm/iszero:
  pc PC * code PC 0x15 * ... * stack SH V
  -o {
    pc PC' * gas GAS' * code PC 0x15 * sh (s SH) *
    ((!eq V 0 -o { stack SH 1 }) +      ← branch A: if V==0, push 1
     (!neq V 0 -o { stack SH 0 }))      ← branch B: if V≠0, push 0
  }.
```

When this rule fires, the consequent (inside `{...}`) produces shared facts (`pc PC'`, `gas GAS'`, etc.) and a `⊕` (plus) that forks the execution tree into two branches. Each branch is a **loli continuation** with a **bang guard**: `!eq V 0 ⊸ {stack SH 1}` means "IF eq(V,0) can be proved, THEN produce `stack SH 1`."

The guard `!eq V 0` is persistent (bang-wrapped) — it needs to be **proved** via backward chaining or FFI, not just found in the state. This is the theory: a loli in the state is a dormant rule that fires when its trigger becomes available. For a persistent trigger like `!P`, "available" means "provable."

### What Goes Wrong

`expandItem` in `compile.js:150-159` decomposes `!P ⊸ {Q}` into `{ linear: [Q], persistent: [!P] }`:

```javascript
// compile.js:150-159
if (t === 'loli') {
  if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
    return bodyAlts.map(a => ({
      linear: a.linear,                  // Q's body — added unconditionally!
      persistent: [c0, ...a.persistent]  // !P — asserted as fact without proving!
    }));
  }
}
```

This transforms a **conditional** ("if P then Q") into an **unconditional** assertion ("Q AND !P"). It applies modus ponens without checking the premise. Both ⊕ branches get their bodies and guards unconditionally, so:

- Branch A gets: `stack SH 1` + `!eq(V,0)` — even when V≠0
- Branch B gets: `stack SH 0` + `!neq(V,0)` — even when V=0

Dead branches run with **corrupted state** (wrong stack values, false persistent facts), producing invalid execution traces instead of becoming stuck leaves. The bug existed before ⊕ (old `evm/eq` with `&` had the same decomposition), but ⊕ on iszero/jumpi amplified it from ~2 false branches to 2^N (263 → 13109 nodes in multisig benchmark).

### Why `expandItem` Does This

`_tryFireLoli` (forward.js:602-649) handles loli continuations in the state, but only supports **linear** triggers — it matches trigger hashes against `state.linear`. A bang trigger like `!eq(V,0)` needs backward proving, which `_tryFireLoli` doesn't do. So `expandItem` was made to eagerly decompose the loli as a **workaround** to avoid the firing mechanism entirely — and the workaround is unsound.

### Why CLF Avoids This Problem Entirely

CLF restricts what can appear inside the monad `{C}` to: atoms, `⊗`, `1`, `!`, `∃`. **No lolis allowed.** This is deliberate — lolis inside the monad create "dormant rules" that need a firing mechanism (matching trigger, proving guard, scheduling). CLF's monadic semantics are simpler: everything in `{C}` immediately decomposes into state updates. The monadic let `{A} ⊗ (A ⊸ {B}) ⊸ {B}` provides sequencing at the **rule level** (between separate forward rules), not inside a single consequent.

Our EVM rules violate this restriction by putting lolis inside `{...}`. This is an extension of CLF, not standard CLF.

### `expandItem` Is Correct for Everything Except Lolis

The `{ linear, persistent }` decomposition is the right model for CLF's allowed monadic connectives:

| Connective | Decomposition | Correct? |
|---|---|---|
| `atom` | `{ linear: [atom] }` | ✓ atom becomes a linear fact |
| `A ⊗ B` | cross product of A, B | ✓ tensor distributes |
| `!A` | `{ persistent: [A] }` | ✓ bang becomes persistent |
| `1` | `{ }` (empty) | ✓ one = no resource |
| `A & B` / `A ⊕ B` | alternatives of A, B | ✓ fork the execution tree |
| `A ⊸ B` | **BUG** | ✗ should stay as linear fact, fire later |

If we remove the loli case, `expandItem` becomes exactly CLF's monadic decomposition — correct by construction.

### `_tryFireLoli` Is Theoretically a Rule Application

`_tryFireLoli` is not ad-hoc — it's an implementation of the loli-left rule applied to facts in the state. A `loli(trigger, body)` in `state.linear` is a fact of type `A ⊸ B`. When `A` appears in the state (or can be proved), the loli-left rule fires: consume the loli, consume A (or mark the proof as used), produce B. `_tryFireLoli` implements this for **linear** triggers. The missing piece is handling **persistent** (bang) triggers.

### The Fix (staged)

**Stage 1: Correctness — extend `_tryFireLoli` for bang triggers**

The minimal fix:
1. **Remove** the loli case from `expandItem` (lines 150-159). Lolis become linear facts in the state, handled by `_tryFireLoli`.
2. **Extend** `_tryFireLoli` to detect bang triggers (`Store.tag(trigger) === 'bang'`).
3. For bang triggers: call `tryFFIDirect(unwrapped_trigger)` or fall back to backward proving.
4. If guard proves true → fire: consume loli, produce body.
5. If guard fails → loli stays dormant, branch becomes a stuck leaf (correct behavior — no corruption).

This is a small code change (~15 LOC) and makes the engine correct for our EVM rules.

**Stage 2: Optimization — eager guard pruning at ⊕ fork time**

Before creating a ⊕ branch, check if its loli guard is decidable (all arguments ground) and false. Skip dead branches at fork time rather than exploring them to quiescence. This is focusing — resolving synchronous choices eagerly when decidable. Reduces 13109 nodes back to ~63.

Note: Stage 2 is an **optimization** that depends on Stage 1 being correct. It should not be conflated with the correctness fix.

**Alternative: Rewrite EVM rules to avoid lolis in consequents**

Instead of `(!eq V 0 -o { stack SH 1 }) + (!neq V 0 -o { stack SH 0 })`, write:

```ill
evm/iszero:
  ... -o {
    ... *
    (stack SH 1 * !eq V 0) + (stack SH 0 * !neq V 0)
  }.
```

Here `!eq V 0` is a persistent fact assertion, not a loli guard. This avoids lolis in the monad entirely (CLF-compliant). **But it has the same bug** — asserting `!eq V 0` as a persistent fact when `eq(V,0)` hasn't been proved is exactly the same unsound decomposition.

The correct CLF-compliant form would need persistent antecedents **at the rule level** — two separate rules:

```ill
evm/iszero_true:  ... * !eq V 0  -o { ... * stack SH 1 }.
evm/iszero_false: ... * !neq V 0 -o { ... * stack SH 0 }.
```

This is always correct (guards are checked by `tryMatch` as persistent antecedents). But it duplicates the shared antecedent (`pc * code * gas * sh * stack`) across rules, inflating the rule count. It also loses the explicit ⊕ structure that connects the two branches.

**Tradeoffs:**

| Approach | Correctness | Code change | Rule count | Theory |
|---|---|---|---|---|
| Extend `_tryFireLoli` | ✓ (after fix) | ~15 LOC | Same | Extends CLF (lolis in monad) |
| Split into separate rules | ✓ (by construction) | ~0 LOC engine | 2× branching rules | CLF-compliant |
| Stage 2 pruning (on top of either) | ✓ + fast | ~30 LOC | Same | Focusing optimization |

**Recommendation:** Fix `_tryFireLoli` (Stage 1). This preserves the expressive ⊕-with-loli-guard pattern, and the fix is small. Add Stage 2 for performance. Consider rule splitting later if we want strict CLF compliance.

### Phase 4 Status: ⊕ Implemented, Bug Found
- [x] Analysis: ⊕ is the correct connective (not &) for decidable case splits
- [x] B1 independence: Problem B is independent of Problem A
- [x] Add `plus` (⊕) connective to `ill.calc` + rules to `ill.rules`
- [x] Grammar: `expr_plus` in tree-sitter, `convert.js`, `cst-to-ast.js`
- [x] Forward engine: `expandItem` treats `plus` like `with` (fork)
- [x] Focusing: ⊕ positive, ⊕L invertible, regex updated for numbered right rules
- [x] EVM rules rewritten: evm/eq (& → +), evm/iszero + evm/jumpi (merged with +)
- [x] Tests: 513 pass (397 core + 116 engine)
- [ ] **BUG: expandItem loli decomposition is unsound** — see above
- [ ] Stage 1: Extend `_tryFireLoli` for bang triggers, remove loli case from `expandItem`
- [ ] Stage 2: Eager guard pruning at ⊕ fork time
- [ ] Decide: keep loli-in-monad extension or split into separate rules?

---

## Symbolic Execution Foundation

### Phase 1: Research & Design — DONE
- [x] Design space exploration (R1-R5, S1-S3, T1-T7) — see `doc/dev/evm-modeling-approaches.md`
- [x] Tool comparison (hevm, halmos, K, Tamarin, Rosette) — see `doc/research/symbolic-arithmetic-design-space.md`
- [x] Expression simplification survey — see `doc/research/expression-simplification.md`
- [x] Equational completion theory — see `doc/research/equational-completion.md`
- [x] Symbolic branching analysis (Problem B) — see `doc/research/symbolic-branching.md`

### Phase 2: Bug Fix — DONE
- [x] Fix tryFFIDirect definitive failure (`forward.js:227`) — remove `skipModeCheck &&`
- [x] Test: non-multiModal FFI with non-numeric ground term → backward proving attempted

### Phase 3: Decide — Expressions vs Pure Backward Chaining
Expression constructors (`plus_expr`, `mul_expr`) embed computation results in term structure.
This may conflict with ILL's philosophy: all computation lives in persistent backward-chaining
predicates, terms are inert data. Alternative approaches (R2 loli/evar, R3 CPS, T6 freeze)
keep computation in the backward prover and avoid expression terms entirely.

- [ ] Prototype both: expression catch-alls (R1) vs loli-freeze (T6+R2)
- [ ] Evaluate: does the engine need expression terms, or can backward chaining handle everything?
- [ ] Decision checkpoint

### Phase 3a: Foundation — Problem A (if expressions chosen)
Only if Phase 3 decides in favor of expression constructors.
- [ ] Expression type constructors (`calculus/ill/prelude/symbolic.ill`)
- [ ] Catch-all backward clauses (equational completion)
- [ ] Confluence proof for restricted Store.put normalization
- [ ] Store.put restricted normalization (ground folding)
- [ ] Import wiring (`evm.ill` → `symbolic.ill`)
- [ ] Integration tests

### Phase 3b: Foundation — Problem A (if pure backward chaining chosen)
Only if Phase 3 decides against expression constructors.
- [ ] T6 loli-freeze: auto-emit loli on FFI mode mismatch (~20 LOC)
- [ ] T7 Mercury modes: reverse-mode FFI, result cache (~100 LOC)
- [ ] Eigenvariable fresh generation (if R2 chosen)
- [ ] Integration tests

### Phase 5: Simplification Approach (choose after benchmarking)
- Approach 1: Skolem + engine normalization (R1×S1 — hevm path)
- Approach 2: Skolem + ILL rules (R1×S2 — K path)
- Approach 3: Loli eigenvariables + constraint propagation (R2)
- Approach 4: Hybrid engine + ILL lemmas (R1×S3)
- Approach 5: CPS decomposition (R3×S1)

Cross-references: `doc/dev/evm-modeling-approaches.md`, `doc/research/equational-completion.md`

---

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

### Hypersequent Interpretation of Symexec Trees
**Priority:** LOW | **Status:** open question | **Depends on:** ⊕ implementation

The symexec tree is structurally a hypersequent: each leaf is a component sequent, the whole tree is their meta-level disjunction. ⊕L creates object-level alternatives; `explore()` builds the hypersequent. Pruning infeasible leaves = eliminating hypersequent components. Avron's framework could formalize what symexec computes. Explore once ⊕ machinery is working.

- [ ] Study Avron (1991) hypersequent calculus in context of symexec trees
- [ ] Formalize: is the symexec tree exactly a hypersequent derivation?
- [ ] Relationship between ⊕L (object-level case split) and hypersequent external structural rules

**See:** doc/research/symbolic-branching.md

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

### Disc-Tree for Backward Proving
**Priority:** LOW | **Status:** to think about once at scale

Discrimination tree indexing for backward chaining (prove/search). Currently backward proving
uses clause-index scan. At scale (100+ backward clauses), disc-tree could give O(depth) vs O(R)
candidate selection — same win as forward disc-tree (Stage 9). Not needed at current 44-rule scale.

- [ ] Profile backward proving at scale to confirm bottleneck
- [ ] Adapt `lib/prover/strategy/disc-tree.js` for backward clause indexing

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

- **Display Calculus Completeness** — decided to stay with ILL fragment (no par, why-not). ⊕ (plus) now added.
- **Proof Nets** — hard for multimodalities, low relevance
- **PDF/HTML proof export** — already have HTML UI
- **Isabelle Export** — formal verification of cut-elim, not needed now
- **Coalgebras over comonads** — deeper study needed, no urgency

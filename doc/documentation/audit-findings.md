---
tags:
  - architecture
  - code-quality
  - soundness
  - testing
  - optimization
  - engine
  - prover
  - implementation
---

# CALC Codebase Audit — Detailed Findings

10-phase audit of 27,322 LOC across ~85 JS files (TODO_0192).
Implementation plan lives in the TODO; this document is the reference for all findings.

## Question

Has the CALC codebase maintained clean separation of concerns, optimization soundness, and architectural coherence as it grew to ~27k LOC? Where is technical debt hiding, where are documentation gaps, and can we still generate proof terms for everything?

## Findings (Initial Overview)

### Scale

| Layer | LOC | Files |
|---|---|---|
| lib/engine/ | 15,639 | ~50 |
| lib/prover/ | 3,820 | ~15 |
| lib/zk/ | 2,376 | ~3 |
| lib/kernel/ | 2,253 | ~8 |
| lib/parser/ | 1,759 | ~6 |
| lib/calculus/ | 494 | ~3 |
| **Total lib/** | **27,322** | **~85** |
| tests/ | 26,426 | 63 |
| doc/ | ~71,875 | ~200 |

### Architecture Summary

Three-layer engine (generic → LNL → ILL) with dependency injection via `matchOpts`. Optimizations toggled via profiles (`bare`/`fast`/`evm`). Backward prover is 5-layer lasagne (L1-L4b). Bridge connects them via lax monad.

### Critical Issues Found

**P1 — Proof term verification gap for `loli_match`**: `guided-term.js` emits `rule: 'loli_match'` for consumed linear loliimplications, but `check-term.js` has NO handler for this rule type. Only `zk/witness.js` handles it. Guided-mode proof terms with linear loli firings cannot be verified by the standard checker.

**P2 — `check-term.js` is test-only**: The proof term checker is never called from any production code path — only from test files. Verification is entirely optional and only exercised by explicit test invocations.

**P3 — `verifyStep` (kernel.js) weakness**: The L1 kernel's premise verification uses subset check (expected ⊆ actual) rather than multiset equality. Extra formulas in actual premises are silently accepted. This weakens the trusted base.

**P4 — `structural-memo.js` hardcodes EVM predicates**: `computeControlHash` uses `Store.TAG['pc']` and `Store.TAG['stack']` directly — not calculus-agnostic. Would break for non-EVM calculi.

**P5 — ZK subsystem is 24/94 failures**: `chunked-witness.test.js` is 0/19 pass. The ZK path has drifted significantly from the main engine.

**P6 — `compose.js` is 2,085 LOC in a single file**: Grade-0 cut elimination, chain fusion, SROA, tabling cache, and multi-pass scheduler all in one file. Multiple concerns, hardest to audit.

### Separation of Concerns Assessment

**Clean:**
- Generic engine core (match/strategy/forward/explore) has zero imports from ill/ or lnl/
- LNL layer adds linear/persistent distinction without ILL knowledge
- Equational theories are pluggable via `eq-theory.js`
- Connectives injected via `opts.connectives` (not hardcoded)
- FFI registry is modular (`register`/`get`/`has`)

**Leaky:**
- `structural-memo.js` knows `pc`/`stack` predicate names (EVM-specific in generic layer)
- `show.js` excludes `['bytecode', 'calldata']` by default (EVM-specific)
- `compose-config.js` and `ill/` have ILL-specific SROA/fusion configs that could be calculus-config files
- `forward.js` and `explore.js` duplicate `matchOpts` assembly (~30 lines each)
- `opt/ffi.js` and `lnl/persistent.js` both have `maxDepth: 20000` hardcoded independently
- `backchain.js` hardcodes `_mvSlotsLen = 4_000_000`, `MAX_TRAIL = 32768`, `_MAX_RESOLVE_ITER = 500_000`

### Optimization Soundness Assessment

**Provably sound (have noFFI/bare fallback):**
- FFI predicates: every FFI has backward clause definitions; `test:noffi` verifies correctness without FFI
- Compiled clauses (tier 1/2/3): dispatch to same clauses as naive resolution
- Backward cache: monotone persistent context guarantees cache validity
- Fingerprint/disc-tree indexing: conservative (candidates ⊇ matches)
- Preserved optimization: syntactic sugar, desugared before engine
- Delta bypass: direct child extraction (structural identity)

**Sound but hard to verify:**
- `compose.js` grade-0 cut elimination: 2085 LOC of rewriting that should preserve semantic equivalence. Chain fusion (inc/plus/checked_sub), SROA, and residual resolution are complex transformations. Tests exist but no formal argument.
- Compiled existential chain (`existential-compile.js`): **zero test coverage**, 150 LOC
- Constraint feed (`constraint-feed.js`): **zero unit test coverage**, 57 LOC — prunes oplus alternatives via SAT
- Prediction/threaded dispatch (`prediction.js`): attaches control metadata, should not affect semantics

**Cannot be verified without test:**
- `existential-compile.js` — only reachable through specific rule shapes with existential slots. No isolated test.

### Naming Issues

**Verbose/Java-enterprise patterns (candidates for academic renaming):**

| Current | Proposed direction |
|---|---|
| `provePersistentWithFFI` | `prove!` or `proveP` (persistent goal resolution) |
| `provePersistentNaive` | `proveP_naive` or `resolve!` |
| `buildDiscriminatorIndex` | `discIndex` |
| `detectFingerprintConfig` | `fpConfig` |
| `findFingerprintValue` | `fpVal` |
| `executePersistentStep` | `execStep` or `step!` |
| `compilePersistentStep` | `compileStep` |
| `compileExistentialChain` | `compileExist` |
| `buildStrategyStack` | `stratStack` |
| `expandConsequentChoices` | `expandRHS` |
| `tryCompiledClause` | `tryCC` |
| `buildClauseDispatch` | `ccDispatch` |
| `applyMatchInPlace` | `apply!` or `applyMut` |
| `resolveExistentials` | `resolveE` |
| `matchDynamicRule` | `matchDyn` |
| `compilePatternMatch` | `compilePM` |
| `executePatternMatch` | `execPM` |
| `compilePremisePut` | `compilePut` |
| `collectExternalFreevars` | `extFV` |
| `proverBoundExternals` | `boundExt` |

### Documentation Gaps

| Topic | Status |
|---|---|
| `existential-compile.js` | Mentioned in dir listing only; no standalone doc |
| `backward-cache.js` semantics | No doc on invalidation conditions or soundness argument |
| `constraint-feed.js` | Not mentioned by name in any doc |
| `fuzz-ffi.js` tool | Not in CLAUDE.md Tooling section |
| `bench-history.js` tool | Not in CLAUDE.md Tooling section |
| `analyze-csub.js` tool | Not in CLAUDE.md Tooling section |
| Proof term pipeline end-to-end | `proof-terms.md` exists but doesn't cover full/guided/off modes or the `loli_match` gap |
| `matchOpts` composition | No doc; only discoverable by reading forward.js/explore.js source |
| Profile system (`optimizer.js`) | `optimization-architecture.md` lists it but no standalone reference |
| Circular dependency workarounds | Not documented; lazy `require()` in 4+ files |

### Observability Gaps

| What | Status |
|---|---|
| Forward engine steps | ✅ `onStep` hook |
| Persistent goal prove/fail | ✅ `onProveSuccess`/`onProveFail` hooks |
| Backward chainer (SLD resolution) | ❌ No hooks; no way to trace clause selection |
| Grade-0 compose passes | ❌ No hooks; 2085 LOC black box |
| Strategy stack decisions | ❌ No hooks; fingerprint/disc-tree/predicate layer choices invisible |
| Compiled clause dispatch tiers | ❌ Profile counters exist but not exposed via hooks |
| Cache hit/miss ratios | ❌ `CALC_PERF_PROFILE=1` only, no hook API |
| Rule compilation phases | ❌ No observability |
| Existential resolution | ❌ No hooks |
| Loli matching | ❌ No hooks |

### Technical Debt

1. **`doc/todo/`** — 48 legacy todo files in-repo (should be in hq-data only)
2. **Circular lazy requires** — `persistent.js`→`backchain.js`, `ffi.js`→`backchain.js`, `compiled-clauses.js`→`ffi.js` (3+ sites)
3. **Duplicate matchOpts assembly** — `forward.js` and `explore.js` build near-identical objects
4. **ZK subsystem drift** — 24 test failures, likely needs major update or explicit deprecation
5. **`monad.test.js`** — 9/53 failures from API drift
6. **`pt.js` summarizeSequent** — `f?.tag` on number hashes always shows `?` (broken debug display)
7. **`sequent.js:varIndex`** — unbounded module-level counter (appears dead in production paths)
8. **`_Gp/_Gt` worklists** — grow permanently, never shrink
9. **`manual-render.js` LaTeX schemas** — missing schemas for ~15 rules (bang, oplus, exists, forall, zero, monad variants)
10. **`guided-term.js` re-exports** — unnecessary indirection for `getLoliFromRule`/`buildRightTensor`

## Audit Phases

### Phase 1: Kernel & Proof Terms (correctness foundation)
**Scope:** `lib/kernel/` (2,253 LOC) + `lib/prover/` (3,820 LOC)
**Goal:** Verify the trusted base is actually trustworthy
- [x] Audit `verifyStep` subset-check weakness (kernel.js:167-174) — C1: confirmed weak, check-term.js is real verifier
- [x] Audit `check-term.js` — catalog all `unverified` gaps — C2: loli_match gap found
- [x] Audit `extractTerm` witness heuristics (generic-term.js) — C3: findEvidence fallback risk
- [x] Audit `unify.js` — undo capacity, shared worklists, theory integration — clean
- [x] Review `store.js` — tagId(0) gotcha, DEDUP collision behavior — clean, documented
- [ ] Document the full proof term pipeline: backward→bridge→forward→guided→check
- [ ] Add observability: backward chainer trace hooks
- [ ] Naming pass: kernel + prover function names
- [ ] Test: add missing `loli_match` check-term handler test
- [ ] Test: `manual-render.js` rule schemas

### Phase 2: Generic Engine Core (algorithmic heart)
**Scope:** `match.js`, `strategy.js`, `forward.js`, `explore.js`, `compile.js`, `backchain.js`, `fact-set.js` (~3,900 LOC)
**Goal:** Verify clean separation, understand every algorithm, add observability
- [ ] Audit `backchain.js` (999 LOC) — singleton pattern, slot machinery, trail
- [ ] Audit `compile.js` (743 LOC) — rule compilation phases A-H, PM instruction set
- [ ] Audit `match.js` (479 LOC) — tryMatch pipeline, matchOpts threading
- [ ] Audit `strategy.js` (302 LOC) — dual strategy mechanism (legacy discriminator vs stack)
- [ ] Audit `explore.js` (444 LOC) — DFS, cycle detection, mutation/undo
- [ ] Audit `fact-set.js` (486 LOC) — FactSet/Arena/State, Zobrist hash
- [ ] Extract shared matchOpts assembly from forward.js/explore.js
- [ ] Add observability: strategy stack decision hooks, existential resolution hooks
- [ ] Document `matchOpts` composition as standalone reference
- [ ] Naming pass: engine function names (see naming table above)
- [ ] Test: `state-ops.js`, `delta-bypass.js` unit tests — compiled-sub.js merged into state-ops.js in S3

### Phase 3: Optimization Modules (soundness audit)
**Scope:** `opt/` (1,630 LOC) + `backward-cache.js` + `optimizer.js`
**Goal:** Verify every optimization preserves semantics, can be toggled, is tested
- [ ] Audit `compiled-clauses.js` (929 LOC) — tier 1/2/3 dispatch, circular dep on ffi.js
- [ ] Audit `ffi.js` (457 LOC) — FFI proving, compiled persistent steps
- [ ] Audit `existential-compile.js` (150 LOC) — zero tests, needs isolation test
- [ ] Audit `prediction.js` (92 LOC) — threaded dispatch metadata
- [ ] Audit `structural-memo.js` (82 LOC) — EVM-specific predicates in generic layer
- [ ] Audit `backward-cache.js` (152 LOC) — soundness argument for cache validity
- [ ] Audit `constraint-feed.js` (57 LOC) — SAT pruning, zero tests
- [ ] Make structural-memo calculus-agnostic (inject predicate names)
- [ ] Document cache invalidation semantics
- [ ] Add tests: existential-compile, constraint-feed
- [ ] Add observability: compiled clause tier counters as hooks

### Phase 4: LNL + ILL Layers (calculus specifics)
**Scope:** `lnl/` (387 LOC) + `ill/` (~700 LOC) + `ill/ffi/` (~2,000 LOC)
**Goal:** Verify clean layering, FFI soundness, loli semantics
- [ ] Audit `persistent.js` (170 LOC) — proof cache, clause resolution
- [ ] Audit `existential.js` (82 LOC) — resolution + compiled chain integration
- [ ] Audit `loli.js` (135 LOC) — dynamic rule firing
- [ ] Audit `binlit-theory.js` (141 LOC) — equational theory correctness
- [ ] Audit `ill/ffi/arithmetic.js` (1,129 LOC) — all FFI predicates vs clause definitions
- [ ] Audit `loli-drain.js` (86 LOC) — optimization soundness
- [ ] Verify: run `fuzz-ffi.js` and expand its coverage
- [ ] Document loli-drain semantics
- [ ] Add `fuzz-ffi.js` to CLAUDE.md Tooling section

### Phase 5: Compose Pipeline (grade-0 cut elimination)
**Scope:** `compose.js` (2,085 LOC) + `resolve-all.js` (290 LOC) + `compose-config.js` (60 LOC) + `residual-resolver.js` (214 LOC)
**Goal:** Understand the most complex single file, verify transformation soundness, consider splitting
- [ ] Map all 7 compose passes with input→output types
- [ ] Audit chain fusion (inc/plus/checked_sub) soundness
- [ ] Audit SROA (array scalarization) soundness
- [ ] Audit tabling cache correctness
- [ ] Consider splitting compose.js into per-pass modules
- [ ] Add observability: per-pass hooks or logging
- [ ] Document compose pipeline end-to-end (expand grade0-composition.md)

### Phase 6: Entry Point & Loader (index.js orchestration)
**Scope:** `index.js` (1,112 LOC) + `convert.js` (799 LOC) + `store-binary.js` (463 LOC) + `directive-loader.js` (266 LOC)
**Goal:** Clean up entry point concerns, verify disk cache, audit convert pipeline
- [ ] Audit `index.js` — separate I/O (disk cache) from orchestration
- [ ] Audit `convert.js` — .ill→Store pipeline, preserved desugaring
- [ ] Audit `store-binary.js` — binary serialization correctness
- [ ] Clean up COMPOSE_DISK_VERSION management
- [ ] Document loader pipeline end-to-end

### Phase 7: Parser & Calculus Infrastructure
**Scope:** `lib/parser/` (1,759 LOC) + `lib/rules/` + `lib/meta-parser/` + `lib/calculus/` (494 LOC)
**Goal:** Verify parser correctness, understand @extends chain, audit grammar generation
- [ ] Audit Earley engine (earley.js) — ambiguity handling, error recovery
- [ ] Audit grammar generation (earley-grammar.js, 687 LOC) — precedence, forward rule annotations
- [ ] Audit meta-parser (@extends chain resolution)
- [ ] Audit .rules parser (rules2-parser.js)
- [ ] Verify: parser round-trip tests (parse → render → parse)

### Phase 8: Documentation & Tooling Refresh
**Scope:** All docs + tools/ + CLAUDE.md
**Goal:** Close all doc gaps, update CLAUDE.md, clean dead docs
- [ ] Write `existential-compile.md` documentation
- [ ] Write `matchOpts-reference.md` documentation
- [ ] Write `proof-term-pipeline.md` (end-to-end: backward→bridge→forward→guided→check)
- [ ] Update `optimization-architecture.md` with cache semantics + constraint-feed
- [ ] Add `fuzz-ffi.js`, `bench-history.js`, `analyze-csub.js` to CLAUDE.md Tooling
- [ ] Remove or archive `doc/todo/` (48 legacy files)
- [ ] Fix `pt.js:summarizeSequent` broken display
- [ ] Clean up circular lazy requires
- [x] Update test-overview.md with current known failures and timing (S3)

### Phase 9: Kolmogorov Density Pass (suckless cleanup)
**Scope:** Full codebase
**Goal:** Reduce LOC while preserving performance and correctness
- [x] Identify dead code paths (unused exports, unreachable branches) (S3: 30 unused exports removed)
- [ ] Deduplicate matchOpts assembly
- [ ] Collapse unnecessary re-exports (guided-term.js, opt/fingerprint.js) — disc-tree-opt.js deleted in S3
- [ ] Remove legacy `unifyBinlit`/`unifyStrlit`/`unifyArrlit` from unify.js
- [ ] Simplify `show.js` EVM-specific defaults
- [ ] Consider merging tiny files (<50 LOC): `grades.js`, `preserved.js` — compiled-sub.js merged into state-ops.js in S3
- [ ] Remove `doc/todo/` (4,019 LOC of legacy)
- [ ] LOC budget: target 10-15% reduction in lib/ without losing features

### Phase 10: Integration Verification
**Scope:** Full test suite
**Goal:** All tests green or explicitly marked as known-failure with tracking
- [ ] Fix or triage monad.test.js 9 failures
- [ ] Fix or triage ZK suite 24 failures (or explicitly deprecate ZK path)
- [ ] Fix or triage rule-analysis.test.js 11 failures
- [ ] Fix or triage type-check.test.js 3 failures
- [ ] Run `test:bare`, `test:fast`, `test:noffi` and verify all pass
- [ ] Verify proof term generation works for all execution profiles
- [ ] Run fuzz-ffi.js extended session
- [ ] Final benchmark comparison (bench:diff) to verify no regressions

## Phase 1 Findings: Kernel & Proof Terms

### Files Audited (6,073 LOC)

**Kernel (lib/kernel/, 2,253 LOC):**
- `store.js` (864) — Content-addressed flat TypedArray arena, SoA layout, FNV-1a dedup
- `unify.js` (551) — Union-find unification + two one-way matchers (pair-theta, indexed-theta)
- `substitute.js` (321) — Single sub, apply, applyIndexed, debruijnSubst, subCompiled
- `sequent.js` (183) — Sequent as `{ contexts, succedent }` with content-addressed hashes
- `ast.js` (200) — AST utilities: freeVars, getLoliFromRule, collectExternalFreevars
- `eq-theory.js` (101) — Equational theory API with O(1) dispatch, strlit built-in
- `fresh.js` (33) — freshEvar (BigInt counter) + freshMetavar (string counter)

**Prover (lib/prover/, 3,820 LOC):**
- `generic-term.js` (583) — Proof term signatures + extraction + CLF monadic terms
- `check-term.js` (402) — Trusted type checker (remaining-threaded linear resources)
- `focused.js` (338) — L3 Andreoli focusing: inversion, focus, decomposition, blur
- `guided-term.js` (284) — Forward trace to complete ILL proof terms
- `bridge.js` (263) — Lax monad mode switch: sequent to forward to rightFocus to ProofTree
- `context.js` (264) — Linear context as sorted Uint32Array multiset
- `generic.js` (224) — L2 search primitives: tryIdentity, applyRule, applicableRules
- `kernel.js` (215) — L1 proof tree verification (structural, weaker than check-term)
- `rule-interpreter.js` (192) — Descriptor to makePremises (defunctionalized)
- `pt.js` (138) — ProofTree class
- `state.js` (120) — FocusedProofState (inversion/focus phases)
- `meta-ctx.js` (111) — MetaCtx: WAM-style trail for metavar backtracking
- `rewrite-trace.js` (85) — Flat rewriting certificates (resource accounting)

### Correctness Findings

**C1. verifyStep uses subset check, not multiset equality (kernel.js:166-173)**
Severity: LOW (check-term.js is the real verifier)

The L1 kernel premise verification iterates expectedLinear and checks `actualLinear.includes(h)`. Problems:
1. Does not track multiplicity: if expected has [A, A], actual [A] passes (includes finds A twice)
2. Does not reject extra formulas in actual: actual [A, B, C] passes when expected is [A]
3. verifyTree comment (line 30-31) claims "Resource tracking enforced at tree level" but verifyTree does NOT do global resource tracking, it just recursively calls verifyStep

The actual trusted verifier is `check-term.js:check()` which uses remaining-threading: each checkTerm call returns `{ remaining }` (the linear delta AFTER consumption). Context-splitting rules thread remaining from one subterm to the next. Final check verifies `remaining.size === 0`.

Verdict: kernel.js:verifyStep is the weaker of two verification paths. check-term.js is the real trusted kernel. No production bugs, but the kernel.js path gives false assurance.

**C2. loli_match not handled in check-term.js**
Severity: MEDIUM (verification gap for guided mode with linear loli firings)

When `guided-term.js:buildStepTerm` encounters a linear loli consumption (not a persistent program rule), it emits `rule: 'loli_match'`. This term type has NO handler in `check-term.js:buildCheckerMap()`. The checker returns `fail('unknown rule: loli_match')`.

Only `zk/witness.js` (line 1009) handles loli_match. The standard checker cannot verify guided-mode terms containing linear loli firings. Test `guided-term.test.js` explicitly tests loli_match construction (line 224) but never feeds the result through check-term.js.

Fix: Add a loli_match checker to buildCheckerMap. Semantically it is: consume loli principal from delta, check antecedent proof against A, add B to delta, continue with second subterm. Structurally identical to focused loli_l (2-subterm variant) which already exists.

**C3. findEvidence fallback to evidence[0] on hash miss (guided-term.js:199-203)**
Severity: LOW (narrow trigger conditions)

When a ground persistent goal hash does not match any evidence entry (via === comparison), the function falls back to evidence[0]. This could return wrong evidence if multiple persistent antecedents share metavars and later goals ground shared metavars, causing hash divergence.

**C4. verifyTree comment misleading (kernel.js:30-31)**
Severity: DOC

Comment says "Resource tracking enforced at tree level by verifyTree." This is false. verifyTree does not track resource consumption between parent and children. The remaining-threading resource check lives in check-term.js, not kernel.js.

### Bug Findings

**B1. pt.js:summarizeSequent uses f?.tag on number hashes (line 104-110)**
Severity: LOW (debug display only)

Formula hashes are numbers. `f?.tag` on a number is always undefined. Every formula displays as '?'. Should use `Store.tag(f)`.

**B2. state.js:toString() calls .slice on number focusHash (line 83)**
Severity: LOW (would crash if toString called on focused state)

focusHash is a Store hash (number). Numbers do not have `.slice()`. Would throw TypeError if FocusedProofState.toString() were called with a focused state. Currently never called in production.

### Design Observations

**D1. Dual verification paths (kernel.js vs check-term.js)**

Two verification mechanisms:
- kernel.js:verifyTree: operates on ProofTree (sequent-level, structural, weaker)
- check-term.js:check: operates on GenericTerm (term-level, remaining-threaded, stronger)

check-term.js is strictly stronger. kernel.js exists as legacy. Consider documenting kernel.js as "structural sanity check" and check-term.js as "the trusted verifier".

**D2. check-term.js is test-only (not production-integrated)**

check-term.js:check() is never called from any production code path. Only used by: proof-terms.test.js, guided-term.test.js, zk-witness.test.js, zk-noffi-witness.test.js. Verification is entirely opt-in via tests.

**D3. Proof term pipeline complete assessment**

| Profile | Term construction | Verification | Unverified gaps |
|---|---|---|---|
| Backward-only | extractTerm | check-term.js:check | None (fully verified) |
| Full (no terms) | none | rightFocus structural | modeSwitch (forward trusted) |
| Full (with terms) | buildMonadicTerm (opaque CLF) | check-term.js monad_r ok(delta) | modeSwitch (opaque) |
| Guided | buildGuidedTerm (detailed ILL) | check-term.js recurses into evidence | loli_match (C2), ffi axioms |
| Flat rewrite trace | buildRewriteTrace | checkRewriteTrace resource conservation | Pattern matching not verified |

Three unverified gaps in production:
1. ffiAxiom: FFI computations trusted (by design, test:noffi covers correctness)
2. constraintUNSAT: dead branches from UNSAT constraints trusted
3. loli_match: linear loli firings in guided mode (fixable, C2)

**D4. Content-addressed store is clean and well-designed**

store.js is the most architecturally clean file:
- SoA layout with TypedArrays (Zig-portable)
- Content addressing via DEDUP Map with FNV-1a + 64-probe linear probing
- Arity-specialized put1/put2/put3 avoid array allocation on hot paths
- Tag registry with PRED_BOUNDARY cleanly separates built-in from user-defined
- Equational theories pluggable via eq-theory.js with O(1) dispatch
- snapshot/restore for binary serialization
- onClear/onReplace hooks for dependents
- Only issue: tagId(0) = atom = invalid (documented gotcha, fix in Zig rewrite)

**D5. Focused prover (focused.js) is clean (338 LOC)**

Clear Andreoli phase structure: pre-focusing (identity, copy), inversion (findInvertible, eagerly apply), focus (chooseFocus, try each with save/restore), decomposition (apply non-invertible), blur (return to inversion when focused formula becomes invertible). MetaCtx (WAM trail) with O(K) rollback. hasBindings() guard avoids O(N*S) tree resolution for ground proofs. No issues found.

**D6. Three matching algorithms (correct separation)**

1. unify(): bidirectional, union-find, for backward prover
2. match(): one-way, pair-based theta, for forward engine (legacy)
3. matchIndexed(): one-way, de Bruijn indexed theta, for forward engine (hot path)

Each serves a different caller. All share equational theory dispatch via _rewriteFromTag[]. arrlit stays inline in all three (Store normalization constraint, well-documented). No issues found.

### Magic Numbers Catalog (kernel + prover)

| File | Constant | Value | Purpose |
|---|---|---|---|
| store.js | INITIAL_CAPACITY | 4,000,000 | Arena term slots |
| store.js | linear probe limit | 64 | DEDUP collision probes |
| unify.js | UNDO_CAPACITY | 128 | matchIndexed undo stack |
| unify.js | _Gp/_Gt initial | 64 | Worklist initial capacity |
| focused.js | maxDepth | 100 | Proof search depth limit |
| bridge.js | maxSteps | 1000 | Forward engine step limit |
| ast.js | getLoliFromRule | 20 | Max bang/forall wrapper depth |

All reasonable defaults with clear documentation.

### Naming Audit (kernel + prover)

**Verbose names that could be shorter:**

| Current | File | Proposed |
|---|---|---|
| collectExternalFreevars | ast.js | extFV |
| proverBoundExternals | ast.js | boundExt |
| getPredicateHead | ast.js | predHead |
| getLoliFromRule | ast.js | ruleBody or loliOf |
| buildRightTensor | ast.js | rTensor |
| computeRuleSpecMeta | rule-interpreter.js | specMeta |
| buildRuleSpecsFromMeta | rule-interpreter.js | specsFromMeta |
| buildSignatureMap | generic-term.js | sigMap |
| genericTermSignature | generic-term.js | termSig |
| buildMonadicTerm | generic-term.js | monadicTerm |
| buildExploreTreeTerm | generic-term.js | exploreTerm |
| buildGuidedTerm | guided-term.js | guidedTerm |
| buildAntecedentProof | guided-term.js | antProof |
| buildConsequentDecompFromFacts | guided-term.js | consqDecomp |
| collectLinearLeaves | guided-term.js | linLeaves |
| executeModeSwitch | bridge.js | modeSwitch |
| buildRewriteTrace | rewrite-trace.js | rwTrace |
| checkRewriteTrace | rewrite-trace.js | checkRW |
| computeChildDelta | generic.js | childDelta |
| addDeltaToSequent | generic.js | addDelta |
| findIdentityPrincipal | generic-term.js | idPrincipal |
| extractBoundValue | generic-term.js | boundVal |

Theory-standard names kept: rightFocus, rightFocusTerm, findInvertible, chooseFocus, debruijnSubst.

### Observability Assessment (kernel + prover)

| Subsystem | Observable? | How |
|---|---|---|
| Backward proof search (focused.js) | No | No hooks; black box until final ProofTree |
| MetaCtx binding/backtracking | No | No hooks |
| Identity/copy axiom attempts | No | No hooks |
| Rule application (generic.js) | No | Only visible via ProofTree output |
| Mode switch (bridge.js) | Partial | Forward trace available via trace: true |
| rightFocus decomposition | No | Success/failure is opaque |
| check-term.js verification | No | Returns valid/error only; no step-by-step trace |

The backward prover is a black box. No trace of what the prover tried, why it failed, or which choice points it explored.

### Phase 1 Tasks Updated

- [x] Audit verifyStep subset-check weakness: C1 confirmed, check-term.js is real verifier
- [x] Audit check-term.js unverified gaps: C2 loli_match gap, ffi/constraintUNSAT by design
- [x] Audit extractTerm witness heuristics: C3 findEvidence fallback risk
- [x] Audit unify.js: clean, well-designed, no issues
- [x] Review store.js: clean, documented, tagId(0) gotcha known
- [x] Bugs found: B1 (pt.js summarize), B2 (state.js toString)
- [ ] Document the full proof term pipeline: backward to bridge to forward to guided to check
- [ ] Add observability: backward prover trace hooks
- [ ] Naming pass: rename verbose functions (see table above)
- [x] Fix C2: add loli_match handler to check-term.js (S2)
- [x] Fix B1: pt.js summarizeSequent should use Store.tag() (S2)
- [x] Fix B2: state.js toString should handle number focusHash (S2)
- [x] Fix C4: correct verifyTree comment about resource tracking (S3)
- [ ] Test: add loli_match verification test through check-term.js


## Conclusion

The codebase has maintained its core architectural discipline (3-layer engine, dependency injection via matchOpts, profile toggles) but accumulated complexity in: (1) large files that mix concerns (compose.js, index.js, backchain.js, compiled-clauses.js); (2) optimization modules with insufficient test isolation (existential-compile, constraint-feed); (3) drifted subsystems (ZK: 24 failures, monad bridge: 9 failures); (4) verbose naming that obscures the underlying theory; and (5) observability gaps in 7/10 major subsystems. The trusted base (kernel.js verifyStep) has a weakness. Proof term generation works but has a known gap (loli_match) and is test-only, not production-integrated. 10 phases of systematic work will address all issues.

## Phase 2 Findings: Generic Engine Core

### Files Audited (~4,822 LOC)

**Pattern Matching + Dispatch (match.js, 479 LOC):**
tryMatch pipeline: setup → matchAllLinear → existential resolution. matchOnePattern: 3 strategies (delta bypass → secondary index → general). Pooled Maps/theta (MAX_SLOTS=128). Re-exports from 4 modules (lnl/persistent, lnl/existential, lnl/loli, opt/ffi). PROFILE gating via CALC_PERF_PROFILE.

**Forward Engine (forward.js, 218 LOC):**
run() main loop: committed-choice forward chaining. applyMatchInPlace (mutating). Builds both legacy discriminatorIndex AND strategy stack but findMatch only uses the legacy path. Three trace levels (evidence/terms/string). Multi-alt SAT filtering. Inline lazy requires for ill/connectives and backchain.

**Strategy Stack (strategy.js, 302 LOC):**
Strategy stack: fingerprint → disc-tree → predicate (catch-all). `findMatch` has DUAL mechanism: legacy discriminatorIndex scan AND full predicate scan (does NOT use strategy stack). `findAllMatches` correctly uses strategy stack for explore. attachPredictions for Opt_H threaded code.

**Rule Compiler (compile.js, 743 LOC):**
8-phase compilation pipeline (A-H): flatten → triggers/discriminator → persistent deps → linearMeta → choice expansion → de Bruijn slots → existential detection → assemble. Plus WAM-inspired compiled pattern matching (PM_BIND/PM_CHECK/PM_GROUND/PM_COMPOUND) and compiled premise construction (PUT_GROUND/PUT_SLOT/PUT_COMPOUND/PUT_ARRLIT). In-memory compile cache cleared on Store.clear().

**Backchainer (backchain.js, 999 LOC):**
Class-based backward chainer with: slot-indexed flat theta array (MAX_SLOTS=32768), trail backtracking (O(delta) undo), iterative search state machine (4 phases), compiled pattern matching + premise construction, two-level indexing (pred → first-arg → clauses), committed-choice + tail-premise optimizations, chase chains, ground matching with equational theory dispatch, arrlit↔acons cross-tag matching. Singleton _defaultBackchainer. In-memory index cache.

**Explore (explore.js, 444 LOC):**
Exhaustive DFS exploration. 8-step algorithm: cycle check → memo check → structural memo → bound check → match → quiescent → branch → record. Arena-based undo (O(1) checkpoint, O(delta) restore). Multi-alt SAT pruning via EqNeqSolver. Evidence trace accumulation. Prediction fast path (Opt_H). Loli drain integration. Clear algorithm documentation (lines 198-218).

**FactSet + Arena + State (fact-set.js, 486 LOC):**
Per-tag sorted Int32Array groups with binary search. Incremental Zobrist hashing (order-independent, multiset-safe). Arena undo log (O(1) checkpoint, O(delta) restore). snapshotBulk() for read-only bulk copies (one allocation). State wraps linear + persistent FactSets. State IS the index.

**State Operations (state-ops.js, 112 LOC):**
Shared consume/produce/mutateState helpers. Preserved-skip optimization with pooled objects. applyCompiledSub dispatch for compiled substitution recipes.

**Delta Bypass (delta-bypass.js, 78 LOC):**
Direct child extraction for flat delta patterns. Skips full unification for patterns where all bindings are positional. _deltaWritten buffer fixed at 8 (B3).

**Pattern Utils (pattern-utils.js, 73 LOC):**
Tree walkers: isGround, collectMetavars, collectFreevars. Shared by compile.js and rule-analysis.js.

**EqNeqSolver (constraint.js, 183 LOC):**
Union-find with forbid list for eq/neq constraints. Checkpoint/restore via undo log. Ground short-circuit for known values. Used by explore for oplus branch pruning.

**Constraint Feed (constraint-feed.js, 57 LOC):**
feedPersistent (arena → solver), filterAltsBySAT (pre-filter oplus alternatives). Clean integration layer.

**Discrimination Tree (disc-tree.js, 252 LOC):**
Trie over preorder traversals of trigger patterns. O(pattern_depth) lookup vs O(R) predicate scan. Handles wildcard subtree matching. Post-filter verifies all trigger predicates present. Default catch-all layer replacing predicate filter.

**Rule Analysis (rule-analysis.js, 284 LOC):**
Preserved/consumed/produced/delta classification. N:M multi-match via hash counting. Delta bypass metadata (bindings, groundChecks, flat flag). Compiled substitution recipes for flat patterns.

**Support Files:**
- compiled-sub.js (31 LOC) — Compiled substitution dispatch
- preserved.js (42 LOC) — Preserved skip helpers
- grades.js (39 LOC) — SELL {0,1,ω} grade constants

### Correctness Findings

**C5. findMatch has DUAL strategy mechanism (strategy.js:192-252)**
Severity: MEDIUM (dead code / redundant work)

`findMatch()` uses TWO separate rule selection paths:
1. Legacy `discriminatorIndex` + `fpConfig` (lines 213-223): O(1) fingerprint lookup via discriminatorIndex built in forward.js
2. Falls through to flat `for (const rule of ruleList)` with inline predicate filtering (lines 226-237)

It does NOT use the strategy stack (`getCandidateRules`). The strategy stack is only used by `findAllMatches` (for explore). Meanwhile `forward.js:run()` builds BOTH a discriminatorIndex AND creates a strategy via detectStrategy — but findMatch ignores the strategy.

Fix: Unify findMatch to use the strategy stack, remove legacy discriminatorIndex path.

**C6. matchOpts assembly duplicated (forward.js:97-112 vs explore.js:160-175)**
Severity: LOW (divergence risk)

Both forward.js:run() and explore.js:explore() assemble a ~15-field matchOpts object with identical logic. If one is updated and the other isn't, behavior diverges silently.

Fix: Extract `buildMatchOpts(opts, calc, rc)` helper.

**C7. forward.js builds redundant legacy discriminatorIndex (forward.js:89-91)**
Severity: LOW (wasted work)

forward.js:run() creates `discriminatorIndex = buildDiscriminatorIndex(rules)` and passes it to findMatch. This duplicates what the fingerprint layer already does. The legacy path exists because findMatch predates the strategy stack.

**C8. PM_BIND and PM_CHECK are identical (compile.js:527-538)**
Severity: LOW (dead distinction)

In executePatternMatch(), PM_BIND and PM_CHECK have byte-identical implementations. PM_CHECK is never emitted by compilePatternMatch() (which only emits PM_BIND). The distinction is vestigial.

Fix: Remove PM_CHECK opcode; collapse to PM_BIND only.

### Bug Findings

**B3. _deltaWritten buffer overflow risk (delta-bypass.js:12)**
Severity: LOW (never triggers with current rules)

`_deltaWritten = new Array(8)`. Patterns with >8 metavar bindings would write past buffer without bounds check. All current rules have arity ≤ 5.

**B4. _pmStack overflow risk (compile.js:508)**
Severity: LOW (executePatternMatch not used in hot path)

`_pmStack = new Array(64)` (32 pairs). Deep patterns would overflow without bounds checking. Currently unused in production (backchain.js has its own _matchHead).

**B5. _mStack overflow risk (backchain.js:202)**
Severity: LOW (current patterns are shallow)

`_mStack = new Array(128)` (64 pairs). Deep pattern matching would overflow. All current patterns fit comfortably.

### Design Observations

**D7. Backchainer is the most ambitious single module (999 LOC)**

Implements a full WAM-inspired backward chainer:
- Slot-indexed theta (flat array, zero allocation in search loop)
- Trail-based backtracking with O(delta) undo
- 4-phase iterative state machine (INIT → SELECT → PREMISE → RESUME)
- Compiled pattern matching (PM_* instructions, Zig-portable)
- Compiled premise construction (PUT_* instructions, post-order)
- Two-level indexing (predicate head → first-arg constructor → clauses)
- Committed-choice + tail-premise optimizations (O(1) stack for linear-recursive predicates)
- Chase chains for transitive metavar resolution
- Ground matching with equational theory dispatch + arrlit↔acons
- Singleton pattern with Store.onClear() cleanup

Clean, well-commented, Zig-portable design. The only critique: singleton pattern forces non-reentrant use.

**D8. FactSet + Arena is clean (486 LOC)**

Zobrist hashing gives O(1) state equality (for cycle detection). snapshotBulk() is clever — one bulk Int32Array instead of 30-40 per-group slices. Arena undo is O(1) checkpoint + O(delta) restore. State IS the index — no separate buildStateIndex.

**D9. compile.js is thorough but large (743 LOC)**

Three distinct responsibilities in one file:
1. Rule compilation (compileRule, 230 LOC) — phases A-H
2. Compiled pattern matching (PM_*, 100 LOC) — unused by hot path
3. Compiled premise construction (PUT_*, 100 LOC) — used by backchainer

(2) is only used by backchain.js. Could be split to compile-pm.js, but the dependency is clean so low urgency.

**D10. Strategy stack not used by forward.js:findMatch**

The strategy stack (fingerprint → disc-tree → predicate) is used by explore.js via findAllMatches. But forward.js:findMatch uses the legacy inline approach. This means:
- explore gets disc-tree indexing (O(pattern_depth) per fact)
- forward gets flat scan + predicate check (O(R) per step)

For EVM rules (~400 rules), forward still benefits from fingerprint O(1) lookup for ~300 rules, with flat scan for the remaining ~100 non-fingerprinted rules. The disc-tree would help those 100 rules.

**D11. explore.js is well-documented**

The 8-step algorithm comment (lines 198-218) is a model of self-documenting code. Cycle detection, memoization, and SAT pruning are all clearly separated.

**D12. EqNeqSolver is minimal and correct (183 LOC)**

Path halving (not full compression) to keep undo simple. Ground short-circuit avoids touching union-find for known values. Clean checkpoint/restore.

**D13. Module-level mutable state (non-reentrant pools)**

| Module | Variable | Type | Risk |
|---|---|---|---|
| match.js | _poolConsumed/_poolReserved/_poolTheta | Map/Array | Cleared per call |
| match.js | _workPatterns/_workPositions | Array(32) | Non-reentrant |
| delta-bypass.js | _deltaWritten | Array(8) | Non-reentrant, size-limited |
| state-ops.js | _poolSkipCount/_poolSkipUsed | Object | Non-reentrant |
| disc-tree.js | _flat/_factFlat/_factArity | Array(64) | Non-reentrant |
| compile.js | _pmStack | Array(64) | Non-reentrant |
| compile.js | _compileCache | Map | Cleared on Store.clear() |
| backchain.js | _defaultBackchainer | Backchainer | Singleton, non-reentrant |
| backchain.js | _indexCache | Map | Cleared on Store.clear() |

All safe for single-threaded JS. Zig port needs thread-local or parameter-passing.

**D14. Compiled substitution pipeline is 4 levels deep**

1. subCompiled (kernel/substitute.js) — Direct Store.put from precomputed recipe
2. applyCompiledSub (compiled-sub.js) — Dispatches to recipe or fallback
3. applyIndexed (kernel/substitute.js) — Arity-specialized recursive traversal
4. apply (kernel/substitute.js) — Generic recursive traversal (legacy)

Clean progression from most-optimized to most-general.

**D15. match.js re-exports from 4 modules**

match.js re-exports: clearBackwardCache (lnl/persistent), resolveExistentials (lnl/existential), matchLoli (lnl/loli), provePersistentWithFFI + executePersistentStep + compilePersistentStep (opt/ffi). This is a facade pattern — callers import from match.js instead of 4 modules. Reasonable for backward compatibility but increases coupling.

### Magic Numbers Catalog (engine core)

| File | Constant | Value | Purpose |
|---|---|---|---|
| backchain.js | MAX_SLOTS | 32768 | Theta array capacity |
| backchain.js | MAX_TRAIL | 32768 | Trail undo capacity |
| backchain.js | _INITIAL_SEARCH_CAP | 512 | Search stack initial size |
| backchain.js | _MAX_RESOLVE_ITER | 500000 | _resolveSlots safety limit |
| backchain.js | _mvSlotsLen | 4000000 | Initial MV→slot mapping capacity |
| match.js | MAX_SLOTS | 128 | Forward theta capacity |
| delta-bypass.js | _deltaWritten | 8 | Written-slots buffer size |
| compile.js | _pmStack | 64 | Pattern match stack |
| disc-tree.js | buffers | 64 | Flatten buffer sizes |
| fact-set.js | DEFAULT_GROUP_CAP | 8 | Initial group capacity |
| forward.js | maxSteps default | 1000 | Forward run step limit |
| explore.js | maxDepth default | 100 | Explore depth limit |
| explore.js | linArena cap | 16384 | Linear undo arena |
| explore.js | perArena cap | 4096 | Persistent undo arena |

All reasonable. Two MAX_SLOTS constants (128 vs 32768) reflect different match-theta vs prove-theta capacities.

### Naming Audit (engine core)

**Verbose names that could be shorter:**

| Current | File | Proposed |
|---|---|---|
| resolveConnectives | compile.js | resolveConn |
| flattenAntecedent | compile.js | flattenAnte |
| unwrapComputation | compile.js | unwrapComp |
| expandChoiceItem | compile.js | expandChoice |
| expandConsequentChoices | compile.js | expandConsqChoices |
| collectOutputVars | compile.js | outputVars |
| buildDiscriminatorIndex | match.js | discIndex |
| detectFingerprintConfig | match.js | fpDetect |
| findFingerprintValue | match.js | fpValue |
| matchOnePattern | match.js | matchLinear1 |
| matchAllLinear | match.js | matchLinearAll |
| buildStrategyStack | strategy.js | buildStack |
| makeFingerprintLayer | strategy.js | fpLayer |
| attachPredictions | strategy.js | attachPred |
| computePatternRoles | rule-analysis.js | patternRoles |
| compileSubstitution | rule-analysis.js | compileSub |
| analyzeDeltas | rule-analysis.js | deltaAnalysis |
| findChangedPositions | rule-analysis.js | changedPos |
| matchDeltaBypass | delta-bypass.js | deltaBypass |
| buildPreservedSkip | preserved.js | preservedSkip |
| filterPreserved | preserved.js | filterPres |
| consumeLinear | state-ops.js | consume |
| produceLinear | state-ops.js | produce |
| producePersistent | state-ops.js | producePers |
| hashFactEntry | fact-set.js | zobristMix |
| compilePatternMatch | compile.js | compilePM |
| executePatternMatch | compile.js | execPM |
| compilePremisePut | compile.js | compilePut |
| compilePremiseKey | compile.js | compileKey |
| hashStateString | explore.js | stateHashStr |
| provePersistentNaive | lnl/persistent | proveNaive |
| provePersistentWithFFI | opt/ffi | proveFFI |
| filterAltsBySAT | constraint-feed.js | satFilter |
| feedPersistent | constraint-feed.js | feedPers |
| applyCompiledSub | compiled-sub.js | compiledSub |

Theory-standard names kept: tryMatch, backchain, checkpoint, restore, Arena, FactSet, lowerBound.

### Observability Assessment (engine core)

| Subsystem | Observable? | How |
|---|---|---|
| Rule selection (strategy.js) | No | No hooks; black box |
| Pattern matching (match.js) | No | No per-attempt hooks |
| Persistent proving | Partial | onProveSuccess/onProveFail hooks (bypassed by compiled step fast path) |
| Backward chaining (backchain.js) | Partial | trace option collects goal/clause attempts |
| Explore DFS (explore.js) | Partial | onStep hook per depth level |
| Forward main loop (forward.js) | Partial | onStep hook per step; trace for rule names |
| Constraint solver (constraint.js) | No | No hooks |
| Compiled PM (compile.js) | No | No hooks |
| Delta bypass (delta-bypass.js) | No | No hooks |

### Phase 2 Architecture Summary

Clean separation: compile → match → strategy → forward/explore. backchain.js is independent. fact-set.js provides the state backbone.

**Key strengths:**
- Zero-allocation hot paths (pooled buffers, typed arrays, slot indexing)
- Zig-portable design (flat arrays, no closures in hot path)
- Arena undo for backtracking (O(1) checkpoint, O(delta) restore)
- Incremental Zobrist hashing for state equality
- Strategy stack architecture (layered rule selection)
- Compiled pattern matching + premise construction (WAM-inspired)

**Key debt:**
1. forward.js:findMatch duplicates fingerprint logic instead of using strategy stack (C5)
2. matchOpts assembly duplicated between forward.js and explore.js (C6)
3. match.js is a facade re-exporting 4 modules (coupling)
4. PM_CHECK opcode defined but never used (C8)
5. Fixed-size buffers without bounds checking (B3-B5)
6. Singleton backchainer (non-reentrant)

### Phase 2 Tasks

- [ ] Unify findMatch to use strategy stack (C5 — remove legacy discriminatorIndex path)
- [ ] Extract buildMatchOpts helper (C6 — deduplicate forward.js/explore.js)
- [x] Remove PM_CHECK opcode (C8) (S3)
- [ ] Add bounds checking to _deltaWritten, _pmStack, _mStack (B3-B5)
- [ ] Naming pass: rename verbose functions (see table above)
- [ ] Consider splitting compile.js PM/PUT instructions to separate module
- [ ] Document match.js as facade, or inline re-exports into callers

## Phase 3 Findings: Optimization Modules (Soundness Audit)

### Files Audited (~2,619 LOC)

**opt/ modules:**
- `compiled-clauses.js` (929 LOC) — Tier 1/2/3 compiled clause dispatch
- `ffi.js` (457 LOC) — FFI proving pipeline + compiled persistent steps
- `existential-compile.js` (150 LOC) — Compiled existential chain (partial evaluation)
- `prediction.js` (92 LOC) — Opt_H threaded code dispatch
- `structural-memo.js` (82 LOC) — EVM-specific structural memoization
- `disc-tree-opt.js` (11 LOC) — Re-export wrapper
- `fingerprint.js` (32 LOC) — Re-export wrapper

**LNL layer (optimization-adjacent):**
- `lnl/persistent.js` (170 LOC) — provePersistentNaive (state → compiled → cache → clause)
- `lnl/existential.js` (82 LOC) — resolveExistentials dispatcher
- `lnl/loli.js` (135 LOC) — Dynamic rule (loli) matching
- `ill/loli-drain.js` (87 LOC) — Persistent-trigger loli drain

**Other:**
- `backward-cache.js` (152 LOC) — Mode-aware backward proof cache

### Correctness Findings

**C9. structural-memo.js hardcodes EVM predicate names (structural-memo.js:25-26)**
Severity: MEDIUM (leaks EVM into generic layer)

`computeControlHash()` hardcodes `Store.TAG['pc']` and `Store.TAG['stack']`. For non-EVM calculi, both are undefined → hash is always 0 → every state gets the same control hash → false memo hits suppress exploration.

Located in `lib/engine/opt/` (supposedly generic layer) but coupled to EVM domain.

Fix: Inject predicate names via options: `computeControlHash(state, { pcPred, stackPred })`.

**C10. backward-cache.js soundness argument is scattered (backward-cache.js:9-10 + explore.js:83-94)**
Severity: MEDIUM (correct but poorly documented)

Cache maps `(pred, inputs) → outputs` from backchainer results. The soundness argument spans two files and contradicts itself:
- backward-cache.js comment: "sound iff persistent context is monotonically growing"
- explore.js comment: "Arena undo DOES retract persistent facts on backtrack" followed by "cached failures may be stale on paths with more persistent facts"

Actual invariant: backchainer resolution depends only on the clause database (immutable within a run), NOT on persistent state. Therefore cached backchainer results are valid across all DFS paths. State lookup is a separate, uncached resolution path. The comments conflate these two paths.

**C11. Circular require between compiled-clauses.js and ffi.js (compiled-clauses.js:637)**
Severity: LOW (works at runtime, fragile for bundlers/Zig port)

`_resolveGuard` does `require('./ffi')` inside the function body. ffi.js already requires compiled-clauses.js at module level. Works because both are fully loaded when _resolveGuard runs, but fragile.

**C12. ffi.js provePersistentWithFFI docstring order is wrong (ffi.js:89)**
Severity: DOC

Comment says "1. FFI — O(1) arithmetic" but actual order is: 1. State lookup, 2. FFI, 3. Compiled clause, 4. Full clause. The code is correct; the docstring is stale.

**C13. First-arg indexing duplicated 4 times in compiled-clauses.js**
Severity: LOW (code duplication, 60 LOC)

The binlit→i/o/e / atom→child / isPredTag dispatch appears in:
1. `_firstArgHead()` (lines 43-58) — used by top-level tryCompiledClause
2. `_tryTier1WithArgs()` (lines 328-341) — standalone
3. `_tryTier2()` loop (lines 551-563) — standalone
4. `_tryTier3()` loop (lines 705-717) — standalone

Functions 2-4 should call `_firstArgHead()` or extract a shared helper.

**C14. existential-compile.js has zero direct tests**
Severity: MEDIUM (optimization correctness unverified in isolation)

`compileExistentialChain` and `executeCompiledStep` are tested only through e2e paths. No test verifies:
- Chain compilation produces correct specs
- Chain deref handles fused rules (A→B→concrete)
- FFI failure fallback per step
- Compiled vs non-compiled paths produce identical results

**C15. constraint-feed.js has zero tests**
Severity: LOW (simple glue, 57 LOC)

`feedPersistent` and `filterAltsBySAT` are simple enough that e2e coverage is sufficient. But `filterAltsBySAT` is critical for oplus pruning soundness — false positives would silently prune valid branches.

### Bug Findings

**B6. backward-cache.js probe metavar lookup is fragile (backward-cache.js:122-135)**
Severity: LOW

Primary lookup `thetaMap.get(mv)` fails when backchainer returns its own slot metavars instead of the probe metavars. Fallback scans all theta entries by metavar name string (O(N) per output). Works but relies on metavar naming convention.

**B7. Tier 2 _applyWrapStack uses shared _localTheta without snapshot (compiled-clauses.js:468-492)**
Severity: MEDIUM (latent bug for complex output wrappers)

Tier 2 does not save theta per recursive frame (Tier 3 correctly does via `savedTheta`). During unwind, `_applyWrapStack` reads `_localTheta` which was clobbered by the base case match. This is safe for current predicates (inc, plus, trie_get) whose output wrappers contain ONLY the recursive output metavar. But a predicate with additional metavars in the output wrapper would produce incorrect results.

Example trigger case: `foo(X, wrap(X, R)) :- foo(X, R)` — output wrapper `wrap(X, R)` needs X's binding from the match phase, which is lost in _localTheta.

Fix: Save theta snapshot per Tier 2 frame (same as Tier 3), or document the restriction.

### Design Observations

**D16. Compiled clause dispatch is partial evaluation of the backward chainer (929 LOC)**

Three tiers = first Futamura projection specialized to the clause set:
- Tier 1: Zero-subgoal → direct dispatch (trivially sound)
- Tier 2: Single self-recursive → iterative loop (sound for structural descent)
- Tier 3: Guards + tail-recursive → guarded loop (guards via Tier 1+2 + FFI, `_noTier3` prevents recursion)

The `_noTier3` flag in `tryCompiledClause` prevents infinite guard recursion — Tier 3 guards can only use Tier 1+2, not Tier 3 itself. This is a clean stratification.

The `_localTheta` / `_recTheta` dual buffer for Tier 2/3 prevents buffer collision when Tier 3 guards call `tryCompiledClause` (which uses `_localTheta` internally).

**D17. Persistent proving has two complete, parallel pipelines**

| Pipeline | For | Stages |
|---|---|---|
| provePersistentWithFFI | `useFFI=true` | State → FFI → Compiled Clause → Full Clause |
| provePersistentNaive | `useFFI=false` | State → Compiled Clause → Backward Cache → Full Clause |

Asymmetry is intentional: FFI mode doesn't need caching (FFI is fast); noFFI mode needs caching (backward chaining is expensive). Both use compiled clause dispatch. Both support evidence + hooks.

**D18. existential-compile.js is clean partial evaluation (150 LOC)**

For deterministic predicates (mode +...+-), ∃x.P(inputs, x) reduces to x := f(inputs). The compiled chain turns this into direct slot-to-slot dataflow: read theta → call FFI handler → write theta. Eliminates: subApplyIdx traversal, generic FFI dispatcher, output slot detection.

**D19. prediction.js (Opt_H) implements threaded code dispatch (92 LOC)**

Only for `fpConfig.type === 'virtual'` (EVM bytecode). Turns DFS exploration from O(R) per step (try all rules) to O(1) (predicted rule → verify match). Captures bytecodeElems/discIndex in closure for V8-constant access.

This is essentially a JIT-like optimization: instead of interpreting each state by scanning all rules, we predict the next rule from the match result.

**D20. loli.js is calculus-agnostic (135 LOC)**

Uses `matchOpts.connectives` for role resolution. No ILL-specific imports. Clean LNL layer module. Generates a synthetic "rule" object compatible with applyMatch, so the rest of the pipeline (mutateState, evidence, etc.) works unchanged.

**D21. loli-drain.js is sound for persistent-trigger lolis (87 LOC)**

Fires lolis whose trigger is ALL persistent (!P). Sound because:
1. Only the loli itself is consumed (no other linear resources)
2. Guards depend only on persistent facts (never retracted)
3. The loli consumption prevents re-firing
4. `while (drained)` handles cascading (new persistent facts enable new lolis)
5. Skips multi-alt lolis (oplus in body) — conservative correctness

**D22. disc-tree-opt.js and fingerprint.js are unnecessary re-export wrappers**

11 LOC and 32 LOC. They exist for opt/ namespace cleanliness but add no logic. Could be deleted — callers already import from disc-tree.js and match.js/strategy.js.

### Toggleability Audit

| Optimization | Toggle | Default |
|---|---|---|
| FFI proving | `dangerouslyUseFFI` | Off (adversarially sound) |
| Compiled clauses | `calc.clauseDispatch` exists | On if clauses available |
| Compiled persistent steps | `matchOpts.useCompiledSteps` | On with FFI, off without |
| Compiled existential chain | `matchOpts.useCompiledSteps` | Same as above |
| Fingerprint | `opts.useFingerprint` | On |
| Disc-tree | Always in strategy stack | On |
| Prediction (Opt_H) | `fpConfig.type === 'virtual'` | Auto-detected |
| Structural memo | `opts.structuralMemo` | Off (opt-in) |
| Backward cache | Always in noFFI path | On (cleared each run) |
| Loli drain | Always in explore.js | On |
| SAT pruning | Always in explore.js | On |
| Preserved optimization | `matchOpts.optimizePreserved` | On |

Most optimizations are always-on with graceful fallback. The major exception is FFI, which is deliberately off-by-default for adversarial soundness. The `useCompiledSteps` toggle correctly disables compiled fast paths when evidence/hooks are needed (observability preserving).

### Proof Term Interaction

| Optimization | Evidence/hook mode | Status |
|---|---|---|
| Compiled persistent steps | **Bypassed** (falls to generic path) | Correct |
| Compiled existential chain | **Bypassed** (falls to provePersistent) | Correct |
| FFI proving | Records `method: 'ffi'` in evidence | OK |
| Compiled clauses | Records `method: 'compiled'` in evidence | OK |
| Backward cache | Records `method: 'clause'` + re-proves for term if needed | OK |

Key principle: evidence/hook mode disables all compiled fast paths to ensure every goal is observable. The match loop in `match.js:matchAllLinear` (line 379) checks `!evidenceOut && !hasHooks` before using `executePersistentStep`. The existential resolver (existential.js:56-57) does the same check.

### Test Coverage Gaps

| Module | Direct test | Indirect coverage |
|---|---|---|
| compiled-clauses.js | `compiled-clauses.test.js` | hooks.test.js |
| ffi.js (proving) | (via e2e tests) | Extensive |
| existential-compile.js | **None** | e2e only |
| prediction.js | `prediction.test.js` | solc-benchmark.test.js |
| structural-memo.js | **None** | compiled-matcher.test.js (indirect) |
| disc-tree.js | `disc-tree.test.js` | Thorough |
| backward-cache.js | **None** | Implicit via forward/explore |
| constraint-feed.js | **None** | None found |

### Magic Numbers

| File | Constant | Value | Purpose |
|---|---|---|---|
| compiled-clauses.js | _MAX_LOCAL | 64 | Local theta buffer |
| compiled-clauses.js | MAX_DEPTH | 10000 | Tier 2/3 recursion limit |
| ffi.js | _FFI_MAX_ARITY | 5 | FFI args buffer |
| existential-compile.js | _args | 5 | FFI args buffer |
| backward-cache.js | maxDepth | 20000 | Backchainer depth for probe |
| persistent.js | maxDepth | 20000 | Same for naive path |

### Naming Audit

| Current | File | Proposed |
|---|---|---|
| buildClauseDispatch | compiled-clauses.js | clauseDispatch |
| tryCompiledClause | compiled-clauses.js | tryCCDispatch |
| _applyWrapStack | compiled-clauses.js | _unwind |
| _analyzeRecursiveClause | compiled-clauses.js | _analyzeRec |
| _analyzeTier3Clause | compiled-clauses.js | _analyzeTier3 |
| _buildTier2And3 | compiled-clauses.js | _buildTiers |
| _resolveGuard | compiled-clauses.js | _guard |
| provePersistentWithFFI | ffi.js | proveWithFFI |
| tryFFIDirect | ffi.js | ffiDirect |
| compilePersistentStep | ffi.js | compilePS |
| compilePersistentSteps | ffi.js | compilePSAll |
| executePersistentStep | ffi.js | execPS |
| compileExistentialChain | existential-compile.js | compileExChain |
| executeCompiledStep | existential-compile.js | execExStep |
| createPredictNext | prediction.js | predictNext |
| computeControlHash | structural-memo.js | controlHash |
| tryBackwardCache | backward-cache.js | tryBWCache |
| clearBackwardCache | backward-cache.js | clearBWCache |
| provePersistentNaive | persistent.js | proveNaive |
| resolveExistentials | existential.js | resolveEx |
| isPersistentTriggerLoli | loli-drain.js | isPersLoli |
| drainPersistentLolis | loli-drain.js | drainLolis |

Theory-standard: Futamura projection, threaded code, partial evaluation, union-find, Zobrist, WAM — all kept.

### Phase 3 Architecture Summary

The optimization modules form a well-structured pipeline:

```
matchAllLinear (match.js)
  ├─ executePersistentStep (fast path, opt/ffi.js)
  │   ├─ FFI spec → direct call
  │   └─ Compiled clause spec → tryCompiledClause
  ├─ provePersistent{WithFFI|Naive} (instrumented path)
  │   ├─ State lookup
  │   ├─ FFI direct (ffi.js) / Compiled clause (compiled-clauses.js)
  │   ├─ Backward cache (backward-cache.js) [noFFI only]
  │   └─ Full clause resolution (backchain.js)
  └─ resolveExistentials (lnl/existential.js)
      ├─ executeCompiledStep (compiled chain, existential-compile.js)
      └─ provePersistent per goal (fallback)
```

**Key strengths:**
- Every optimization has a graceful fallback to clause resolution
- Evidence/hook mode correctly bypasses all fast paths
- Clean separation between compile-time (rule loading) and run-time (match execution)
- Dual pipeline (FFI/noFFI) with toggle at matchOpts level
- Tier 1/2/3 compiled clauses are elegant partial evaluation

**Key debt:**
1. structural-memo hardcodes EVM predicates (C9)
2. Tier 2 output wrapping has latent bug for complex wrappers (B7)
3. First-arg indexing duplicated 4x in compiled-clauses.js (C13)
4. Backward cache soundness argument is scattered/contradictory (C10)
5. existential-compile.js and constraint-feed.js have zero tests (C14, C15)
6. disc-tree-opt.js and fingerprint.js are unnecessary re-export wrappers

### Phase 3 Tasks

- [ ] Fix C9: Make structural-memo calculus-agnostic (inject predicate names)
- [x] Fix B7: Save theta snapshot per Tier 2 frame (S2)
- [ ] Fix C13: Extract first-arg indexing to shared helper in compiled-clauses.js
- [ ] Fix C10: Consolidate backward cache soundness argument into one location
- [x] Fix C12: Update ffi.js docstring to match actual resolution order (S3)
- [ ] Add test: existential-compile.js isolation test (C14)
- [ ] Add test: constraint-feed.js filterAltsBySAT (C15)
- [ ] Add test: backward-cache.js direct (cache hit, miss, negative, invalidation)
- [ ] Consider: Remove fingerprint.js re-export wrapper — disc-tree-opt.js deleted in S3
- [ ] Naming pass: rename verbose functions (see table)

## Phase 4 Findings: LNL + ILL Layers (Soundness Audit)

### Files Audited (~3,273 LOC)

**LNL layer (lib/engine/lnl/, 387 LOC):**
- `persistent.js` (170 LOC) — provePersistentNaive: state → compiled clause → backward cache → full clause
- `existential.js` (82 LOC) — resolveExistentials: compiled chain → provePersistent → freshEvar
- `loli.js` (135 LOC) — matchLoli: trigger decomposition → linear match → persistent prove → body expand

**ILL layer (lib/engine/ill/, 801 LOC):**
- `backchain-ill.js` (115 LOC) — ILL-specific backchainer defaults (normalize, FFI, proof terms)
- `binlit-theory.js` (141 LOC) — Equational theory: binlit ↔ i/o/e structural form
- `connectives.js` (30 LOC) — ILL connective table (tag → category/arity/polarity)
- `loli-drain.js` (86 LOC) — Persistent-trigger loli drain optimization
- `bytecode-loader.js` (155 LOC) — Hex bytecode → grade-0 arr_get facts
- `compose-config.js` (60 LOC) — ILL chain fusion + SROA config for compose pipeline
- `residual-resolver.js` (214 LOC) — Compile-time persistent goal resolution

**FFI layer (lib/engine/ill/ffi/, 2,085 LOC):**
- `arithmetic.js` (1129 LOC) — 36+ FFI functions: pure arithmetic + EVM 256-bit modular/signed
- `array.js` (312 LOC) — arrlit O(1) + trie O(log N) operations, arrToTrie conversion
- `memory.js` (207 LOC) — Write-log memory model: mem_read, mem_expand, sha3_compute
- `calldata.js` (65 LOC) — cd_read for ground binlit calldata
- `convert.js` (126 LOC) — binToInt/intToBin + FFI-specific isGround
- `mode.js` (47 LOC) — Mode checking for FFI dispatch
- `index.js` (199 LOC) — Registry + defaultMeta for 46 FFI predicates

### Correctness Findings

**C16. Generic engine layer has 8 direct imports from ILL layer**
Severity: MEDIUM (prevents non-ILL calculi from using the generic engine)

The three-layer architecture (generic → LNL → ILL) is violated by direct imports:

| Generic module | ILL import | Purpose |
|---|---|---|
| `match.js:159` | `ill/ffi/convert.binToInt` | findFingerprintValue BigInt decode |
| `match.js:188` | `ill/ffi/array.trieNav` | Virtual fingerprint trie navigation |
| `constraint.js:17-18` | `ill/ffi/convert.{binToInt,isGround}` | EqNeqSolver value extraction |
| `forward.js:94` | `ill/connectives.ILL_CONNECTIVES` | Default connective table |
| `explore.js:102` | `ill/connectives.ILL_CONNECTIVES` | Default connective table |
| `opt/prediction.js:57` | `ill/ffi/array.trieNav` | Trie-based bytecode lookup |
| `opt/ffi.js:13` | `ill/ffi` (index) | FFI registry access |
| `opt/existential-compile.js:19` | `ill/ffi` (index) | FFI registry access |

A non-ILL calculus cannot use the generic engine without ILL being present. Fix: extract `binToInt`/`trieNav`/`isGround` to kernel or generic utility; inject connectives as required parameter (no defaults); inject FFI registry via matchOpts.

**C17. backchain.js hardcodes ILL defaults as fallback (backchain.js:897-914)**
Severity: MEDIUM (non-ILL calculi get ILL normalization and FFI)

`backchain()` uses ILL-specific defaults when callers don't provide overrides:
- `opts.normalize || illDefaults.normalize` (binlit canonicalization)
- `opts.tryFFI || illDefaults.tryFFI` (ILL arithmetic FFI)
- `opts.buildClauseTerm || illDefaults.buildClauseTerm` (ILL proof term construction)
- `opts.theories` default: `[...defaultTheories, binlitTheory]`

The import `const illDefaults = require('./ill/backchain-ill')` at line 26 is unconditional (top-level), so importing backchain.js always triggers ILL side effects (see C21).

Fix: Make normalize/tryFFI/theories required opts fields with no defaults, or use a neutral default (identity normalize, null tryFFI).

**C18. Two conflicting `isGround` definitions (pattern-utils.js vs ill/ffi/convert.js)**
Severity: LOW (confusing but correct in respective domains)

| Property | `pattern-utils.js:isGround` | `ill/ffi/convert.js:isGround` |
|---|---|---|
| arrlit elements | Recurses into | Opaque (always ground) |
| freevar | `false` (structural) | `true` (eigenvariable) |
| Invalid hash | `true` (vacuous) | `false` |
| Used by | compile.js, persistent.js (generic) | mode.js, arithmetic FFI, **constraint.js** (generic!) |

`constraint.js` (generic layer) uses the FFI-specific `isGround` — semantically wrong for a generic module. The difference matters when freevars appear in constraints.

**C19. residual-resolver.js duplicates FFI logic for 11 predicates (214 LOC)**
Severity: LOW (code duplication, divergence risk)

Identical arithmetic formulas appear in:
1. `ill/ffi/arithmetic.js` / `ill/ffi/array.js` / `ill/ffi/calldata.js` (runtime: `args[] → {success, theta}`)
2. `ill/residual-resolver.js` (compile-time: `goalHash → factHash|null`)

Different signatures prevent direct reuse, but the computation (binToInt → operate → intToBin) is identical. A formula change (e.g., EVM gas rule) requires updating both.

Fix: Extract shared `computeResult(pred, groundArgs) → bigint|null`, wrap in FFI-style and resolver-style adapters.

**C20. backchain-ill.js has import-time side effects (lines 22-29)**
Severity: MEDIUM (global Store mutation on require)

```js
const _ATOM_E = Store.put('atom', ['e']);     // registers 'e' atom
Store.put('atom', ['ae']);                     // registers 'ae' atom
Store.put('o', [_ATOM_E]);                    // registers 'o' predicate tag
Store.put('i', [_ATOM_E]);                    // registers 'i' predicate tag
setTheories([...defaultTheories, binlitTheory]); // installs ILL equational theory globally
```

Any `require('backchain.js')` → `require('ill/backchain-ill')` → these Store mutations fire. Non-ILL calculi importing the backchainer get ILL atoms/tags/theories registered globally.

Fix: Move tag registration and theory setup to an explicit `initILL()` function called by the ILL entry point.

**C21. sstore_gas returns conservative estimate for symbolic inputs**
Severity: LOW (documented design choice, technically unsound for exhaustive verification)

`sstore_gas(OldVal, NewVal, Cost)` returns `cost=5000` when inputs are non-ground (line 1041-1042). The true cost is 20000 when `OldVal=0 && NewVal≠0`. This under-approximation means gas deduction is lower than reality for symbolic SSTORE → paths that should OOG may be falsely accepted.

Documented as "conservative default" — acceptable for concrete execution. For exhaustive symbolic verification, this creates false positives (accepting infeasible paths).

### Design Observations

**D23. LNL layer is clean and minimal (387 LOC, 3 files)**

No ILL-specific imports. Connectives arrive via `matchOpts.connectives`. provePersistent via `matchOpts.provePersistent`. This is the model for how the ILL layer should be connected too.

- `persistent.js`: 4-stage pipeline (state → compiled clause → backward cache → full clause)
- `existential.js`: compiled chain → per-goal provePersistent → freshEvar fallback
- `loli.js`: full loli lifecycle (trigger decompose → linear match → persistent prove → body expand → choice detect)

`_singleGoal` reusable array in existential.js avoids allocation per provePersistent call.

**D24. ILL connective table enables calculus polymorphism (30 LOC)**

`resolveConnectives(ct)` (compile.js:36-51) maps structural properties to roles:
- multiplicative positive arity-2 → product (tensor)
- multiplicative negative arity-2 → implication (loli)
- exponential arity-2 → exponential (bang)
- monad arity-1 → computation (monad)
- additive positive/negative → internal/external choice (oplus/with)

Any calculus with these structural roles works with the engine. The connective table is the correct boundary — but the ILL defaults in forward.js/explore.js undermine it.

**D25. FFI arithmetic is comprehensive and correct (1129 LOC)**

36+ functions covering:
- Pure arithmetic: plus (multi-modal: `++- ` and `-++`), inc, mul, sub (saturating), div, mod
- EVM modular: sub256 (wrapping), div256/mod256 (zero-safe), exp256 (square-and-multiply)
- EVM signed: sdiv256, smod256, slt, sar256, signextend256
- EVM compound: addmod256, mulmod256 (unbounded intermediates via BigInt)
- Bitwise: and, or, not, xor, shr, shl, byte256, byte_replace
- EVM predicates: checked_sub, sstore_gas, byte_size256, is_push/is_dup/is_swap
- Non-numeric: string_concat, string_length, fixed_mul, fixed_div, trim

Shared `EMPTY_THETA = []` avoids allocation for comparison predicates (lt, le, eq, neq). `MOD_256`, `SIGN_BIT`, `MOD_2_256` constants cached at module level.

`exp256` correctly implements square-and-multiply with modular reduction at each step. `0^0 = 1` per EVM spec (line 689-691).

**D26. binlit equational theory is elegant (141 LOC)**

Single source of truth for the binary number representational equivalence. Three concerns:
1. `canRewrite`: identifies binlit → atom/o/i rewrite opportunities
2. `rewrite`: expands binlit(N) to structural form matching a destination tag
3. `canonicalize`: normalizes structural forms back to compact binlit (recursive into compounds)

The canonicalize recursion is necessary: forward engine state may contain nested binary terms (e.g., `inc(i(o(e)), ?Y)` → needs `inc(binlit(2n), ?Y)` for consistent hashing).

**D27. Memory FFI models McCarthy's write-log correctly (207 LOC)**

`mem_read` walks `write(offset, value, rest)` chain with byte-level coverage tracking:
- Exact hit optimization: `wOff === offset && coveredCount === 0` → return value hash directly (handles symbolic values)
- Partial overlap: extract concrete bytes into 32-byte result buffer
- Multiple overlapping writes: first-writer-wins (write-log semantics)
- `readByte` helper for sha3_compute: word-aligned read then byte extraction

`mem_expand`: EVM high-water-mark formula `cost(words) = 3w + w²/512`. Zero-length access does NOT expand (EVM spec).

**D28. Array FFI dual representation is clean (312 LOC)**

arrlit path: O(1) via `Store.getArrayElements` (Uint32Array direct indexing)
trie path: O(log N) via `trieNav` (bit-indexed binary trie, `tn(left, val, right)`)

`arrToTrie` converts arrlit → trie when large arrays need persistent functional updates. `Store.onClear` hook ensures cached trie tag IDs are reset on Store clear (test isolation).

`notMember` handles both arrlit and acons/ae chains — clean dual-representation pattern.

**D29. bytecode-loader correctly handles PUSH data (155 LOC)**

The key insight: PUSH data bytes are NOT valid instruction positions. `isFillerPosition` array marks them to prevent generating arr_get facts that would create phantom specialized rules. This was a real bug at some point (comment at line 79-82 explains the consequence: "data byte 0x01 → phantom ADD rule").

Entry point detection: PC=0 always + JUMPDEST (0x5b) positions. Standard EVM analysis.

**D30. compose-config is the correct DI point (60 LOC)**

Chain fusion configs describe predicate families with algebraically collapsible chains:
- `inc(X,Y) * inc(Y,Z) → plus(X, 2, Z)` (unary step → binary accumulate)
- `plus(X,2,Y) * plus(Y,3,Z) → plus(X, 5, Z)` (binary + binary → binary)
- `checked_sub(G,3,G2) * checked_sub(G2,5,G3) → checked_sub(G,8,G3)`

SROA config: `arr_get`/`arr_set` on `stack` resource → scalarize.

Both injected via `index.js` with ILL defaults. Non-ILL calculi provide their own configs.

**D31. residual-resolver covers 11 predicates at compile time (214 LOC)**

Required because FFI operates on runtime args arrays, but compile-time resolution operates on Store hashes. The `_isGroundArg` helper (line 210-212) checks `typeof h === 'number' && Store.tag(h) !== 'metavar'` — correct for compile-time ground check.

`cd_read` resolver has the same leading-zero limitation as the FFI version — well-documented in both places.

### Layer Architecture Assessment

```
                   ┌──────────────────────────────────────────┐
                   │  index.js (integration point)            │
                   │  Wires ILL defaults into generic engine  │
                   └─────────────┬────────────────────────────┘
                                 │ injects via opts
          ┌──────────────────────┼──────────────────────────┐
          │  ILL Layer           │                          │
          │  backchain-ill.js    │  ill/ffi/*               │
          │  binlit-theory.js    │  compose-config.js       │
          │  connectives.js      │  bytecode-loader.js      │
          │  loli-drain.js       │  residual-resolver.js    │
          └──────────────────────┼──────────────────────────┘
                                 │
          ┌──────────────────────┼──────────────────────────┐
          │  LNL Layer           │                          │
          │  persistent.js       │  CLEAN — no ILL imports  │
          │  existential.js      │  Connectives via DI      │
          │  loli.js             │                          │
          └──────────────────────┼──────────────────────────┘
                                 │
          ┌──────────────────────┼──────────────────────────┐
          │  Generic Layer       │                          │
          │  match.js ──────────────→ ill/ffi/convert ✗     │
          │  constraint.js ─────────→ ill/ffi/convert ✗     │
          │  forward.js ────────────→ ill/connectives ✗     │
          │  explore.js ────────────→ ill/connectives ✗     │
          │  backchain.js ──────────→ ill/backchain-ill ✗   │
          │  opt/ffi.js ────────────→ ill/ffi ✗             │
          │  opt/prediction.js ─────→ ill/ffi/array ✗       │
          │  opt/existential-compile→ ill/ffi ✗             │
          └─────────────────────────────────────────────────┘
```

The LNL layer is perfectly clean. The generic layer has 8 upward dependency violations marked ✗. The root cause is that `binToInt`, `trieNav`, and `isGround` are genuinely generic operations (BigInt extraction from Store terms) that happen to live in the ILL FFI module.

Fix strategy:
1. Move `binToInt`/`intToBin`/`isGround` to `kernel/` or `engine/` (they depend only on Store)
2. Move `trieNav` to `engine/` or make the trie tag pluggable
3. Remove ILL connective defaults from forward.js/explore.js (require explicit connectives)
4. Make backchain.js imports lazy + neutral defaults

### Test Coverage

| Module | Direct tests | Coverage quality |
|---|---|---|
| lnl/persistent.js | **None** | e2e via forward/explore |
| lnl/existential.js | **None** | e2e via forward/explore |
| lnl/loli.js | **None** | Indirect via evidence.test.js |
| ill/backchain-ill.js | **None** | Via backchain callers |
| ill/binlit-theory.js | Yes | primitives.test.js (44 tests) |
| ill/connectives.js | Structural data only | No logic to test |
| ill/loli-drain.js | Partial | evidence.test.js (13 tests) |
| ill/bytecode-loader.js | Yes | bytecode-loader.test.js (23 tests) |
| ill/compose-config.js | Indirect | Via sroa/fusion tests |
| ill/residual-resolver.js | Partial | compose-chain-fusion.test.js |
| ill/ffi/arithmetic.js | Yes | primitives.test.js (44 tests) |
| ill/ffi/array.js | Yes | arrlit.test.js (82 tests) |
| ill/ffi/memory.js | Yes | memory.test.js (33 tests) |
| ill/ffi/calldata.js | Partial | calldata.test.js (via ILL rules) |
| ill/ffi/convert.js | Yes | Used across many tests |
| ill/ffi/mode.js | **None** | 47 LOC, simple logic |
| ill/ffi/index.js | Indirect | Via forward.test.js |

Key gap: LNL layer has zero direct tests. Since it's the clean separation layer, testing it in isolation would catch regressions when the layers are refactored.

### Magic Numbers

| File | Constant | Value | Purpose |
|---|---|---|---|
| arithmetic.js | MOD_256 | 2^256-1 | 256-bit mask |
| arithmetic.js | SIGN_BIT | 2^255 | Two's complement sign |
| arithmetic.js | MOD_2_256 | 2^256 | Two's complement modulus |
| memory.js | 32 | 32 | EVM word size (bytes) |
| memory.js | 512 | 512 | EVM memory cost divisor |
| calldata.js | 32 | 32 | CD read size (bytes) |
| bytecode-loader.js | 0x60-0x7f | PUSH1-PUSH32 | EVM PUSH opcode range |
| bytecode-loader.js | 0x5b | JUMPDEST | EVM JUMPDEST opcode |
| index.js | 46 entries | — | FFI predicate count |

All EVM-standard constants. No unexplained magic numbers.

### Naming Audit

| Current | File | Proposed |
|---|---|---|
| provePersistentNaive | persistent.js | proveNaive |
| resolveExistentials | existential.js | resolveEx |
| matchLoli | loli.js | matchDynRule |
| isPersistentTriggerLoli | loli-drain.js | isPersLoli |
| drainPersistentLolis | loli-drain.js | drainLolis |
| isAllPersistentAntecedent | loli-drain.js | isAllBang |
| findFingerprintValue | match.js | fpValue |
| buildClauseTerm | backchain-ill.js | clauseTerm |
| buildFFITerm | backchain-ill.js | ffiTerm |
| buildTypeTerm | backchain-ill.js | typeTerm |
| computeControlHash | structural-memo.js | controlHash |
| residualResolver | residual-resolver.js | resolve |
| loadBytecode | bytecode-loader.js | loadBC |
| bytecodeArrGetGuard | bytecode-loader.js | bcGuard |
| ILL_CHAIN_CONFIGS | compose-config.js | CHAIN_CONFIGS |
| ILL_SROA_CONFIG | compose-config.js | SROA_CONFIG |

Theory-standard: binToInt, intToBin, canonicalize, rewrite, trieNav, union-find, checkpoint/restore — all kept.

### Phase 4 Tasks

- [ ] Fix C16: Move binToInt/intToBin/isGround(FFI)/trieNav to kernel/ or engine/ utility
- [ ] Fix C16: Remove ILL connective defaults from forward.js/explore.js (require explicit parameter)
- [ ] Fix C17: Remove ILL defaults from backchain.js (neutral defaults or required opts)
- [ ] Fix C20: Move backchain-ill.js side effects to explicit initILL() function
- [ ] Fix C19: Extract shared arithmetic computation for residual-resolver.js and FFI
- [ ] Fix C18: Rename FFI isGround to distinguish from pattern-utils.isGround
- [ ] Add test: LNL persistent.js direct test (state lookup, compiled clause, cache, clause fallback)
- [ ] Add test: LNL existential.js direct test (compiled chain, provePersistent, freshEvar)
- [ ] Add test: LNL loli.js direct test (trigger decompose, linear match, persistent prove)
- [ ] Add test: ffi/mode.js direct test
- [ ] Naming pass: rename verbose functions (see table)
- [ ] Consider: Extract trie operations from ill/ffi/array.js to separate engine module

## Phase 5 Findings: Compose Pipeline (Grade-0 Cut Elimination)

### Files Audited (~2,375 LOC)

- `compose.js` (2085 LOC) — Three-layer API: L1 atomic operations → L2 analysis → L3 orchestration
- `resolve-all.js` (290 LOC) — Compile-time SLD resolution (enumerate all ground solutions)

(compose-config.js and residual-resolver.js were audited in Phase 4; cross-references noted here.)

### Pipeline Map: 8 Passes

```
composeGrade0(compiledRules, connectives, getModeMeta, clauses, definitions, extraGrade0Facts, scopeGuard, opts)
│
├─ Pass 1: Linear composition (grade-0 cut elimination)
│   composePair(producer, consumer, cutPredHead, rc, getModeMeta)
│   For each grade-0 predicate: all producer×consumer pairs
│   Input: compiled rules with hasGrade0
│   Output: raw rules without grade-0 types (cut eliminated)
│
├─ Pass 2: Multi-stage persistent specialization
│   specializePersistent(rule, factHash, factName, predHead, rc, getModeMeta)
│   Stage order: buildEliminationOrder → Kahn's toposort
│   Includes tabling: resolveAll for grade-0 clauses with premises
│   Input: raw rules + grade-0 facts (from clauses + extraGrade0Facts)
│   Output: specialized rules with persistent goals resolved
│   Transitive: _resolveResidualOnce after each specialization
│
├─ Pass 3-4: Batch residual resolution (safety net)
│   _resolveResidualBatch(pool, rc, getModeMeta, resolver)
│   Catches any remaining resolvable goals missed by transitive pass
│
├─ Pass 5: Basic block fusion (linear cut elimination)
│   _fuseBasicBlocks(pool, rc, getModeMeta, linearFusionPredicate, fusionBarriers)
│   fuseLinearPair / fuseLinearPairExpanded (handles oplus)
│   Chains 1:1 producer→consumer pairs via ground threading resource
│   Input: specialized rules + pc predicate
│   Output: fused mega-rules (marked isFused: true)
│
├─ Pass 5.5: Additive chain fusion
│   _fuseAdditiveChains(pool, rc, getModeMeta, chainConfigs)
│   Collapses inc→inc→inc chains to plus(X, N, Y) etc.
│   Safety: intermediate metavars must not appear elsewhere
│
├─ Pass 5.6: Second residual resolution (after fusion)
│   Fusion may create newly-ground goals
│
├─ Pass 6: McCarthy normalization + SROA
│   _sroaStackDecomposition → _mccarthyNormalize → _trySROA
│   McCarthy: peel acons layers via select/store axioms
│   SROA: expand cons pattern into individual slots
│   Only for isFused rules with array-access goals
│
└─ Pass 6.5: Post-SROA residual resolution
    McCarthy + SROA ground variables, enabling dependent goal resolution
```

### Correctness Findings

**C22. Tabling cache uses weak 32-bit hash key (compose.js:39-44)**
Severity: LOW (collision unlikely in practice, catastrophic if triggered)

`_tablingCacheKey` accumulates clause hashes via `h = (h * 31 + cl.hash) | 0` — a 32-bit hash. Two different clause sets could collide → cache returns wrong grade-0 facts → silently incorrect rule specialization. The probability is ~1/2^32 per pair, but the consequence is silent soundness violation.

`_composeFullKey` (line 46-58) has the same issue, covering the full compose output cache.

Fix: Use a Map keyed by a tuple or string representation, or use a collision-resistant hash. Or at minimum, store the original key material alongside the cache entry for verification on hit.

**C23. resolve-all.js is ILL-coupled (lines 17, 24, 167, 211-237)**
Severity: MEDIUM (same class as C16 — prevents non-ILL calculi)

Direct ILL imports:
- `require('./ill/binlit-theory')` — binlit canonicalization
- `require('./ill/ffi/convert')` — binToInt/intToBin for `between` handler
- `require('./backchain')` → `require('./ill/backchain-ill')` → ILL Store side effects
- `setTheories([...defaultTheories, binlitTheory])` called on every `resolveAll` invocation

The `between` predicate handler (lines 211-237) is domain-specific — hardcoded in a generic SLD resolver. Should be injectable via opts or a predicate extension mechanism.

**C24. composePair handles only single-instance grade-0 predicates per rule (compose.js:263-264)**
Severity: LOW (documented limitation, bridge detection catches violations)

`findByPredHead` returns the FIRST match. If a rule produces or consumes two grade-0 facts of the same predicate head, only the first participates in the cut. This is guarded by the bridge detection (Pass 1 validation, lines 1798-1804) which rejects multi-predicate grade-0 rules.

**C25. Theta composition in _resolveResidualOnce uses O(N²) linear scan (compose.js:736-741)**
Severity: LOW (N = number of resolved goals, typically < 20)

```js
for (let j = 0; j < combinedTheta.length; j++) {
  combinedTheta[j][1] = apply(combinedTheta[j][1], theta_i);
}
for (const [mv, val] of theta_i) {
  if (!combinedTheta.find(([m]) => m === mv)) combinedTheta.push([mv, val]);
}
```

The `.find(([m]) => m === mv)` on line 740 is O(N) per theta_i entry. Total: O(N*M) where N = combinedTheta.length, M = theta_i.length. Fine for compose-time (not hot path) but could use a Set for idempotent composition.

**C26. fuseLinearPair predicate-by-predicate matching is unsound for duplicate predicates (compose.js:893-932)**
Severity: LOW (guarded by uniqueness check, returns null on failure)

When matching producer consequent linear against consumer antecedent linear, the code only matches predicates that appear exactly once on each side (line 910: `pPredCount[pPred] !== 1 || cPredCount[pPred] !== 1`). Predicates with multiplicity > 1 are left unmatched. If unmatched producer facts don't appear in the consumer's antecedent, the fused rule will produce them as extra consequent resources — changing the rule's semantics.

The code does return `null` on unification failure (line 928), but the unmatched-resource handling (line 939: `[...pUnmatched, ...cConseqFlat.linear]`) may silently produce extra linear resources. This is sound (extra resources are never consumed) but may confuse downstream analysis.

### Bug Findings

**B8. _fuseBasicBlocks marks ALL chain members as fused, but branches may not cover all (compose.js:1229-1233)**
Severity: LOW (over-aggressive removal, conservative for soundness)

```js
for (let i = 0; i <= maxFusedUpTo; i++) fusedRules.add(chain[i]);
```

When oplus branches exist, some branches may not fuse (fuseLinearPairExpanded returns subset of branches). But `maxFusedUpTo` marks all rules up to the maximum depth as consumed. If branch A fuses to depth 5 but branch B only fuses to depth 3, rules at depth 4-5 are removed even though branch B needs them.

However: the fused rules from BOTH branches are added to newRules, and the original un-fused rules were entry-point rules (chain[0] is always fused). The removed intermediate rules (chain[1..N]) are only reachable via the chain head, which is now replaced by fused versions. So this is actually safe — the intermediate rules were only reachable via the chain and are now superseded. But the reasoning is subtle and undocumented.

### Design Observations

**D33. compose.js is the most complex but well-structured module (2085 LOC)**

Three-layer API cleanly separates concerns:
- L1 (composePair, specializePersistent, fuseLinearPair): pure transformations on rule pairs
- L2 (buildPredicateMap, buildEliminationOrder): analysis for scheduling
- L3 (composeGrade0): multi-pass orchestrator

Each pass is a pure function transforming a rule pool. The passes are composable and independently testable. The 8-pass pipeline handles increasingly complex optimizations:
1. Grade-0 cut → 2. Persistent specialization → 3-4. Residual → 5. Block fusion → 5.5. Chain fusion → 5.6. Residual → 6. McCarthy+SROA → 6.5. Residual

The residual resolver runs 3 times — after specialization, after fusion, after SROA — propagating groundness from each transformation. This cascading pattern is correct: each transformation may ground new variables, enabling further resolution.

**D34. Soundness argument for the pipeline**

The compose pipeline is a compile-time implementation of SELL cut admissibility (Nigam-Miller PPDP 2009). Each composePair call performs a single cut elimination step on grade-0 formulas. Grade-0 erasure (Atkey 2018) ensures these intermediates are compile-time scaffolding.

Key soundness invariants:
1. **Alpha-renaming** before every pair composition prevents variable capture
2. **Unification** ensures the cut formula matches (null = no composition)
3. **topological persistent goal sorting** ensures inputs grounded before use
4. **Bridge detection** rejects rules that both consume and produce the same grade-0 type
5. **Safety check** in chain fusion ensures intermediate vars are private
6. **Hidden producer analysis** in block fusion prevents fusing away runtime-needed rules
7. **Fusion barriers** prevent fusing across dynamic jump targets

**D35. sortPersistentGoals is a critical correctness component (compose.js:164-228)**

Greedy topological sort using mode metadata (+/- per position). Essential because the runtime backchainer resolves goals strictly in order. Wrong ordering → non-ground inputs → FFI failure → false negative (missing rule).

The algorithm handles:
- MultiModal predicates: allow 1 ungrounded input (becomes computed output)
- Unknown modes: conservative (all metavars must be grounded)
- Cycles/remaining: appended in original order (best-effort)

**D36. resolve-all.js most-constrained-first heuristic prevents infinite branching**

The key insight: a generative predicate like `plus(?, 3, ?)` with two free vars generates infinitely many solutions. By always picking the most-constrained goal first (fewest free metavars), constraining goals run before generative ones, bounding the search.

Ground goals (0 free metavars) delegate to the Backchainer which has FFI support for O(1) arithmetic evaluation. This avoids expensive SLD recursion through binary arithmetic clauses.

The native `between` handler generates Lo..Hi directly instead of SLD recursion through inc/lt/le — O(N) instead of O(N²).

**D37. _fuseBasicBlocks hidden producer analysis is sophisticated (compose.js:1048-1077, 1098-1105)**

`_collectInvisibleCut` recursively traverses oplus/with/exists to find cut predicate values produced inside choice branches. These values are "invisible" to flattenAntecedent. Their consumers CANNOT be fused away because the hidden producer might fire at runtime.

This is a critical correctness analysis — without it, fusing away a consumer of a hidden-branch-produced resource would silently break those execution paths.

**D38. Oplus handling in fuseLinearPairExpanded is correct (compose.js:975-1031)**

When a producer has oplus in its consequent, each branch is projected into a separate rule and fused independently. Persistent goals from oplus branches are treated as guards (moved to antecedent, not consequent) — this ensures dead branches with contradictory guards never fire.

The projection creates multiple fused rules (one per viable branch), and _fuseBasicBlocks tracks all branches via the `branches` array (lines 1204-1219).

**D39. _openExists correctly handles debruijnSubst for fusion (compose.js:814-839)**

Unlike `expandConsequentChoices` (which fully expands oplus into alternatives), `_openExists` only opens exists binders via `debruijnSubst(body, 0n, freshMetavar())` — replacing bound(0) with fresh metavars. This preserves oplus/with as opaque linear elements for runtime resolution while making exists-wrapped resources available for fusion matching.

**D40. McCarthy normalization is textbook correct (compose.js:1300-1436)**

Implements McCarthy's array select/store axioms (McCarthy 1962) for acons encoding:
- Read-head: `get([H|T], 0, V) → V = H`
- Read-tail: `get([H|T], N, V) → get(T, N-1, V)` when N > 0
- Write-head: `set([H|T], 0, W, R) → R = [W|T]`
- Write-tail: `set([H|T], N, W, R) → set(T, N-1, W, I), R = [H|I]`

Termination: structural recursion on acons depth. Confluence: ground indices ensure at most one rule fires per goal. Applied iteratively for deeper chains.

### Test Coverage

| Function | Direct tests | Quality |
|---|---|---|
| composePair | 7 tests | Good (alpha-rename, unif fail, existentials) |
| specializePersistent | 5 tests | Good (basic + edge cases) |
| composeGrade0 | 9 + 4 + 3 integration | Thorough |
| buildPredicateMap | 3 tests | Basic |
| buildEliminationOrder | 4 tests | Good (cycle detection) |
| _fuseAdditiveChains | 6 + 10 tests | Thorough (inc + checked_sub + plus) |
| _resolveResidualOnce | 5 + 11 tests | Thorough (transitive, arr_get/set) |
| _resolveResidualBatch | 1 test | Minimal |
| _sroaStackDecomposition | 15 tests | Good (McCarthy + SROA) |
| resolveAll | 14 tests | Good (between, tabling, maxSolutions) |
| **fuseLinearPair** | **None (indirect only)** | Via _fuseBasicBlocks |
| **fuseLinearPairExpanded** | **None (indirect only)** | Via _fuseBasicBlocks |
| **sortPersistentGoals** | **None** | Critical, untested in isolation |
| **_openExists** | **None** | Via fuseLinearPair |
| **_buildFactArgIndexes** | **None** | Via composeGrade0 |
| **Cache collision** | **None** | Silent corruption risk |

Total: ~115 tests across 8 test files. Good coverage of L1 atomic operations and chain/SROA passes. Gaps in fusion primitives and persistent goal sorting.

### Magic Numbers

| File | Constant | Value | Purpose |
|---|---|---|---|
| compose.js | MAX_COMPOSED_PER_STAGE | 100000 | Safety bound for rule explosion |
| compose.js | MAX_FUSE_CHAIN | 20 | Fusion chain depth limit (~40 metavars < 64 slot limit) |
| compose.js | _buildFactArgIndexes threshold | 8 | Facts below this use linear scan |
| resolve-all.js | DEFAULT_MAX_SOLUTIONS | 10000 | Tabling enumeration bound |
| resolve-all.js | MAX_DEPTH | 2000 | SLD search depth limit |

All reasonable with clear documentation.

### Naming Audit

| Current | File | Proposed |
|---|---|---|
| composeGrade0 | compose.js | compose0 |
| composePair | compose.js | cutPair |
| specializePersistent | compose.js | specialize |
| fuseLinearPair | compose.js | fusePair |
| fuseLinearPairExpanded | compose.js | fusePairEx |
| buildPredicateMap | compose.js | predMap |
| buildEliminationOrder | compose.js | elimOrder |
| sortPersistentGoals | compose.js | sortGoals |
| _fuseAdditiveChains | compose.js | _fuseChains |
| _resolveResidualOnce | compose.js | _resolveOnce |
| _resolveResidualBatch | compose.js | _resolveBatch |
| _sroaStackDecomposition | compose.js | _sroa |
| _mccarthyNormalize | compose.js | _mccarthy |
| _collectInvisibleCut | compose.js | _invisibleCut |
| _buildFactArgIndexes | compose.js | _factIndex |
| _indexedFactLookup | compose.js | _indexLookup |
| _decomposePatternIntoTheta | compose.js | _decompTheta |
| _collectArrGoals | compose.js | _arrGoals |
| _peelAcons | compose.js | _peelCons |
| _openExists | compose.js | _openEx |
| _openConseqExists | compose.js | _openConseqEx |
| resolveAll | resolve-all.js | resolve |
| alphaRenameClause | resolve-all.js | alphaRen |
| composeMapTheta | resolve-all.js | composeSub |
| countFreeMetavars | resolve-all.js | freeCount |
| buildSimpleIndex | resolve-all.js | simpleIdx |

Theory-standard: cut elimination, McCarthy axioms, Kahn's algorithm, SROA, alpha-rename, topological sort — all kept.

### Splitting Recommendation

compose.js at 2085 LOC is the largest single file. The three-layer structure suggests a natural split:

| Module | LOC | Contents |
|---|---|---|
| compose-core.js | ~350 | L1: composePair, specializePersistent, helpers (alphaRename, findByPredHead, _buildRuleHash, sortPersistentGoals) |
| compose-fusion.js | ~600 | Pass 5: fuseLinearPair, fuseLinearPairExpanded, _fuseBasicBlocks, _openExists |
| compose-chain.js | ~200 | Pass 5.5: _fuseAdditiveChains |
| compose-sroa.js | ~400 | Pass 6: _sroaStackDecomposition, _mccarthyNormalize, _trySROA, _decomposePatternIntoTheta, _collectArrGoals, _peelAcons |
| compose.js | ~535 | L2 analysis (buildPredicateMap, buildEliminationOrder) + L3 orchestration (composeGrade0) + caching |

This would reduce compose.js from 2085 to ~535 LOC. Each sub-module has clean boundaries and no circular deps. However, the current single-file structure works and all passes are well-separated by comments. This is a low-priority refactor.

### Phase 5 Tasks

- [x] Fix C22: Replace weak 32-bit cache key with canonical string keys (S2)
- [ ] Fix C23: Move resolve-all.js ILL imports to injection (same pattern as C16)
- [ ] Fix C23: Make `between` handler injectable via opts.nativePredicates
- [ ] Add test: sortPersistentGoals isolation (mode-aware ordering, cycles, multiModal)
- [ ] Add test: fuseLinearPair direct (exists opening, predicate matching, unification failure)
- [ ] Add test: cache collision detection/prevention
- [ ] Consider: Split compose.js into 5 modules (see splitting recommendation)
- [ ] Naming pass: rename verbose functions (see table)
- [ ] Document: pipeline pass diagram in doc/documentation/ (expand grade0-composition.md)

## Phase 6 Findings: Entry Points, Loaders & Serialization

### Files Audited (~3,039 LOC)

**Entry points:**
- `lib/index.js` (83 LOC) — Node.js entry point (async lazy-loading facade)
- `lib/browser.js` (101 LOC) — Browser entry point (bundle hydration)
- `lib/api.js` (87 LOC) — Shared environment-agnostic API facade

**Loaders:**
- `lib/engine/index.js` (1,113 LOC) — MDE module: caching, loading, bytecode, calc assembly
- `lib/engine/convert.js` (799 LOC) — MDE → content-addressed hash converter
- `lib/engine/directive-loader.js` (266 LOC) — Shared ILL-native test/debug infrastructure

**Serialization:**
- `lib/engine/store-binary.js` (463 LOC) — Binary Store serialization + compact GC

**Support:**
- `lib/engine/optimizer.js` (133 LOC) — Profile-driven engine configuration
- `lib/engine/type-check.js` (292 LOC) — Load-time sort checking
- `lib/hash.js` (85 LOC) — FNV-1a 32-bit hashing

### Architecture: Dual Entry Point + MDE Wiring

```
lib/index.js (Node.js)              lib/browser.js (Browser)
  ├─ calculus.loadILL()                ├─ hydrateCalculus(bundle)
  └─ createCalcAPI(calculus) ─┐        └─ createCalcAPI(calculus) ─┐
                               │                                    │
                     lib/api.js (shared facade)                     │
                       ├─ proveString → prover + sequent parser     │
                       ├─ parseFormula → calculus.parse              │
                       └─ getManualProofAPI → strategy/manual        │
                                                                     │
lib/engine/index.js (MDE module) ─── forward engine entry ──────────┘
  ├─ load(filePath, opts) → calc context
  │    ├─ Two-tier caching: full program + SDK imports
  │    ├─ Compose disk cache (pre-composed Store snapshot)
  │    └─ _buildCalc: parse → compile → compose → type-check → optimize
  ├─ precompile(filePaths, cachePath) → binary cache
  ├─ loadPrecompiled(cachePath) → calc context
  ├─ codeToArrlit / bytesToSemantic / bytecodeToTrie → bytecode pipeline
  └─ normalizeQuery → decomposeQuery + bytecode normalization
```

### Correctness Findings

**C27. engine/index.js hardcodes ILL as the only calculus (17 references)**
Severity: HIGH (architectural — prevents generic engine reuse)

Top-level imports (lines 23-25):
```js
const { ILL_CONNECTIVES } = require('./ill/connectives');
const { getModes: _illGetModes, getModeMeta: _illGetModeMeta } = require('./opt/ffi');
const _illCompileOpts = { connectives: ILL_CONNECTIVES, getModes: _illGetModes };
```

Used in 12 call sites across: `_buildCalc`, `_loadWithCachedImports`, `_parseFreshWithSdk`, `precompile`. All `forward.compileRule()` calls use `_illCompileOpts`. All compose pipeline invocations hardcode ILL chain configs, SROA config, binlit theory.

Additionally, 3 EVM-specific bytecode functions (`codeToArrlit`, `bytesToSemantic`, `bytecodeToTrie`, ~191 LOC) import from `ill/ffi/convert` and `ill/ffi/array`. These are domain-specific (EVM bytecode → trie conversion) in the generic engine entry point.

Combined with C16 (Phase 4: 8 upward violations in generic engine core), this means the engine layer has **25 total ILL/EVM coupling points**.

Fix: Inject calculus config via opts (connectives, getModes, compileOpts). Move bytecode functions to `ill/bytecode-loader.js` or a new `ill/bytecode-normalize.js`.

**C28. convert.js _exprParser triggers synchronous ILL loading at require time (line 23)**
Severity: MEDIUM (import-time side effect, prevents non-ILL use of convert)

```js
const _exprParser = (() => {
  const ill = require('../calculus').loadILL();  // synchronous file I/O + parse
  const tables = computeParserTables(ill.constructors);
  ...
})();
```

Any `require('./convert')` triggers full ILL calculus loading from disk. Since engine/index.js imports convert at the top level, and most engine modules transitively require engine/index, the ILL calculus is always loaded. Hardcodes ILL-specific parser config: exists/forall binders, binary normalization, forward rules, concat operator.

Fix: Make _exprParser lazy (call on first parseExpr/loadFile) or accept a parser parameter.

**C29. compactSnapshot remapMeta remaps ALL numbers, not just Store IDs (store-binary.js:439-446)**
Severity: LOW (works in practice, fragile for future metadata fields)

```js
function remapMeta(obj) {
    if (typeof obj === 'number') return remap[obj] || obj;
    ...
}
```

Walks metadata recursively and remaps every number via the ID renumbering table. Non-hash numbers (like `_composeCache: 2`, or future numeric settings) would be incorrectly remapped if they fall within the Store ID range. Currently safe because:
1. Small version numbers (1-6) map to themselves when all low IDs are reachable
2. Most non-hash fields are strings (querySettings values)
3. `|| obj` fallback preserves numbers with remap[n]=0 (unreachable IDs)

But if future metadata includes larger non-hash numbers (counts, sizes, thresholds), they would be silently remapped.

Fix: Tag hash fields explicitly, or use a schema-driven remapper that only processes known hash paths.

**C30. _composeDiskCacheKey uses weak 32-bit hash (engine/index.js:43-53)** — **FIXED (S2)**
Severity: LOW (same class as C22 — collision invalidates cache, not soundness)

Fixed: SHA-256 on canonical string with section delimiters. 16-char hex key for filenames.

**C31. directive-loader.js hardcodes EVM program path (line 19)**
Severity: LOW (tool-specific, not library code)

```js
const PROGRAM = path.join(ROOT, 'calculus', 'ill', 'programs', 'evm.ill');
```

The shared test/debug infrastructure assumes EVM as the default program. Non-EVM .ill test suites would need to override.

### Bug Findings

**B9. decomposeQuery _substituteBound doesn't track de Bruijn depth (convert.js:644-678, 693-732)**
Severity: MEDIUM (wrong results for queries with nested quantifiers inside connectives)

`decomposeQuery` peels outermost quantifiers, then applies `_substituteBound(body, subs)` to replace bound variables. But `_substituteBound` does a flat Map lookup — it doesn't track depth when descending into nested exists/forall binders inside the body.

Example trigger: `forall X. (P(X) * exists Y. Q(X, Y))`
1. Peeling strips `forall X` (totalDepth=1)
2. body = `tensor(P(bound(0)), exists(Q(bound(0), bound(0))))`
3. Substitution: bound(0) → freevar('_q0')
4. `_substituteBound` replaces ALL bound(0) — including inside `exists(Q(bound(0), bound(0)))` where bound(0) refers to Y, not X

The kernel has `debruijnSubst` (substitute.js:165) which correctly tracks depth by incrementing when descending through exists/forall binders.

Currently safe for typical queries (flat `forall X. forall Y. ... tensor(facts...)` with no quantifiers inside tensor), but structurally unsound for nested quantifiers.

Fix: Use `debruijnSubst` from kernel/substitute.js per binder, or add depth tracking to `_substituteBound`.

### Design Observations

**D41. engine/index.js is the wiring layer (1,113 LOC, 4 concerns)**

The file assembles all engine components but mixes four distinct responsibilities:
1. **Caching** (lines 27-142, 460-836): Two-tier auto-cache, compose disk cache, precompile/loadPrecompiled — ~540 LOC
2. **Calc assembly** (lines 156-356): `_buildCalc` — compile rules, compose grade-0, type-check, build indexes, create engine — ~200 LOC
3. **Bytecode normalization** (lines 887-1079): `codeToArrlit`, `bytesToSemantic`, `bytecodeToTrie` — ~191 LOC (EVM-specific)
4. **Module/label infrastructure** (lines 247-394): SELL labels, module algebra resolution — ~150 LOC

Natural split: caching → `engine/cache.js`, bytecode → `ill/bytecode-normalize.js`, module algebra → `engine/modules.js`. Would reduce engine/index.js from 1,113 to ~350 LOC (_buildCalc + load + exports).

**D42. Two-tier caching architecture is well-designed**

```
load(filePath)
  ├─ composeDiskCache hit? → Store.restore (skip parse + compose: ~40ms)
  ├─ full cache hit?       → Store.restore (skip parse: ~15ms)
  ├─ imports cache hit?    → Store.restore SDK + parse top file (~8ms)
  └─ cold start           → parse all + cache both tiers (~210ms)
```

Content-addressed cache keys: `hashCombine(treeHashes, CACHE_VERSION)` ensures cache invalidation on source changes. Two-tier: SDK imports change rarely (cached indefinitely), top-level file changes often (cached per hash). Compose cache adds a third tier for expensive grade-0 composition.

**D43. optimizer.js profiles are a clean DI pattern (133 LOC)**

Three built-in profiles control 10 optimization flags:
- `bare`: all off (correctness baseline, useful for debugging)
- `fast`: FFI + compiledSub + preserved (general-purpose)
- `evm`: all on (maximum optimization, EVM-tuned)

`resolveProfile` supports: string name, custom object, `CALC_PROFILE` env var override. `createEngine` resolves function pointers once at creation (V8 monomorphic IC). Clean, extensible design.

**D44. store-binary.js is architecturally solid (463 LOC)**

Binary format v6: header (24B) + SoA term arrays + flat child buffer + DEDUP hashes + string/bigint/array tables + tag registry + JSON metadata + CRC32 footer. Format designed for zero-copy restore where possible.

`compactSnapshot` implements mark-sweep GC: DFS from metadata roots → renumber contiguously → remap children + arrays + metadata. Typically compacts ~40% of dead nodes accumulated during rule compilation.

**D45. type-check.js is a clean load-time sort checker (292 LOC)**

Builds sort table from LF-style arrow declarations: `plus: bin -> bin -> bin -> type` → `{ argSorts: ['bin','bin','bin'], returnSort: 'type' }`. Checks forward rules and backward clauses against the table. Zero runtime cost — all work at `_buildCalc` time. Diagnostics mode (non-strict) prints warnings; strict mode throws.

**D46. convert.js has clean two-pass loading (799 LOC)**

Pass 1 (definitions): type declarations, named_arg stripping → sort table entries.
Pass 2 (rules/clauses/queries): forward rules, backward clauses, query directives, grade-0 clauses.

Named argument resolution (`_resolveNamedCallSite`) implements positional-then-named convention with comprehensive error messages (missing args, duplicates, positional-after-named). Preserved resource desugaring (`desugarPreserved`) is clean with proper error cases ($!P, !$P, $-in-consequent).

Import tree building + content hashing (`buildImportTree`, `computeTreeHashes`) enables precise cache invalidation without parsing.

**D47. Dual entry points via shared facade**

| Entry | Path | Load method | Target |
|---|---|---|---|
| Node.js | `lib/index.js` | `calculus.loadILL()` (async, from files) | CLI, tests, benchmarks |
| Browser | `lib/browser.js` | `hydrateCalculus(bundle)` (sync, from JSON) | SolidJS UI |
| Engine | `lib/engine/index.js` | `convert.load()` → `_buildCalc()` | Forward/explore execution |

All three delegate to `api.js:createCalcAPI()` for the shared prove/parse/render surface. The engine entry point adds forward execution, caching, and bytecode normalization.

**D48. decomposeQuery handles quantifier elimination correctly (for flat queries)**

Standard proof-theoretic approach:
- `forall X. A(X)` → eigenvariable (freevar): universally quantified inputs
- `exists X. A(X)` → witness variable (metavar): existentially quantified unknowns

De Bruijn index mapping is correct for top-level quantifier prefixes. The depth-tracking issue (B9) only affects nested quantifiers inside other connectives.

### Test Coverage

| Module | Direct Test | Key Indirect Coverage |
|---|---|---|
| engine/index.js | convert.test.js, store-binary.test.js | ~20 engine tests, 5 benchmarks |
| convert.js | convert.test.js | preserved-sugar, named-args, separator, primitives, quantifiers |
| store-binary.js | store-binary.test.js (round-trip, CRC, alignment, caching) | arrlit.test.js (direct import) |
| directive-loader.js | **None** | Only via tools/test-ill.js runtime |
| browser.js | ui-flow.test.js, manual-proof-flow.test.js | e2e-solidjs.js |
| api.js | **None** (indirect via browser + index tests) | ui-flow, manual-proof-flow |
| optimizer.js | **None** | All mde.load() calls (~20 engine tests) |
| type-check.js | type-check.test.js (full unit suite) | Integration via mde.load multisig |
| hash.js | **None** | All Store operations (ubiquitous) |

Notable gaps: `directive-loader.js`, `optimizer.js`, `api.js`, and `hash.js` have no direct test files.

### Magic Numbers

| File | Constant | Value | Purpose |
|---|---|---|---|
| engine/index.js | COMPOSE_DISK_VERSION | 2 | Compose cache format version |
| engine/index.js | CACHE_VERSION | 5 | Binary cache format version (parse + compile) |
| store-binary.js | MAGIC | 0x43414C43 | "CALC" file signature |
| store-binary.js | VERSION | 6 | Binary format version (v6: flat childOff+childBuf) |
| store-binary.js | CRC polynomial | 0xEDB88320 | IEEE 802.3 CRC32 |
| store-binary.js | string length | u16 | Max 65535 bytes per string |
| store-binary.js | bigint byte length | u16 | Max 65535 bytes (~524k bits) |
| directive-loader.js | MAX_STEPS | 10000 | Default forward step limit |
| directive-loader.js | MAX_DEPTH | 100 | Default explore depth limit |
| optimizer.js | 10 flags | bool | Profile optimization flags |
| hash.js | FNV_PRIME | 0x01000193 | FNV-1a 32-bit prime |
| hash.js | FNV_OFFSET | 0x811c9dc5 | FNV-1a 32-bit offset basis |

### Naming Audit

| Current | File | Proposed |
|---|---|---|
| _composeDiskCacheKey | engine/index.js | _composeCacheKey |
| _saveComposeSnapshot | engine/index.js | _saveCSnap |
| _loadComposeSnapshot | engine/index.js | _loadCSnap |
| _serializeCompiledRules | engine/index.js | _serRules |
| _deserializeCompiledRules | engine/index.js | _deserRules |
| _snapshotToFile | engine/index.js | _snapToFile |
| _loadWithCachedImports | engine/index.js | _loadCached |
| _parseFreshWithSdk | engine/index.js | _parseFresh |
| _computeSdkPaths | engine/index.js | _sdkPaths |
| buildLabelDeps | engine/index.js | labelDeps |
| _resolveModuleExpr | engine/index.js | _resolveModule |
| resolveImports | convert.js | resolveImport |
| buildImportTree | convert.js | importTree |
| computeTreeHashes | convert.js | treeHashes |
| extractTopLevelImports | convert.js | topImports |
| stripNamedArgsFromArrowChain | convert.js | stripNamedArgs |
| resolveNamedArgSentinels | convert.js | resolveNamed |
| _resolveNamedCallSite | convert.js | _resolveCall |
| desugarPreserved | convert.js | desugarPres |
| _assertNoPreserved | convert.js | _noPres |
| decomposeQuery | convert.js | decompQuery |
| _substituteBound | convert.js | _substBound |
| compactSnapshot | store-binary.js | compact |
| scanDirectives | directive-loader.js | scanDir |
| detectDuplicates | directive-loader.js | detectDup |
| loadProgram | directive-loader.js | loadProg |
| parseModality | directive-loader.js | modality |
| resolveQueryHash | directive-loader.js | resolveQuery |
| resolveExecOpts | directive-loader.js | execOpts |
| normalizeLeafState | directive-loader.js | normLeaf |
| groupByPredicate | directive-loader.js | groupByPred |
| stateHasFreevars | directive-loader.js | hasFreevars |
| resolveProfile | optimizer.js | profile |
| createEngine | optimizer.js | engine |
| buildSortTable | type-check.js | sortTable |
| checkForwardRule | type-check.js | checkRule |
| hashCombine2 | hash.js | mix2 |
| hashCombine | hash.js | mix |
| hashString | hash.js | hashStr |
| hashBigInt | hash.js | hashBig |
| hydrateCalculus | browser.js | hydrate |

Theory-standard: FNV-1a, CRC32, de Bruijn, LF (sort checking), content addressing — all kept.

### Splitting Recommendation

engine/index.js at 1,113 LOC could be split:

| Module | LOC | Contents |
|---|---|---|
| engine/cache.js | ~540 | Two-tier caching, compose disk cache, precompile/loadPrecompiled, snapshot helpers |
| ill/bytecode-normalize.js | ~191 | codeToArrlit, bytesToSemantic, bytecodeToTrie, normalizeQuery |
| engine/modules.js | ~150 | SELL labels, buildLabelDeps, _resolveModuleExpr, resolveLabels, filterRules |
| engine/index.js | ~230 | _buildCalc, load (delegating to cache.js), exports |

This would also improve the ILL coupling story (C27) by isolating the 3 EVM-specific functions.

### Phase 6 Tasks

- [x] Fix B9: Replace _substituteBound with kernel debruijnSubst (S2)
- [ ] Fix C27: Inject ILL config into engine/index.js via opts (connectives, getModes, compileOpts)
- [ ] Fix C27: Move bytecode functions (codeToArrlit, bytesToSemantic, bytecodeToTrie) to ill/ layer
- [ ] Fix C28: Make convert.js _exprParser lazy or parameterized
- [ ] Fix C29: Add schema-driven remapMeta that only processes known hash fields
- [ ] Add test: directive-loader.js unit tests (scanDirectives, detectDuplicates, loadProgram)
- [ ] Add test: optimizer.js unit tests (resolveProfile, createEngine, CALC_PROFILE env var)
- [ ] Add test: decomposeQuery with nested quantifiers inside connectives (B9 regression)
- [ ] Consider: Split engine/index.js into 4 modules (see splitting recommendation)
- [ ] Naming pass: rename verbose functions (see table)


## Phase 7 Findings: Parser & Grammar (Soundness Audit)

### Files Audited (~2,758 LOC)

**Parser layer:**
- `lib/parser/earley.js` (379 LOC) — Core Earley recognizer + tree extraction
- `lib/parser/earley-grammar.js` (687 LOC) — Grammar generation from constructor annotations
- `lib/parser/declarations.js` (568 LOC) — Declaration parser (.ill/.calc/.family)
- `lib/parser/sequent-parser.js` (92 LOC) — Sequent string parser
- `lib/parser/balanced-split.js` (33 LOC) — Balanced parentheses split utility

**Calculus layer:**
- `lib/calculus/index.js` (173 LOC) — Calculus loader + cache
- `lib/calculus/builders.js` (282 LOC) — AST/parser/renderer factories
- `lib/calculus/modes.js` (39 LOC) — Monad rule generation

**Meta-parser layer:**
- `lib/meta-parser/loader.js` (226 LOC) — .family/.calc @extends chain loader
- `lib/rules/rules2-parser.js` (279 LOC) — Sequent-notation rule parser

### Correctness Findings

**C32. sequent-parser.js uses plain `split('|-')` (sequent-parser.js:26)**
Severity: MEDIUM (wrong parse for nested turnstiles)

`parseSequent` does `src.split('|-')` — a flat string split with no depth tracking. If a hypothesis contains a nested turnstile (e.g. from a proof term or quoted sequent), the split breaks the parse. `rules2-parser.js:23` has the same issue. Compare with `declarations.js:_findTopLevelSeparator` which correctly tracks paren/brace/bracket depth.

Fix: Use balanced split or `_findTopLevelSeparator`-style depth tracking for `|-`.

**C33. balanced-split.js doesn't track bracket depth (balanced-split.js:14-31)**
Severity: LOW (no current callers split inside arrays)

`balancedSplit` tracks `()` and `{}` depth but NOT `[]`. If a separator appears inside an array literal (e.g. `[A <- B]`), it would incorrectly split. Currently safe because: (1) arrays don't contain `<-` or `,` at the grammar level in ways that conflict, (2) `declarations.js:_findTopLevelSeparator` (which handles `|-`) has its own implementation that DOES track `[]`.

Fix: Add `bracketDepth` tracking for `[`/`]` to `balancedSplit`.

**C34. earley-grammar.js bang handling is hardcoded (earley-grammar.js:230-282)**
Severity: LOW (correct, but prevents generic reuse)

Bang (`!`, `!_0`, `!_ω`) grammar rules are hardcoded rather than derived from constructor annotations. The `computeEarleyGrammar` function (line 47-49) explicitly skips bang in the generic classifier, then manually adds 3 grammar rules with hardcoded `GRADE_W`/`GRADE_0` imports. This makes the grammar generator ILL-specific for graded modalities.

A non-ILL calculus with its own exponential modality would need to modify earley-grammar.js directly. Currently only ILL uses this, so low urgency.

**C35. earley-grammar.js binder/non-binder branch duplication (earley-grammar.js:162-293)**
Severity: LOW (130 LOC code duplication)

The unary prefix section has two near-identical branches: lines 220-260 (with binders) and lines 261-293 (without binders). The only difference is the target nonterminal: `NT(BINDER_UNARY)` vs `NT(UNARY)`. Similarly, binary operator rules (lines 162-213) duplicate the same pattern. A single branch with a computed target NT would halve the code.

Same duplication exists in binary operator level generation (lines 155-217): the `if (binderDefs)` and `else` branches are structurally identical except for whether RHS is `NT(bnt)` (binder) or `NT(nt)`/`NT(next)` (closed).

**C36. Number/hex parsing duplicated in fast path and _evalRule (earley-grammar.js:453-465 + 612-624)**
Severity: LOW (40 LOC duplication)

The hex-to-arrlit conversion (detect `0x` prefix, check length > 64 hex chars, split into byte-pair binlits) appears identically in:
1. `buildParserFromGrammar` single-token fast path (lines 453-465)
2. `_evalRule` number handler (lines 612-624)

Fix: Extract `parseNumber(raw) → Store hash` helper.

**C37. _substituteHashes is 3rd instance of flat hash-walking substitution (declarations.js:69-101)**
Severity: LOW (code duplication across 2 files)

Three flat hash-walking substitution functions exist:
1. `declarations.js:_substituteHashes` (lines 69-101) — metavar → bound for eigenvars
2. `convert.js:_substituteBound` (lines 644-676) — bound → freevar for query decomposition
3. `kernel/substitute.js:apply` — generic substitution

All three walk the Store tree, check a Map for replacements, rebuild changed nodes. The first two are specialized (no depth tracking) but structurally identical. Neither handles de Bruijn depth adjustment — which is fine for `_substituteHashes` (metavar→bound, no depth shift needed) but was flagged as B9 for `_substituteBound` (bound→freevar in nested quantifiers).

**C38. declarations.js findDeclEnd doesn't track bracket depth (declarations.js:344-373)**
Severity: LOW (same gap as balanced-split)

`findDeclEnd` tracks `()` and `{}` depth but not `[]`. A declaration body containing `[... . ...]` (array with a period inside) would terminate the declaration prematurely. In practice, array elements never contain periods in ILL syntax. But if a string-like value or comment contained a period inside brackets, the parse would break.

### Bug Findings

**B10. rules2-parser.js block splitting is fragile (rules2-parser.js:266)**
Severity: LOW

`body.split(/\.\s*\n/)` splits rule blocks on period-followed-by-newline. A period inside a comment on the last line of a block, or a period in a string annotation, could cause a mis-split. The declaration parser handles this correctly via `findDeclEnd` with depth tracking. Currently safe because `.rules` files have clean, simple structure.

**B11. earley.js item key overflow for large grammars (earley.js:9-10, 213)**
Severity: LOW (never triggers)

Item key packing: `key = (ruleIdx * 256 + dot) * (n+1) + origin`. With 256 max dot positions, this limits RHS length to 255. The comment says "safe up to ~2^37 tokens / 65536 rules / 256 dot" — but there's no runtime assertion. The ILL grammar generates ~80 rules, well within limits. A calculus with many operators (>250 precedence levels × 2 rules each) could exceed 65536 rules.

### Design Observations

**D23. Earley parser is clean and minimal (379 LOC)**

Textbook Earley with Aycock-Horspool nullable handling. Key design choices:
- Chart pool (`_chartPool`) avoids per-parse allocation — grows monotonically to accommodate largest input seen
- Item packing into single integer key for Set-based dedup (O(1) per item)
- Back-pointer tree (`t: 's'|'c'|'n'`) for scan/complete/nullable
- `extract` walks back-pointers right-to-left to reconstruct children
- No Leo optimization — right-recursive grammars are O(n²) not O(n). Acceptable for formula parsing (formulas are short)

**D24. Earley grammar generation is elegant stratified CFG (687 LOC)**

Danielsson-Norell style: one nonterminal pair (closed + open) per precedence level. Associativity encoded via same/next references:
- Left-assoc: `L_p → L_p op L_{p+1}` (left-recursive)
- Right-assoc: `L_p → L_{p+1} op L_p` (right-recursive)

Binder scoping via open/closed technique is theoretically clean: `forall X. A * B` parses as `forall(X, tensor(A, B))` because binder body is START (open), while binary LHS is closed.

The fused `_extractEval` (single-pass: back-pointers → Store hashes) avoids intermediate tree allocation. App spine accumulation via Symbol marker is clever — collects `f x y z` as `{ head: f, args: [x, y, z] }` during bottom-up evaluation, then finalizes to `Store.put('f', [x, y, z])` at pass-through.

Binary normalization (`i X` → `binlit(X*2+1)`, `e` → `binlit(0n)`) is handled both in `_finalizeApp` (for parsed `i 42`) and in `_evalRule` ident handler (for bare `e`). Clean separation.

**D25. Declaration parser is calculus-agnostic (568 LOC)**

Handles 4 declaration types (import, query, directive, declaration) with zero calculus-specific logic. Expression parsing is injected via `parseExpr` callback. Key features:
- `_findTopLevelSeparator` with full depth tracking (parens, braces, brackets)
- Query settings parser `(key: value, key: [v1, v2])` — mini-language for SELL scoped rule sets
- Eigenvariable processing: `[X Y Z]` → metavar→bound substitution + forall wrapping
- Module algebra parser: union/subtract/intersect operations on module expressions
- Annotation extraction: regex-based @key value parsing from declaration body suffix

**D26. Calculus loader pipeline is well-factored (builders.js + index.js + modes.js)**

Clear separation of concerns:
1. `computeParserTables` / `computeRendererFormats` / `computeConnectivesByType` — pure data extraction (serializable for ill.json bundle)
2. `buildParserFromTables` / `buildRendererFromFormats` / `buildAST` — runtime object construction from tables
3. `buildParser` / `buildRenderer` — convenience composites

`deriveRoles` maps (category, arity, polarity) → semantic role (product, implication, unit, etc.). Clean triple-based dispatch with collision warning.

`modes.js:generateMonadRules` returns hardcoded descriptors for monad_r/monad_l. These are the ONLY generated rules — all other rules come from .rules files. The monad rules encode the lax monad's mode shift (backward→forward) and stickiness (monad_l only fires when succedent is monadic).

**D27. Meta-parser/loader.js follows @extends chains recursively (226 LOC)**

Framework parser (`_frameworkParser`) uses arrows + application but NO connective operators — because .calc/.family files DEFINE connectives, they don't USE them. `loadWithExtends` follows @extends chains with child-wins merge semantics (child constructors override parent). Clean recursive design.

`extractDeclarations` classifies declarations by analyzing Store hashes: arrow chains → type/constructor declarations, simple identifiers → nullary constructors. Uses `isTypeExpr(hash)` to distinguish type declarations from value declarations.

**D28. rules2-parser.js is a direct sequent→descriptor compiler (279 LOC)**

Parses sequent notation `G ; D, A * B |- C` directly into flat descriptors compatible with the rule interpreter. Key analysis:
- Principal formula detection: compound (non-freevar/atom) in succedent → right rule, in linear context → left rule
- Context flow classification: empty/axiom/preserved/copy/split based on context variable distribution across premises
- Child mapping: freevar names in principal formula → child indices in descriptor
- `@formulas` directive distinguishes formula variables from context variables

This is the bridge between human-readable sequent notation and the engine's machine-level descriptors.

### Test Coverage

| Module | Direct test | Indirect coverage |
|---|---|---|
| earley.js | `earley.test.js` | All parser tests |
| earley-grammar.js | `earley-grammar.test.js` | All parse tests, calculus.test.js |
| declarations.js | separator.test.js, sell.test.js, calculus.test.js | test:ill (all .ill files) |
| sequent-parser.js | **None** | zk-witness.test.js (indirect) |
| balanced-split.js | **None** | Via declarations.js callers |
| calculus/index.js | calculus.test.js | Extensive (all tests load ILL) |
| calculus/builders.js | earley-grammar.test.js, calculus.test.js, multi-logic.test.js | Extensive |
| calculus/modes.js | **None** | Via calculus/index.js (implicit) |
| meta-parser/loader.js | **None** | Via calculus/index.js (implicit) |
| rules2-parser.js | **None** | Via calculus/index.js (implicit) |

### Magic Numbers

| File | Constant | Value | Purpose |
|---|---|---|---|
| earley.js | key packing | 256 | Max RHS length per rule |
| earley.js | _chartPool | grows | Reused chart sets (monotonic growth) |
| earley-grammar.js | GRADE_0, GRADE_W | imported | Bang grade constants |
| earley-grammar.js | hex length check | 64 | Hex chars threshold for arrlit conversion |
| earley-grammar.js | memo | Map | Expression cache (cleared on Store.clear/restore) |

### Naming Audit

| Current | File | Proposed |
|---|---|---|
| computeEarleyGrammar | earley-grammar.js | earleyGrammar |
| computeEarleyGrammarFromTables | earley-grammar.js | earleyGrammarFromTables |
| buildParserFromGrammar | earley-grammar.js | parserFromGrammar |
| _extractEval | earley-grammar.js | _extract (replaces generic extract) |
| _extractNullableEval | earley-grammar.js | _extractNull |
| _extractVarNames | earley-grammar.js | _varNames |
| _finalizeApp | earley-grammar.js | _appFinalize |
| parseDeclarations | declarations.js | parseDecls |
| _findTopLevelSeparator | declarations.js | _findSep |
| _applyEigenvars | declarations.js | _eigenWrap |
| _substituteHashes | declarations.js | _subHashes |
| parseQuerySettings | declarations.js | _querySettings |
| parseModuleDefinition | declarations.js | _moduleDef |
| parseDirectiveArgs | declarations.js | _directiveArgs |
| stripComments | declarations.js | _stripComments |
| extractAnnotations | declarations.js | _extractAnns |
| findFirstAnnotationAt | declarations.js | _findAnnAt |
| createSequentParser | sequent-parser.js | sequentParser |
| computeParserTables | builders.js | parserTables |
| computeRendererFormats | builders.js | rendererFormats |
| buildParserFromTables | builders.js | parserFromTables |
| buildRendererFromFormats | builders.js | rendererFromFormats |
| computeConnectivesByType | builders.js | connByType |
| generateMonadRules | modes.js | monadRules |
| extractDeclarations | loader.js | extractDecls |
| loadWithExtends | loader.js | loadChain |
| parseRuleBlock | rules2-parser.js | _ruleBlock |
| isContextVar | rules2-parser.js | _isCtxVar |

Theory-standard: Earley, nullable, Aycock-Horspool, de Bruijn, eigenvariable, stratified CFG, Danielsson-Norell — all kept.

### Phase 7 Architecture Summary

The parser pipeline forms a clean layered stack:

```
.calc/.family files
  → meta-parser/loader.js (framework parser, @extends chains)
    → declarations.js (calculus-agnostic declaration structure)
      → earley-grammar.js (stratified CFG from operator tables)
        → earley.js (generic Earley recognizer)

.rules files
  → rules2-parser.js (sequent notation → flat descriptors)
    → balanced-split.js (shared balanced split utility)

.ill files (runtime)
  → builders.js:buildParserFromTables → earley-grammar.js:buildParserFromGrammar
  → sequent-parser.js (sequent strings, via calculus.parse)
```

**Key strengths:**
- Clean separation: generic Earley engine → grammar generator → declaration parser → calculus loader
- Fused extract+evaluate avoids intermediate tree allocation
- Expression memoization cleared on Store.clear/restore (correctness invariant)
- Framework parser correctly uses a restricted subset (arrows+application) for .calc/.family files
- Module algebra parser enables composable rule sets
- `computeParserTables`/`computeRendererFormats` are pure-data extractors — serializable for ill.json bundle, enabling browser hydration without re-parsing

**Key debt:**
1. `sequent-parser.js` and `rules2-parser.js` use flat `split('|-')` — vulnerable to nested turnstiles (C32)
2. balanced-split.js doesn't track `[]` bracket depth (C33)
3. Bang handling hardcoded in earley-grammar.js (C34)
4. Binder/non-binder branch duplication in earley-grammar.js (~130 LOC) (C35)
5. Number/hex parsing duplicated in fast path and _evalRule (C36)
6. `_substituteHashes` is 3rd instance of flat hash-walking substitution (C37)
7. `sequent-parser.js`, `balanced-split.js`, `modes.js`, `meta-parser/loader.js`, `rules2-parser.js` have zero direct tests

### Phase 7 Tasks

- [ ] Fix C32: Use balanced split for `|-` in sequent-parser.js and rules2-parser.js
- [ ] Fix C33: Add `[]` bracket tracking to balanced-split.js
- [ ] Fix C35: Deduplicate binder/non-binder branches in earley-grammar.js
- [ ] Fix C36: Extract shared number/hex parsing helper in earley-grammar.js
- [ ] Fix C37: Consider extracting shared hash-walking substitution (declarations.js + convert.js)
- [ ] Add test: balanced-split.js (bracket depth, nested separators)
- [ ] Add test: sequent-parser.js direct (simple sequents, edge cases)
- [ ] Add test: modes.js generateMonadRules descriptor validation
- [ ] Add test: meta-parser/loader.js @extends chain, declaration extraction
- [ ] Add test: rules2-parser.js direct (simple rule blocks → descriptors)
- [ ] Naming pass: rename verbose functions (see table)

## Phase 8 Findings: Documentation & Tooling Refresh

### Scope

- `doc/` directory: 194 files (~72,310 LOC across theory/documentation/def/research/todo)
- `tools/` directory: 16 files (~2,850 LOC)
- `CLAUDE.md` (215 LOC)
- Circular lazy requires audit
- pt.js summarizeSequent bug

### CLAUDE.md Inaccuracies

**CLM1. `provePersistentGoals` does not exist (line 156)**
Severity: HIGH (wrong API name in developer-facing docs)

CLAUDE.md FFI Principle says:
> `provePersistentGoals` (match.js): FFI → state lookup → clause resolution

This function name does not exist anywhere in the codebase. Actual names:
- `provePersistentWithFFI` in `lib/engine/opt/ffi.js`
- `provePersistentNaive` in `lib/engine/lnl/persistent.js`
- `match.js` re-exports `provePersistentWithFFI` aliased as `provePersistent`

Fix: Replace with `provePersistent` (match.js) or explain both paths.

**CLM2. PRED_BOUNDARY is 31, not 26 (line 163)**
Severity: MEDIUM

Common Gotchas claims `PRED_BOUNDARY` is 26. Actual: 31 pre-registered tags (atom through named_arg). The list grew as connectives were added (oplus, zero, arrlit, acons, named_arg added since the original 26).

**CLM3. `zero` ASCII is "zero", not "0" (line 127)**
Severity: LOW

ILL Connectives table shows `zero | 0 | positive`. Actual ASCII annotation in ill.calc: `@ascii "zero"`. The word "zero" is the ASCII representation, not the digit.

**CLM4. `bang` is binary (grade -> formula -> formula), not unary (line 128)**
Severity: MEDIUM

Table shows `bang | ! | positive | exponential (reusable resource)` implying unary. Actual: `bang: grade -> formula -> formula` — takes a grade argument (`GRADE_0`, `GRADE_1`, `GRADE_W`). The `!A` syntax is sugar for `bang(GRADE_W, A)`. This is already documented in the SELL section but contradicted in the connectives table.

**CLM5. `lib/engine/opt/` directory listing incomplete (line 94-95)**
Severity: LOW

CLAUDE.md lists only 2 of 7 files in opt/:
- Listed: `compiled-clauses.js`, `existential-compile.js`
- Missing: `disc-tree-opt.js`, `ffi.js`, `fingerprint.js`, `prediction.js`, `structural-memo.js`

The `ffi.js` omission is significant — it contains the core FFI proving pipeline.

**CLM6. parser/ directory listing incomplete (line 97-99)**
Severity: LOW

Lists only `earley.js` and `earley-grammar.js`. Missing: `declarations.js` (568 LOC), `sequent-parser.js` (92 LOC), `balanced-split.js` (33 LOC).

### Documentation Staleness Assessment

**42 files in doc/documentation/ audited. Classification:**

| Status | Count | Files |
|---|---|---|
| Current | 20 | backward-prover, content-addressed-store, parser-pipeline, ill-debug-framework, ill-test-framework, strategy-layers, lax-monad, term-resource-proposition, explore-optimizations, grade0-composition, proof-terms, loader-and-precompile, sell-graded-modality, sell-rule-filtering, calldata-representation, fusion-symex-spectrum, sort-checking, calc-vs-hevm, design-language, zk-proof-certification |
| Partially stale | 9 | architecture, forward-chaining-engine, optimization-architecture, forward-optimization-roadmap, eigenvariable-walkthrough, INDEX, test-overview, ANKI, primitives-implementation |
| Stale | 7 | notes (2017 era), CHANGELOG (v1/v2 migration history), benchmark-v2 (historical), operations-analysis (pre-Store era), prover-optimization (dead paths), typed-dsl-logical-framework (dead links), symexec-optimizations (superseded by explore-optimizations) |
| Partially stale (EVM historical) | 2 | evm-modeling-approaches, performance-study |
| Long reference (evergreen) | 1 | polynomial-memoization |

**Biggest systematic staleness: opt/ module location drift**

Three docs (`architecture.md`, `forward-chaining-engine.md`, `optimization-architecture.md`) list `delta-bypass.js`, `preserved.js`, `compiled-sub.js`, `backward-cache.js`, `constraint.js`, `loli-drain.js` as `lib/engine/opt/` modules. All live at `lib/engine/` root. Only 7 files are actually in `opt/`: `compiled-clauses.js`, `disc-tree-opt.js`, `existential-compile.js`, `ffi.js`, `fingerprint.js`, `prediction.js`, `structural-memo.js`.

**Dead wiki-link cross-references in stale docs:**

`[[dsl_refactor]]`, `[[content-addressed-formulas]]`, `[[dev/constructor-indexing]]`, `[[dev/FFI-IMPLEMENTATION-PLAN.md]]`, `[[backward-prover-optimization]]`, `[[proof-calculi-foundations]]` — all dead links in old docs.

### doc/todo/ Legacy Directory (48 files + meta.yaml)

CLAUDE.md explicitly states: "TODOs are managed externally via the `hq` CLI, not in this repo. Don't create `doc/todo/` here." Yet `doc/todo/` exists with 48 numbered markdown files (~3,792 LOC total), ranging from `0001_loli-decomposition-bug.md` to `0048_pos-consensus-mvp.md`.

These are legacy pre-hq todos. Many are completed or subsumed. They should be archived or removed per the stated policy.

### Missing Documentation

**MD1. existential-compile.md — not written**
The compiled existential chain (`opt/existential-compile.js`, 150 LOC) has no documentation. It implements partial evaluation for deterministic `∃x.P(inputs, x)` goals — reducing to direct slot-to-slot dataflow. This is a key optimization with no explanation of its invariants or correctness argument.

**MD2. matchOpts-reference.md — not written**
`matchOpts` is the ~15-field configuration object that controls the match/forward/explore pipeline. It's assembled identically in forward.js and explore.js (C6 from Phase 2) but never documented. Fields include: `provePersistent`, `connectives`, `useCompiledSteps`, `useFFI`, `optimizePreserved`, `evidenceOut`, `hooks`, `calc`, etc.

**MD3. proof-term-pipeline.md — not written**
The end-to-end proof term flow (backward → bridge → forward → guided → check) spans 5+ files but has no single document explaining the complete pipeline, the three execution profiles (full/guided/off), or how proof terms are constructed, verified, and composed.

### Tools Inventory

**16 tools audited. CLAUDE.md coverage:**

| Tool | LOC | In CLAUDE.md? | Significance |
|---|---|---|---|
| bench-compare.js | 306 | Yes | Cross-commit benchmark comparison |
| debug-ill.js | 568 | Yes | ILL debug runner with observation directives |
| explore-inspect.js | 90 | Yes | Leaf analysis for symbolic execution |
| test-ill.js | 170 | Yes | ILL-native test runner |
| bench-history.js | 519 | **No** | Commit-history benchmark across N commits |
| bench-to-doc.js | 157 | **No** | Converts bench-history JSON to markdown/chart |
| fuzz-ffi.js | 172 | **No** | FFI correctness fuzzer (FFI vs clause comparison) |
| bytecode-to-ill.js | 136 | **No** | EVM hex bytecode → CALC facts converter |
| precompile.js | 60 | **No** | Binary cache precompiler for .ill files |
| test-timing.js | 324 | **No** | Per-file test execution time profiler |
| analyze-csub.js | 57 | **No** | One-off compiled substitution analysis |
| fetch-vmtests.sh | 21 | **No** | Ethereum VMTest fixture fetcher |
| hevm-bench.sh | 152 | **No** | hevm vs CALC side-by-side benchmark |
| collect-tags.js | 77 | **No** | doc/ tag frequency counter → tags.yaml |
| list-tags.sh | 41 | **No** | doc/ tag listing with search |

11 of 16 tools (69%) are undocumented. The most significant omissions are `bench-history.js` (519 LOC, commit-range benchmarking), `fuzz-ffi.js` (FFI soundness testing), and `precompile.js` (binary cache generation).

### Circular Lazy Requires

**32 lazy requires found across the codebase. 2 true circular dependencies:**

**Circular 1: engine/explore.js ↔ engine/index.js**
- `engine/index.js` (top-level) → `engine/explore.js`
- `engine/explore.js:112` (lazy, inside function) → `engine/index.js`
- Broken by lazy require in explore.js. Used only for `codeToArrlit` bytecode normalization — an ILL-specific utility that shouldn't need to be in the explore→index path.

**Circular 2: engine/opt/compiled-clauses.js ↔ engine/opt/ffi.js**
- `opt/ffi.js:15` (top-level) → `opt/compiled-clauses.js`
- `opt/compiled-clauses.js:637` (lazy, inside `_resolveGuard`) → `opt/ffi.js`
- Explicitly documented in comment. Guards in Tier 3 compiled clauses need FFI dispatch for arithmetic guards.

**Notable non-circular lazy requires (init-order sensitive):**
- `engine/convert.js:23` — IIFE calls `loadILL()` at require time (C28 from Phase 6)
- `engine/forward.js:94` — lazy `require('./ill/connectives')` for ILL-specific role resolution
- `engine/explore.js:102` — lazy `require('./ill/connectives')` (same pattern)
- `engine/backward-cache.js:109` — lazy `require('./backchain')` to avoid loading 999-LOC module eagerly
- `parser/declarations.js:185,216` — lazy `require('../kernel/store')` inside conditional branches

### Bug Confirmation: pt.js summarizeSequent (pt.js:98-113)

**B12. summarizeSequent always displays '?' for all formulas**
Severity: MEDIUM (broken debug display)

`summarizeSequent(s)` accesses `.tag` on integer hash values:
```js
linear.map(f => f?.tag || '?').join(', ')   // f is a number, .tag is undefined
s.succedent?.tag || '?'                     // succedent is a number
```

Since all sequent formulas are content-addressed integer hashes (not objects), `.tag` on a number is always `undefined`, so every call produces output like `? ; ?, ? ⊢ ?`. This affects `ProofTree.toJSON()` and `ProofTree.toString()` — both call `summarizeSequent`.

Fix: Use `Store.tag(hash)` or `show(hash)` to dereference hashes before display.

No test covers this path — `summarizeSequent` is called only from debug display methods that no test exercises.

### test-overview.md Staleness

Current claims: "63 test files, 1605 tests in `npm test`"

Let me document what should be updated:
- Test count needs refreshing (CLAUDE.md says 1774 tests)
- Known failures list needs updating
- Architecture layer map and benchmark scripts are still accurate
- Missing newer test files added since the doc was written

### Phase 8 Architecture Summary

**Documentation health:**
- 20/42 documentation files are current (48%)
- 7 files are fully stale and should be archived or removed
- 9 files need targeted updates (mostly opt/ path drift)
- 3 key documents don't exist yet (existential-compile, matchOpts-reference, proof-term-pipeline)
- 48 legacy todo files violate stated CLAUDE.md policy

**CLAUDE.md health:**
- 6 factual inaccuracies found (1 HIGH, 2 MEDIUM, 3 LOW)
- Directory structure listing is incomplete for opt/ and parser/
- 11/16 tools undocumented (69%)

**Tooling health:**
- All 4 documented tools are accurate
- 11 undocumented tools exist, 3 are significant (bench-history, fuzz-ffi, precompile)

**Circular requires:**
- 2 true circular dependencies, both safely broken by lazy requires
- 30 other lazy requires for init-order or conditional loading

### Phase 8 Tasks

**CLAUDE.md fixes (immediate):**
- [x] Fix CLM1: Replace `provePersistentGoals` with correct function names (S3)
- [x] Fix CLM2: Update PRED_BOUNDARY from 26 to 31 (S3)
- [x] Fix CLM3: Fix `zero` ASCII from `0` to `zero` in connectives table (S3)
- [x] Fix CLM4: Note bang is binary (grade, formula) in connectives table (S3)
- [x] Fix CLM5: Add missing opt/ files to directory listing (S3)
- [x] Fix CLM6: Add missing parser/ files to directory listing (S3)
- [x] Add undocumented tools to CLAUDE.md Tooling section (S3: all 8 tools documented)

**Documentation fixes:**
- [ ] Fix opt/ path drift in architecture.md, forward-chaining-engine.md, optimization-architecture.md
- [x] Update test-overview.md with current test count and known failures (S3)
- [x] Update INDEX.md with newer documentation files (S3)
- [x] Archive or remove 7 fully stale docs (S3: deleted, preserved in git history)
- [ ] Update eigenvariable-walkthrough.md sections 9-10 (∃ is now implemented)
- [x] Fix B12: pt.js summarizeSequent — use Store.tag(hash) instead of hash.tag (S2)

**New documentation:**
- [ ] Write existential-compile.md (compiled ∃-chain partial evaluation)
- [ ] Write matchOpts-reference.md (15-field config object)
- [ ] Write proof-term-pipeline.md (backward → bridge → forward → guided → check)

**Cleanup:**
- [x] Remove or archive doc/todo/ (S3: deleted 49 files, ~4,019 LOC)
- [x] Remove dead wiki-link cross-references in stale docs (S3: stale docs deleted, dsl_refactor link removed from family-design.md)
- [ ] Consider breaking circular: explore.js → index.js (move codeToArrlit to a shared utility)

## Phase 9 Findings: Kolmogorov Density Pass

### Baseline

- `lib/` total: **27,322 LOC** across ~85 JS files
- `doc/todo/` legacy: **4,019 LOC** across 48 markdown files
- Target: 10-15% reduction in lib/ without losing features

### Unused Exports (30 confirmed)

Exports that exist in `module.exports` but are never imported by any file outside the defining module.

**Kernel layer (4 exports):**

| File | Export | LOC | Notes |
|---|---|---|---|
| kernel/store.js | `ARRAY_CHILD_TAGS` | 0 | Internal lookup table |
| kernel/store.js | `storeArray` | 0 | Low-level; `putArray` is the public API |
| kernel/store.js | `getArrayEntry` | 0 | Raw entry accessor; `getArrayElements` used instead |
| kernel/sequent.js | `setSuccedent` | ~5 | Sequent mutation helper, zero callers |

**Engine layer (14 exports):**

| File | Export | LOC | Notes |
|---|---|---|---|
| engine/backchain.js | `formatTerm` | ~15 | Debug helper, never imported |
| engine/backchain.js | `getCandidates` | ~10 | Candidate lookup, never imported |
| engine/backchain.js | `clearState` | ~3 | Registered via Store.onClear internally |
| engine/resolve-all.js | `alphaRenameClause` | ~20 | Internal to resolveAll |
| engine/tree-utils.js | `isTerminal` | ~5 | Internal to tree-utils |
| engine/optimizer.js | `PROFILES` | 0 | Profile registry, never consumed externally |
| engine/optimizer.js | `PROFILE_DEFAULTS` | 0 | Default profile, never consumed externally |
| engine/directive-loader.js | `hasFreevar` | ~5 | Internal helper |
| engine/index.js | `codeToArrlit` | ~30 | Used internally but export is unused |
| engine/compose.js | `fuseLinearPair` | ~20 | Only called by internal `fuseLinearPairExpanded` |
| engine/type-check.js | `_extractSortName` | ~5 | Private helper (underscore-prefixed) |
| engine/fact-set.js | `REMOVE_OP` | 0 | Internal arena opcode constant |
| engine/opt/structural-memo.js | `checkMemo` | ~10 | Exported but never imported |
| engine/ill/loli-drain.js | `isPersistentTriggerLoli`, `isAllPersistentAntecedent` | ~10 | Internal predicates |

**Prover layer (5 exports):**

| File | Export | LOC | Notes |
|---|---|---|---|
| prover/rule-interpreter.js | `buildRuleSpecsFromMeta` | ~15 | Internal two-phase helper |
| prover/check-term.js | `buildCheckerMap` | ~10 | Internal to createChecker |
| prover/generic-term.js | `genericTermSignature` | ~5 | Internal to buildSignatureMap |
| prover/generic-term.js | `SPECIAL_SIGNATURES` | 0 | Internal lookup table |
| prover/guided-term.js | (not a re-export — has real logic) | 0 | False positive cleared |

**Other (5 exports):**

| File | Export | LOC | Notes |
|---|---|---|---|
| kernel/unify.js | `isFreevar` | ~3 | Internal predicate |
| kernel/unify.js | `getVarName` | ~3 | Internal name accessor |
| kernel/eq-theory.js | `strlitTheory` | 0 | `defaultTheories` is the entry point |
| meta-parser/loader.js | `extractDeclarations` | ~40 | Internal to loadWithExtends |
| meta/focusing.js | `flowToPolarity` | ~5 | Internal to buildFocusingMeta |
| browser.js | `isInitialized` | ~3 | No external consumers |

**Impact:** Removing these from `module.exports` reduces public API surface. Estimated ~30 LOC of export declarations, plus enables future dead code elimination of the functions themselves if they become unreferenced.

### Dead Code (confirmed)

**DC1. unifyBinlit and unifyStrlit (kernel/unify.js:46-82)**
37 LOC. Two functions defined but never called, never exported. Comment claims "kept for tests" but no test references them. eq-theory dispatch replaced their functionality. `unifyArrlit` (line 85) IS still live — called by `unifyUF`.

**DC2. doc/todo/ legacy directory (48 files, 4,019 LOC)**
Violates stated CLAUDE.md policy ("TODOs are managed externally via hq CLI"). All files are pre-hq legacy. Should be deleted.

### Duplication Analysis

| # | Category | Duplicate LOC | Net savings | Risk |
|---|---|---|---|---|
| DUP1 | matchOpts assembly (forward.js + explore.js) | 24 | 24 | LOW — self-referencing closure needs factory pattern |
| DUP2 | _firstArgHead pattern 4× (compiled-clauses.js) | 98 | 67 | LOW — mechanical extraction |
| DUP3 | Hash-walking substitution (declarations.js + convert.js) | 33 | 30 | LOW — share via kernel/substitute.js |
| DUP4 | Number/hex parsing 2× (earley-grammar.js) | 12 | 5 | NONE — trivial extraction |
| DUP5 | Binder/non-binder branches (earley-grammar.js) | 130 | 60 | LOW — compute target NT, single branch |
| DUP6 | Bang grammar rules 2× (earley-grammar.js) | 22 | 11 | NONE — extract helper with NT parameter |
| DUP7 | loli_monad rule gen 2× (earley-grammar.js) | 14 | 7 | NONE — merge into binary op loop |
| DUP8 | backchainIndex guard (forward.js + explore.js) | 8 | 4 | NONE — extract to backchain.ensureIndex |
| | **Total** | **341** | **208** | |

### Pure Re-export / Wrapper Files

| File | LOC | Verdict | Savings |
|---|---|---|---|
| engine/opt/disc-tree-opt.js | 11 | **DELETE** — pure re-export of 1 function from disc-tree.js | 11 |
| prover/index.js | 13 | **DELETE** — re-exports `create`/`prove` from strategy/auto.js | 13 |
| engine/opt/fingerprint.js | 32 | KEEP — aggregates 3 modules, useful as facade | 0 |
| engine/compiled-sub.js | 31 | **MERGE** into state-ops.js — 1 function, 9 LOC logic | ~20 |
| | **Total** | | **44** |

### Tiny Files Assessment (<50 LOC)

| File | LOC | Verdict |
|---|---|---|
| engine/opt/disc-tree-opt.js | 11 | Delete (pure re-export) |
| prover/index.js | 13 | Delete (pure re-export) |
| engine/ill/connectives.js | 30 | Keep — standalone config table |
| engine/compiled-sub.js | 31 | Merge into state-ops.js |
| engine/opt/fingerprint.js | 32 | Keep — useful facade |
| kernel/fresh.js | 33 | Keep — clean single-responsibility |
| parser/balanced-split.js | 33 | Keep — shared utility, 3 consumers |
| calculus/modes.js | 39 | Keep — standalone descriptor |
| engine/grades.js | 39 | Keep — Store.onClear lifecycle |
| engine/preserved.js | 42 | Keep — 2 cohesive functions |

### show.js EVM-specific Defaults

`show.js` (124 LOC) has EVM-specific behavior in two functions:

1. `classifyLeaf` (lines 66-92): hardcodes atom names `stop`, `revert`, `invalid`, `pc` for EVM leaf classification
2. `showInteresting` (lines 102-122): default `exclude` set `['bytecode', 'calldata']` is EVM-specific

Both are used by 8+ test files and tools. The EVM defaults are pragmatic — show.js is a debug utility, and EVM is the primary use case. Making these configurable would add complexity for no current benefit. The default exclusion set already accepts an override via `opts.exclude`.

**Verdict:** Keep as-is. The EVM defaults are documented and overridable.

### LOC Budget

| Category | Savings |
|---|---|
| Dead code (unifyBinlit/unifyStrlit) | 37 |
| doc/todo/ removal | 4,019 (markdown, not lib/) |
| Duplication consolidation | 208 |
| Re-export file deletion | 44 |
| Unused export cleanup (declaration lines only) | ~30 |
| **lib/ total savings** | **~319 LOC** |
| **As % of 27,322** | **~1.2%** |

The 10-15% target (2,700-4,100 LOC) is unrealistic without removing features or major modules. The codebase is already quite dense — the prior 8 phases found very little truly dead code. The 1.2% is the honest achievable savings from cleanup alone.

Additional savings possible from:
- Removing doc/todo/ (~4,019 markdown LOC, not lib/)
- The naming pass from Phases 1-7 (shorter names save a few bytes but not LOC)
- Collapsing earley-grammar.js binder/non-binder branches (~60 LOC, already counted in DUP5)

### Phase 9 Tasks

**Immediate (safe, no risk):**
- [x] Delete unifyBinlit and unifyStrlit from unify.js (DC1, 37 LOC) (S3)
- [x] Delete doc/todo/ directory (DC2, 49 files, ~4,019 LOC) (S3)
- [x] Delete engine/opt/disc-tree-opt.js, update 1 importer (S3)
- [x] Delete prover/index.js, update 3 importers to use strategy/auto.js directly (S3)
- [x] Merge engine/compiled-sub.js into engine/state-ops.js (S3)
- [x] Remove unused exports from module.exports (30 symbols across 17 files) (S3)

**Medium effort (duplication):**
- [ ] Extract shared _firstArgHead helper in compiled-clauses.js (DUP2, ~67 LOC saved)
- [ ] Extract buildMatchOpts factory (DUP1, ~24 LOC saved)
- [ ] Extract _parseNumber helper in earley-grammar.js (DUP4, ~5 LOC saved)
- [ ] Collapse binder/non-binder branches in earley-grammar.js (DUP5, ~60 LOC saved)
- [ ] Extract bang/loli_monad grammar helpers (DUP6+7, ~18 LOC saved)
- [ ] Extract shared hash-walking substitution to kernel/ (DUP3, ~30 LOC saved)
- [ ] Extract backchainIndex guard helper (DUP8, ~4 LOC saved)

**Decision needed:**
- [ ] LOC budget reality check — 1.2% is the honest achievable without feature removal. Adjust target or accept.

## Phase 10 Findings: Integration Verification

### Test Suite Status Summary

| Suite | Pass | Fail | TODO | Total | Status |
|---|---|---|---|---|---|
| `npm test` (main) | 2009 | 0 | 12 | 2021 | **GREEN** |
| `test:ill` | 95 | 3 | 0 | 98 | 3 SHA3 failures |
| `test:noffi` | 13 | 0 | 0 | 13 | **GREEN** |
| `test:zk` | 66 | 28 | 0 | 94 | 28 failures (up from 24) |
| `fuzz-ffi` | 850 | 0 | 50 skipped | 900 | **GREEN** |
| proof-terms | 127 | 0 | 0 | 127 | **GREEN** |
| evidence | 13 | 0 | 0 | 13 | **GREEN** |
| hooks | 12 | 0 | 0 | 12 | **GREEN** |
| clause-terms | 18 | 0 | 0 | 18 | **GREEN** |

### Main Suite (`npm test`) — 0 failures

All 2009 tests pass. 12 tests marked as TODO (known failures) — all are VMTest loop fixtures:
- `loop-add-10M`, `loop-divadd-10M`, `loop-divadd-unr100-10M`
- `loop-exp-{1b,2b,4b,8b,16b,32b}-{100k,1M}`
- `loop-mul`, `loop-mulmod-2M`, `loop-exp-nop-1M`

These are large EVM loop tests that exceed resource limits. Correctly marked as TODO known failures.

### Heavy Suite Tests — triaged

**monad.test.js: 9 failures (test bug, not code bug)**

All 9 failures are in `rightFocus succedent decomposition` suite (lines 490-620). Root cause: tests call `rightFocus(linear, persistent, hash)` without the 4th `roles` parameter. Since `rightFocus` was parameterized with a `roles` map (e.g. `{ product: 'tensor', unit: 'one', exponential: 'bang' }`), all decomposition branches (`roles.product && tag === roles.product`) evaluate to `false`, causing tensor/one/bang decomposition to never trigger.

The atom tests pass because atom lookup doesn't use roles. The connective decomposition tests fail because roles is `{}`.

Fix: Pass `deriveRoles(constructors, polarity)` as 4th arg in each test, or hardcode `{ product: 'tensor', unit: 'one', exponential: 'bang' }`.

**rule-analysis.test.js: 11 failures in 320s (not a hang)**

The test file (1,310 LOC) loads the full EVM model via `mde.load()` in a `before` hook. Completes in ~320 seconds: 67 pass, 11 fail. The 11 failures need triage (likely stale assertions from pre-refactor era). This test is in `test:heavy` with `--timeout=1800000` (30 min) and `--max-old-space-size=8192`.

Triage: 11 failures need investigation, but NOT a hang — just very slow.

**type-check.test.js: 3 failures (assertion format mismatch)**

All 3 failures are in `_checkTerm` and `checkForwardRule` suites. Root cause: test regex expects error message `expects 3 args, got 2` but actual message includes sort information: `'plus' expects 3 args (bin, bin, bin), got 2`. The error message format changed when sort names were added to arity error reporting.

Fix: Update test regexes to match the new format, e.g. `/expects 3 args.*got 2/`.

### test:ill — 3 SHA3 failures

All 3 failures are in `calculus/ill/tests/forward/evm-sha3.ill`:
- `expect_sha3_32bytes`
- `expect_sha3_64bytes`
- `expect_sha3_0bytes`

Root cause: Tests expect symbolic SHA3 representation (`sha3(0xff ++ 0)`) in the final stack, but when `js-sha3` is available, the FFI computes the concrete Keccak-256 hash. The test assertion (`Pattern not found in final state`) fails because the concrete hash doesn't match the symbolic pattern.

This is a representation mismatch — the tests were written for symbolic SHA3, but FFI produces ground results. These tests would pass in noFFI mode (no SHA3 FFI).

Triage: Known — SHA3 tests need `(useFFI: false)` setting or concrete expected values.

### test:zk — 28 failures (up from planned 24)

**Breakdown by root cause:**

| Root cause | Failures | Details |
|---|---|---|
| `compiled is not defined` (ReferenceError) | 20 | Undefined variable at `flat-witness.js:349` |
| `deltaRemove: hash N not in live delta` | 3 | Resource accounting mismatch in witness generator |
| `Cannot read properties of undefined (reading 'chips')` | 1 | Null witness returned |
| `witness should exist` | 1 | Missing witness assertion |
| subtestsFailed (cascading) | 3 | Parent suites reporting child failures |

**B13. flat-witness.js:349 — `compiled` variable undefined**
Severity: HIGH (blocks 20 ZK tests)

In `generateFlatWitness`, line 349 does `row.push(compiled)` but `compiled` is never defined in the function scope. The variable was likely removed or renamed during a refactor but this reference was not updated. It should be a computed value `isLoli ? 0 : 1` (or similar boolean distinguishing compiled rules from loli matches).

**deltaRemove errors** are real resource accounting bugs in the tree-based witness generator (`witness.js`). The live delta tracking gets out of sync when proof term decomposition encounters unexpected structure.

### Proof Term Verification

All proof term-related tests pass:
- `proof-terms.test.js`: 127/127 (backward proof terms, all connectives)
- `clause-terms.test.js`: 18/18 (clause-level backward terms)
- `evidence.test.js`: 13/13 (forward execution evidence)
- `hooks.test.js`: 12/12 (engine observability hooks)

The forward → guided → check pipeline works for all tested profiles. The `check-term.js` verifier correctly validates proof terms across connective decomposition.

### FFI Soundness

`fuzz-ffi.js` ran 850 predicate tests (50 per predicate × 17 predicates), 0 mismatches between FFI and clause resolution. 50 skipped (`dec` predicate — predecessor, not fuzz-testable with random inputs).

### NoFFI Adversarial Soundness

`test:noffi`: 13/13 pass. All tests run with `dangerouslyUseFFI: false`, forcing clause resolution for all persistent goals. No soundness regressions.

### Benchmark Verification

No benchmark comparison run in this phase (no code changes to compare against). The most recent commit `9b01c1a` (Tier 1 allocation reduction) already has verified benchmarks.

### Cross-Phase Failure Summary

| Finding | Source | Severity | Status |
|---|---|---|---|
| monad.test.js 9 failures | Phase 10 | LOW | Test bug — missing `roles` parameter |
| type-check.test.js 3 failures | Phase 10 | LOW | Test bug — regex format mismatch |
| rule-analysis.test.js 11 failures (320s) | Phase 10 | MEDIUM | Heavy test, 67 pass / 11 fail |
| test:ill SHA3 3 failures | Phase 10 | LOW | Known — FFI vs symbolic mismatch |
| test:zk 20 failures (compiled) | Phase 10 | HIGH | Bug B13 — undefined variable in flat-witness.js |
| test:zk 3 failures (deltaRemove) | Phase 10 | MEDIUM | Resource accounting bug in witness.js |
| 12 TODO VMTest loops | Phase 10 | LOW | Known — resource limit, correctly marked |

### Phase 10 Tasks

**Immediate fixes:**
- [ ] Fix B13: Define `compiled` variable in flat-witness.js:349 (unblocks 20 ZK tests)
- [ ] Fix monad.test.js: Pass roles parameter to rightFocus tests (9 fixes)
- [ ] Fix type-check.test.js: Update 3 regexes to match new error format
- [ ] Fix test:ill SHA3: Add `(useFFI: false)` setting or update expected values

**Investigation needed:**
- [ ] Triage rule-analysis.test.js 11 failures — determine root cause (67 pass / 11 fail in 320s)
- [ ] Triage test:zk deltaRemove errors (3) — resource accounting in witness.js
- [ ] Triage test:zk remaining 5 failures — chips/witness existence

**Verification (no action needed):**
- [x] npm test: 2009 pass, 0 fail — GREEN
- [x] test:noffi: 13 pass, 0 fail — GREEN
- [x] fuzz-ffi: 850 pass, 0 fail — GREEN
- [x] Proof term generation: 127+18+13+12 pass — GREEN
- [x] Evidence + hooks: all pass — GREEN
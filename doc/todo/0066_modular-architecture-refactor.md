---
title: "Modular Architecture Refactor — Core/Optimization Separation"
created: 2026-03-03
modified: 2026-03-04
summary: "Extract optimizations from core engine via hook system, make Lax monad explicit as 2-mode adjoint, enable multiple logics. Comprehensive plan with all deliberations."
tags: [architecture, refactor, modularity, lax-monad, optimization, adjoint-logic, separation-of-concerns, proof-certificates]
type: design
status: planning
priority: 10
cluster: Theory
depends_on: []
required_by: [TODO_0006, TODO_0008, TODO_0010, TODO_0012, TODO_0064]
starred: true
---

# Modular Architecture Refactor — Core/Optimization Separation

## Table of Contents

1. [Motivation](#motivation)
2. [Current State Audit](#current-state-audit)
3. [Architecture Decisions (with deliberations)](#architecture-decisions)
4. [Performance Analysis](#performance-analysis)
5. [Extensibility: Ownership, Graded Modalities, Proof Certificates](#extensibility)
6. [Refactor Plan (Phases 1-3)](#refactor-plan)
7. [Optimization Migration Table](#optimization-migration-table)
8. [Success Criteria](#success-criteria)
9. [Non-Goals](#non-goals)
10. [Context Recovery Guide](#context-recovery-guide)
11. [References](#references)

---

## 1. Motivation

CALC evolved from a generalized calculus sandbox to a competitive symbolic execution engine. Each step specialized further: ILL fragments (oplus, loli-in-monad), forward chaining, EVM programs, performance optimization. While the theoretical foundations remained sound, the implementation accumulated optimization code deeply interleaved with core logic — particularly in the forward engine.

**The problem:** We "hacked" the Lax monad by implementing its optimizations (committed choice, FFI bypass, fingerprint indexing) without first having a clean core that implements the theory. We can't turn optimizations off. We can't easily add new logics.

**The goal:** A suckless, modular architecture where:
1. The core is minimal, readable, and implements the theory faithfully
2. Optimizations are separate modules (`opt/`) registered via hooks
3. The Lax monad is explicit as a 2-mode adjoint system (backward ↔ forward)
4. Multiple logics can coexist
5. Performance is preserved (< 2% regression on solc_symbolic)
6. Future extensions (ownership modalities, graded types, proof certificates) are easy to add

---

## 2. Current State Audit

### 2.1 What's Clean (kernel + prover: 3,328 LOC)

**Score: 9.5/10.** The backward prover is exemplary:

- **L1 kernel.js** (191 LOC) — pure proof verification, one hardcoded `copy` rule (minor smell)
- **L2 generic.js** (232 LOC) — calculus-generic search primitives, zero ILL assumptions
- **L3 focused.js** (300 LOC) — pure Andreoli focusing, parameterized by calculus polarity
- **rule-interpreter.js** (167 LOC) — descriptor-driven, generates from .rules files
- **store.js** (583 LOC) — content-addressed substrate, calculus-agnostic
- **unify.js** (728 LOC) — optimizations clearly marked, core logic preserved
- **substitute.js** (306 LOC) — three substitution paths (simple/indexed/compiled), additive

**Only ILL assumptions:** two-context default in sequent.js (parameterized), pre-registered tags 0-25 (extensible via PRED_BOUNDARY), `copy` rule hardcoding in kernel.js.

See `doc/documentation/architecture.md` for the full prover lasagne (L1-L5).

### 2.2 What's Dirty (engine: 5,364 LOC, ~45% optimization)

The forward engine has **severe optimization entanglement**:

| File | LOC | Optimization % | Entanglement |
|------|-----|----------------|-------------|
| match.js | 853 | 40% | **SEVERE** — fingerprint, compiled steps, pooling all in core matching |
| symexec.js | 497 | 70-75% | **EXTREME** — prediction, memo, solver, drain all in go(); 7 solver checkpoint/restore sites; boundCount shared state between memo and core DFS |
| strategy.js | 285 | 50% | **HIGH** — fingerprint hard to disable |
| compile.js | 535 | 35% | MODERATE — discriminator detection removable |
| fact-set.js | 487 | 40% | LOW — Zobrist optional, Arena needed for DFS |
| forward.js | 128 | 30% | MODERATE — fingerprint index rebuild |
| prove.js | 280 | 10% | LOW — FFI is optional flag |
| disc-tree.js | 253 | 30% | LOW — swappable strategy layer |
| ffi/* | 1,153 | 100% | MINIMAL — cleanly separable |

### 2.3 Specific Entanglement Points (with code locations)

**1. match.js:matchOnePattern (lines ~454-561)** — Three dispatch strategies nested in one 108-line function:
- Delta bypass: `if (role === 'delta') { ... }` — skip matching for produced-and-consumed facts
- Secondary index O(1): `if (secondaryIndex) { ... }` — fingerprint-based candidate lookup
- General matching: linear scan over FactSet group
Cannot disable one strategy without rewriting the function.

**2. match.js:provePersistentGoals (lines 261-337)** — Three-level cascade hardcoded in sequence:
- Level 1: FFI arithmetic (`tryFFIDirect`) — O(1) for inc, plus, neq, mul
- Level 2: State lookup — scan `state.persistent.group(tagId)`
- Level 3: Backward clause resolution (`prove.js`)
Order and dispatch cannot be configured per-predicate. If FFI returns `{ success: false }`, it's definitive — no clause fallback. See `doc/documentation/forward-optimization-roadmap.md` "Persistent proving order" for analysis.

**⚠ FFI definitive failure is a composability blocker.** This is not just an ordering issue — it's a semantic decision. When FFI is registered for a predicate and returns false, clause resolution never fires. The refactor should make this configurable per-predicate: FFI-definitive (current, fast) vs FFI-advisory (falls through to clauses on failure).

**3. symexec.js:go() (lines 310-482)** — 170-line DFS function with ALL of these interleaved:
- Cycle detection via `pathVisited` Set (core)
- Global state memo via `globalVisited` Set (core)
- Structural memo via `computeControlHash` + `globalControl` Map (optimization, lines 321-330)
- Bound tracking via `boundCount` (core + structural memo interaction)
- Prediction (Opt_H) via `predictNext` + fast-path tryMatch (optimization, lines 337-349)
- Constraint solver via `solver.checkpoint/restore/checkSAT` (optimization, lines 367-398)
- Persistent-loli drain via `drainPersistentLolis` (optimization, lines 373-374)
- SAT-based alternative pruning (optimization, lines 388-467)
Cannot disable any optimization without 100+ LOC refactoring.

**Additional severity notes:**
- Constraint solver has **7 checkpoint/restore call sites** throughout go() — it's not a peripheral hook but a deeply woven undo protocol
- `boundCount` is **shared mutable state** between structural memo logic and core DFS termination — a data dependency, not just control flow coupling
- `drainPersistentLolis` is called in **3 different contexts** (single-alt, multi-alt-single-survivor, multi-alt-foreach) with subtly different sequencing requirements

**4. symexec.js:predictNext (lines 244-264)** — Prediction requires:
- `fpConfig.type === 'virtual'` (fingerprint config, from strategy.js)
- `rule.nextPointerSlot` / `rule.nextPointerValue` (compiled at `compileRule` time)
- Bytecode array lookup via `ffi.convert.binToInt`
- Discriminator index from `buildDiscriminatorIndex`
All tightly coupled between strategy.js, compile.js, and ffi/convert.js.

**5. strategy.js:detectStrategy (lines ~171-182)** — Always attaches `attachPredictions` if fpConfig exists. No way to use fingerprint indexing without prediction metadata. `attachPredictions` (lines 133-159) computes `nextPointerSlot` for each rule — even when prediction is unused.

### 2.4 What's Missing (the Lax Monad Gap)

TODO_0006 documents this precisely. The forward engine **is** the Lax monad's monadic computation (see TODO_0006 §2.1), but:

1. **No backward→forward mode switch.** L3 focused.js has no concept of `{S}`. Users invoke `symexec.explore()` directly — there's no backward prover that hands off to forward.
2. **No mixed-mode programs.** Can't combine backward and forward chaining in one query.
3. **No formal connection.** Forward and backward are separate worlds sharing only Store. The mode switch (TODO_0006 §4.2) is the critical bridge: sequent `{ contexts, succedent }` ↔ multiset state `{ linear, persistent }`.
4. **No proof objects from forward.** `symexec.explore()` produces execution trees but not verifiable proofs.

**What IS implicit already** (from TODO_0006 §2.2):
- `forward.js:run()` IS the monadic computation (committed choice loop)
- `provePersistentGoals` IS "forward invokes backward" (LolliMon pattern)
- Quiescence detection IS monad exit
- `symexec.explore()` IS exhaustive monad — tree of all monadic values

---

## 3. Architecture Decisions (with deliberations)

### Decision 1: One code path with hook points (not parallel core/optimized)

**Considered alternatives:**

**Option A: Separate `engine/core/` directory** with pure theory implementations (match-core.js, forward-core.js, symexec-core.js) + existing optimized engine files.
- Pro: Clean trust boundary, core is independently auditable
- Con: **Two parallel implementations to maintain.** Every bug fix must be mirrored. Drift risk. Which one runs in production? If only the optimized one runs, the "core" rots.

**Option B: One code path, hook points, optimizations in `opt/`.**
- Pro: One source of truth. No "is the bug in core or optimized?" Each opt/ file is self-contained.
- Con: Core readability slightly reduced by hook dispatch code.

**Option C: In-place refactoring (extract optimizations but no directory split).**
- Pro: Minimal file changes, good git history
- Con: No clear separation between core and optimization code in the filesystem.

**Decision: Option B.** One code path. The existing engine files become the hook-point versions. Optimizations extracted to `opt/` files. Default profile = "evm" (same behavior as today). "bare" profile = all hooks unset (naive fallbacks).

```
engine/
├── match.js          ← one code path, with hook points
├── forward.js        ← committed choice loop, with hook points
├── explore.js        ← DFS exploration, with hook points (renamed from symexec.js)
├── prove.js          ← backward chaining, with hook points
├── optimizer.js      ← hook registry + profiles
├── compile.js        ← rule compilation (shared)
├── convert.js        ← .ill → hashes (shared)
├── state-ops.js      ← state operations (shared)
└── opt/
    ├── fact-set.js
    ├── fingerprint.js
    ├── disc-tree.js
    ├── ffi.js
    ├── compiled-pers.js
    ├── prediction.js
    ├── structural-memo.js
    ├── constraint.js
    └── loli-drain.js
```

**Why not two code paths:** The HOL Light / Metamath Zero model (small kernel + untrusted tactics) works because the kernel *verifies* the tactics' output. In CALC's forward engine, there's no separate verification step (yet — proof certificates would add one). Until then, a separate "core" that nobody runs is dead code. The hook system means the core IS the running code, just with naive fallbacks when no optimization is registered.

### Decision 2: Model B hook dispatch (function pointers at creation time)

**Considered alternatives:**

**Model A: Runtime hook array check** — `if (hooks.length > 0) for (hook of hooks) hook(state, ...)`
- Creates polymorphic call sites. V8 inline cache tracks call target; 5+ distinct types → megamorphic.
- **Measured precedent:** RES_0069 documented 59 closures at one call site → V8 megamorphic → 25% regression.
- Cost estimate: hooks fire ~468 times/explore × ~1µs overhead per megamorphic call = 468µs = **8.8% regression**. Unacceptable.

**Model B: Function pointers resolved at engine creation** — `const findCandidates = opts.findCandidates || naiveScan;`
- V8 sees monomorphic call sites (one function per site).
- Cost: ~0.2µs overhead per call × 468 calls = 93µs = **1.75% regression**. Acceptable (within solc_symbolic noise of ±0.7-0.9ms).
- **Already used by strategy.js:** `buildStrategyStack` composes layers at load time — same pattern.

**Decision: Model B.** All hooks resolved once at `explore()` / `run()` startup. The go() hot loop makes direct calls to the resolved function pointers.

```javascript
// At explore() startup — resolved ONCE
const findCandidates = opts.findCandidates || naiveScan;
const provePersistent = opts.provePersistent || clauseResolve;
const checkMemo = opts.checkMemo || null;
const predict = opts.predict || null;
const prune = opts.prune || null;

// In go() hot loop — direct call, V8 monomorphic IC
matches = findCandidates(state, rules, strategy);
// No condition check — null hooks are just never called in the code path
```

**Zig mapping:** Model B maps directly to `*const fn(...)` function pointers. Zig also enables Model C (comptime dispatch) for zero overhead in Zig binary — hooks resolved at compile time.

### Decision 3: State normalization at API boundary only

**Problem:** If code branches on state type (`if (state.linear.group) ... else ...`) in the hot path, V8's hidden class tracking sees two object shapes → megamorphic property access → 20-40% regression.

**Decision:** Internally, always FactSet-based State. `fromObject()` at entry (once), `toObject()` at exit (once). Never branch on state type inside `go()` or `tryMatch()`.

The "bare" profile still uses FactSet internally — it's a different optimization profile, not a different state representation. The FactSet is core infrastructure (it provides Arena undo for DFS backtracking), not an optimization.

### Decision 4: Lax monad as 2-mode adjoint (not standalone)

**Question:** Given that we want adjoint logic eventually (for MTDC, ownership modalities, graded types), should we implement `{A}` as a standalone monad or design it as the first instance of a general adjoint framework?

**Considered alternatives:**

**Option A: Standalone `{A}` (CLF-style, hardcoded 2 modes)**
- Pro: Simpler. ~500 LOC. Well-understood (CLF, LolliMon, Celf, Ceptre all do it).
- Con: If we later generalize to adjoint, the hardcoded "backward/forward" distinction must be refactored into parameterized modes.

**Option B: `{A}` as first instance of N-mode adjoint system**
- Pro: Generalizes to ownership, graded, etc. without rearchitecting. Mode-switching infrastructure written once.
- Con: Slightly more abstract upfront. Requires a mode theory object even though we only have 2 modes.

**Option C: Skip `{A}`, jump straight to full adjoint logic**
- Pro: No wasted work on intermediate step.
- Con: Requires designing mode preorder upfront — which modes? what ordering? what structural rules? This is a research question with zero implementation experience. Risk of committing to wrong mode theory.

**Decision: Option B — `{A}` as 2-mode adjoint.**

The critical insight (from RES_0052 §6): `{A}` IS a 2-mode adjoint system. The two modes are `backward` (unrestricted: weakening + contraction) and `forward` (linear: committed choice). The lax monad is `↑_fwd(↓_bwd A)` — downshift to forward, upshift back to backward.

The **hard engineering** is mode-switching infrastructure (sequent↔multiset conversion in L3, quiescence detection, result return to backward prover). This infrastructure is identical for 2 modes or N modes. Generalizing from 2 to N modes later is ~200 LOC of refactoring (add mode entries, parameterize structural rules), not rearchitecture.

**Why not jump straight to full adjoint (Option C):**
- Adjoint logic requires designing the mode preorder upfront. What modes exist? What's the partial order? Which structural rules per mode? These are research questions (TODO_0012) that shouldn't block the core extraction.
- `{A}` has known, tight requirements — 30 years of proven design (CLF 2004, LolliMon 2005).
- Testing: mixed-mode programs with 2 modes is a sharp, testable boundary. N modes means combinatorial test explosion on the first attempt.
- Risk: `{A}` first = low risk (proven theory) then medium risk (generalize with data). Adjoint first = medium-high risk (commit blind).

**Concrete design:**

```javascript
// Mode theory — 2 modes for now, extensible to N
const modes = {
  backward: { structural: { weakening: true, contraction: true } },
  forward:  { structural: { weakening: false, contraction: false } }
};

// Shifts — {A} is the first shift. Later: ownership, graded, etc.
const shifts = [
  { from: 'backward', to: 'forward', connective: 'monad', polarity: 'negative' }
];
```

When adjoint modalities are added later:
```javascript
const modes = {
  backward: { structural: { weakening: true, contraction: true } },
  forward:  { structural: { weakening: false, contraction: false } },
  affine:   { structural: { weakening: true, contraction: false } },
  relevant: { structural: { weakening: false, contraction: true } },
};

const shifts = [
  { from: 'backward', to: 'forward', connective: 'monad', polarity: 'negative' },
  { from: 'affine', to: 'backward', connective: 'upshift_a_b', polarity: 'negative' },
  // ... more adjoint pairs
];
```

### Decision 5: Proof certificates — deferred but designed-for

Proof certificates (TODO_0008, TODO_0045) are out of scope for this refactor. However, the architecture must not make them hard to add later.

**Design-for principles:**

1. **Hook points produce enough data for certificates.** Each hook receives the full match context (rule, theta, consumed, produced) and could log it. A future `certificateHook` would record this per step.

2. **`go()` already returns tree nodes.** The execution tree (`{ type: 'branch', children: [{ rule, child }] }`) IS the skeleton of a proof certificate. Each node records which rule fired. A future extension adds `theta`, `consumed`, `produced` to each node.

3. **provePersistentGoals must record evidence.** Currently returns only success/failure. For certificates, it must return HOW each persistent goal was proved (FFI, state lookup, or clause resolution). The hook system makes this natural: each proving strategy returns evidence alongside the result.

4. **The mode switch bridge (Phase 2) must produce proof terms.** When L3 calls the forward engine via `{A}`, the forward engine must return something L1 kernel can verify. The certificate structure (per THY_0001):
```javascript
{
  type: 'step',
  rule: ruleName,
  theta: substitution,
  consumed: { hash: count },
  produced: { hash: count },
  persistent_proved: [{ goal, method: 'ffi'|'state'|'clause', evidence }],
}
```

5. **Connection to FPC (Miller).** The certificate is a focused proof in the forward fragment. The "clerk" (deterministic phase) checks structural rules; the "expert" (= the certificate) supplies rule choices and substitutions. See RES_0077 §4 for the clerk/expert pattern.

**What NOT to do:** Don't introduce per-step logging overhead in the hot path. Certificates should be opt-in via a hook, not always-on. The hook point is there; the logging is off by default.

### Decision 6: Zig-portable hook design

The hook architecture must map cleanly to Zig. This is a **hard constraint** on the design — if a JS pattern doesn't translate to Zig without significant performance regression or ugly code, find an alternative pattern.

**Zig mapping of Model B:**
- **Hooks = function pointers.** Model B's `const findCandidates = opts.findCandidates || naiveScan` maps to `*const fn(...)` in Zig. Monomorphic call sites. Zero overhead.
- **Zig bonus: comptime dispatch (Model C).** If the profile is known at compile time, Zig can resolve hooks at comptime → zero-cost abstractions. The JS Model B pattern enables this Zig upgrade without changing the API.
- **Context structs, not closures.** Hooks take explicit parameters (state, rules, config) and return explicit results. No captured mutable state, no `this`, no prototype chains. This maps directly to Zig function signatures.

**Zig-friendly data structure constraints (already met):**
- **Avoid Map/WeakMap in hot paths.** Use typed arrays, integer indices, flat arrays.
- **Keep Arena/FactSet as-is.** They're already Zig-native (flat Int32Array, push4/checkpoint/restore).
- **Profile = plain struct.** A profile is a set of function pointers + config values. Maps to a Zig struct with `?*const fn(...)` optional function pointers.

**Design validation:** Before finalizing hook signatures, verify each one translates to a clean Zig function pointer type. If a hook needs to capture state (e.g., solver needs its own checkpoint), pass that state as an explicit context parameter, not via closure.

See `doc/documentation/forward-optimization-roadmap.md` "Zig Port Mapping" for the translation table.

---

## 4. Performance Analysis

### 4.1 Current Hot Path

**solc_symbolic benchmark: 477 nodes, ~5.3ms median, ~11µs/node.** Profile is flat:

| Component | Est. time | % | Per-node | Notes |
|---|---|---|---|---|
| tryMatch | ~1.8ms | 34% | ~3.8µs × 468 | 415 prediction hits + 53 findAllMatches |
| mutateState | ~1.3ms | 24% | ~2.8µs × 456 | consume + produce + tagId lookups |
| other/overhead | ~1.2ms | 23% | | DFS frames, alloc, Set/Map ops |
| undo | ~0.28ms | 5% | | Arena restore |
| hashing | ~0.27ms | 5% | | stateHash + controlHash |
| solver | ~0.17ms | 3% | | EqNeq checkpoint/restore |
| drain+predict+snap | ~0.3ms | 6% | | Loli drain, prediction lookup, leaf snapshots |

**Per DFS node (~25-35 function calls):**
```
go(depth, predicted)
├─ tryMatch (or findAllMatches)     ~3.8µs
│  ├─ matchAllLinear                  worklist loop
│  │  ├─ matchOnePattern × N          pattern matching
│  │  └─ provePersistentGoals         FFI / state / clause cascade
│  └─ resolveExistentials             usually no-op
├─ mutateState                       ~2.8µs
│  ├─ consumeLinear                    FactSet.remove × count
│  ├─ produceLinear                    FactSet.insert × count
│  └─ producePersistent                FactSet.insert × count
├─ drainPersistentLolis              ~0.3µs (0-1 loli fires)
├─ Arena checkpoint/restore          ~0.6µs
└─ go(depth+1) recursive             ~0µs (just a call)
```

### 4.2 Hook Overhead Budget

**Target: < 2% regression = < 106µs additional per explore.**

| Source | Overhead per call | Calls/explore | Total | % |
|--------|-------------------|---------------|-------|---|
| findCandidates hook (Model B) | ~0.2µs | 53 | 10µs | 0.2% |
| provePersistent hook (Model B) | ~0.2µs | ~300 | 60µs | 1.1% |
| predict hook (Model B) | ~0.2µs | 415 | 83µs | 1.6% |
| Total | | | ~153µs | ~2.9% |

This is slightly over budget. Mitigation: prediction hook is only called when prediction is registered (the common case for "evm" profile is to have it compiled into the code path, same as today). The hook overhead vanishes when the function pointer IS the same function V8 already inlined.

**What creates real overhead is changing the function, not calling through a pointer.** V8's JIT specializes on the observed target. If `findCandidates` is always `fingerprintLookup`, V8 inlines through the pointer. The ~0.2µs is for the polymorphic case (V8 tracks 2-4 possible targets).

### 4.3 What To Avoid (will regress performance)

| Anti-pattern | Why | Impact |
|---|---|---|
| Hook array dispatch (`for (hook of hooks) hook()`) | Megamorphic IC | ~8% regression |
| Dual-mode State internally (FactSet vs plain object) | Hidden class polymorphism | 20-40% regression |
| Per-hook Arena/undo strategies | Correctness nightmare, cache misses | Undefined |
| Closures in innermost loop (new allocations) | GC pressure | ~5% regression |
| Conditional hook checks in tight loop (`if (hooks.length > 0)`) | Branch prediction | ~0.5% per check |

### 4.4 Validation Plan

**Two test suites:**

1. **Full suite** (`npm run test:all` / `CALC_PROFILE=bare npm run test:all`) — 2 minute timeout per test. Every test must pass with every profile, including bare. This is the correctness guarantee: the core without optimizations produces valid results.

2. **Pragmatic suite** (`npm run test:fast`) — default timeouts. Runs core unit tests + integration tests with appropriate profiles enabled (e.g., EVM tests run with `evm` profile for fingerprint+prediction). This is the development feedback loop.

After each extraction step:
```bash
# Correctness: bare profile, extended timeout
CALC_PROFILE=bare npm run test:all -- --timeout 120000

# Performance: evm profile, benchmark comparison
npm run bench:diff -- HEAD --suite=symexec --iterations=20
# Acceptance: regression < 2% (within stdev 0.7-0.9ms)

# Pragmatic: default profiles, normal timeout
npm run test:fast
```

V8 profiling if regression detected:
```bash
node --prof benchmarks/engine/multisig-bench.js
node --prof-process isolate-*.log > profile.txt
# Check: ticks in "stub"/"builtin" should remain < 10%
# Check: no megamorphic warnings in --trace-ic
```

---

## 5. Extensibility: Ownership, Graded Modalities, Proof Certificates

### 5.1 How Future Extensions Fit

The three major planned extensions are on **orthogonal axes** (from TODO_0064 §4):

```
                 Axis 1: Types
                (∀X, Π, dependent, QTT)
                        |
   Axis 2: Modes ────────+──── Axis 4: Forward/Backward
   (subexp, adjoint,    |     (lax monad, stages)
    MTDC, grades)       |
                        |
                    Axis 3: Fixed Points
                   (tabling, cyclic, muMALL)
```

| Feature | Axis | What it is | Where it lives in CALC |
|---------|------|------------|----------------------|
| Lax monad `{A}` | 4 | Polarity shift (bwd→fwd) | L3 mode-switch rule + sequent↔state bridge |
| Ownership `[P]A` | 2 | Principal indexing on formulas | Store hash + rule matching |
| Graded `[]_r A` | 2 | Quantity annotation on modalities | EqNeqSolver + constraint propagation |
| Proof certificates | — | Logging what `go()` does | Hook that records per-step evidence |

**They are fully orthogonal.** Ownership and grading don't change the mode-switching infrastructure. The Lax monad doesn't change how formulas are indexed. Certificates don't change execution, just record it.

### 5.2 Ownership Modality `[P]A`

**What it is:** `[Alice] resource(X)` means "Alice holds resource X." Principal-indexed formula wrapper. (See RES_0003 Authorization Logic, DEF_0018 Says Modality, TODO_0014 Multimodal Implementation.)

**What changes for CALC:**
1. **Parser:** Add `[P] A` syntax to `.calc` declarations. `P` is an object-level term (e.g., an address).
2. **Store:** `ownership(P, A)` is a compound term — content-addressed hash includes P. No Store changes needed (compound terms already work).
3. **Rule matching:** Rules check ownership: `[P] A * [P] B -o [P] C` ensures same principal. Unification handles this (P is a metavar bound in the rule).
4. **Forward engine:** Propagate ownership through state. Rules consume `[P] A` and produce `[P] B`. No engine change — formulas are just hashes.

**Impact on this refactor: NONE.** Ownership is a new connective in the calculus layer (`.calc` + `.rules` files). The engine doesn't know about ownership — it just sees hashes. The hook system is irrelevant. The mode-switching infrastructure is irrelevant. **Ownership is purely additive.**

**Estimated cost:** ~600 LOC (parser + calculus definition + tests). Independent of this TODO.

### 5.3 Graded Modality `[]_r A`

**What it is:** `[]_10 eth` means "10 units of eth resource." Grade `r` is an object-level term (e.g., `binlit(10n)`). (See RES_0074 QTT/Graded Types, RES_0022.)

**What changes for CALC:**
1. **Parser:** Add `[]_r A` syntax. `r` is an object-level term.
2. **Store:** `graded(r, A)` is a compound term. No Store changes.
3. **Rule matching:** Grade arithmetic via `plus`, `mult` predicates. Already works — these are persistent goals proved via FFI.
4. **Constraint solver:** EqNeqSolver (already integrated in symexec.js) handles grade constraints.

**Impact on this refactor: NONE.** Same reasoning as ownership — grades are formula-level, not engine-level. The hook system, mode switching, optimization extraction are all orthogonal.

**Estimated cost:** ~600 LOC (parser + rules + solver integration + tests). Independent of this TODO.

### 5.4 Why Adjoint Generalizes Cleanly

The 2-mode adjoint design (Decision 4) generalizes to N modes because the mode theory is a data structure, not hardcoded control flow:

```javascript
// Adding a mode: one entry in the modes object
modes.affine = { structural: { weakening: true, contraction: false } };

// Adding a shift: one entry in the shifts array
shifts.push({ from: 'affine', to: 'backward', connective: 'upshift_a_b' });
```

The mode-switching infrastructure (L3 calls forward engine, forward engine returns result) is parameterized by mode. It doesn't know about specific modes — just "which mode am I switching FROM and TO?" The context transfer (sequent→state, state→sequent) is generic.

**What would require rearchitecting:** If ownership or grades needed their own execution mode (e.g., "affine mode" with different matching rules). In that case, the forward engine would need per-mode matching strategies. The hook system supports this — a mode-specific `findCandidates` hook.

But based on existing research (RES_0074 §12, RES_0003), ownership and grades are formula-level annotations, not execution modes. They don't need separate matching — they're just terms that unification handles.

### 5.5 Proof Certificate Design-For Checklist

These properties must hold after the refactor to keep certificates easy:

- [ ] Every `go()` tree node records `rule` name (already true)
- [ ] Hook points receive `theta`, `consumed`, `produced` (must verify after extraction)
- [ ] `provePersistentGoals` can return evidence alongside success/failure (requires API change — add optional evidence array parameter)
- [ ] `mutateState` / `consumeLinear` / `produceLinear` are traceable (consumed/produced hashes available from undo log — Arena records them)
- [ ] Mode switch bridge (Phase 2) has a place for proof term return (design into the bridge API)

---

## 6. Refactor Plan (Phases 1-3)

### Phase 0: Assessment (this document) — DONE

- [x] Audit kernel + prover (clean: 9.5/10)
- [x] Audit engine code (dirty: ~45% optimization, severe entanglement)
- [x] Audit Lax monad gap (TODO_0006 documents well)
- [x] Research external architectures (RES_0077)
- [x] Performance analysis (Model A vs B, V8 IC behavior)
- [x] Extensibility analysis (ownership, graded, certificates)
- [x] Write this plan
- [x] User review and decisions

### Phase 1: Hook System + Optimization Extraction

**Goal:** Introduce `optimizer.js` with Model B dispatch. Refactor engine files to use hook points. Move optimizations to `opt/`. Profiles are **granular** — multiple profiles can coexist per calculus (e.g., ILL-EVM programs vs ILL-arithmetic programs), and each program invocation can select its profile. "bare" profile = naive fallbacks (theory-faithful, slow but correct).

**Approach:** Refactor in-place, one optimization at a time. After each extraction, tests pass and benchmark shows < 2% regression.

#### Phase 1.0: Parameterize kernel.js copy rule

Before extracting engine optimizations, fix the one structural ILL assumption in the kernel:

- **Currently:** `kernel.js` hardcodes the `copy` rule with explicit linear/cartesian context handling (lines 50-77). Binary context names are implicit.
- **After:** Context structure (names, structural rules per zone) comes from the calculus object. `copy` becomes a parameterized structural rule, not a special case. ~40 LOC.
- **Why now:** Phase 1 extractions will establish the hook pattern. Clean kernel boundaries make it clear what's "core theory" vs "optimization." Also unblocks Phase 3 (multi-logic) without a later kernel rewrite.

#### Phase 1.1: optimizer.js + profiles

Create `engine/optimizer.js`:
```javascript
// Profile = plain object describing which optimizations to enable.
// Profiles are granular: per-program, not per-calculus.
// A single calculus (e.g., ILL) can have multiple profiles
// for different program classes.

function createEngine(profile) {
  return {
    // Strategy / rule selection
    findCandidates: profile.fingerprint ? fpLookup : naiveScan,

    // Persistent proving — FFI mode is per-predicate configurable:
    //   'definitive' (current: FFI failure is terminal, fast)
    //   'advisory'   (FFI failure falls through to clause resolution)
    provePersistent: profile.ffi ? ffiFirst : clauseOnly,

    // Exploration hooks
    checkMemo: profile.structuralMemo ? memoCheck : null,
    predict: profile.prediction ? predictNext : null,
    prune: profile.solver ? solverCheck : null,
    drain: profile.loliDrain ? drainLolis : null,

    // State operations
    // (FactSet stays as core — it provides Arena undo, which is core DFS infrastructure)
  };
}

// Built-in profiles. Users can define custom profiles or compose from these.
const profiles = {
  bare: {},  // all hooks null → naive fallbacks. Theory-faithful core.
  fast: { ffi: true },  // FFI only — good baseline for any ILL program.
  evm:  { ffi: true, fingerprint: true, discTree: true, prediction: true,
           structuralMemo: true, solver: true, loliDrain: true,
           compiledPersistent: true, deltaBypass: true },
};

// Per-program profile selection:
//   mde.load('evm.ill', { profile: 'evm' })
//   mde.load('arith.ill', { profile: 'fast' })
//   mde.load('custom.ill', { profile: { ffi: true, solver: true } })
```

#### Phase 1.2: Migration order (cleanest first → hardest last)

**Step 1: FFI extraction** (EASY, ~50 LOC change)
- Currently: `ffi` imported directly in match.js, hardcoded `tryFFIDirect` call in `provePersistentGoals`
- After: `opt/ffi.js` exports a `provePersistent` hook. Default (no FFI) = clause-only resolution.
- Risk: LOW. FFI is already a self-contained module.

**Step 2: Disc-tree extraction** (EASY, ~30 LOC change)
- Currently: `disc-tree.js` is imported in match.js and strategy.js
- After: `opt/disc-tree.js` exports a `findCandidates` layer for `buildStrategyStack`.
- Risk: LOW. Already a self-contained strategy layer.

**Step 3: Fingerprint extraction** (MODERATE, ~100 LOC change)
- Currently: fingerprint config built in strategy.js, fingerprint index built in forward.js, fingerprint lookup in strategy.js, prediction metadata attached in strategy.js
- After: `opt/fingerprint.js` owns all fingerprint logic. Exports `findCandidates` layer.
- Risk: MODERATE. Entangled with prediction (step 6).

**Step 4: Compiled persistent steps** (MODERATE, ~80 LOC change)
- Currently: `compilePersistentStep` in match.js (lines 382-427), called in `matchAllLinear` Phase 2
- After: `opt/compiled-pers.js` provides compiled closures. `provePersistentGoals` hook decides whether to use them.
- Risk: MODERATE. V8 polymorphic IC concern if compiled closures have >4 shapes.

**Step 5: Delta bypass + preserved optimization** (EASY, ~40 LOC change)
- Currently: role-based `delta` check in `matchOnePattern`, `filterPreserved` in state-ops.js
- After: `opt/delta-bypass.js` provides optimized matching for delta-role patterns.
- Risk: LOW. Self-contained code paths.

**Step 6: Prediction (Opt_H)** (HARD, ~150 LOC change)
- Currently: `predictNext` function in symexec.js (lines 244-264), prediction fast-path in go() (lines 337-349), `attachPredictions` in strategy.js (lines 133-159), `nextPointerSlot` computed in compile.js
- After: `opt/prediction.js` owns prediction infrastructure. Exports `predict` hook for go().
- Risk: HIGH. Tightly coupled to fingerprint, compile.js, ffi/convert.js. Must be extracted AFTER fingerprint (step 3).
- V8 concern: prediction fast path must remain monomorphic. The hook pointer should resolve to the prediction function at engine creation, not be checked per-node.

**Step 7: Structural memoization** (HARD, ~80 LOC change)
- Currently: `computeControlHash` in symexec.js (lines 155-168), `globalControl` map + `boundCount` tracking in go() (lines 321-330, 474-479)
- After: `opt/structural-memo.js` exports `checkMemo` hook.
- Risk: HIGH. `boundCount` is shared between memo logic and the core DFS (it determines whether a subtree is fully explored). This coupling must be resolved carefully.

**Step 8: Constraint solver** (HARD, ~100 LOC change)
- Currently: `EqNeqSolver` imported in symexec.js, solver.checkpoint/restore/checkSAT woven throughout go() (lines 219-221, 367-398, 444-451)
- After: `opt/constraint.js` exports `prune` hook. Multi-alt SAT filtering becomes a hook callback.
- Risk: HIGH. Solver state is checkpointed/restored per DFS node — the undo protocol must be preserved exactly. The hook interface must support per-node checkpoint/restore lifecycle.

**Step 9: Persistent-loli drain** (MODERATE, ~40 LOC change)
- Currently: `drainPersistentLolis` in symexec.js (lines 103-126), called after every mutateState
- After: `opt/loli-drain.js` exports `drain` hook.
- Risk: MODERATE. Drain produces new persistent facts that feed the solver (lines 377, 456). This sequencing must be preserved.

#### Phase 1.3: "bare" profile validation

After all extractions, verify with the **hybrid test strategy**:

```bash
# 1. Full correctness: bare profile, 2 minute timeout per test
#    Every test must pass — this IS the core correctness guarantee.
CALC_PROFILE=bare npm run test:all -- --timeout 120000

# 2. Performance: evm profile, benchmark comparison
npm run bench:diff -- HEAD --suite=symexec --iterations=20
# "evm" profile should show < 2% regression vs pre-refactor

# 3. Pragmatic development suite: appropriate profiles, normal timeouts
#    Core unit tests + integration tests with profiles that make them fast.
#    EVM tests run with 'evm' profile, arithmetic tests with 'fast', etc.
npm run test:fast
```

The **bare** profile is the theoretical core: naive linear scan matching, clause-only persistent proving, no prediction, no memo, no solver, no drain. It's slow but demonstrates that the core is correct without any optimization.

The **pragmatic** suite (`test:fast`) is the daily driver. It maps test groups to profiles: EVM integration tests use `evm` profile, arithmetic tests use `fast`, core prover tests use `bare`. This keeps the development loop fast while the full bare suite catches optimization-dependent bugs in CI.

### Phase 2: Explicit Lax Monad as 2-Mode Adjoint (~500 LOC)

**Goal:** Implement TODO_0006 Option B with adjoint-ready design. When the backward prover encounters goal `{S}`, switch to forward mode.

**Depends on:** Phase 1 is recommended but not strictly blocking (see Phase 2.7 "Phase 1 dependency").

#### Phase 2.1: Mode theory infrastructure

Mode theory is data, not code. Consistent with D2.5:

```javascript
// lib/calculus/modes.js
const modeTheory = {
  modes: {
    backward: {
      structural: { weakening: true, contraction: true },
      stateType: 'sequent',       // Γ; Δ ⊢ C
      search: 'focused'           // L3 focused.js
    },
    forward: {
      structural: { weakening: false, contraction: false },
      stateType: 'multiset',      // { linear: FactSet, persistent: FactSet }
      search: 'committedChoice'   // forward.run()
    }
  },
  shifts: [
    {
      connective: 'monad',        // the Store tag that triggers the shift
      from: 'backward',           // source mode
      to: 'forward',              // target mode
      polarity: 'negative'        // negative → right-rule invertible (fires eagerly)
    }
  ]
};
```

#### Phase 2.2: Mode switch in L3

When the backward prover's inversion phase encounters a `monad(S)` succedent, `monad_r` fires (it is invertible because monad is negative). This triggers the mode switch:

```
Γ; Δ ⊢ {S}
1. findInvertible(seq) finds monad(S) as invertible right formula
2. monad_r fires — descriptor has modeShift field
3. rule-interpreter returns { type: 'modeSwitch', ... } instead of sub-goals
4. L3's applyAndRecurse detects modeSwitch, calls bridge.executeModeSwitch()
5. Bridge converts sequent → multiset state: Δ → linear FactSet, Γ → persistent FactSet
6. forward.run(state, calc.forwardRules, profile) until quiescence
7. Bridge returns result to L3; backward chaining continues
```

**Key bridge code** (TODO_0006 §4.2): sequent `{ contexts: { linear, cartesian }, succedent }` ↔ multiset state `{ linear: FactSet, persistent: FactSet }`.

**L3 code change** (~20 LOC in `applyAndRecurse`): After `applyRule()`, check if result contains a `modeSwitch` instead of premises. If so, call `bridge.executeModeSwitch()` instead of recursing into premises. The rest of L3 (findInvertible, chooseFocus, search) is unchanged — monad_r is just another invertible rule from L3's perspective.

#### Phase 2.3: Connective and rule registration

**`monad` tag already exists in Store.** The Pratt parser (`builders.js:182-188`) creates `monad(body)` for `{ body }` syntax after `-o`. The engine's `hasMonad()` (`convert.js:145-153`) classifies forward rules by detecting this tag. No Store changes needed.

**Parser scope:** Currently `{ }` only parses after `-o` (loli-in-monad). For Phase 2, extend the parser to allow standalone `{S}` as a succedent in queries: `#query init -o { target }`. This lets the backward prover encounter `monad(target)` as a goal and trigger the mode switch. ~10 LOC in `builders.js`.

**Polarity: NEGATIVE.** The monad's right rule is invertible (fires eagerly in inversion). Three independent confirmations:
1. CLF type grammar: `{S}` is **asynchronous** (= negative), alongside loli, with, top
2. Adjoint logic: `{A} = ↑(↓A)`, outer ↑ is negative → composite is negative
3. CALC's focusing discipline: contextFlow = `preserved` → negative (single premise receives full context)

**monad_r: structural rule generated from mode theory.** Like `copy` in `kernel.js`, monad_r is not a user-written rule in `.rules` files. It is generated programmatically from the mode theory's shift entry. The descriptor:

```javascript
monad_r: {
  connective: 'monad',
  side: 'r',
  arity: 1,
  invertible: true,             // negative connective → right-rule invertible
  contextFlow: 'preserved',     // linear context passes intact to forward engine
  modeShift: { from: 'backward', to: 'forward' }
}
```

The `modeShift` field distinguishes this from regular rules. When `rule-interpreter.js` sees `modeShift`, it returns a bridge call instead of sub-goals (see D2.5 Layer 3).

**monad_l: deferred.** The left elimination rule (`let {p} = e in E`) would decompose a monadic value in the linear context. It is NOT invertible (negative + left = requires focus). monad_l is needed only when programs produce monadic values as intermediate results in backward reasoning. This doesn't arise in current CALC programs. Deferred to Phase 3 or a separate TODO.

**Nested monads: forbidden.** CLF's type stratification forbids `{S}` inside synchronous types S (i.e., `{ A * { B } }` is ill-formed). The only way `{S}` enters the synchronous fragment is through `!{S}`. CALC's existing loli-in-monad pattern (`{ A * (trigger -o { B }) }`) is a different CLF extension (loli-in-monad, THY_0001), not nested monads — the loli is treated as an opaque linear fact at runtime.

**Subsumes:** TODO_0010 (Ceptre stages — backward chaining sequences forward phases via `phase1 -o {rules1}. phase2 -o {rules2}.`).

#### Phase 2.4: Proof certificate hook point

The mode switch bridge must return enough information for future certificates (consistent with D2.2):
```javascript
// Bridge returns (returnMode: 'trace'):
{
  state: finalState,        // forward engine's quiescent state (FactSet-based)
  quiescent: true|false,    // true = normal quiescence, false = bound/timeout
  trace: executionTrace     // sequence of rule firings (for future certificate extraction)
}
```

#### Phase 2.5: Resolved Design Decisions

Research references for this section: RES_0078 (shift rule integration), RES_0079 (forward-backward return types), RES_0080 (quiescence theory). See also RES_0052 (CLF lax monad deep study) §6-8, TODO_0006 §4.

**D2.1: Persistent context mapping — implicit (zone-based). DECIDED.**

All cartesian context facts become persistent when entering forward mode. No explicit `!` wrapper needed. This matches adjoint logic's approach: structural rules (weakening, contraction) come from the mode, not from a constructor. CALC's cartesian zone IS the persistence mode. CLF's explicit `!A` is equivalent but adds constructor overhead.

Future-proof: adjoint logic parameterizes structural rules by mode. Zone-based persistence maps cleanly: `cartesian zone = unrestricted mode`, `linear zone = linear mode`. Adding affine/relevant modes later = adding new zones with different structural rules, not changing the zone-based design.

**D2.2: Forward engine return types — parametric by query mode. DECIDED.**

Support all three return modes, selected per invocation:

| Query mode | Returns | Use case |
|---|---|---|
| `'state'` | Final state only | `#run`-style queries, production forward execution |
| `'trace'` | Final state + execution trace (rule sequence) | L3 mode switch bridge, future proof certificates |
| `'tree'` | Full execution tree (all branches) | `symexec.explore()` exhaustive exploration |

The forward engine internally tracks all information regardless. The `returnMode` parameter determines packaging.

Research backing: LolliMon returns success/failure + bindings only (= `'state'`). Celf returns full proof terms in `#query` (= `'trace'`) and just state in `#exec`/`#trace` (= `'state'`). CALC supports both plus the exhaustive tree that neither CLF system has.

```javascript
// API:
forward.run(state, rules, { returnMode: 'state' })   // → { state, quiescent }
forward.run(state, rules, { returnMode: 'trace' })    // → { state, quiescent, trace }
symexec.explore(state, rules, { ... })                 // → execution tree (always 'tree')

// L3 bridge:
bridge.runForward(state, rules, { returnMode: 'trace' })
// → { state, quiescent, trace } — trace enables future certificate extraction
```

**D2.3: Quiescence types — two for committed choice, tree types for explore. DECIDED.**

Committed choice (`run()` / L3 bridge):
- `{ type: 'quiescent', state }` — normal: no rules fire (true quiescence per CLF)
- `{ type: 'bound', state }` — step limit hit (practical approximation of non-termination)

Exhaustive (`explore()`): existing tree node types: `leaf`, `bound`, `cycle`, `dead`.

Research backing: CLF/LolliMon/Ceptre only define quiescence (no rules applicable). None have cycle detection or depth bounds — non-termination is simply possible. CALC's `bound` and `cycle` are practical extensions for exhaustive exploration (documented in THY_0001 §3). The committed choice mode inherits CLF's clean two-outcome model.

**D2.4: Profile selection — per-program at load time. DECIDED.**

Profile set at `mde.load()` time per program. No special handling for mode switch — the same profile applies whether the forward engine is called standalone or via L3 bridge. Each optimization knows what mode it helps in.

```javascript
const calc = mde.load('evm.ill', { profile: 'evm' });
// Same profile used by standalone explore() AND by L3 mode switch bridge
```

**D2.5: Shift rule integration — mode theory + descriptor dispatch. DECIDED (design below).**

This is the most architecturally significant decision. The design has four layers:

**Layer 1: Mode theory as data.** The calculus object carries a mode theory defining all modes, their structural rules, and shifts between them:

```javascript
// lib/calculus/modes.js
const modeTheory = {
  modes: {
    backward: {
      structural: { weakening: true, contraction: true },
      stateType: 'sequent',
      search: 'focused'           // L3 focused.js
    },
    forward: {
      structural: { weakening: false, contraction: false },
      stateType: 'multiset',
      search: 'committedChoice'   // forward.run()
    }
  },
  shifts: [
    {
      connective: 'monad',        // the connective that triggers the shift
      from: 'backward',           // source mode
      to: 'forward',              // target mode
      polarity: 'negative'        // negative → right-rule invertible (fires eagerly)
    }
  ]
};
```

**Layer 2: Shift as descriptor.** The monad's right rule is a regular descriptor with a `modeShift` field:

```javascript
// In ill.rules (or generated from mode theory):
monad_r: {
  connective: 'monad',
  side: 'r',
  arity: 1,
  invertible: true,              // negative connective → right-rule is invertible
  contextFlow: 'preserved',      // linear context passes intact to forward engine
  modeShift: { from: 'backward', to: 'forward' }
}
```

The focusing discipline handles WHEN the rule fires (inversion phase, since invertible). The `modeShift` field tells the rule interpreter WHAT to do (call the bridge instead of recursive backward search).

**Layer 3: Rule interpreter dispatch.** When `rule-interpreter.js` encounters a descriptor with `modeShift`, it generates a premise computation that calls the bridge:

```javascript
// In rule-interpreter.js:
if (descriptor.modeShift) {
  // Instead of generating sub-goals for backward search,
  // call the mode switch bridge
  return {
    type: 'modeSwitch',
    targetMode: descriptor.modeShift.to,
    succedent: extractSuccedent(goal, descriptor)
  };
}
```

**Layer 4: Bridge execution.** The bridge converts state representations and calls the target mode's search strategy:

```javascript
// In lib/prover/bridge.js (new file, ~100 LOC):
function executeModeSwitch(state, modeSwitch, calc) {
  const { targetMode, succedent } = modeSwitch;
  const mode = calc.modeTheory.modes[targetMode];

  // 1. Convert sequent → target mode's state representation
  const targetState = convertState(state, 'backward', targetMode, calc);

  // 2. Run target mode's search strategy
  const result = mode.search === 'committedChoice'
    ? forward.run(targetState, calc.forwardRules, calc)
    : /* future modes */ null;

  // 3. Optionally check succedent against final state (see D2.6b)
  if (succedent) checkSuccedent(result.state, succedent, calc);

  // 4. Convert result back to source mode's representation
  return convertResult(result, targetMode, 'backward', calc);
}
```

**Why this design (tradeoff analysis):**

| Option | Extensibility | Purity | Complexity | Chosen? |
|---|---|---|---|---|
| A: Hardcode in L3 | Poor — new case per shift | High — simple code | ~20 LOC | No |
| B: Descriptor + executionMode | Good — new descriptors | Medium — L3 stays generic | ~80 LOC | Basis |
| C: Full mode theory object | Best — modes are data | Highest — fully parametric | ~200 LOC | **Yes** |
| D: Shifts as derived rules | Good — reuses rule interpreter | Low — overloads "premise" | ~100 LOC | No |

Option C chosen because: (1) aligns with adjoint logic theory where modes and shifts are first-class, (2) adding new modes (affine, relevant, ownership) = adding entries to data, not new code paths, (3) the conversion functions are explicit and testable, (4) maps cleanly to Zig (mode theory = struct, shifts = array of structs).

**Polarity justification (three independent sources):**
1. **CLF grammar:** `{S}` is asynchronous (= negative), alongside loli, with, top (Watkins et al. 2004)
2. **Adjoint logic:** `{A} = ↑(↓A)`, outer ↑ is negative → composite is negative (Pruiksma et al. 2018)
3. **CALC focusing.js:** contextFlow `preserved` → negative polarity; negative + right = invertible

**Research backing:** Adjoint logic treats shifts as regular connectives with standard polarity: ↑ is negative (right-rule invertible), ↓ is positive (right-rule requires focus). The monad `{A} = ↑(↓A)` is a composed shift. In CALC, this means `monad_r` is invertible (fires eagerly in inversion phase) — exactly matching L3's existing inversion phase. See RES_0078 for how Celf hardcodes this in `solve` via pattern match on `TMonad S`, how LolliMon hardcodes it via `Const "{}"`, and how Ceptre uses a hybrid (user-defined stage transition rules + hardcoded quiescence detection). CALC's descriptor + mode theory approach is cleaner than any of these implementations.

**Concrete example — how a new mode would be added later:**

```javascript
// 1. Add mode to theory
calc.modeTheory.modes.affine = {
  structural: { weakening: true, contraction: false },
  stateType: 'multiset',
  search: 'committedChoice'  // or 'focused' with affine structural rules
};

// 2. Add shift connective
calc.modeTheory.shifts.push({
  connective: 'affine_monad', from: 'backward', to: 'affine', polarity: 'negative'
});

// 3. Add descriptor (in .rules file or programmatically)
// affine_monad_r: { connective: 'affine_monad', side: 'r', arity: 1,
//   invertible: true, modeShift: { from: 'backward', to: 'affine' } }

// 4. Add conversion function
// convertState('backward', 'affine', ...) — like backward→forward but allows weakening
```

No new code paths in L3 or rule interpreter — just data.

**D2.6: Sequent ↔ State bridge — parametric. DECIDED.**

**(a) Multiplicities: FactSet counts are correct. No change needed.**

The linear context Δ in sequent calculus IS a multiset — the same formula can appear multiple times. CALC's FactSet `{hash: count}` model handles this correctly. Celf tracks individual occurrences by position; CALC tracks by hash + count. Both are semantically equivalent for ground formulas, and CALC's forward engine only works with ground facts.

**(b) Succedent: parametric — checked or unchecked. DECIDED.**

Support both modes, selected per invocation:

| Mode | What happens to S | Use case |
|---|---|---|
| `succedent: S` | After quiescence, check final state matches S (Celf `rightFocus`-style decomposition) | Theory-mode queries, mixed backward/forward programs |
| `succedent: null` | Run to quiescence, return raw final state | EVM-style programs, symexec, Ceptre-style undirected execution |

Research backing: In Celf, the succedent S is passed to `forwardChain` and checked via `rightFocus` after quiescence. `rightFocus` decomposes the synchronous type S against the final state: tensor splits the state multiplicatively, `1` requires empty linear state, `!A` checks persistent context, `exists x.S'` finds a witness. If the check fails, L3 backtracks. In `#exec`/`#trace` mode, Celf skips the check. CALC supports both. See RES_0079 for Celf source code analysis.

When `succedent` is provided, the check is:
```javascript
// Decompose S against final state (rightFocus analog):
// S = A * B → split state: some facts match A, rest match B
// S = 1     → linear state must be empty
// S = !A    → A must be in persistent state
// S = ∃x.S' → find witness x in state, recurse with S'[x]
```

**(c) Reverse direction: parametric — raw state or decomposed. DECIDED.**

Support both, matching (b):

| When succedent = null | Return raw `{ linear: FactSet, persistent: FactSet }` |
|---|---|
| When succedent = S | Decompose via rightFocus: return the remaining context after S is matched, as sequent terms for L3 to continue |

Implementation phasing: Start with `succedent: null` (return raw state). Add rightFocus decomposition when mixed backward/forward programs are needed. The bridge API supports both from day one — the decomposition is just initially unimplemented and returns an error if called.

**D2.7: Loli drain at quiescence — yes, always drain. DECIDED.**

Lolis that CAN fire MUST fire before declaring quiescence. The state is not quiescent if there's a dormant loli whose guard is provable. CALC's existing `drainPersistentLolis` handles this correctly.

Dormant lolis that CANNOT fire (guard unprovable) are valid residual resources — they stay in the final state as unconsumed capabilities. This is sound: a loli `!G -o B` where G is not provable is simply an unused capability, like a coupon you never redeemed.

Research backing: CLF forbids lolis inside the monad entirely, so this question doesn't arise in standard theory. CALC's extension (loli-in-monad, THY_0001 §1.2) requires the drain mechanism for correct quiescence. From the CHR perspective, CALC's drain is analogous to exhaustive propagation before declaring saturation. See RES_0080 for full analysis.

Implementation: The L3 bridge calls `forward.run()`, which already uses `drainPersistentLolis` in its main loop. No additional work needed.

#### Phase 2.6: Important distinctions for implementation

**Modes ≠ principals/users.** Modes are finite, static categories of structural behavior (linear, affine, unrestricted). Principals/users are first-order terms — quantified over, dynamic, unbounded. In CALC, Ethereum addresses (uint160) are terms, not modes. Ownership `[P] resource(X)` uses principal P as a term variable in formulas; rules quantify universally over P. This scales to 2^160 addresses. See §5.2 (ownership modality) — it's formula-level, orthogonal to modes.

**`!eq(X,Y)` as proposition vs substitution.** Persistent equality facts stay in state as propositions (not converted to substitutions) because: (1) they serve as path conditions readable in execution traces, (2) other rules pattern-match on them (e.g., `contra/eq_neq`), (3) the EqNeqSolver already tracks them as constraints via union-find for O(α(n)) queries, (4) rewriting all state hashes on every equality would be expensive. The solver IS the global substitution mechanism — it just doesn't rewrite state. The redundancy (fact in state + equation in solver) is intentional: state for rule matching, solver for constraint propagation.

#### Phase 2.7: Implementation details

This section captures concrete implementation knowledge needed for Phase 2 coding.

**Entry point: how does the backward prover encounter `{S}`?**

Two paths:

1. **Query-driven.** `#query init -o { target }` in a .ill file. The parser creates `loli(init, monad(target))`. The backward prover decomposes loli (loli_r), gets `monad(target)` as the succedent goal. `findInvertible(seq)` finds `monad(target)` on the right (invertible because negative). monad_r fires, triggering mode switch.

2. **Programmatic.** `prover.prove(sequent)` where sequent has `monad(S)` as succedent. Same path as above but constructed in code.

Note: `convert.js` sends queries to the `queries` map (line 209: `if (hasMonad(bodyHash))` classifies as forward rule), not to `forwardRules`. A query `#query init -o { target }` would correctly NOT be classified as a forward rule — it is a backward-mode query whose goal happens to contain `{S}`.

**convertState preconditions.**

When monad_r fires, the linear context should contain only **ground atomic facts** (predicates and atoms). This is guaranteed by the focusing discipline: before monad_r fires (in the inversion phase), all invertible left formulas have already been decomposed. After inversion, the linear context contains only atoms and focused (non-invertible) formulas. Focused formulas are negative connectives on the left — but `{S}` on the right fires before any left focus, so the context is fully inverted.

The conversion `convertState(sequent, 'backward', 'forward')` maps:
- `seq.contexts.linear` (array of ground atom hashes) → `State.linear` FactSet
- `seq.contexts.cartesian` (array of ground atom hashes) → `State.persistent` FactSet

**Which forward rules fire.**

Only `calc.forwardRules` (compiled by `mde.load()`) fire during forward mode. These are rules whose consequent contains `monad(...)`. Backward-only rules (`calc.clauses`) are used by `prove.js` for persistent goal resolution during forward execution — they are not forward rules.

**monad_r is a structural rule.**

Like `copy` in `kernel.js` (lines 50-77), monad_r is **not** defined in `.rules` files. It is generated programmatically from the mode theory's shift entry. The generation happens at calculus load time:

```javascript
// In modes.js or rule-interpreter.js:
for (const shift of modeTheory.shifts) {
  const rName = `${shift.connective}_r`;
  ruleSpecs[rName] = {
    connective: shift.connective,
    side: 'r',
    arity: 1,
    invertible: true,
    contextFlow: 'preserved',
    modeShift: shift,
    // makePremises returns a modeSwitch object, not sub-sequents
    makePremises: (formula, seq, idx) => ({
      type: 'modeSwitch',
      targetMode: shift.to,
      body: Store.child(formula, 0),  // unwrap monad(S) → S
      sequent: seq
    })
  };
}
```

**L3 code modification (~20 LOC).**

In `focused.js:applyAndRecurse` (line 101), after `applyRule()` returns, check for `modeSwitch`:

```javascript
const applyAndRecurse = (seq, rName, spec, position, index, state, searchFn, depth, delta) => {
  // NEW: check for mode switch before standard applyRule
  if (spec.modeShift) {
    const modeSwitch = spec.makePremises(
      position === 'R' ? seq.succedent : Seq.getContext(seq, 'linear')[index],
      seq, index
    );
    const result = bridge.executeModeSwitch(modeSwitch, calc);
    // ... wrap result as ProofTree node, return
  }

  // Existing code: standard rule application + recursion into premises
  const result = applyRule(seq, position, index, spec);
  // ...
};
```

The `bridge.executeModeSwitch()` call replaces the recursive `searchFn()` calls for premises. L3's inversion/focus/decomposition phases are completely unchanged.

**Phase 1 dependency.**

Phase 2 does NOT strictly depend on Phase 1 (hook system extraction). The bridge calls `forward.run()` directly, which works regardless of whether optimizations are extracted to `opt/`. Phase 1 makes Phase 2 cleaner (the bridge uses the same hook-point API as standalone forward execution), but is not blocking. For fast iteration, Phase 2 can start with the current engine and migrate to hook-point API later.

**Parser extension for standalone `{S}`.**

Currently `{ }` only parses after `-o` in `builders.js:182-188`. For Phase 2, extend the parser to support `{S}` as a standalone expression:

```javascript
// In parseAtom(), add before the default case:
if (src[pos] === '{') {
  pos++; ws();
  const body = parseExpr(0);
  ws(); consume('}');
  return Store.put('monad', [body]);
}
```

This enables: `#query init -o { target }` (already works, loli handles it) and `#query { target }` (new, direct monadic goal).

#### Phase 2.8: Test plan

**Unit tests (~15 tests):**

1. Mode theory construction and validation
2. monad_r descriptor generation from shift entry
3. `findInvertible(seq)` finds `monad(S)` on the right
4. `convertState` sequent → multiset (correct linear/persistent mapping)
5. `convertState` multiset → sequent (reverse direction, for result return)
6. Parser: standalone `{S}` expression
7. Parser: `A -o {S}` (existing behavior preserved)

**Integration tests (~10 tests):**

8. Simple backward→forward: `#query a -o { b }` where a forward rule converts `a` to `b`
9. Quiescence detection: forward engine stops when no rules fire
10. Bound detection: forward engine hits step limit
11. Persistent context: cartesian facts available as persistent during forward mode
12. Multiple forward rules: correct committed-choice selection
13. Profile independence: same result with 'bare' and 'evm' profiles
14. Return modes: 'state' vs 'trace' produce correct shapes
15. Succedent check: when `succedent: S` provided, verify final state matches S

**Regression tests:**

16. All existing `npm run test:all` still pass (monad_r doesn't interfere with existing backward proofs)
17. All existing `npm run test:engine` still pass (forward engine unchanged)
18. `npm run bench:diff -- HEAD --suite=symexec` shows < 2% regression

---

### Phase 3: Multi-Logic Support (~200 LOC)

**Goal:** Multiple calculus objects coexist. Each `.calc` + `.rules` file produces an independent calculus.

**Depends on:** Phase 1 (clean separation means calculus-specific code is in opt/, not core).

**Current blockers:**
- Tag namespace is global (pre-registered tags 0-25, dynamic tags 26+)
- Forward engine imports from calculus-specific files (e.g., `ffi/arithmetic.js`)

**Fixes:**
- Store remains global (content-addressing benefits from sharing)
- Tag registry becomes per-calculus or namespaced (`ill:tensor`, `cll:tensor`)
- Calculus object carries all logic-specific data (already mostly true — `calc.forwardRules`, `calc.clauses`, `calc.types`)
- FFI bindings are per-calculus (already true — `calc.ffi` object)

---

## 7. Optimization Migration Table

| # | Optimization | Current Location | Target Module | Hook Point | Difficulty | V8 Risk |
|---|---|---|---|---|---|---|
| 0 | Copy rule parameterization | kernel.js:50-77 | kernel.js (in-place) | N/A (structural fix) | EASY | NONE |
| 1 | FFI arithmetic | ffi/* + match.js:267-279 | opt/ffi.js | provePersistent | EASY | LOW |
| 2 | Disc-tree | disc-tree.js + strategy.js | opt/disc-tree.js | findCandidates | EASY | LOW |
| 3 | Fingerprint indexing | strategy.js:94-121 + forward.js | opt/fingerprint.js | findCandidates | MODERATE | LOW |
| 4 | Compiled persistent steps | match.js:382-427 | opt/compiled-pers.js | provePersistent | MODERATE | MEDIUM |
| 5 | Delta bypass | match.js:~460-480 | opt/delta-bypass.js | matchOnePattern | EASY | LOW |
| 6 | Preserved optimization | state-ops.js:67-92 | opt/preserved.js | produceLinear | EASY | LOW |
| 7 | Compiled substitution | substitute.js + state-ops.js:84-89 | opt/compiled-sub.js | applySubstitution | EASY | LOW |
| 8 | Fingerprint prediction (Opt_H) | symexec.js:244-264 + strategy.js:133-159 | opt/prediction.js | predict | HARD | MEDIUM |
| 9 | Structural memoization | symexec.js:155-168, 321-330, 474-479 | opt/structural-memo.js | checkMemo | HARD | LOW |
| 10 | EqNeq constraint solver | constraint.js + symexec.js:219-221, 367-398, 444-451 | opt/constraint.js | prune | HARD | LOW |
| 11 | Persistent-loli drain | symexec.js:103-126 | opt/loli-drain.js | drain | MODERATE | LOW |

**Migration order:** 0 (copy rule) → 1 → 2 → 5 → 6 → 7 → 3 → 4 → 11 → 9 → 8 → 10

---

## 8. Success Criteria

1. `CALC_PROFILE=bare npm run test:all -- --timeout 120000` passes (no optimizations, 2m timeout, correct)
2. `npm run test:all` passes with "evm" profile (same speed as today, < 2% regression)
3. `npm run test:fast` exists — pragmatic suite with per-test-group profile mapping
4. Each optimization can be toggled independently via profiles
5. Profiles are **granular** — per-program, not just per-calculus (e.g., ILL-EVM vs ILL-arith)
6. Core engine (minus opt/) is readable — hook points are small and clear
7. `kernel.js` copy rule is parameterized — context structure comes from calculus object
8. Hook signatures are Zig-portable — explicit context params, no closures, no `this`
9. FFI failure mode is configurable per-predicate (definitive vs advisory)
10. Backward prover can invoke forward engine via `{S}` goal (Phase 2, 2-mode adjoint)
11. `{A}` design generalizes to N modes without rearchitecting (mode theory object)
12. A second calculus can be loaded alongside ILL (Phase 3)
13. Proof certificate hook points exist (though certificates themselves are deferred)
14. No optimization notes found during refactoring are lost (captured in optimization TODOs)

---

## 9. Non-Goals

- **Zig port (implementation).** JS-level refactor. But Zig portability IS a design constraint on hook signatures — patterns must map cleanly to Zig function pointers.
- **New optimizations.** Organizing existing ones only. New ideas → optimization TODOs.
- **Breaking API changes.** External API (`mde.load`, `symexec.explore`) stays the same.
- **Proof certificates (implementation).** Deferred. Design-for only. See §5.5.
- **Full adjoint logic.** Only 2-mode (backward/forward). N-mode generalization is Phase 3+ / TODO_0012.
- **Ownership / graded modalities.** Orthogonal. Not blocked by this refactor. See §5.2-5.3.

---

## 10. Context Recovery Guide

If context is cleared, read these files to rebuild understanding:

### Architecture
- `doc/documentation/architecture.md` — Prover lasagne (L0-L5), file structure
- `doc/documentation/forward-optimization-roadmap.md` — All 16 optimization stages, key learnings, performance profile, disproven optimizations

### Theory
- `doc/theory/0001_exhaustive-forward-chaining.md` — CALC's three CLF extensions, execution tree judgment
- `doc/todo/0006_lax-monad-integration.md` — Lax monad deep analysis, three implementation options, operational semantics
- `doc/research/0052_clf-lax-monad-deep-study.md` — CLF monad theory, Curry-Howard, adjunction

### External Research
- `doc/research/0077_modular-proof-kernel-architectures.md` — LCF, FPC, Dedukti, Ceptre, Metamath Zero architectures. Eight named patterns.
- `doc/research/0078_mode-switch-shift-focused-proof-search.md` — How Celf/LolliMon/Ceptre implement mode switching. Source code analysis.
- `doc/research/0079_clf-forward-backward-return-value.md` — What forward engines return to backward provers. CLF proof terms, Celf `Let'` constructors.
- `doc/research/0080_quiescence-forward-chaining-linear-logic.md` — Quiescence vs saturation. Loli drain semantics. CHR comparison.

### Code (engine hot path)
- `lib/engine/symexec.js` — DFS exploration. `go()` is the hot loop (lines 310-482). All optimization entanglement here.
- `lib/engine/match.js` — Pattern matching. `provePersistentGoals` (lines 261-337) and `matchOnePattern` (lines 454-561) are the key entanglement points.
- `lib/engine/strategy.js` — Rule selection. `buildStrategyStack` (lines 94-121), `detectStrategy` (lines 171-182), `findAllMatches` (lines 251-271).
- `lib/engine/forward.js` — Committed choice main loop. `run()` IS the monadic computation.
- `lib/engine/fact-set.js` — FactSet + Arena + State. Core DFS infrastructure.
- `lib/engine/state-ops.js` — `consumeLinear`, `produceLinear`, `producePersistent`.
- `lib/engine/compile.js` — Rule compilation (de Bruijn slots, metavar analysis, consequent precomputation).

### Related TODOs
- TODO_0006 — Lax monad {A} integration (deep analysis, three options)
- TODO_0008 — Proof certificates / metaproofs
- TODO_0010 — Ceptre stages (subsumed by Phase 2)
- TODO_0012 — MTDC / multi-type display calculus (future adjoint generalization)
- TODO_0014 — Multimodal implementation (ownership, authorization)
- TODO_0045 — Execution tree judgment formalization
- TODO_0058 — Symexec optimization history (done, but useful for performance context)
- TODO_0064 — Higher-order extensions overview (four axes, phased roadmap)

### Memory
- `/home/mhhf/.claude/projects/-home-mhhf-src-calc/memory/MEMORY.md` — Session-persistent notes on architecture, modules, key patterns
- `/home/mhhf/.claude/projects/-home-mhhf-src-calc/memory/higher-order-survey.md` — Higher-order extensions survey notes

---

## 11. References

### CALC Internal
- TODO_0006 — Lax Monad {A} integration
- TODO_0064 — Higher-Order Extensions Overview
- THY_0001 — Exhaustive Forward Chaining theory
- RES_0008 — CLF/Celf/Ceptre research
- RES_0035 — Prover architecture (LCF model)
- RES_0052 — CLF Lax Monad deep study (§6 adjunction, §8 CALC's extensions)
- RES_0074 — QTT, Graded Types, Adjoint Logic, MTDC
- RES_0077 — Modular Proof Kernel Architectures (LCF, FPC, Dedukti, Ceptre, Metamath Zero)
- RES_0078 — Mode-switch shift rule integration in focused provers (Celf/LolliMon/Ceptre source analysis)
- RES_0079 — CLF forward-backward return value (what forward returns to backward, proof terms)
- RES_0080 — Quiescence in forward-chaining linear logic (quiescence vs saturation, loli drain)

### Key External
- Watkins et al. (2004) — CLF: Dependent Logical Framework
- Lopez et al. (2005) — LolliMon: forward+backward via Lax monad
- Pruiksma et al. (2018) — Adjoint Logic (mode preorder, shifts)
- Pruiksma (2024) — Adjoint Logic with Applications (PhD thesis, CMU-CS-24-103)
- Miller (2013) — Foundational Proof Certificates (clerk/expert)
- Harrison (2009) — HOL Light kernel (~400 LOC, LCF model)
- Digama (2019) — Metamath Zero (spec/proof separation)
- Simmons & Pfenning (2009) — Linear Logical Approximations (quiescence vs saturation)
- Betz & Frühwirth (2013) — CHR with Disjunction (soundness for additives in forward chaining)

### Relationship to Existing TODOs

| TODO | Relationship |
|------|-------------|
| **0006** | Phase 2 implements Option B (2-mode adjoint). This TODO provides architectural foundation. |
| **0008** | Proof certificates designed-for (§5.5). Easier to implement after clean core. |
| **0010** | Subsumed by Phase 2 — monad sequences forward phases. |
| **0012** | Phase 3 multi-logic enables MTDC. Adjoint generalization (Phase 2 design) supports N modes. |
| **0014** | Orthogonal — ownership modalities are formula-level, not engine-level (§5.2). |
| **0045** | Execution tree judgment. Certificate design-for (§5.5) connects to this. |
| **0064** | This refactor is the foundation for all higher-order extensions. |

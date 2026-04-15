---
title: "matchOpts Reference — Engine Configuration Object"
created: 2026-04-14
modified: 2026-04-14
summary: Complete reference for the matchOpts callback composition object that configures forward engine behavior.
tags: [architecture, forward-chaining, implementation, engine]
---

# matchOpts Reference

`matchOpts` is the configuration object that parameterizes the forward engine's matching, persistent proving, and dynamic rule handling. It is assembled once at run start via `match.buildMatchOpts()` — no module-level mutable state.

## Assembly

Both `forward.run()` and `explore.explore()` construct matchOpts via:

```js
const matchOpts = match.buildMatchOpts({
  useFFI, evidence, rc, ffiCtx, canonicalize,
  onProveFail, onProveSuccess, backchainUseFFI, optimizePreserved,
});
```

`buildMatchOpts` (in `match.js`) maps these inputs to the full field set, including wiring `provePersistent` to either the FFI-accelerated or naive pipeline.

## Fields

### Core Callbacks

| Field | Type | Set by | Used by |
|---|---|---|---|
| `provePersistent` | `(patterns, startIdx, theta, slots, state, calc, evidenceOut, matchOpts) → idx` | `buildMatchOpts` | `match.js`, `lnl/existential.js`, `lnl/loli.js` |
| `matchDynamicRule` | `(factHash, state, calc, matchOpts) → match \| null` | `buildMatchOpts` (→ `matchLoli`) | `strategy.js` (loli scan) |
| `dynamicRuleTag` | `string \| null` | `buildMatchOpts` (→ `rc.implication`) | `strategy.js` (filter state for loli candidates) |

`provePersistent` is the most critical callback. With FFI enabled, it wires to `opt/ffi.js:provePersistent` (state → FFI → compiled clause → full clause pipeline). Without FFI, it wires to `lnl/persistent.js:proveNaive` (state → clause resolution only).

### Connective Resolution

| Field | Type | Set by | Used by |
|---|---|---|---|
| `connectives` | `Object` (resolved roles: `{ product, implication, exponential, computation, ... }`) | `buildMatchOpts` (from `rc`) | `lnl/loli.js`, `compile.js` |

The resolved connective table maps structural roles to tag names. Created once via `compile.js:resolveConnectives(ct)` from the connective table in `ill/connectives.js`.

### FFI Configuration

| Field | Type | Set by | Used by |
|---|---|---|---|
| `ffiParsedModes` | `Object \| null` (`{ pred: ['+','-',...] }`) | `buildMatchOpts` (from `ffiCtx`) | `lnl/persistent.js`, `opt/ffi.js` |
| `ffiMeta` | `Object \| null` | `buildMatchOpts` (from `ffiCtx`) | `opt/ffi.js` |
| `ffiGet` | `Function \| null` | `buildMatchOpts` (from `ffiCtx`) | `opt/ffi.js` |
| `ffiIsGround` | `Function \| null` | `buildMatchOpts` (from `ffiCtx`) | `opt/ffi.js` |
| `useCompiledSteps` | `boolean` | `buildMatchOpts` (= `useFFI`) | `match.js`, `lnl/existential.js` |
| `backchainUseFFI` | `boolean` | `buildMatchOpts` | `lnl/persistent.js` |

When `ffiCtx` is null (bare profile or non-ILL calculus), all FFI fields are null and the engine falls back to clause resolution everywhere.

### Optimization Flags

| Field | Type | Set by | Used by |
|---|---|---|---|
| `optimizePreserved` | `boolean` | `buildMatchOpts` | `match.js` (skip re-producing preserved facts) |
| `canonicalize` | `Function \| null` (`hash → hash`) | `buildMatchOpts` | `lnl/persistent.js`, `opt/ffi.js` (equational theory normalization) |

### Instrumentation Hooks

| Field | Type | Set by | Used by |
|---|---|---|---|
| `evidence` | `boolean` | `buildMatchOpts` | `match.js`, `lnl/loli.js`, `lnl/existential.js` |
| `onProveSuccess` | `Function \| null` | `buildMatchOpts` | `lnl/persistent.js`, `opt/ffi.js` |
| `onProveFail` | `Function \| null` | `buildMatchOpts` | `lnl/persistent.js`, `opt/ffi.js` |

When hooks are set, the compiled persistent step fast path and compiled existential chain are bypassed to ensure all goals are observable.

## Profile Impact

| Profile | useFFI | evidence | optimizePreserved | Notes |
|---|---|---|---|---|
| `bare` | false | false | false | Clause resolution only, no optimizations |
| `fast` | true | false | true | FFI + preserved skip |
| `evm` | true | false | true | All optimizations |
| guided | true | true | true | Evidence collection, compiled fast paths bypassed |

## Not in matchOpts

These engine behaviors are configured elsewhere:
- **Strategy stack** — built by `optimizer.js:createEngine()`, passed separately to `strategy.findMatch()`
- **Solver** — `EqNeqSolver` created per `explore()` call, used directly in the DFS loop
- **Structural memo** — `createMemoCtx()` in `explore()`, used directly in `go()`
- **Prediction** — `createPredictNext()` in `explore()`, closure over strategy state
- **Loli drain** — called directly from `explore()` DFS loop

## Key Files

| File | Role |
|---|---|
| `lib/engine/match.js:buildMatchOpts` | Factory — assembles matchOpts from inputs |
| `lib/engine/forward.js` | Caller — constructs matchOpts for committed-choice |
| `lib/engine/explore.js` | Caller — constructs matchOpts for exhaustive DFS |
| `lib/engine/opt/ffi.js` | Consumer — reads FFI fields for accelerated proving |
| `lib/engine/lnl/persistent.js` | Consumer — reads canonicalize, modes, hooks |

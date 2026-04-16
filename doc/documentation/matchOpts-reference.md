---
title: "matchOpts Reference — Engine Configuration Object"
created: 2026-04-14
modified: 2026-04-16
summary: Complete reference for the matchOpts callback composition object that configures forward engine behavior.
tags: [architecture, forward-chaining, implementation, engine, layering]
---

# matchOpts Reference

`matchOpts` is the frozen callback bag (20 fields) that parameterizes the forward engine's matching, persistent proving, and dynamic rule handling. It serves as the **dependency inversion mechanism** — inner layers (generic) define interface contracts, outer layers (lnl, opt, ffi) provide implementations, the composition root (`index.js`) wires them.

## Assembly

Each layer exports a protocol factory (`buildGenericProtocol`, `buildLnlProtocol`, `buildOptProtocol`, `buildFfiProtocol`, `buildProofProtocol`) returning its field contributions. The composition root (`index.js:_buildMatchOpts`) spreads them flat and freezes:

```js
// index.js — composition root (ML functor analogy: spread = include)
function _buildMatchOpts(execOpts) {
  const useFFI = execOpts.dangerouslyUseFFI || false;
  return match.buildMatchOpts({
    ...match.buildGenericProtocol({ optimizePreserved, evidence, ... }),
    ...match.buildLnlProtocol({ matchLoli, resolveEx, drainLolis, rc, ... }),
    ...match.buildOptProtocol({ execPS, execExStep, tryCCDispatch, ... }),
    ...match.buildFfiProtocol(ffiContext),
    ...match.buildProofProtocol({ useFFI, proveWithFFI, proveNaive }),
  });
}
```

`buildMatchOpts` freezes the object (`Object.freeze`) — all matchOpts instances are read-only with identical shape (V8 monomorphic hidden class). `EMPTY_MATCH_OPTS` provides a minimal same-shape object for direct callers (tests, benchmarks).

## Canonical Empty Default Invariant

`EMPTY_MATCH_OPTS` is the **canonical empty default** for matchOpts — the full 20-field frozen record with every callback null and every flag at its factory default. It is a no-op baseline: shape-identical to populated instances (preserving V8 monomorphic IC), but semantically inert (no FFI, no compiled dispatch, no hooks). Consumer code may assume matchOpts is always present: entry functions (`tryMatch`, `findMatch`, `findAllMatches`, `proveNaive`, `proveWithFFI`, `resolveEx`, `matchLoli`, `drainLolis`) declare `matchOpts = EMPTY_MATCH_OPTS` as a default parameter. This eliminates ~20 defensive `matchOpts && matchOpts.foo` guards throughout consumer code — field access is direct and V8 IC-friendly.

Note: this is not a mathematical monoid identity — there is no binary combining operation on matchOpts. It is simply the distinguished empty record that fills the default-parameter slot.

Consequence: if you need a factory default (e.g. `backchainUseFFI` = `true`), encode it in the factory, not in a consumer-side `!== undefined ? ... : default` fallback. The factory is the single source of truth for defaults. `backchainUseFFI = true` in `buildLnlProtocol` is a pragmatic adversarial-soundness default (FFI enabled unless the caller explicitly opts out via `dangerouslyUseFFI: false`), not a platonic property of the empty record.

Layer ownership is enforced by `tests/engine/layer-dag.test.js` at both the `require()` level and the matchOpts field-access level.

## Fields

### Core Callbacks

| Field | Type | Set by | Used by |
|---|---|---|---|
| `provePersistent` | `(patterns, startIdx, theta, slots, state, calc, evidenceOut, matchOpts) → idx` | `buildProofProtocol` | `match.js`, `lnl/existential.js`, `lnl/loli.js` |
| `matchDynamicRule` | `(factHash, state, calc, matchOpts) → match \| null` | `buildLnlProtocol` (→ `matchLoli`) | `strategy.js` (loli scan) |
| `dynamicRuleTag` | `string \| null` | `buildLnlProtocol` (→ `rc.implication`) | `strategy.js` (filter state for loli candidates) |

`provePersistent` is the most critical callback. With FFI enabled, it wires to `opt/ffi.js:provePersistent` (state → FFI → compiled clause → full clause pipeline). Without FFI, it wires to `lnl/persistent.js:proveNaive` (state → clause resolution only).

### Connective Resolution

| Field | Type | Set by | Used by |
|---|---|---|---|
| `connectives` | `Object` (resolved roles: `{ product, implication, exponential, computation, ... }`) | `buildLnlProtocol` (from `rc`) | `lnl/loli.js`, `compile.js` |

The resolved connective table maps structural roles to tag names. Created once via `compile.js:resolveConnectives(ct)` from the connective table in `ill/connectives.js`.

### FFI Configuration

| Field | Type | Set by | Used by |
|---|---|---|---|
| `ffiParsedModes` | `Object \| null` (`{ pred: ['+','-',...] }`) | `buildFfiProtocol` (from `ffiCtx`) | `lnl/persistent.js`, `opt/ffi.js` |
| `ffiMeta` | `Object \| null` | `buildFfiProtocol` (from `ffiCtx`) | `opt/ffi.js` |
| `ffiGet` | `Function \| null` | `buildFfiProtocol` (from `ffiCtx`) | `opt/ffi.js` |
| `ffiIsGround` | `Function \| null` | `buildFfiProtocol` (from `ffiCtx`) | `opt/ffi.js` |
| `useCompiledSteps` | `boolean` | `buildOptProtocol` (= `useFFI`) | `match.js`, `lnl/existential.js` |
| `backchainUseFFI` | `boolean` | `buildLnlProtocol` | `lnl/persistent.js` |

When `ffiCtx` is null (bare profile or non-ILL calculus), all FFI fields are null and the engine falls back to clause resolution everywhere.

### Optimization Flags

| Field | Type | Set by | Used by |
|---|---|---|---|
| `optimizePreserved` | `boolean` | `buildGenericProtocol` | `match.js` (skip re-producing preserved facts) |
| `canonicalize` | `Function \| null` (`hash → hash`) | `buildGenericProtocol` | `lnl/persistent.js`, `opt/ffi.js` (equational theory normalization) |

### Instrumentation Hooks

| Field | Type | Set by | Used by |
|---|---|---|---|
| `evidence` | `boolean` | `buildGenericProtocol` | `match.js`, `lnl/loli.js`, `lnl/existential.js` |
| `onProveSuccess` | `Function \| null` | `buildGenericProtocol` | `lnl/persistent.js`, `opt/ffi.js` |
| `onProveFail` | `Function \| null` | `buildGenericProtocol` | `lnl/persistent.js`, `opt/ffi.js` |

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
- **Strategy stack** — built by `optimizer.js:engine()`, passed separately to `strategy.findMatch()`
- **Solver** — `EqNeqSolver` created per `explore()` call, used directly in the DFS loop
- **Structural memo** — `createMemoCtx()` in `explore()`, used directly in `go()`
- **Prediction** — `createPredictNext()` in `explore()`, closure over strategy state
- **Loli drain** — called directly from `explore()` DFS loop

## Key Files

| File | Role |
|---|---|
| `lib/engine/match.js` | Protocol factories (`build*Protocol`) + `buildMatchOpts` (freeze) + `EMPTY_MATCH_OPTS` |
| `lib/engine/index.js` | Composition root — `_buildMatchOpts` wires all layer protocols |
| `lib/engine/forward.js` | Caller — receives matchOpts via `opts.matchOpts` |
| `lib/engine/explore.js` | Caller — receives matchOpts via `opts.matchOpts` |
| `lib/engine/opt/ffi.js` | Consumer — reads FFI fields for accelerated proving |
| `lib/engine/lnl/persistent.js` | Consumer — reads canonicalize, modes, hooks |
| `tests/engine/layer-dag.test.js` | Enforces field-access boundaries per layer |

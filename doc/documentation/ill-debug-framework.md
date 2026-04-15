---
title: ILL-Native Debug Framework
modified: 2026-04-10
summary: Observation directives and engine hooks for debugging ILL forward/backward execution.
tags: [debugging, engine, forward-chaining, hooks, ill, testing]
---

# ILL-Native Debug Framework

Observation directives and engine hooks for debugging ILL programs. Companion to the test framework (`ill-test-framework.md`).

## Two Tools, One Loader

| Tool | Purpose | Output |
|---|---|---|
| `test-ill.js` | Judgments (`#expect*`) | PASS/FAIL verdicts |
| `debug-ill.js` | Observations + verbose judgments | Information |

Both share `lib/engine/directive-loader.js` for file discovery, directive scanning, and program loading.

## Observation Directives

No separator (`|-`/`=>`), no expected outcome — pure information gathering.

```ill
#trace_name                        initial_state .
#dump_state_name                   initial_state .
#debug_name                        initial_state .
#benchmark_name (iterations: 10)   initial_state .
#compare_name (mode_a: ffi)        initial_state .
#inspect_name (label: evm)         I .

% Query references — reuse a named query's state instead of inlining:
#benchmark_name (query: other_query_name) (iterations: 10) I .
```

| Directive | Output |
|---|---|
| `#trace` | Step-by-step rule firings via `onStep` hook |
| `#dump_state` | Final state grouped by predicate |
| `#debug` | Per-leaf exploration analysis (leaf count, depth, classification) |
| `#benchmark` | Warmup + N iterations with min/mean/p50/max timing |
| `#compare` | Side-by-side mode comparison (e.g. FFI vs noFFI) |
| `#inspect` | Compiled rule metadata dump (linear/persistent counts, slots, alts) |

## Query References

The `(query: name)` setting lets an observation directive reuse another query's initial state instead of inlining it. The body (typically `I`) is ignored when `query` is set.

```ill
#import(../../programs/multisig.ill)

#benchmark_multisig (query: symex) (iterations: 10) (mode: explore) I .
#trace_multisig (query: symex) I .
#compare_multisig (query: symex) (mode_a: ffi) (mode_b: noffi) I .
```

Resolution: `calc.queries.get(settings.query)`. Throws with known query names on miss.

## Engine Hooks API

Opt-in callbacks on `exec()`/`explore()` — zero cost when not provided.

```js
// forward.run() — monotonic step counter
calc.exec(state, {
  onStep: ({ step, rule, consumed, theta, slots, state }) => { ... },
  onProveFail: (goal, reason) => { ... },
});
// explore() — DFS depth (separate field name, following Prolog convention)
calc.explore(state, {
  onStep: ({ depth, rule, consumed, theta, slots, state }) => { ... },
});
```

**`onStep`** fires after state mutation. `exec()` emits `{ step }` (monotonic 1-based counter). `explore()` emits `{ depth }` (DFS nesting level, 0-based). Separate field names follow the Prolog Byrd Box convention (invocation vs depth). `consumed` and `theta` are snapshots (`.slice()` / `{...spread}`). `state` is a live FactSet reference — inspect via `show.js` utilities, do not mutate.

**`onProveFail`** fires during persistent goal resolution (in `proveNaive`). Three failure reasons:
- `'cached_failure'` — backward cache recorded this goal as unprovable
- `'external_binding'` — clause resolution bound external freevars (unsound for forward)
- `'exhausted'` — all clauses tried, none succeeded

**Performance:** Same null-check pattern as the engine's `trace`/`evidence` flags. `const onStep = opts.onStep || null; if (onStep) onStep({...})`. When null, V8 branch prediction makes the check zero-cost.

## Usage

```bash
npm run debug:ill -- calculus/ill/tests/forward/debug-demo.ill
npm run debug:ill -- file.ill --only trace
npm run debug:ill -- file.ill --only judgment
npm run debug:ill -- calculus/ill/tests/forward/evm-multisig.ill --program calculus/ill/programs/multisig_nocall.ill
```

## Verbose Judgment Output

`debug-ill.js` also processes `#expect*` directives with enriched output:

| Directive | test-ill.js | debug-ill.js |
|---|---|---|
| `#expect |- A` | PASS/FAIL | Proof trace + θ |
| `#expect S => P` | PASS/FAIL | Execution steps + final state |
| `#expect_not S => P` | PASS/FAIL | All leaves shown, none match P |

## Shared Infrastructure (`directive-loader.js`)

Both tools import from `lib/engine/directive-loader.js` which provides:
- **Discovery**: `findIllFiles`, `scanDirectives`, `detectDuplicates`
- **Loading**: `loadProgram` (base program + overlay), constants (`PROGRAM`, `MAX_STEPS`, `MAX_DEPTH`)
- **Execution**: `resolveExecOpts(settings)` — parses `maxSteps`/`maxDepth`/`rules` from query settings into engine-compatible options
- **State**: `normalizeLeafState(leaf)` — FactSet→plain object, `decomposeQuery`, `stateHasFreevars`, `isSubset`
- **Display**: `show`, `classifyLeaf`, `showInteresting`, `groupByPredicate`, `formatState`
- **Backward**: `extractGoals`, `buildProveOpts`
- **Tree**: `getAllLeaves`, `countLeaves`, `maxDepth`, `countNodes`

## File Structure

```
lib/engine/directive-loader.js    # Shared: discovery, scanning, loading, utilities
tools/test-ill.js                 # Judgment runner (TODO_0143)
tools/debug-ill.js                # Observation runner + verbose judgments (TODO_0147)
tools/explore-inspect.js          # Interactive tree inspector (uses directive-loader re-exports)
calculus/ill/tests/forward/debug-demo.ill     # Demo file (EVM)
calculus/ill/tests/forward/evm-multisig.ill  # Multisig exploration (--program)
tests/engine/hooks.test.js                   # Hook API tests
```

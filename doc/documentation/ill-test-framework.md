---
title: ILL-Native Test Framework
modified: 2026-04-09
summary: Test directives as provability judgments — backward entailment and forward reachability.
tags: [testing, engine, forward-chaining, backward, ill, metalogic]
---

# ILL-Native Test Framework

Tests as provability judgments. No imperative machinery — the logic IS the framework.

Follows the Twelf `#query` / CLF `#trace` / Celf `#exec` tradition: test directives are metalogical judgments embedded in the object language. The runner is a thin dispatch layer — all test semantics live in the logic.

## Directive Syntax

```ill
#expect_<name> |- !goal .                    % backward: goal is provable
#expect_not_<name> |- !goal .                % backward: goal is NOT provable
#expect_<name> LHS => RHS .                  % forward: all paths reach RHS
#expect_not_<name> LHS => RHS .              % forward: no path reaches RHS
#expect_some_<name> LHS => RHS .             % forward: some path reaches RHS
#expect_<name> [X] |- !goal(X) .             % eigenvariable: for all X
#expect_<name> [X] LHS(X) => RHS .           % eigenvariable: symbolic execution
```

## Two Judgment Forms

**Backward entailment (`|-`)**: `|- !A` — A is derivable via backward proof search. The `!` (bang) marks the goal as persistent. `decomposeQuery` strips the bang and quantifiers; the inner goal is passed to `calc.prove()`.

**Forward reachability (`=>`)**: `S => P` — executing initial state S reaches a state containing P. Corresponds to `|- S -o {P * ⊤}` theoretically. Currently operational dispatch via `calc.exec()`/`calc.explore()`.

The pattern `P` on the RHS uses **subset matching** (P ⊆ final_state), which is the operational realization of **⊤-absorption**: in ILL, additive top (⊤) absorbs any multiplicative context. So `P * ⊤` holds iff P is present, regardless of what else remains. This lets tests assert on interesting facts (e.g., `stop`, `stack [0x2a]`) without mentioning the full final state (gas, bytecode, memory, etc.).

## Three Modalities

| Prefix | Quantifier | `|-` | `=>` |
|---|---|---|---|
| `expect_` | Universal | Provable | All paths match |
| `expect_not_` | Negation | Not provable | No path matches |
| `expect_some_` | Existential | (= expect) | Some path matches |

## Per-Directive Settings

Optional `(key: value)` block before the separator overrides engine behavior:

```ill
#expect_foo (useFFI: false) |- !goal .          % pure clause resolution (no FFI)
#expect_bar (rules: [alpha]) LHS => RHS .       % SELL rule-label filtering
#expect_baz (maxDepth: 200) |- !deep_goal .     % override search depth
#expect_qux (explore: true) LHS => RHS .        % force exhaustive exploration
```

| Setting | Applies to | Default | Effect |
|---|---|---|---|
| `useFFI` | `\|-` | `true` | `false` disables FFI, testing pure clause resolution |
| `rules` | `=>` | all | SELL scoped rule sets |
| `maxDepth` | `\|-`, `=>` (explore) | `100` | Search depth limit (backward proof depth / explore tree depth) |
| `explore` | `=>` | `false` | `true` forces exhaustive exploration (for nondeterministic forks without eigenvariables) |

## Eigenvariables

`[X Y Z]` declares universally-quantified variables. The parser wraps both sides in `forall`, and `decomposeQuery` generates matching freevar names.

For forward `=>`, eigenvariables trigger `explore()` (exhaustive symbolic execution) instead of `exec()` (single deterministic execution).

## Runner

`tools/test-ill.js` — discovers `calculus/ill/tests/**/*.ill`, dispatches via `node:test`.
For verbose debug output, use `tools/debug-ill.js` (see `ill-debug-framework.md`).

```bash
npm run test:ill                     # run ILL tests
npm run debug:ill -- <file.ill>      # verbose debug output
```

## Test File Structure

```
calculus/ill/tests/
  backward/
    arithmetic.ill      # inc, plus, mul clause tests (14 tests)
    bitwise.ill         # and, or, xor clause tests (9 tests)
    comparison.ill      # lt, le, sub clause tests (10 tests)
    division.ill        # div, mod, exp clause tests (8 tests)
    memory.ill          # mem_read, no_overlap — McCarthy axioms (11 tests)
    memory-noffi.ill    # same as memory.ill with (useFFI: false) (11 tests)
    sha3-compute.ill    # sha3_compute, mem_read_range (5 tests)
  forward/
    evm-arithmetic.ill  # ADD, SUB, MUL, DIV, LT opcodes + negative tests (9 tests)
    evm-call.ill        # Abstract CALL nondeterminism (explore: true) (3 tests)
    evm-memory.ill      # MSTORE, MLOAD, MSIZE integration (4 tests)
    evm-sha3.ill        # SHA3 opcode — symbolic hash constructor (3 tests)
    evm-stop.ill        # STOP opcode reachability (3 tests)
    debug-demo.ill      # Debug framework demo (trace, dump_state, inspect) (1 test)
  settings/
    directives.ill      # Per-directive settings: maxDepth, rules (3 tests)
  symbolic/
    properties.ill      # Eigenvariable property tests: backward + forward (4 tests)
```

## Writing Tests

Import the program under test, then write directives:

```ill
#import(../../programs/bin.ill)
#expect_inc_zero |- !inc e (i e) .
#expect_not_bad |- !inc e (o e) .
```

Each directive name must be unique across all files (the runner detects and rejects duplicates).

For forward tests, provide initial state on the left and expected pattern on the right:

```ill
#import(../../programs/evm.ill)
#expect_stop pc 0 * bytecode [0x00] => stop .
```

The `=>` pattern uses subset matching: `P subset final_state`. Unmentioned facts (gas, bytecode, etc.) are ignored.

## Dispatch Pipeline

```
.ill file → mde.load(cache:true) + overlay → splitQueries map
  → filter #expect* entries → for each:
    → parseModality(kind) → 'all' | 'not' | 'some'
    → separator '|-' → dispatchBackward
        → decomposeQuery (strip ∀/!) → calc.prove(goal)
        → modality check on success/failure
    → separator '=>' → dispatchForward
        → hasFreevar? → explore (symbolic) | exec (concrete)
        → checkTreeModality | checkExecModality
            → isSubset(pattern, state) → modality check
```

## Implementation Notes

- Runner uses two-phase load: (1) cache heaviest shared import (evm.ill) via binary disk cache, (2) overlay lightweight test files on top. Cold start ~80ms, warm ~40ms
- Forward `exec` defaults `maxSteps: 10000`; `explore` defaults `maxDepth: 100` (overridable via per-directive settings)
- Budget exhaustion with `expect_some` marks the test as skipped (inconclusive) via `t.skip()`, not pass or fail
- Inconclusive leaves (`bound`, `cycle`) are failures for `expect`/`expect_not`; ignored for `expect_some` (don't block ∃-witness)
- Dead leaves (additive false) and memo leaves are always skipped
- Store is content-addressed; multiple file loads accumulate without interference
- Boolean settings (`useFFI`, `explore`) are validated — only `'true'`/`'false'` accepted
- Duplicate directive names across files are detected at load time (throws before tests run)
- Setting values support identifiers (`true`), numbers (`50`), and slash-paths (`evm/push`)

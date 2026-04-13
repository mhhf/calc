# Test Overview

Measured 2026-04-13. 63 test files, 2035 tests total.

## Scripts

| Script | Files | Tests | Time | When to run |
|---|---|---|---|---|
| `npm test` | 48 | 2035 | ~4s | Every iteration |
| `npm run test:noffi` | 1 | 13 | ~1s | Engine changes affecting FFI/clause resolution |
| `npm run test:zk` | 8 | 94 | ~0.4s | ZK/witness changes (24 known failures) |
| `npm run test:heavy` | 6 | ~160 | 5-30 min | Major changes, release validation |
| `npm run test:all` | 63 | all | 5-30 min | Compound of above |
| `npm run test:bare` | 48 | 1605 | ~30s | Verify correctness without optimizations |
| `npm run test:fast` | 48 | 1605 | ~5s | Verify CALC_PROFILE=fast |
| `npm run test:e2e` | 1 | — | ~10s | UI changes (Playwright) |

## Per-File Timing (measured, sorted slowest-first)

| File | Duration | Status | Tests | Layer |
|---|---|---|---|---|
| engine/rule-analysis.test.js | 4.9m | 11 fail | 78 | Engine Generic + EVM |
| engine/vmtest/vmtest.test.js | 1.4s | pass | 331 | EVM |
| engine/noffi-e2e.test.js | 1.1s | pass | 13 | EVM + noFFI |
| engine/store-binary.test.js | 759ms | pass | 34 | Kernel + Engine Generic |
| engine/solc-benchmark.test.js | 347ms | pass | 11 | EVM |
| engine/memory.test.js | 336ms | pass | 34 | Engine ILL + EVM |
| engine/compiled-matcher.test.js | 322ms | pass | 16 | Engine Opt |
| engine/type-check.test.js | 290ms | 3 fail | 29 | Engine Generic |
| engine/prediction.test.js | 277ms | pass | 7 | Engine Opt + EVM |
| rewrite-trace.test.js | 239ms | 1 fail | 8 | Proof Terms + ZK |
| chunked-witness.test.js | 229ms | 19 fail | 19 | ZK |
| engine/e2e.test.js | 229ms | pass | 9 | Engine Generic + EVM |
| engine/sha3.test.js | 224ms | pass | 4 | Engine ILL + EVM |
| engine/sell.test.js | 222ms | pass | 49 | SELL/Graded |
| engine/explore.test.js | 219ms | pass | 34 | Engine Generic |
| engine/arrlit.test.js | 204ms | pass | 83 | Kernel + Engine ILL |
| engine/preserved-sugar.test.js | 204ms | pass | 15 | Engine Generic + ILL |
| zk-benchmark.test.js | 202ms | pass | 4 | ZK + EVM |
| engine/forward.test.js | 202ms | pass | 12 | Engine Generic + ILL |
| engine/disc-tree.test.js | 201ms | pass | 19 | Engine Generic |
| engine/named-args.test.js | 196ms | pass | 37 | Parser + Engine |
| engine/convert.test.js | 194ms | pass | 36 | Engine Generic |
| engine/backchain-agnostic.test.js | 192ms | pass | 34 | Engine Generic |
| engine/compose.test.js | 184ms | pass | 21 | SELL/Graded |
| monad.test.js | 165ms | 9 fail | 53 | Backward Prover |
| earley-grammar.test.js | 164ms | pass | 50 | Parser + Calculus |
| manual-prover-logic.test.js | 160ms | pass | 43 | Backward Prover |
| proof-terms.test.js | 157ms | pass | 127 | Proof Terms |
| engine/clause-terms.test.js | 155ms | pass | 18 | Proof Terms + Engine Opt |
| engine/separator.test.js | 154ms | pass | 22 | Parser |
| quantifiers.test.js | 151ms | pass | 28 | Kernel + Engine |
| zk-noffi-witness.test.js | 151ms | 2 fail | 9 | ZK + noFFI |
| manual-proof-flow.test.js | 134ms | pass | 15 | UI/API |
| sequent-ext.test.js | 134ms | pass | 37 | Kernel + Prover |
| zk-custom-chip.test.js | 134ms | pass | 4 | ZK + EVM |
| engine/primitives.test.js | 133ms | pass | 44 | Engine ILL + Kernel |
| engine/fact-set.test.js | 132ms | pass | 37 | Engine Generic |
| kernel.test.js | 130ms | pass | 20 | Kernel + Prover |
| focused-prover.test.js | 129ms | pass | 42 | Backward Prover |
| rules2-parser.test.js | 127ms | pass | 11 | Parser + Prover |
| prover.test.js | 126ms | pass | 21 | Backward Prover |
| calculus.test.js | 125ms | pass | 53 | Calculus |
| rule-interpreter.test.js | 125ms | pass | 33 | Backward Prover |
| sequent.test.js | 124ms | pass | 8 | Kernel |
| ast.test.js | 123ms | pass | 18 | Kernel |
| api.test.js | 122ms | pass | 7 | UI/API |
| manual-api.test.js | 121ms | pass | 7 | Backward Prover |
| focusing.test.js | 120ms | pass | 15 | Backward Prover |
| guided-term.test.js | 120ms | 1 fail | 17 | Proof Terms |
| zk-witness.test.js | 120ms | 1 fail | 17 | ZK |
| engine/constraint.test.js | 119ms | pass | 13 | Engine Generic |
| ui-flow.test.js | 118ms | pass | 7 | UI/API |
| generic-prover.test.js | 117ms | pass | 34 | Backward Prover |
| multi-logic.test.js | 110ms | pass | 12 | Calculus + Engine ILL |
| zk-uint256.test.js | 110ms | pass | 16 | ZK |
| earley.test.js | 109ms | pass | 45 | Parser |
| engine/evidence.test.js | 109ms | pass | 13 | Engine Opt + ILL |
| meta-ctx.test.js | 100ms | pass | 8 | Kernel + Prover |
| kernel-ops.test.js | 97ms | pass | 17 | Kernel |
| hash.js | 94ms | pass | 14 | Kernel |
| zk-symbolic-solc.test.js | ~30m* | unknown | 2 | ZK + EVM |
| zk-chunked-tree.test.js | ~10m* | unknown | 6 | ZK + EVM |
| zk-custom-chip-solc.test.js | ~10m* | unknown | 4 | ZK + EVM |

`*` = not measured, estimated from declared timeout

## Architecture Layer Map

| Layer | Files in `npm test` | Files in other suites |
|---|---|---|
| **Kernel** | hash.js, ast, kernel-ops, sequent, sequent-ext, meta-ctx | — |
| **Backward Prover** | focusing, focused-prover, generic-prover, prover, kernel, rule-interpreter, manual-api, manual-prover-logic, manual-proof-flow | monad (test:heavy, 9 fail) |
| **Parser** | earley, earley-grammar, rules2-parser, engine/separator, engine/named-args | — |
| **Calculus** | calculus, multi-logic | — |
| **Engine Generic** | engine/convert, forward, explore, fact-set, constraint, backchain-agnostic, compile-matcher, disc-tree | engine/rule-analysis (test:heavy, 5m), engine/type-check (test:heavy, 3 fail) |
| **Engine ILL** | engine/primitives, arrlit, evidence, preserved-sugar, sha3 | — |
| **Engine Opt** | engine/compiled-matcher, prediction | — |
| **EVM** | engine/e2e, memory, solc-benchmark, vmtest | engine/noffi-e2e (test:noffi) |
| **SELL/Graded** | engine/sell, compose | — |
| **Proof Terms** | proof-terms, engine/clause-terms | guided-term (test:zk, 1 fail), rewrite-trace (test:zk, 1 fail) |
| **ZK** | zk-benchmark, zk-custom-chip, zk-uint256 | zk-witness, zk-noffi-witness, chunked-witness (test:zk); zk-symbolic-solc, zk-chunked-tree, zk-custom-chip-solc (test:heavy) |
| **UI/API** | api, ui-flow | e2e-solidjs (test:e2e) |

## Known Failures

After S1 (TODO_0193) all `npm test`, `test:heavy`, `test:noffi`, and `test:ill` suites are green. ZK suite has 24 known failures tracked via `{ todo: true }` markers in `test:zk`.

## Benchmarks (separate from tests)

| Script | What | Duration |
|---|---|---|
| `npm run bench` | Proof search + MGU micro | ~5s |
| `npm run bench:engine` | Backward chaining (bin arithmetic) | ~10s |
| `npm run bench:explore` | DFS symbolic execution tree | ~30s |
| `npm run bench:multisig` | EVM 5-step execution | ~15s |
| `npm run bench:diff` | Cross-commit comparison (git worktrees) | ~30s |

## Measurement Tool

`node tools/test-timing.js [options]` — runs each test file individually and reports per-file timing.

Options: `--timeout=<ms>`, `--skip=<regex>`, `--only=<regex>`, `--category=core|engine|all`, `--save`, `--json`, `--profile=bare|fast|evm`

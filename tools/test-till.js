#!/usr/bin/env node
/**
 * till-native test runner — timed judgments as directives (TODO_0265 Phase 4).
 *
 * The till twin of test-ill.js: discovers #expect/#expect_not/#expect_some
 * directives in calculus/till/tests/**.ill and dispatches:
 *   =>  with a `settle: T` setting — calc.settle(initial, T), then a TIMED
 *       subset check (unstamped pattern facts are stamp wildcards, stamped
 *       facts match their exact cohort — Matching spec / D11); add
 *       `exact: true` to demand an exact cover (extra facts fail);
 *   |-  backward entailment via calc.prove (numeric prelude clauses).
 *
 * Suite body shared with the other timed calculi (tools/spec-runner.js).
 *
 * Usage: node --test --test-concurrency=1 tools/test-till.js
 *   CALC_NOFFI=1 forces useFFI:false on every dispatch (npm run
 *   test:noffi:till) — the FFI-principle gate over ALL till specs.
 *   CALC_TILL_DIR=<dir> points the runner at an EXTERNAL spec tree
 *   (.ill/.till files with #expect directives) instead of
 *   calculus/till/tests — e.g. the PP2 sandbox (Phase 6):
 *     CALC_TILL_DIR=~/src/game npm run test:till
 */

import path from 'path';
import tillConfig from '../calculus/till/calculus-config.js';
import { defineSpecSuite } from './spec-runner.js';

const TEST_DIR = process.env.CALC_TILL_DIR
  ? path.resolve(process.env.CALC_TILL_DIR)
  : path.join(import.meta.dirname, '..', 'calculus', 'till', 'tests');

defineSpecSuite({ config: tillConfig, testDir: TEST_DIR });

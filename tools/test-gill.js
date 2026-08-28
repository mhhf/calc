#!/usr/bin/env node
/**
 * gill-native test runner (TODO_0284 P2) — the gill twin of test-till.js:
 * #expect directives in calculus/gill/tests/**.{ill,till,gill}, dispatched
 * through the shared timed-spec suite (tools/spec-runner.js) under gill's
 * calculus config.
 *
 * Usage: node --test --test-concurrency=1 tools/test-gill.js
 *   CALC_NOFFI=1 — the FFI-principle gate over ALL gill specs
 *   CALC_GILL_DIR=<dir> — external spec tree instead of calculus/gill/tests
 */

import path from 'path';
import gillConfig from '../calculus/gill/calculus-config.js';
import { defineSpecSuite } from './spec-runner.js';

const TEST_DIR = process.env.CALC_GILL_DIR
  ? path.resolve(process.env.CALC_GILL_DIR)
  : path.join(import.meta.dirname, '..', 'calculus', 'gill', 'tests');

defineSpecSuite({ config: gillConfig, testDir: TEST_DIR });

#!/usr/bin/env node
/**
 * will-native test runner (TODO_0297 P0) — the will twin of test-gill.js:
 * #expect directives in calculus/will/tests/**.{ill,till,gill,will},
 * dispatched through the shared timed-spec suite (tools/spec-runner.js)
 * under will's calculus config.
 *
 * Usage: node --test --test-concurrency=1 tools/test-will.js
 *   CALC_NOFFI=1 — the FFI-principle gate over ALL will specs
 *   CALC_WILL_DIR=<dir> — external spec tree instead of calculus/will/tests
 */

import path from 'path';
import willConfig from '../calculus/will/calculus-config.js';
import { defineSpecSuite } from './spec-runner.js';

const TEST_DIR = process.env.CALC_WILL_DIR
  ? path.resolve(process.env.CALC_WILL_DIR)
  : path.join(import.meta.dirname, '..', 'calculus', 'will', 'tests');

defineSpecSuite({ config: willConfig, testDir: TEST_DIR });

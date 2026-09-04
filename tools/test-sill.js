#!/usr/bin/env node
/**
 * sill-native test runner (TODO_0285 P5) — the sill twin of test-gill.js:
 * #expect directives in calculus/sill/tests/**.{ill,till,gill,sill},
 * dispatched through the shared timed-spec suite (tools/spec-runner.js)
 * under sill's calculus config.
 *
 * Usage: node --test --test-concurrency=1 tools/test-sill.js
 *   CALC_NOFFI=1 — the FFI-principle gate over ALL sill specs
 *   CALC_SILL_DIR=<dir> — external spec tree instead of calculus/sill/tests
 */

import path from 'path';
import sillConfig from '../calculus/sill/calculus-config.js';
import { defineSpecSuite } from './spec-runner.js';

const TEST_DIR = process.env.CALC_SILL_DIR
  ? path.resolve(process.env.CALC_SILL_DIR)
  : path.join(import.meta.dirname, '..', 'calculus', 'sill', 'tests');

defineSpecSuite({ config: sillConfig, testDir: TEST_DIR });

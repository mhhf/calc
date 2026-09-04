#!/usr/bin/env node
/**
 * Per-calculus spec runner — ONE driver for the timed calculi
 * (till/gill/will/sill): #expect/#expect_not/#expect_some directives in
 * calculus/<name>/tests/**, dispatched through the shared timed-spec
 * suite (tools/spec-runner.js) under the calculus's config.
 *
 * Runs under `node --test`, where extra argv entries are read as further
 * test FILES — so the calculus is selected by environment:
 *   CALC_SPEC=till|gill|will|sill   (required)
 *   CALC_NOFFI=1 — forces useFFI:false on every dispatch (the
 *     FFI-principle gate over ALL specs; npm run test:noffi:<name>)
 *   CALC_<NAME>_DIR=<dir> — an EXTERNAL spec tree instead of
 *     calculus/<name>/tests, e.g. the PP2 sandbox:
 *       CALC_TILL_DIR=~/src/game npm run test:till
 */

import path from 'path';
import { defineSpecSuite } from './spec-runner.js';

const NAME = process.env.CALC_SPEC;
const KNOWN = ['till', 'gill', 'will', 'sill'];
if (!KNOWN.includes(NAME)) {
  throw new Error(`test-calc: set CALC_SPEC to one of ${KNOWN.join('|')} (got '${NAME}')`);
}
const config = (await import(`../calculus/${NAME}/calculus-config.js`)).default;
const TEST_DIR = process.env[`CALC_${NAME.toUpperCase()}_DIR`]
  ? path.resolve(process.env[`CALC_${NAME.toUpperCase()}_DIR`])
  : path.join(import.meta.dirname, '..', 'calculus', NAME, 'tests');

defineSpecSuite({ config, testDir: TEST_DIR });

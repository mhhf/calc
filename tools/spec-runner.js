/**
 * Timed-calculus spec suite — shared runner body (TODO_0284 P2).
 *
 * The directive dispatch formerly inline in test-till.js, parameterized
 * over the calculus config so every timed calculus (till, gill, later
 * will) runs its executable specs through ONE code path: #expect/
 * #expect_not/#expect_some directives in a spec tree, `=>` with a
 * `settle: T` setting via calc.settle + timed subset/exact check, `|-`
 * via calc.prove over the file's clauses. Each spec file loads as its own
 * program (file-local rule sets). CALC_NOFFI=1 forces useFFI:false on
 * every dispatch — the FFI-principle gate.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import path from 'path';
import mde from '../lib/engine/index.js';
import convert from '../lib/engine/convert.js';
import { timedSubset, timedExact } from '../lib/engine/timed/timed-views.js';
import dl from './directive-loader.js';

const { ROOT, findIllFiles, scanDirectives, detectDuplicates, parseModality, extractGoals, buildProveOpts, show } = dl;
const MAX_STEPS = 10000;
const NOFFI = process.env.CALC_NOFFI === '1';

function formatTimedState(state) {
  const facts = Object.entries(state.linear).map(([h, c]) => show(Number(h)) + (c > 1 ? ` x${c}` : ''));
  return `Final: ${facts.join(', ') || '(empty)'}`;
}

function dispatchSettle(calc, entry, modality, settings) {
  const initial = convert.decomposeQuery(entry.lhsHash);
  const pattern = convert.decomposeQuery(entry.rhsHash);
  const opts = { maxSteps: MAX_STEPS };
  if (settings.maxSteps) opts.maxSteps = parseInt(settings.maxSteps, 10);
  if (settings.rules) opts.rules = settings.rules;
  if (settings.useFFI !== undefined) opts.useFFI = settings.useFFI === 'true';
  if (settings.seed !== undefined) opts.seed = parseInt(settings.seed, 10);
  if (NOFFI) opts.useFFI = false;
  const res = calc.settle(initial, settings.settle, opts);
  // (exact: true) demands an exact cover of the linear zone — extra facts
  // fail, unlike the default subset check (unstamped pattern facts stay
  // stamp wildcards in both modes).
  const check = settings.exact === 'true' ? timedExact : timedSubset;
  const matches = check(pattern, res.state);
  if (modality === 'not') {
    assert.ok(!matches, `Pattern should NOT be reachable.\n${formatTimedState(res.state)}`);
  } else {
    assert.ok(matches, `Pattern not ${settings.exact === 'true' ? 'an exact cover of' : 'found in'} settled state.\n${formatTimedState(res.state)}`);
  }
}

function dispatchBackward(calc, entry, modality, settings) {
  assert.equal(entry.lhsHash, null, 'empty LHS only for |-');
  const goals = extractGoals(entry.rhsHash);
  assert.ok(goals.length > 0, 'No goals found in |- directive');
  const proveOpts = buildProveOpts(settings);
  if (NOFFI) proveOpts.useFFI = false;
  const allSuccess = goals.map(g => calc.prove(g, proveOpts)).every(r => r.success);
  if (modality === 'not') {
    assert.ok(!allSuccess, `Expected NOT provable but succeeded: ${goals.map(g => show(g)).join(', ')}`);
  } else {
    assert.ok(allSuccess, `Expected provable but failed: ${goals.map(g => show(g)).join(', ')}`);
  }
}

/** Define the node:test suite for every spec file under testDir. */
function defineSpecSuite({ config, testDir }) {
  const files = findIllFiles(testDir);
  const fileDirectives = scanDirectives(files, /#(expect\w+)/g);
  if (fileDirectives.size === 0) return;
  detectDuplicates(fileDirectives);

  for (const [file, names] of fileDirectives) {
    const rel = path.relative(ROOT, file);
    // Per-file program: file-local rule sets (no cross-file interference).
    const calc = mde.load(file, { calculusConfig: config, cache: false });
    const entries = [...calc.splitQueries.entries()]
      .filter(([kind]) => names.has(kind) && parseModality(kind) !== null);
    if (entries.length === 0) continue;

    describe(rel, () => {
      for (const [kind, entry] of entries) {
        const modality = parseModality(kind);
        const settings = calc.querySettings.get(kind) || {};
        it(kind, () => {
          if (entry.separator === '|-') dispatchBackward(calc, entry, modality, settings);
          else if (entry.separator === '=>') {
            assert.ok(settings.settle != null,   // null = unparseable value, e.g. (settle: -1)
              `#${kind}: timed => directives need a (settle: T) setting`);
            dispatchSettle(calc, entry, modality, settings);
          } else assert.fail(`Unknown separator: ${entry.separator}`);
        });
      }
    });
  }
}

export { defineSpecSuite };
export default { defineSpecSuite };

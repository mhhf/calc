#!/usr/bin/env node
/**
 * till-native test runner — timed judgments as directives (TODO_0265 Phase 4).
 *
 * The till twin of test-ill.js: discovers #expect/#expect_not/#expect_some
 * directives in calculus/till/tests/**.ill and dispatches:
 *   =>  with a `settle: T` setting — calc.settle(initial, T), then a TIMED
 *       subset check (unstamped pattern facts are stamp wildcards, stamped
 *       facts match their exact cohort — Matching spec / D11);
 *   |-  backward entailment via calc.prove (numeric prelude clauses).
 *
 * Each spec file loads as its OWN program (rules are file-local — scenario
 * rule sets stay isolated, mirroring the oracle suite; the shared numeric
 * prelude arrives via each file's #import of prelude/rat.ill).
 *
 * Usage: node --test --test-concurrency=1 tools/test-till.js
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import mde from '../lib/engine/index.js';
import convert from '../lib/engine/convert.js';
import tillConfig from '../calculus/till/calculus-config.js';
import { timedSubset } from '../lib/engine/timed.js';
import dl from './directive-loader.js';
const { ROOT, findIllFiles, scanDirectives, detectDuplicates, parseModality, extractGoals, buildProveOpts, show } = dl;
const TEST_DIR = path.join(import.meta.dirname, '..', 'calculus', 'till', 'tests');
const MAX_STEPS = 10000;

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
  const res = calc.settle(initial, settings.settle, opts);
  const matches = timedSubset(pattern, res.state);
  if (modality === 'not') {
    assert.ok(!matches, `Pattern should NOT be reachable.\n${formatTimedState(res.state)}`);
  } else {
    assert.ok(matches, `Pattern not found in settled state.\n${formatTimedState(res.state)}`);
  }
}

function dispatchBackward(calc, entry, modality, settings) {
  assert.equal(entry.lhsHash, null, 'empty LHS only for |-');
  const goals = extractGoals(entry.rhsHash);
  assert.ok(goals.length > 0, 'No goals found in |- directive');
  const proveOpts = buildProveOpts(settings);
  const allSuccess = goals.map(g => calc.prove(g, proveOpts)).every(r => r.success);
  if (modality === 'not') {
    assert.ok(!allSuccess, `Expected NOT provable but succeeded: ${goals.map(g => show(g)).join(', ')}`);
  } else {
    assert.ok(allSuccess, `Expected provable but failed: ${goals.map(g => show(g)).join(', ')}`);
  }
}

const files = findIllFiles(TEST_DIR);
const fileDirectives = scanDirectives(files, /#(expect\w+)/g);
if (fileDirectives.size === 0) process.exit(0);
detectDuplicates(fileDirectives);

for (const [file, names] of fileDirectives) {
  const rel = path.relative(ROOT, file);
  // Per-file program: file-local rule sets (no cross-file interference).
  const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
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
          assert.ok(settings.settle !== undefined,
            `#${kind}: till => directives need a (settle: T) setting`);
          dispatchSettle(calc, entry, modality, settings);
        } else assert.fail(`Unknown separator: ${entry.separator}`);
      });
    }
  });
}

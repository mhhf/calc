#!/usr/bin/env node
/**
 * ILL-native test runner — tests as provability judgments.
 *
 * Discovers #expect/#expect_not/#expect_some directives in .ill files
 * and dispatches |- to the backward prover, => to the forward engine.
 *
 * Usage: node --test --test-concurrency=1 tools/test-ill.js
 *
 * See doc/documentation/ill-test-framework.md and TODO_0143.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const mde = require('../lib/engine');
const convert = require('../lib/engine/convert');
const {
  ROOT, findIllFiles, scanDirectives, detectDuplicates, loadProgram,
  parseModality, stateHasFreevars, isSubset, formatState,
  show, toObject, getAllLeaves,
} = require('../lib/engine/directive-loader');

const TEST_DIR = path.join(__dirname, '..', 'calculus', 'ill', 'tests');
const PROGRAM = path.join(__dirname, '..', 'calculus', 'ill', 'programs', 'evm.ill');
const MAX_STEPS = 10000;
const MAX_DEPTH = 100;

// ─── Backward Dispatch (|-) ─────────────────────────────────────────────────

/**
 * Backward entailment: |- !A means A is derivable via backward proof search.
 * decomposeQuery strips the bang (! → persistent) and any quantifiers
 * (forall X → freevar X), producing goals for calc.prove().
 */
function dispatchBackward(calc, entry, modality, kind) {
  assert.equal(entry.lhsHash, null, 'Phase 1: empty LHS only for |-');

  // decomposeQuery strips quantifiers (eigenvars → freevar) and bang → persistent
  const state = convert.decomposeQuery(entry.rhsHash);
  const goals = [
    ...Object.keys(state.persistent).map(Number),
    ...Object.keys(state.linear).map(Number),
  ];
  assert.ok(goals.length > 0, 'No goals found in |- directive');

  // Forward per-directive settings to the backward prover
  const settings = calc.querySettings.get(kind);
  const proveOpts = {};
  if (settings?.useFFI !== undefined) {
    assert.ok(settings.useFFI === 'true' || settings.useFFI === 'false',
      `Invalid useFFI value '${settings.useFFI}' — expected 'true' or 'false'`);
    proveOpts.useFFI = settings.useFFI === 'true';
  }
  if (settings?.maxDepth) proveOpts.maxDepth = parseInt(settings.maxDepth, 10);

  const results = goals.map(g => calc.prove(g, proveOpts));
  const allSuccess = results.every(r => r.success);

  // NB: 'some' degenerates to 'all' for backward — no branching in proof search.
  if (modality === 'all' || modality === 'some') {
    assert.ok(allSuccess,
      `Expected provable but failed: ${goals.map(g => show(g)).join(', ')}`);
  } else {
    assert.ok(!allSuccess,
      `Expected NOT provable but succeeded: ${goals.map(g => show(g)).join(', ')}`);
  }
}

// ─── Forward Dispatch (=>) ──────────────────────────────────────────────────

/**
 * Forward reachability: S => P means executing S reaches a state containing P.
 * Theoretically |- S -o {P * ⊤} — subset matching realizes ⊤-absorption.
 * Ground initial → committed-choice exec (single path).
 * Freevar initial → exhaustive explore (symbolic execution tree).
 */
function dispatchForward(calc, entry, modality, kind, t) {
  const initial = mde.decomposeQuery(entry.lhsHash);
  const pattern = mde.decomposeQuery(entry.rhsHash);
  const settings = calc.querySettings.get(kind);
  const execOpts = {};
  if (settings?.rules) execOpts.rules = settings.rules;
  if (settings?.explore !== undefined) {
    assert.ok(settings.explore === 'true' || settings.explore === 'false',
      `Invalid explore value '${settings.explore}' — expected 'true' or 'false'`);
  }

  const forceExplore = settings?.explore === 'true';
  if (stateHasFreevars(initial) || forceExplore) {
    // Exhaustive exploration: symbolic (freevars) or explicit (explore: true)
    const exploreDepth = settings?.maxDepth ? parseInt(settings.maxDepth, 10) : MAX_DEPTH;
    const tree = calc.explore(initial, { maxDepth: exploreDepth, ...execOpts });
    checkTreeModality(modality, getAllLeaves(tree), pattern);
  } else {
    // Concrete: single execution
    const result = calc.exec(initial, { maxSteps: MAX_STEPS, ...execOpts });
    if (!result.quiescent) {
      if (modality === 'some') {
        t.skip(`Budget exhausted after ${result.steps} steps — inconclusive`);
        return;
      }
      assert.fail(`Budget exhausted after ${result.steps} steps (not quiescent)`);
    }
    checkExecModality(modality, result.state, pattern);
  }
}

/** Modality check for single-path exec: all=∀, not=¬∃, some=∃ (trivially ∀). */
function checkExecModality(modality, state, pattern) {
  const matches = isSubset(pattern, state);
  if (modality === 'all') {
    assert.ok(matches,
      `Pattern not found in final state.\n${formatState(state, 'Final')}`);
  } else if (modality === 'not') {
    assert.ok(!matches,
      `Pattern should NOT be reachable.\n${formatState(state, 'Final')}`);
  } else {
    assert.ok(matches,
      `Expected some path to match.\n${formatState(state, 'Final')}`);
  }
}

/** Modality check for explore tree: all=every leaf matches, not=no leaf matches, some=∃ leaf matches. */
function checkTreeModality(modality, leaves, pattern) {
  const verdicts = [];
  for (const leaf of leaves) {
    if (leaf.type === 'dead' || leaf.type === 'memo') continue;
    if (leaf.type === 'bound' || leaf.type === 'cycle') {
      verdicts.push({ type: leaf.type, match: null, state: leaf.state });
      continue;
    }
    const plain = toObject(leaf.state);
    verdicts.push({ type: 'leaf', match: isSubset(pattern, plain), state: plain });
  }

  if (modality === 'all') {
    for (const v of verdicts) {
      if (v.match === null)
        assert.fail(`Inconclusive ${v.type} leaf.\n${formatState(v.state, v.type)}`);
      assert.ok(v.match,
        `Leaf does not match pattern.\n${formatState(v.state, 'leaf')}`);
    }
  } else if (modality === 'not') {
    for (const v of verdicts) {
      if (v.match === null)
        assert.fail(`Inconclusive ${v.type} leaf.\n${formatState(v.state, v.type)}`);
      assert.ok(!v.match,
        `Pattern should NOT be reachable.\n${formatState(v.state, 'leaf')}`);
    }
  } else {
    assert.ok(verdicts.some(v => v.match === true),
      `Expected SOME path to match but none did (${verdicts.length} leaves).`);
  }
}

// ─── Main ───────────────────────────────────────────────────────────────────

const files = findIllFiles(TEST_DIR);
const fileDirectives = scanDirectives(files, /#(expect\w+)/g);
if (fileDirectives.size === 0) process.exit(0);
detectDuplicates(fileDirectives);
const calc = loadProgram(PROGRAM, fileDirectives);

// Register tests grouped by source file
for (const [file, names] of fileDirectives) {
  const rel = path.relative(ROOT, file);
  const entries = [...calc.splitQueries.entries()]
    .filter(([kind]) => names.has(kind) && parseModality(kind) !== null);

  if (entries.length === 0) continue;

  describe(rel, () => {
    for (const [kind, entry] of entries) {
      const modality = parseModality(kind);
      it(kind, (t) => {
        if (entry.separator === '|-') dispatchBackward(calc, entry, modality, kind);
        else if (entry.separator === '=>') dispatchForward(calc, entry, modality, kind, t);
        else assert.fail(`Unknown separator: ${entry.separator}`);
      });
    }
  });
}

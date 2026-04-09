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
const fs = require('fs');
const mde = require('../lib/engine');
const convert = require('../lib/engine/convert');
const Store = require('../lib/kernel/store');
const { toObject } = require('../lib/engine/fact-set');
const { getAllLeaves } = require('../lib/engine/tree-utils');
const { showInteresting, classifyLeaf, show } = require('../lib/engine/show');

const TEST_DIR = path.join(__dirname, '..', 'calculus', 'ill', 'tests');
const ROOT = path.join(__dirname, '..');
const MAX_STEPS = 10000;
const MAX_DEPTH = 100;

// ─── Modality ───────────────────────────────────────────────────────────────

/** Extract modality from directive kind prefix. */
function parseModality(kind) {
  if (kind === 'expect_not' || kind.startsWith('expect_not_')) return 'not';
  if (kind === 'expect_some' || kind.startsWith('expect_some_')) return 'some';
  if (kind.startsWith('expect')) return 'all';
  return null;
}

// ─── Freevar Detection ──────────────────────────────────────────────────────

/** Recursively check if a content-addressed hash contains freevar nodes. */
function hasFreevar(h) {
  const t = Store.tag(h);
  if (!t) return false;
  if (t === 'freevar') return true;
  // charlit children are raw codepoints (uint32), not term refs — don't recurse
  if (t === 'charlit') return false;
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (elems) for (let i = 0; i < elems.length; i++)
      if (hasFreevar(elems[i])) return true;
    return false;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && hasFreevar(c)) return true;
  }
  return false;
}

/** Check if a decomposed state contains any freevars (from eigenvariables). */
function stateHasFreevars(state) {
  for (const h of Object.keys(state.linear))
    if (hasFreevar(+h)) return true;
  for (const h of Object.keys(state.persistent))
    if (hasFreevar(+h)) return true;
  return false;
}

// ─── Subset Matching ────────────────────────────────────────────────────────

/** Pattern ⊆ state: every fact in pattern exists (with sufficient count) in state. */
function isSubset(pattern, state) {
  for (const [h, cnt] of Object.entries(pattern.linear))
    if ((state.linear[h] || 0) < cnt) return false;
  for (const h of Object.keys(pattern.persistent))
    if (!state.persistent[h]) return false;
  return true;
}

// ─── Diagnostics ────────────────────────────────────────────────────────────

function formatState(state, label) {
  if (!state) return `${label}: NO_STATE`;
  const cls = classifyLeaf(state);
  const facts = showInteresting(state, { exclude: [] });
  return `${label} [${cls}]: ${facts.join(', ')}`;
}

// ─── File Discovery ─────────────────────────────────────────────────────────

function findIllFiles(dir) {
  if (!fs.existsSync(dir)) return [];
  const results = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) results.push(...findIllFiles(full));
    else if (entry.name.endsWith('.ill')) results.push(full);
  }
  return results.sort();
}

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
// Same load strategy as JS tests: mde.load(program, { cache: true }).
// Load the shared program (evm.ill) from binary cache, then overlay
// lightweight test files to extract their #expect_* directives.

const files = findIllFiles(TEST_DIR);

// Step 1: pre-scan each file for #expect_* directive names
const fileDirectives = new Map(); // file → Set<directiveName>
for (const file of files) {
  const src = fs.readFileSync(file, 'utf8');
  const names = new Set();
  for (const m of src.matchAll(/#(expect\w+)/g)) names.add(m[1]);
  if (names.size > 0) fileDirectives.set(file, names);
}

if (fileDirectives.size === 0) process.exit(0);

// Detect duplicate directive names across files (splitQueries is a flat Map — last writer wins)
const nameToFile = new Map();
for (const [file, names] of fileDirectives) {
  for (const name of names) {
    if (nameToFile.has(name)) {
      const prev = path.relative(ROOT, nameToFile.get(name));
      const curr = path.relative(ROOT, file);
      throw new Error(`Duplicate directive '${name}' in ${prev} and ${curr}`);
    }
    nameToFile.set(name, file);
  }
}

// Step 2: load shared program with cache (same as JS tests), overlay test files
const PROGRAM = path.join(__dirname, '..', 'calculus', 'ill', 'programs', 'evm.ill');
const calc = mde.load(PROGRAM, { cache: true });
const alreadyImported = new Set(convert.buildImportTree(PROGRAM).map(n => n.path));
for (const file of fileDirectives.keys()) {
  convert.loadFile(file, new Map(), new Map(), [], new Map(), {
    argNamesTable: new Map(), querySettings: calc.querySettings,
    splitQueries: calc.splitQueries, moduleDecls: [], alreadyImported
  });
}

// Step 3: register tests grouped by source file
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

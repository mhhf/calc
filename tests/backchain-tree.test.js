'use strict';

const test = require('node:test');
const assert = require('node:assert');
const path = require('path');

const { backchainWithTree } = require('../lib/prover/backchain-tree');
const mde = require('../lib/engine');
const Store = require('../lib/kernel/store');
const { initILL, makeILLBackchainOpts } = require('../lib/engine/ill/backchain-ill');
const { FORMAT_VERSION } = require('../lib/prover/serialize-tree');

test('backchain-tree — plus (i e) (i e) R: default is opaque FFI leaf', () => {
  Store.clear();
  initILL();
  const prog = mde.load(path.join(__dirname, '..', 'calculus/ill/programs/bin.ill'), { cache: false });

  const e = Store.put('atom', ['e']);
  const ie = Store.put('i', [e]);
  const R = Store.put('metavar', ['R']);
  const goal = Store.put('plus', [ie, ie, R]);

  const res = backchainWithTree(goal, prog.clauses, prog.definitions, {
    ...makeILLBackchainOpts(),
    calculus: 'ill',
    profile: 'backchain',
    maxDepth: 200,
  });

  assert.strictEqual(res.success, true);
  assert.strictEqual(res.tree.format, FORMAT_VERSION);
  assert.strictEqual(res.tree.root.rule, 'ffi', 'default: FFI intercepts plus → opaque leaf');
  assert.strictEqual(res.tree.root.premises.length, 0);
  assert.ok(Object.keys(res.tree.formulas).length > 0);
});

test('backchain-tree — useFFI:false expands plus clauses into a tree', () => {
  Store.clear();
  initILL();
  const prog = mde.load(path.join(__dirname, '..', 'calculus/ill/programs/bin.ill'), { cache: false });

  const e = Store.put('atom', ['e']);
  const ie = Store.put('i', [e]);
  const R = Store.put('metavar', ['R']);
  const goal = Store.put('plus', [ie, ie, R]);

  const res = backchainWithTree(goal, prog.clauses, prog.definitions, {
    ...makeILLBackchainOpts(),
    calculus: 'ill',
    profile: 'backchain-teaching',
    useFFI: false,
    maxDepth: 200,
  });

  assert.strictEqual(res.success, true);
  assert.ok(/^plus\//.test(res.tree.root.rule),
    `teaching mode: expected plus/* at root, got "${res.tree.root.rule}"`);
  // plus/s4 recurses on a smaller subproblem → at least one premise
  assert.ok(res.tree.root.premises.length >= 1,
    'teaching mode: plus/s4 should have ≥1 premise');
});

test('backchain-tree — no clauses → failure', () => {
  Store.clear();
  initILL();
  const empty = new Map();
  const defs = new Map();
  const a = Store.put('atom', ['a']);
  const goal = Store.put('nope', [a]);
  const res = backchainWithTree(goal, empty, defs, { ...makeILLBackchainOpts() });
  assert.strictEqual(res.success, false);
});

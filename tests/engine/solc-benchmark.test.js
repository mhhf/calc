/**
 * Tests for real solc-compiled bytecode symbolic execution.
 * MultisigNoCall.sol compiled with solc 0.8.28.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const { explore } = require('../../lib/engine/explore');
const { getAllLeaves, countNodes } = require('../../lib/engine/tree-utils');
const { classifyLeaf } = require('../../lib/engine/show');
const Store = require('../../lib/kernel/store');

describe('Solc multisig explore', { timeout: 30000, concurrency: 1 }, () => {
  let tree, allLeaves, classes;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    tree = explore(state, calc.forwardRules, {
      maxDepth: 2000,
      calc: { clauses: calc.clauses, definitions: calc.definitions },
      dangerouslyUseFFI: true // Benchmark test
    });

    allLeaves = getAllLeaves(tree);
    classes = {};
    for (const leaf of allLeaves) {
      const cl = classifyLeaf(leaf.state);
      classes[cl] = (classes[cl] || 0) + 1;
    }
  });

  it('explores to expected tree shape', () => {
    assert.strictEqual(countNodes(tree), 267, 'Expected 267 nodes');
    assert.strictEqual(allLeaves.length, 1, 'Expected 1 leaf');
  });

  it('has 1 STOP leaf (successful termination)', () => {
    assert.strictEqual(classes.STOP, 1,
      `Expected 1 STOP leaf, got ${classes.STOP}`);
  });

  it('all STOP leaves emit Vote event (log3)', () => {
    const stops = allLeaves.filter(l => classifyLeaf(l.state) === 'STOP');
    for (const leaf of stops) {
      let hasLog = false;
      const log3TagId = Store.TAG['log3'];
      if (log3TagId !== undefined && leaf.state.linear.groupLen(log3TagId) > 0) {
        hasLog = true;
      }
      assert(hasLog, 'Every STOP leaf should emit a log3 (Vote event)');
    }
  });

  it('only leaf is STOP (all infeasible branches collapsed)', () => {
    assert.strictEqual(allLeaves.length, 1);
    assert.strictEqual(classifyLeaf(allLeaves[0].state), 'STOP');
  });

  it('has no bound or cycle leaves (full exploration)', () => {
    const bound = allLeaves.filter(l => l.type === 'bound');
    const cycle = allLeaves.filter(l => l.type === 'cycle');
    assert.strictEqual(bound.length, 0, 'No depth-bound leaves');
    assert.strictEqual(cycle.length, 0, 'No cycle leaves');
  });

  it('completes under 1s', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    const t0 = performance.now();
    explore(state, calc.forwardRules, {
      maxDepth: 2000,
      calc: { clauses: calc.clauses, definitions: calc.definitions },
      dangerouslyUseFFI: true
    });
    const dt = performance.now() - t0;

    assert(dt < 1000, `Expected < 1s, got ${dt.toFixed(0)}ms`);
  });
});

describe('Solc multisig symbolic (structural memo)', { timeout: 30000, concurrency: 1 }, () => {
  let treeFull, treeMemo;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    const opts = { maxDepth: 500, calc: { clauses: calc.clauses, definitions: calc.definitions }, dangerouslyUseFFI: true };

    treeFull = explore(state, calc.forwardRules, { ...opts, structuralMemo: false });
    treeMemo = explore(state, calc.forwardRules, { ...opts, structuralMemo: true });
  });

  it('full exploration has 214 nodes and 2 leaves', () => {
    assert.strictEqual(countNodes(treeFull), 214, 'Expected 214 nodes');
    assert.strictEqual(getAllLeaves(treeFull).length, 2, 'Expected 2 leaves');
  });

  it('structural memo has same tree (no redundant branches to memo)', () => {
    const n = countNodes(treeMemo);
    assert.strictEqual(n, 214, `Expected 214 nodes with memo, got ${n}`);
  });

  it('leaves are STOP + REVERT (all infeasible branches pruned)', () => {
    const leaves = getAllLeaves(treeFull);
    const classes = {};
    for (const l of leaves) {
      const { classifyLeaf } = require('../../lib/engine/show');
      const cl = classifyLeaf(l.state);
      classes[cl] = (classes[cl] || 0) + 1;
    }
    assert.strictEqual(classes.STOP, 1, 'Expected 1 STOP leaf');
    assert.strictEqual(classes.REVERT, 1, 'Expected 1 REVERT leaf');
  });

  it('no bound or cycle nodes (full exploration achieved)', () => {
    const leaves = getAllLeaves(treeFull);
    const bound = leaves.filter(l => l.type === 'bound');
    const cycle = leaves.filter(l => l.type === 'cycle');
    assert.strictEqual(bound.length, 0, 'No depth-bound leaves');
    assert.strictEqual(cycle.length, 0, 'No cycle leaves');
  });

  it('completes under 1s with structural memo', async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    const t0 = performance.now();
    explore(state, calc.forwardRules, {
      maxDepth: 500,
      structuralMemo: true,
      calc: { clauses: calc.clauses, definitions: calc.definitions },
      dangerouslyUseFFI: true
    });
    const dt = performance.now() - t0;

    assert(dt < 1000, `Expected < 1s, got ${dt.toFixed(0)}ms`);
  });
});

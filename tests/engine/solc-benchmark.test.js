/**
 * Tests for real solc-compiled bytecode symbolic execution.
 * MultisigNoCall.sol compiled with solc 0.8.28.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import mde from '../../calculus/ill/index.js';
import { getAllLeaves, countNodes } from '../../lib/engine/tree-utils.js';
import { classifyLeaf } from '../../calculus/ill/index.js';
import Store from '../../lib/kernel/store.js';
describe('Solc multisig explore', { timeout: 30000, concurrency: 1 }, () => {
  let tree, allLeaves, classes;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));

    tree = calc.explore(state, {
      maxDepth: 2000,
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
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));

    const t0 = performance.now();
    calc.explore(state, {
      maxDepth: 2000,
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
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));

    treeFull = calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true, structuralMemo: false });
    treeMemo = calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true, structuralMemo: true });
  });

  it('full exploration has 1987 nodes and 31 leaves', () => {
    assert.strictEqual(countNodes(treeFull), 1987, 'Expected 1987 nodes');
    assert.strictEqual(getAllLeaves(treeFull).length, 31, 'Expected 31 leaves');
  });

  it('structural memo skips isomorphic member subtrees (513 nodes)', () => {
    const n = countNodes(treeMemo);
    assert.strictEqual(n, 513, `Expected 513 nodes with memo, got ${n}`);
  });

  it('leaves are the 31 feasible paths (18 STOP + 13 REVERT)', () => {
    const leaves = getAllLeaves(treeFull);
    const classes = {};
    for (const l of leaves) {
      const cl = classifyLeaf(l.state);
      classes[cl] = (classes[cl] || 0) + 1;
    }
    assert.strictEqual(classes.STOP, 18, 'Expected 18 STOP leaves');
    assert.strictEqual(classes.REVERT, 13, 'Expected 13 REVERT leaves');
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
      path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill')
    );
    const state = mde.normalizeQuery(calc.queries.get('symex'));

    const t0 = performance.now();
    calc.explore(state, {
      maxDepth: 500,
      structuralMemo: true,
      dangerouslyUseFFI: true
    });
    const dt = performance.now() - t0;

    assert(dt < 1000, `Expected < 1s, got ${dt.toFixed(0)}ms`);
  });
});

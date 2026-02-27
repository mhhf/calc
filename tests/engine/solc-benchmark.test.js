/**
 * Tests for real solc-compiled bytecode symbolic execution.
 * MultisigNoCall.sol compiled with solc 0.8.28.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const { explore } = require('../../lib/engine/symexec');
const { getAllLeaves, countNodes } = require('../../lib/engine/tree-utils');
const { classifyLeaf } = require('../../lib/engine/show');
const Store = require('../../lib/kernel/store');

describe('Solc multisig symexec', { timeout: 30000 }, () => {
  let tree, allLeaves, classes;

  before(async () => {
    Store.clear();
    const calc = await mde.load(
      path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc.ill')
    );
    const state = mde.decomposeQuery(calc.queries.get('symex'));

    tree = explore(state, calc.forwardRules, {
      maxDepth: 2000,
      calc: { clauses: calc.clauses, types: calc.types }
    });

    allLeaves = getAllLeaves(tree);
    classes = {};
    for (const leaf of allLeaves) {
      const cl = classifyLeaf(leaf.state);
      classes[cl] = (classes[cl] || 0) + 1;
    }
  });

  it('explores to expected tree shape', () => {
    assert.strictEqual(countNodes(tree), 301, 'Expected 301 nodes');
    assert.strictEqual(allLeaves.length, 16, 'Expected 16 leaves');
  });

  it('has 1 STOP leaf (successful termination)', () => {
    assert.strictEqual(classes.STOP, 1,
      `Expected 1 STOP leaf, got ${classes.STOP}`);
  });

  it('all STOP leaves emit Vote event (log3)', () => {
    const stops = allLeaves.filter(l => classifyLeaf(l.state) === 'STOP');
    for (const leaf of stops) {
      let hasLog = false;
      for (const h of Object.keys(leaf.state.linear)) {
        if (Store.tag(Number(h)) === 'log3') { hasLog = true; break; }
      }
      assert(hasLog, 'Every STOP leaf should emit a log3 (Vote event)');
    }
  });

  it('all non-STOP leaves are dead branches (stuck lolis)', () => {
    const nonStop = allLeaves.filter(l => classifyLeaf(l.state) !== 'STOP');
    for (const leaf of nonStop) {
      let hasLoli = false;
      for (const h of Object.keys(leaf.state.linear)) {
        if (Store.tag(Number(h)) === 'loli') { hasLoli = true; break; }
      }
      assert(hasLoli,
        'Every non-STOP leaf should have a stuck loli (dead branch)');
    }
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
      calc: { clauses: calc.clauses, types: calc.types }
    });
    const dt = performance.now() - t0;

    assert(dt < 1000, `Expected < 1s, got ${dt.toFixed(0)}ms`);
  });
});

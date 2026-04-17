/**
 * Tests for forward-trace/v1 serialization. Exercises both the
 * symex (exhaustive explore) and exec (linear forward) paths on a
 * small hand-built tree first, then a real program end-to-end.
 */

'use strict';

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');

const Store = require('../lib/kernel/store');
const {
  serializeExploreTree,
  serializeExecTrace,
  extractLeafTrace,
  FORMAT_VERSION,
} = require('../lib/prover/serialize-trace');

function put(tag, args) { return Store.put(tag, args); }

describe('serializeExploreTree — hand-built tree', () => {
  let tree, hA, hB;
  before(() => {
    Store.clear();
    hA = put('atom', ['stop']);
    hB = put('atom', ['pc']);
    tree = {
      type: 'branch',
      state: null,
      children: [
        {
          rule: 'step/a',
          child: {
            type: 'leaf',
            state: { linear: { [hA]: 1 }, persistent: {} },
            trace: [
              { rule: { name: 'step/a' }, consumed: { [hB]: 1 }, theta: [], slots: [], persistentEvidence: [], loliHash: null },
            ],
          },
        },
        {
          rule: 'step/b',
          child: {
            type: 'leaf',
            state: { linear: { [hB]: 1 }, persistent: {} },
            trace: [
              { rule: { name: 'step/b' }, consumed: { [hA]: 1 }, theta: [], slots: [], persistentEvidence: [], loliHash: null },
              { rule: { name: 'step/b' }, consumed: { [hB]: 1 }, theta: [], slots: [], persistentEvidence: [], loliHash: null },
            ],
          },
        },
      ],
    };
  });

  it('has correct top-level shape', () => {
    const out = serializeExploreTree(tree, { calculus: 'ill', profile: 'default', mode: 'symex' });
    assert.strictEqual(out.format, FORMAT_VERSION);
    assert.strictEqual(out.mode, 'symex');
    assert.strictEqual(out.calculus, 'ill');
    assert.ok(out.formulas);
    assert.ok(out.tree);
    assert.ok(Array.isArray(out.leaves));
  });

  it('computes correct stats', () => {
    const out = serializeExploreTree(tree);
    assert.strictEqual(out.stats.totalNodes, 3); // 1 branch + 2 leaves
    assert.strictEqual(out.stats.branchCount, 1);
    assert.strictEqual(out.stats.leafCount, 2);
    assert.strictEqual(out.stats.maxDepth, 1);
    assert.strictEqual(out.stats.totalTraceSteps, 3);
    assert.strictEqual(out.stats.maxTraceLen, 2);
  });

  it('assigns stable DFS-preorder ids', () => {
    const out = serializeExploreTree(tree);
    assert.strictEqual(out.tree.id, 'n0');
    assert.strictEqual(out.tree.idx, 0);
    assert.strictEqual(out.tree.children[0].child.id, 'n1');
    assert.strictEqual(out.tree.children[1].child.id, 'n2');
  });

  it('does NOT embed per-leaf trace in the first payload', () => {
    const out = serializeExploreTree(tree);
    for (const leaf of out.leaves) {
      assert.strictEqual(leaf.trace, undefined,
        `leaf ${leaf.leafIndex} should not carry trace in first payload`);
      assert.ok(typeof leaf.stepCount === 'number');
    }
  });

  it('populates formula pool with referenced hashes', () => {
    const out = serializeExploreTree(tree);
    const poolKeys = Object.keys(out.formulas);
    assert.ok(poolKeys.length >= 2, `expected ≥2 pool entries, got ${poolKeys.length}`);
    // hA and hB both should be referenced
    assert.ok(poolKeys.some(k => out.formulas[k].tag === 'atom' && out.formulas[k].name === 'stop'));
    assert.ok(poolKeys.some(k => out.formulas[k].tag === 'atom' && out.formulas[k].name === 'pc'));
  });

  it('classifies leaves: stop atom → STOP status', () => {
    const out = serializeExploreTree(tree);
    assert.strictEqual(out.leaves[0].status, 'STOP');
    // second leaf has pc → RUNNING
    assert.strictEqual(out.leaves[1].status, 'RUNNING');
  });

  it('extractLeafTrace returns correct step count', () => {
    const leaf0 = extractLeafTrace(tree, 0);
    assert.ok(leaf0);
    assert.strictEqual(leaf0.stepCount, 1);
    assert.strictEqual(leaf0.trace.length, 1);
    assert.strictEqual(leaf0.trace[0].ruleName, 'step/a');

    const leaf1 = extractLeafTrace(tree, 1);
    assert.strictEqual(leaf1.stepCount, 2);
    assert.strictEqual(leaf1.trace[0].ruleName, 'step/b');
    assert.strictEqual(leaf1.trace[1].ruleName, 'step/b');
  });

  it('extractLeafTrace returns null for out-of-range', () => {
    const missing = extractLeafTrace(tree, 99);
    assert.strictEqual(missing, null);
  });

  it('is JSON-serializable with no functions or circular refs', () => {
    const out = serializeExploreTree(tree);
    const json = JSON.stringify(out);
    const parsed = JSON.parse(json);
    assert.strictEqual(parsed.format, FORMAT_VERSION);
    assert.strictEqual(parsed.stats.leafCount, 2);
  });
});

describe('serializeExecTrace — linear forward', () => {
  let hA, hB, trace, finalState;
  before(() => {
    Store.clear();
    hA = put('atom', ['a']);
    hB = put('atom', ['b']);
    finalState = { linear: { [hB]: 1 }, persistent: {} };
    trace = [
      { rule: { name: 'r1' }, consumed: { [hA]: 1 }, theta: [], slots: [], persistentEvidence: [], loliHash: null },
    ];
  });

  it('produces exec-mode payload with embedded trace', () => {
    const out = serializeExecTrace(finalState, trace, { calculus: 'ill' });
    assert.strictEqual(out.mode, 'exec');
    assert.strictEqual(out.stats.leafCount, 1);
    assert.strictEqual(out.stats.totalTraceSteps, 1);
    assert.strictEqual(out.leaves[0].trace.length, 1);
    assert.strictEqual(out.leaves[0].trace[0].ruleName, 'r1');
  });
});

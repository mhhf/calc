/**
 * DisplayProver Tests
 *
 * Tests for the generic display calculus prover.
 */

const { test, describe } = require('node:test');
const assert = require('node:assert');

const { DisplayProver, LNLDisplayProver, ProofStep, SearchStrategy } = require('../lib/display-prover.js');
const { TreeSequent, LNLTreeSequent } = require('../lib/sequent-tree.js');

// Mock node for testing
function mockNode(id, vals = [], str = null) {
  const hash = BigInt(id * 1000 + (vals.length > 0 ? vals.reduce((a, v) => a + (v?.id || 0), 0) : 0));
  return {
    id,
    vals,
    hash,
    copy: () => mockNode(id, vals.map(v => v?.copy?.() || v), str),
    toString: () => str || `node_${id}`
  };
}

describe('DisplayProver - Basic', () => {

  test('creates prover with default options', () => {
    const prover = new DisplayProver();
    assert.strictEqual(prover.strategy, SearchStrategy.DFS);
    assert.strictEqual(prover.maxDepth, 100);
  });

  test('creates prover with custom options', () => {
    const prover = new DisplayProver({
      strategy: SearchStrategy.BFS,
      maxDepth: 50,
      debug: true
    });
    assert.strictEqual(prover.strategy, SearchStrategy.BFS);
    assert.strictEqual(prover.maxDepth, 50);
    assert.strictEqual(prover.debug, true);
  });

  test('prove returns result object', () => {
    const prover = new DisplayProver();
    const goal = new TreeSequent({
      antecedent: mockNode(1, [], 'A'),
      succedent: mockNode(2, [], 'B')
    });

    const result = prover.prove(goal);

    assert.ok('success' in result);
    assert.ok('proofTree' in result);
    assert.ok('steps' in result);
  });

});

describe('DisplayProver - Identity', () => {

  test('proves identity: A |- A (TreeSequent)', () => {
    const prover = new DisplayProver();
    const formula = mockNode(1, [], 'A');
    const goal = new TreeSequent({
      antecedent: formula,
      succedent: formula  // Same reference
    });

    const result = prover.prove(goal);

    assert.strictEqual(result.success, true);
    assert.strictEqual(result.proofTree.ruleName, 'Id');
  });

  test('proves identity: · ; A |- A (LNLTreeSequent)', () => {
    const prover = new DisplayProver();
    const formula = mockNode(1, [], 'A');
    const empty = mockNode(99, [], '·');

    const goal = new LNLTreeSequent({
      cartesian: empty,
      linear: formula,
      succedent: formula  // Same reference
    });

    // Mock isEmpty to recognize our empty node
    prover.isEmpty = (tree) => tree && tree.id === 99;

    const result = prover.prove(goal);

    assert.strictEqual(result.success, true);
    assert.strictEqual(result.proofTree.ruleName, 'Id');
  });

  test('does not prove non-identity: A |- B', () => {
    const prover = new DisplayProver();
    const goal = new TreeSequent({
      antecedent: mockNode(1, [], 'A'),
      succedent: mockNode(2, [], 'B')
    });

    const result = prover.prove(goal);

    // Without rules, this should fail (can't prove A |- B)
    assert.strictEqual(result.success, false);
  });

});

describe('ProofStep', () => {

  test('creates proof step with sequent', () => {
    const seq = new TreeSequent({
      antecedent: mockNode(1),
      succedent: mockNode(2)
    });
    const step = new ProofStep(seq);

    assert.strictEqual(step.sequent, seq);
    assert.strictEqual(step.ruleName, null);
    assert.deepStrictEqual(step.premises, []);
    assert.strictEqual(step.proved, false);
  });

  test('isLeaf returns true for no premises', () => {
    const step = new ProofStep(new TreeSequent({}));
    assert.strictEqual(step.isLeaf(), true);
  });

  test('isLeaf returns false with premises', () => {
    const parent = new ProofStep(new TreeSequent({}));
    const child = new ProofStep(new TreeSequent({}), null, [], parent);
    parent.premises = [child];

    assert.strictEqual(parent.isLeaf(), false);
  });

  test('markProved propagates up', () => {
    const root = new ProofStep(new TreeSequent({}));
    const child = new ProofStep(new TreeSequent({}), null, [], root);
    root.premises = [child];

    child.markProved();

    assert.strictEqual(child.proved, true);
    assert.strictEqual(root.proved, true);
  });

  test('markProved does not propagate if siblings unproved', () => {
    const root = new ProofStep(new TreeSequent({}));
    const child1 = new ProofStep(new TreeSequent({}), null, [], root);
    const child2 = new ProofStep(new TreeSequent({}), null, [], root);
    root.premises = [child1, child2];

    child1.markProved();

    assert.strictEqual(child1.proved, true);
    assert.strictEqual(child2.proved, false);
    assert.strictEqual(root.proved, false);
  });

  test('markProved propagates when all siblings proved', () => {
    const root = new ProofStep(new TreeSequent({}));
    const child1 = new ProofStep(new TreeSequent({}), null, [], root);
    const child2 = new ProofStep(new TreeSequent({}), null, [], root);
    root.premises = [child1, child2];

    child1.markProved();
    child2.markProved();

    assert.strictEqual(root.proved, true);
  });

});

describe('LNLDisplayProver', () => {

  test('extends DisplayProver', () => {
    const prover = new LNLDisplayProver();
    assert.ok(prover instanceof DisplayProver);
  });

  test('accepts mode-specific rules', () => {
    const prover = new LNLDisplayProver({
      cartesianRules: { exchange: {} },
      linearRules: { assoc: {} },
      bridgeRules: { absorption: {} }
    });

    assert.ok(prover.cartesianRules.exchange);
    assert.ok(prover.linearRules.assoc);
    assert.ok(prover.bridgeRules.absorption);
  });

});

describe('SearchStrategy', () => {

  test('DFS strategy value', () => {
    assert.strictEqual(SearchStrategy.DFS, 'dfs');
  });

  test('BFS strategy value', () => {
    assert.strictEqual(SearchStrategy.BFS, 'bfs');
  });

  test('prover respects maxDepth in DFS', () => {
    const prover = new DisplayProver({
      strategy: SearchStrategy.DFS,
      maxDepth: 0  // Immediate cutoff
    });

    const goal = new TreeSequent({
      antecedent: mockNode(1, [], 'A'),
      succedent: mockNode(2, [], 'B')
    });

    const result = prover.prove(goal);
    assert.strictEqual(result.success, false);
  });

});

describe('DisplayProver - Debug', () => {

  test('collectDebug returns tree structure', () => {
    const prover = new DisplayProver({ debug: true });
    const formula = mockNode(1, [], 'A');
    const goal = new TreeSequent({
      antecedent: formula,
      succedent: formula
    });

    const result = prover.prove(goal);

    assert.ok(result.debug);
    assert.strictEqual(result.debug.depth, 0);
    assert.ok('sequent' in result.debug);
    assert.ok('rule' in result.debug);
    assert.ok('proved' in result.debug);
    assert.ok('premises' in result.debug);
  });

  test('debug is null when debug option is false', () => {
    const prover = new DisplayProver({ debug: false });
    const formula = mockNode(1, [], 'A');
    const goal = new TreeSequent({
      antecedent: formula,
      succedent: formula
    });

    const result = prover.prove(goal);

    assert.strictEqual(result.debug, null);
  });

});

describe('DisplayProver - Tree Equality', () => {

  test('treesEqual with same reference', () => {
    const prover = new DisplayProver();
    const node = mockNode(1, [], 'A');

    assert.strictEqual(prover.treesEqual(node, node), true);
  });

  test('treesEqual with same structure', () => {
    const prover = new DisplayProver();
    const node1 = mockNode(1, [mockNode(2)], 'A(B)');
    const node2 = mockNode(1, [mockNode(2)], 'A(B)');

    assert.strictEqual(prover.treesEqual(node1, node2), true);
  });

  test('treesEqual with different id', () => {
    const prover = new DisplayProver();
    const node1 = mockNode(1, [], 'A');
    const node2 = mockNode(2, [], 'B');

    assert.strictEqual(prover.treesEqual(node1, node2), false);
  });

  test('treesEqual with different children', () => {
    const prover = new DisplayProver();
    const node1 = mockNode(1, [mockNode(2)], 'A(B)');
    const node2 = mockNode(1, [mockNode(3)], 'A(C)');

    assert.strictEqual(prover.treesEqual(node1, node2), false);
  });

  test('treesEqual with null', () => {
    const prover = new DisplayProver();
    const node = mockNode(1);

    assert.strictEqual(prover.treesEqual(node, null), false);
    assert.strictEqual(prover.treesEqual(null, node), false);
    assert.strictEqual(prover.treesEqual(null, null), true);
  });

});

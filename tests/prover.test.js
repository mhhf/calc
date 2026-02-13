/**
 * Tests for v2 ProofTree and FocusedProofState
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const { ProofTree, fromGoal, leaf } = require('../lib/prover/pt');
const { FocusedProofState, inversion, focus } = require('../lib/prover/state');
const Seq = require('../lib/kernel/sequent');
const calculus = require('../lib/calculus');

describe('v2 ProofTree', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('construction', () => {
    it('should create proof tree from goal', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('B'));
      const pt = fromGoal(s);
      assert.strictEqual(pt.rule, null);
      assert.strictEqual(pt.proven, false);
      assert.strictEqual(pt.premisses.length, 0);
    });

    it('should create leaf (axiom)', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      assert.strictEqual(pt.rule, 'id');
      assert.strictEqual(pt.proven, true);
    });
  });

  describe('properties', () => {
    it('isGoal should return true for unproven', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('B'));
      const pt = fromGoal(s);
      assert.strictEqual(pt.isGoal(), true);
    });

    it('isGoal should return false for proven', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      assert.strictEqual(pt.isGoal(), false);
    });

    it('isLeaf should return true for no premisses', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      assert.strictEqual(pt.isLeaf(), true);
    });

    it('isComplete should check entire subtree', () => {
      const s1 = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const s2 = Seq.fromArrays([AST.freevar('B')], [], AST.freevar('B'));
      const p1 = leaf(s1, 'id');
      const p2 = leaf(s2, 'id');

      const pt = new ProofTree({
        conclusion: Seq.fromArrays([], [], AST.tensor(AST.freevar('A'), AST.freevar('B'))),
        premisses: [p1, p2],
        rule: 'tensor_r',
        proven: true
      });

      assert.strictEqual(pt.isComplete(), true);
    });
  });

  describe('traversal', () => {
    it('getGoals should find unproven nodes', () => {
      const s1 = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const s2 = Seq.fromArrays([AST.freevar('B')], [], AST.freevar('B'));
      const p1 = leaf(s1, 'id');
      const p2 = fromGoal(s2);  // Unproven!

      const pt = new ProofTree({
        conclusion: Seq.fromArrays([], [], AST.tensor(AST.freevar('A'), AST.freevar('B'))),
        premisses: [p1, p2],
        rule: 'tensor_r',
        proven: false
      });

      const goals = pt.getGoals();
      assert.strictEqual(goals.length, 1);
      assert.strictEqual(goals[0], p2);
    });

    it('size should count all nodes', () => {
      const s1 = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const s2 = Seq.fromArrays([AST.freevar('B')], [], AST.freevar('B'));
      const p1 = leaf(s1, 'id');
      const p2 = leaf(s2, 'id');

      const pt = new ProofTree({
        conclusion: Seq.fromArrays([], [], AST.tensor(AST.freevar('A'), AST.freevar('B'))),
        premisses: [p1, p2],
        rule: 'tensor_r',
        proven: true
      });

      assert.strictEqual(pt.size(), 3);
    });

    it('depth should compute tree depth', () => {
      const s1 = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const p1 = leaf(s1, 'id');

      const pt = new ProofTree({
        conclusion: Seq.fromArrays([], [], AST.freevar('A')),
        premisses: [p1],
        rule: 'some_rule',
        proven: true
      });

      assert.strictEqual(pt.depth(), 2);
    });
  });

  describe('copy', () => {
    it('should deep copy proof tree', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      const pt2 = pt.copy();

      assert.notStrictEqual(pt, pt2);
      assert.notStrictEqual(pt.conclusion, pt2.conclusion);
      assert.strictEqual(pt.rule, pt2.rule);
    });

    it('should copy state if present', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const state = focus('R');
      const pt = new ProofTree({ conclusion: s, state });
      const pt2 = pt.copy();

      assert.notStrictEqual(pt.state, pt2.state);
      assert.strictEqual(pt2.state.position, 'R');
    });
  });

  describe('serialization', () => {
    it('toJSON should produce plain object', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      const json = pt.toJSON();

      assert.strictEqual(json.rule, 'id');
      assert.strictEqual(json.proven, true);
      assert.ok(Array.isArray(json.premisses));
    });

    it('toString should produce readable output', () => {
      const s = Seq.fromArrays([AST.freevar('A')], [], AST.freevar('A'));
      const pt = leaf(s, 'id');
      const str = pt.toString();

      assert.ok(str.includes('id'));
      assert.ok(str.includes('✓'));
    });
  });
});

describe('v2 FocusedProofState', () => {
  describe('construction', () => {
    it('should create inversion state', () => {
      const state = inversion();
      assert.strictEqual(state.phase, 'inversion');
      assert.strictEqual(state.position, null);
      assert.strictEqual(state.focusHash, null);
    });

    it('should create focus state', () => {
      const state = focus('R');
      assert.strictEqual(state.phase, 'focus');
      assert.strictEqual(state.position, 'R');
    });

    it('should create focus state with hash', () => {
      const state = focus('L', 'abc123');
      assert.strictEqual(state.position, 'L');
      assert.strictEqual(state.focusHash, 'abc123');
    });
  });

  describe('transitions', () => {
    it('focus should enter focus phase', () => {
      const state = inversion();
      state.focus('R');
      assert.strictEqual(state.isFocused(), true);
      assert.strictEqual(state.position, 'R');
    });

    it('blur should exit focus phase', () => {
      const state = focus('R');
      state.blur();
      assert.strictEqual(state.isInversion(), true);
      assert.strictEqual(state.position, null);
    });
  });

  describe('queries', () => {
    it('isFocused should return true in focus phase', () => {
      const state = focus('R');
      assert.strictEqual(state.isFocused(), true);
    });

    it('isInversion should return true in inversion phase', () => {
      const state = inversion();
      assert.strictEqual(state.isInversion(), true);
    });

    it('isFocusedRight should check position', () => {
      const state = focus('R');
      assert.strictEqual(state.isFocusedRight(), true);
      assert.strictEqual(state.isFocusedLeft(), false);
    });

    it('isFocusedLeft should check position', () => {
      const state = focus('L', 'hash');
      assert.strictEqual(state.isFocusedLeft(), true);
      assert.strictEqual(state.isFocusedRight(), false);
    });
  });

  describe('copy', () => {
    it('should deep copy state', () => {
      const state = focus('L', 'abc123');
      const state2 = state.copy();

      assert.notStrictEqual(state, state2);
      assert.strictEqual(state2.phase, 'focus');
      assert.strictEqual(state2.position, 'L');
      assert.strictEqual(state2.focusHash, 'abc123');
    });
  });

  describe('serialization', () => {
    it('toString should produce readable output', () => {
      assert.strictEqual(inversion().toString(), 'inversion');
      assert.ok(focus('R').toString().includes('focus'));
    });

    it('toJSON should produce plain object', () => {
      const state = focus('L', 'abc123');
      const json = state.toJSON();
      assert.strictEqual(json.phase, 'focus');
      assert.strictEqual(json.position, 'L');
      assert.strictEqual(json.focusHash, 'abc123');
    });
  });
});

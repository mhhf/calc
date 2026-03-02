/**
 * Tests for v2 ProofTree and FocusedProofState
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const { ProofTree, fromGoal, leaf } = require('../lib/prover/pt');
const { inversion, focus } = require('../lib/prover/state');
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
      assert.strictEqual(pt.premises.length, 0);
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

    it('isLeaf should return true for no premises', () => {
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
        premises: [p1, p2],
        rule: 'tensor_r',
        proven: true
      });

      assert.strictEqual(pt.isComplete(), true);
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
      assert.ok(Array.isArray(json.premises));
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

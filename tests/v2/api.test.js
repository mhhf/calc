/**
 * Tests for v2 API
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calc = require('../../lib/v2');

describe('v2 API', () => {
  let ill;

  before(async () => {
    ill = await calc.loadILL();
  });

  describe('loadILL', () => {
    it('should load ILL calculus', () => {
      assert.ok(ill.AST);
      assert.ok(ill.parse);
      assert.ok(ill.render);
      assert.ok(ill.rules);
    });

    it('should have AST constructors', () => {
      const { AST } = ill;
      assert.ok(typeof AST.tensor === 'function');
      assert.ok(typeof AST.loli === 'function');
      assert.ok(typeof AST.with === 'function');
      assert.ok(typeof AST.one === 'function');
      assert.ok(typeof AST.freevar === 'function');
    });
  });

  describe('prove (shorthand)', () => {
    it('should prove A ⊢ A', () => {
      const A = ill.AST.freevar('A');
      const seq = calc.Seq.fromArrays([A], [], A);
      const result = calc.prove(ill, seq);
      assert.strictEqual(result.success, true);
    });

    it('should prove modus ponens', () => {
      const { AST } = ill;
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const seq = calc.Seq.fromArrays([P, AST.loli(P, Q)], [], Q);
      const result = calc.prove(ill, seq);
      assert.strictEqual(result.success, true);
    });
  });

  describe('createProver', () => {
    it('should create reusable prover', () => {
      const prover = calc.createProver(ill);
      assert.ok(typeof prover.prove === 'function');
    });

    it('should prove multiple goals with same prover', () => {
      const prover = calc.createProver(ill);
      const { AST } = ill;

      const A = AST.freevar('A');
      const B = AST.freevar('B');

      // A ⊢ A
      const r1 = prover.prove(calc.Seq.fromArrays([A], [], A));
      assert.strictEqual(r1.success, true);

      // B ⊢ B
      const r2 = prover.prove(calc.Seq.fromArrays([B], [], B));
      assert.strictEqual(r2.success, true);

      // A, B ⊢ A ⊗ B
      const r3 = prover.prove(calc.Seq.fromArrays([A, B], [], AST.tensor(A, B)));
      assert.strictEqual(r3.success, true);
    });
  });

  describe('Seq', () => {
    it('should create and manipulate sequents', () => {
      const A = ill.AST.freevar('A');
      const B = ill.AST.freevar('B');

      const s = calc.Seq.fromArrays([A], [], B);
      assert.strictEqual(calc.Seq.getContext(s, 'linear').length, 1);
      assert.strictEqual(s.succedent.tag, 'freevar');
    });
  });
});

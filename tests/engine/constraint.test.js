/**
 * Tests for constraint solver (eq/neq branch pruning)
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');
const Store = require('../../lib/kernel/store');
const { EqNeqSolver } = require('../../lib/engine/constraint');

describe('EqNeqSolver', () => {
  beforeEach(() => { Store.clear(); });

  // Helper: create !eq X Y as a persistent fact hash
  function mkEq(a, b) {
    return Store.put('eq', [a, b]);
  }

  function mkNeq(a, b) {
    return Store.put('neq', [a, b]);
  }

  function mkBinlit(n) {
    return Store.put('binlit', [BigInt(n)]);
  }

  function mkFreevar(name) {
    return Store.put('freevar', [name]);
  }

  describe('ground constraints', () => {
    it('ground eq with equal values → SAT', () => {
      const solver = new EqNeqSolver();
      solver.addConstraint(mkEq(mkBinlit(5), mkBinlit(5)));
      assert.strictEqual(solver.checkSAT(), true);
    });

    it('ground eq with unequal values → UNSAT', () => {
      const solver = new EqNeqSolver();
      solver.addConstraint(mkEq(mkBinlit(5), mkBinlit(0)));
      assert.strictEqual(solver.checkSAT(), false);
    });

    it('ground neq with unequal values → SAT', () => {
      const solver = new EqNeqSolver();
      solver.addConstraint(mkNeq(mkBinlit(5), mkBinlit(0)));
      assert.strictEqual(solver.checkSAT(), true);
    });

    it('ground neq with equal values → UNSAT', () => {
      const solver = new EqNeqSolver();
      solver.addConstraint(mkNeq(mkBinlit(5), mkBinlit(5)));
      assert.strictEqual(solver.checkSAT(), false);
    });
  });

  describe('symbolic constraints', () => {
    it('eq X Y then neq X Y → UNSAT', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      solver.addConstraint(mkEq(X, Y));
      solver.addConstraint(mkNeq(X, Y));
      assert.strictEqual(solver.checkSAT(), false);
    });

    it('transitive: eq X Y, eq Y Z, neq X Z → UNSAT', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      const Z = mkFreevar('Z');
      solver.addConstraint(mkEq(X, Y));
      solver.addConstraint(mkEq(Y, Z));
      solver.addConstraint(mkNeq(X, Z));
      assert.strictEqual(solver.checkSAT(), false);
    });

    it('SAT: neq X 0, neq Y 0, eq X Y', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      const zero = mkBinlit(0);
      solver.addConstraint(mkNeq(X, zero));
      solver.addConstraint(mkNeq(Y, zero));
      solver.addConstraint(mkEq(X, Y));
      assert.strictEqual(solver.checkSAT(), true);
    });

    it('SAT: independent neq constraints', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      solver.addConstraint(mkNeq(X, Y));
      assert.strictEqual(solver.checkSAT(), true);
    });
  });

  describe('checkpoint/restore', () => {
    it('restore undoes union', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      const cp = solver.checkpoint();
      solver.addConstraint(mkEq(X, Y));
      solver.addConstraint(mkNeq(X, Y));
      assert.strictEqual(solver.checkSAT(), false);
      solver.restore(cp);
      assert.strictEqual(solver.checkSAT(), true);
    });

    it('restore undoes forbid', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      solver.addConstraint(mkEq(X, Y));
      const cp = solver.checkpoint();
      solver.addConstraint(mkNeq(X, Y));
      assert.strictEqual(solver.checkSAT(), false);
      solver.restore(cp);
      assert.strictEqual(solver.checkSAT(), true);
    });

    it('nested checkpoints', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const Y = mkFreevar('Y');
      const Z = mkFreevar('Z');

      const cp1 = solver.checkpoint();
      solver.addConstraint(mkEq(X, Y));

      const cp2 = solver.checkpoint();
      solver.addConstraint(mkEq(Y, Z));
      solver.addConstraint(mkNeq(X, Z));
      assert.strictEqual(solver.checkSAT(), false);

      solver.restore(cp2);
      assert.strictEqual(solver.checkSAT(), true);

      solver.restore(cp1);
      // X, Y no longer unified
      solver.addConstraint(mkNeq(X, Y));
      assert.strictEqual(solver.checkSAT(), true);
    });
  });

  describe('mixed ground/symbolic', () => {
    it('eq X 5, neq X 5 → UNSAT (symbolic meets ground via union)', () => {
      const solver = new EqNeqSolver();
      const X = mkFreevar('X');
      const five = mkBinlit(5);
      solver.addConstraint(mkEq(X, five));
      solver.addConstraint(mkNeq(X, five));
      assert.strictEqual(solver.checkSAT(), false);
    });

    it('non-eq/neq predicates are ignored', () => {
      const solver = new EqNeqSolver();
      const h = Store.put('plus', [mkBinlit(1), mkBinlit(2), mkBinlit(3)]);
      assert.strictEqual(solver.addConstraint(h), false);
      assert.strictEqual(solver.checkSAT(), true);
    });
  });
});

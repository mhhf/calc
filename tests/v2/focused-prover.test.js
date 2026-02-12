/**
 * Tests for v2 FocusedProver
 * Verifies against v1's proofstate.js test cases
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const { createProver, buildRuleSpecs } = require('../../lib/v2/prover/focused/prover');
const Seq = require('../../lib/v2/kernel/sequent');
const calculus = require('../../lib/v2/calculus');

describe('v2 FocusedProver', () => {
  let calc, AST, prover, ruleSpecs, alternatives;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    const built = buildRuleSpecs(calc);
    ruleSpecs = built.specs;
    alternatives = built.alternatives;
    prover = createProver(calc);
  });

  // Helper: create sequent from formula strings
  const seq = (linear, succ) => {
    const linearFormulas = linear.map(f =>
      typeof f === 'string' ? calc.parse(f) : f
    );
    const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, [], succFormula);
  };

  describe('findInvertible', () => {
    it('should find negative formula on right', () => {
      // A ⊸ B is negative, so right rule is invertible
      const s = seq([], AST.loli(AST.freevar('A'), AST.freevar('B')));
      const inv = prover.findInvertible(s);
      assert.strictEqual(inv?.position, 'R');
    });

    it('should find positive formula on left', () => {
      // A ⊗ B is positive, so left rule is invertible
      const s = seq([AST.tensor(AST.freevar('A'), AST.freevar('B'))], AST.freevar('C'));
      const inv = prover.findInvertible(s);
      assert.strictEqual(inv?.position, 'L');
    });

    it('should not find atomic formulas', () => {
      // Atoms are not invertible (use identity)
      const s = seq([AST.freevar('A')], AST.freevar('B'));
      const inv = prover.findInvertible(s);
      assert.strictEqual(inv, null);
    });

    it('should not find positive on right (not invertible)', () => {
      // A ⊗ B on right is positive, right rule NOT invertible
      const s = seq([], AST.tensor(AST.freevar('A'), AST.freevar('B')));
      const inv = prover.findInvertible(s);
      assert.strictEqual(inv, null);
    });
  });

  describe('chooseFocus', () => {
    it('should focus on positive succedent', () => {
      const s = seq([], AST.tensor(AST.freevar('A'), AST.freevar('B')));
      const choices = prover.chooseFocus(s);
      assert.ok(choices.length >= 1);
      assert.ok(choices.some(c => c.position === 'R'));
    });

    it('should focus on negative in context', () => {
      const s = seq([AST.loli(AST.freevar('A'), AST.freevar('B'))], AST.freevar('C'));
      const choices = prover.chooseFocus(s);
      // Should have left focus option for loli (negative)
      assert.ok(choices.some(c => c.position === 'L'));
    });

    it('should not focus on positive in context as left', () => {
      // Positive on left = invertible, not focusable as left focus
      const s = seq([AST.tensor(AST.freevar('A'), AST.freevar('B'))], AST.freevar('C'));
      const choices = prover.chooseFocus(s);
      // No left focus choices (tensor is positive)
      assert.ok(!choices.some(c => c.position === 'L'));
    });
  });

  describe('tryIdentity', () => {
    it('should match identical atoms', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = prover.tryIdentity(s, 'R', -1);
      assert.ok(result?.success);
    });

    it('should unify metavars', () => {
      // Metavars (starting with _) are unification variables
      const s = seq([AST.freevar('_X')], AST.freevar('_Y'));
      const result = prover.tryIdentity(s, 'R', -1);
      assert.ok(result?.success);
      assert.ok(result.theta.length > 0);
    });

    it('should fail for different freevars', () => {
      // Regular freevars are ground - X ⊢ Y should fail
      const s = seq([AST.freevar('X')], AST.freevar('Y'));
      const result = prover.tryIdentity(s, 'R', -1);
      assert.strictEqual(result, null);
    });

    it('should fail for non-matching atoms', () => {
      const s = seq([AST.atom('p')], AST.atom('q'));
      const result = prover.tryIdentity(s, 'R', -1);
      assert.strictEqual(result, null);
    });
  });

  describe('proof search - identity', () => {
    it('should prove Q ⊢ Q', () => {
      const Q = AST.freevar('Q');
      const s = seq([Q], Q);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove A ⊢ A with atoms', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('proof search - linear implication', () => {
    it('should prove P, P ⊸ Q ⊢ Q (modus ponens)', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const s = seq([P, AST.loli(P, Q)], Q);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove A ⊢ B ⊸ (A ⊗ B)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A], AST.loli(B, AST.tensor(A, B)));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('proof search - tensor', () => {
    it('should prove P ⊗ Q ⊢ P ⊗ Q', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const f = AST.tensor(P, Q);
      const s = seq([f], f);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove P ⊗ Q ⊢ Q ⊗ P (commutativity)', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const s = seq([AST.tensor(P, Q)], AST.tensor(Q, P));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove A, B ⊢ A ⊗ B', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A, B], AST.tensor(A, B));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('proof search - with (additive conjunction)', () => {
    it('should prove A & B ⊢ A', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([AST.with(A, B)], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove A & B ⊢ B', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([AST.with(A, B)], B);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove A ⊢ A & A', () => {
      const A = AST.freevar('A');
      const s = seq([A], AST.with(A, A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('proof search - currying', () => {
    it('should prove (A ⊗ B) ⊸ C ⊢ A ⊸ (B ⊸ C)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const s = seq(
        [AST.loli(AST.tensor(A, B), C)],
        AST.loli(A, AST.loli(B, C))
      );
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove A ⊸ (B ⊸ C) ⊢ (A ⊗ B) ⊸ C', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const s = seq(
        [AST.loli(A, AST.loli(B, C))],
        AST.loli(AST.tensor(A, B), C)
      );
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('proof search - distribution', () => {
    it('should prove P ⊸ (R & Q) ⊢ (P ⊸ Q) & (P ⊸ R)', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const R = AST.freevar('R');
      const s = seq(
        [AST.loli(P, AST.with(R, Q))],
        AST.with(AST.loli(P, Q), AST.loli(P, R))
      );
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('proof search - unit', () => {
    it('should prove ⊢ 1 with empty context', () => {
      const s = seq([], AST.one());
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove 1 ⊢ 1', () => {
      const s = seq([AST.one()], AST.one());
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove 1, A ⊢ A', () => {
      const A = AST.freevar('A');
      const s = seq([AST.one(), A], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });

  describe('resource linearity', () => {
    it('should fail A ⊢ A ⊗ A (cannot duplicate)', () => {
      const A = AST.freevar('A');
      const s = seq([A], AST.tensor(A, A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, false);
    });

    it('should fail A, B ⊢ A (cannot discard B)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A, B], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, false);
    });
  });

  describe('proof tree structure', () => {
    it('should produce valid proof tree for A ⊢ A', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });

      assert.ok(result.proofTree);
      assert.strictEqual(result.proofTree.proven, true);
      assert.ok(result.proofTree.rule.includes('id'));
    });

    it('should produce multi-level proof tree', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([AST.tensor(A, B)], AST.tensor(B, A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });

      assert.ok(result.proofTree);
      assert.strictEqual(result.proofTree.rule, 'tensor_l');
      assert.ok(result.proofTree.premisses.length > 0);
    });
  });

  describe('proof search - bang (exponential)', () => {
    it('should prove !A ⊢ A (dereliction)', () => {
      const A = AST.freevar('A');
      const s = seq([AST.bang(A)], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should prove !A ⊢ !A via identity', () => {
      // !A ⊢ !A works via identity on matching formulas
      // Identity is tried BEFORE inversion, so !A = !A matches directly
      const A = AST.freevar('A');
      const bangA = AST.bang(A);
      const s = seq([bangA], bangA);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
      assert.strictEqual(result.proofTree.rule, 'id');
    });

    it('should prove ⊢ A ⊸ !A requires empty context (promotion)', () => {
      // This is NOT provable in standard ILL
      // A ⊸ !A means "given A, produce unlimited A" - not valid
      const A = AST.freevar('A');
      const s = seq([], AST.loli(A, AST.bang(A)));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      // This should fail: after loli_r, we have A ⊢ !A
      // But promotion requires empty linear context
      assert.strictEqual(result.success, false);
    });

    it('should prove !A, !A ⊢ A ⊗ A (can use bang multiple times)', () => {
      const A = AST.freevar('A');
      const s = seq([AST.bang(A), AST.bang(A)], AST.tensor(A, A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });

    it('should fail !A ⊢ A ⊗ A (single bang cannot duplicate)', () => {
      // With just dereliction, !A becomes A, and we can't duplicate
      const A = AST.freevar('A');
      const s = seq([AST.bang(A)], AST.tensor(A, A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      // Without copy rule from cartesian, this should fail
      assert.strictEqual(result.success, false);
    });
  });

  describe('proof search - cartesian context (absorption/copy)', () => {
    // Helper to create sequent with cartesian context
    const seqWithCart = (linear, cart, succ) => {
      const linearFormulas = linear.map(f =>
        typeof f === 'string' ? calc.parse(f) : f
      );
      const cartFormulas = cart.map(f =>
        typeof f === 'string' ? calc.parse(f) : f
      );
      const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
      return Seq.fromArrays(linearFormulas, cartFormulas, succFormula);
    };

    it('should prove ·; A ⊢ A (copy from cartesian)', () => {
      const A = AST.freevar('A');
      const s = seqWithCart([], [A], A);
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
      assert.strictEqual(result.proofTree.rule, 'copy');
    });

    it('should prove ·; A ⊢ !A (promotion with cartesian)', () => {
      // Empty linear + A in cartesian = can promote!
      const A = AST.freevar('A');
      const s = seqWithCart([], [A], AST.bang(A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
      assert.strictEqual(result.proofTree.rule, 'bang_r');
    });

    it('should prove ·; A ⊢ A ⊗ A (copy twice)', () => {
      // Can use cartesian formula multiple times via copy
      const A = AST.freevar('A');
      const s = seqWithCart([], [A], AST.tensor(A, A));
      const result = prover.prove(s, { rules: ruleSpecs, alternatives });
      assert.strictEqual(result.success, true);
    });
  });
});

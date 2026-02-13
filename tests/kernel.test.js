/**
 * Tests for L1 Kernel (proof verification)
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const { createKernel } = require('../lib/v2/prover/kernel');
const { createProver, buildRuleSpecs } = require('../lib/v2/prover/focused/prover');
const Seq = require('../lib/v2/kernel/sequent');
const calculus = require('../lib/v2/calculus');
const { ProofTree, leaf } = require('../lib/v2/prover/pt');

describe('L1 Kernel - Proof Verification', () => {
  let calc, AST, kernel, prover, ruleSpecs, alternatives;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    const built = buildRuleSpecs(calc);
    ruleSpecs = built.specs;
    alternatives = built.alternatives;
    prover = createProver(calc);
    kernel = createKernel(calc);
  });

  const seq = (linear, succ) => {
    const linearFormulas = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, [], succFormula);
  };

  const seqWithCart = (linear, cart, succ) => {
    const linearFormulas = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const cartFormulas = cart.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, cartFormulas, succFormula);
  };

  // Helper: prove and verify
  const proveAndVerify = (s) => {
    const result = prover.prove(s, { rules: ruleSpecs, alternatives });
    assert.strictEqual(result.success, true, 'Expected proof to succeed');
    const verification = kernel.verifyTree(result.proofTree);
    return verification;
  };

  describe('verifyStep', () => {
    it('should accept valid identity A |- A', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = kernel.verifyStep(s, 'id', []);
      assert.strictEqual(result.valid, true);
    });

    it('should reject identity with wrong formula', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A], B);
      const result = kernel.verifyStep(s, 'id', []);
      assert.strictEqual(result.valid, false);
    });

    it('should reject identity with premises', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = kernel.verifyStep(s, 'id', [s]);
      assert.strictEqual(result.valid, false);
    });

    it('should accept valid loli_r step', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const conclusion = seq([], AST.loli(A, B));
      const premise = seq([A], B);
      const result = kernel.verifyStep(conclusion, 'loli_r', [premise]);
      assert.strictEqual(result.valid, true);
    });

    it('should reject loli_r with wrong number of premises', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const conclusion = seq([], AST.loli(A, B));
      const result = kernel.verifyStep(conclusion, 'loli_r', []);
      assert.strictEqual(result.valid, false);
    });

    it('should reject unknown rule', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = kernel.verifyStep(s, 'nonexistent_r', []);
      assert.strictEqual(result.valid, false);
    });

    it('should accept valid tensor_l step', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const conclusion = seq([AST.tensor(A, B)], C);
      const premise = seq([A, B], C);
      const result = kernel.verifyStep(conclusion, 'tensor_l', [premise]);
      assert.strictEqual(result.valid, true);
    });

    it('should accept valid one_r step', () => {
      const conclusion = seq([], AST.one());
      const result = kernel.verifyStep(conclusion, 'one_r', []);
      assert.strictEqual(result.valid, true);
    });
  });

  describe('verifyTree - known-good proofs', () => {
    it('should verify A |- A', () => {
      const A = AST.freevar('A');
      const v = proveAndVerify(seq([A], A));
      assert.strictEqual(v.valid, true);
      assert.deepStrictEqual(v.errors, []);
    });

    it('should verify P, P -o Q |- Q', () => {
      const P = AST.freevar('P');
      const Q = AST.freevar('Q');
      const v = proveAndVerify(seq([P, AST.loli(P, Q)], Q));
      assert.strictEqual(v.valid, true);
    });

    it('should verify A * B |- B * A', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const v = proveAndVerify(seq([AST.tensor(A, B)], AST.tensor(B, A)));
      assert.strictEqual(v.valid, true);
    });

    it('should verify |- 1', () => {
      const v = proveAndVerify(seq([], AST.one()));
      assert.strictEqual(v.valid, true);
    });

    it('should verify A & B |- A', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const v = proveAndVerify(seq([AST.with(A, B)], A));
      assert.strictEqual(v.valid, true);
    });

    it('should verify A |- B -o (A * B)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const v = proveAndVerify(seq([A], AST.loli(B, AST.tensor(A, B))));
      assert.strictEqual(v.valid, true);
    });

    it('should verify A |- A & A', () => {
      const A = AST.freevar('A');
      const v = proveAndVerify(seq([A], AST.with(A, A)));
      assert.strictEqual(v.valid, true);
    });

    it('should verify !A |- A (dereliction)', () => {
      const A = AST.freevar('A');
      const v = proveAndVerify(seq([AST.bang(A)], A));
      assert.strictEqual(v.valid, true);
    });

    it('should verify currying: (A * B) -o C |- A -o (B -o C)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const v = proveAndVerify(seq(
        [AST.loli(AST.tensor(A, B), C)],
        AST.loli(A, AST.loli(B, C))
      ));
      assert.strictEqual(v.valid, true);
    });

    it('should verify cartesian copy: ;A |- A', () => {
      const A = AST.freevar('A');
      const s = seqWithCart([], [A], A);
      const v = proveAndVerify(s);
      assert.strictEqual(v.valid, true);
    });
  });

  describe('verifyTree - tampered proofs', () => {
    it('should reject tree with unproven goal', () => {
      const A = AST.freevar('A');
      const tree = new ProofTree({ conclusion: seq([A], A) });
      const v = kernel.verifyTree(tree);
      assert.strictEqual(v.valid, false);
      assert.ok(v.errors.length > 0);
    });

    it('should reject tree with wrong rule name', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      // Build a tree that claims to use tensor_r but is actually identity
      const tree = new ProofTree({
        conclusion: s,
        rule: 'tensor_r',
        proven: true,
        premisses: []
      });
      const v = kernel.verifyTree(tree);
      assert.strictEqual(v.valid, false);
    });
  });
});

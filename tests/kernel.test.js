/**
 * Tests for L1 Kernel (proof verification)
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import { createKernel } from '../lib/prover/kernel.js';
import { createProver } from '../lib/prover/focused.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import Seq from '../lib/kernel/sequent.js';
import calculus from '../lib/calculus/index.js';
import { ProofTree, leaf } from '../lib/prover/pt.js';
import { gradeW } from '../lib/engine/grades.js';
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
      const v = proveAndVerify(seq([AST.bang(gradeW(),A)], A));
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

  // Round-15 F1: verifyTree threads the linear resource discipline —
  // rule-shape-valid trees that leak or duplicate resources are rejected,
  // and steps the kernel cannot re-derive are reported in `unverified`.
  describe('verifyTree - resource accounting (round-15 F1)', () => {
    it('rejects a forged id with unconsumed context: A, B |- A', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const v = kernel.verifyTree(leaf(seq([A, B], A), 'id'));
      assert.strictEqual(v.valid, false);
      assert.ok(v.errors.some(e => /unconsumed/.test(e)), v.errors.join('; '));
    });

    it('rejects the leak under a rule: A * B |- A via tensor_l + id', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const tree = new ProofTree({
        conclusion: seq([AST.tensor(A, B)], A),
        rule: 'tensor_l',
        proven: true,
        premises: [leaf(seq([A, B], A), 'id')],
      });
      const v = kernel.verifyTree(tree);
      assert.strictEqual(v.valid, false);
    });

    it('accepts exact hand-split trees: A, B |- A * B with split premises', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const tree = new ProofTree({
        conclusion: seq([A, B], AST.tensor(A, B)),
        rule: 'tensor_r',
        proven: true,
        premises: [leaf(seq([A], A), 'id'), leaf(seq([B], B), 'id')],
      });
      const v = kernel.verifyTree(tree);
      assert.strictEqual(v.valid, true, v.errors.join('; '));
      assert.strictEqual(v.unverified, undefined);
    });

    it('rejects additive branches consuming different resources (with_r)', () => {
      // the kernel-side twin of the prover's with_r soundness fix:
      // a, b |- (a * b) & a must not verify — branch 2 silently drops b
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const goal = AST.with(AST.tensor(A, B), A);
      const branch1 = new ProofTree({
        conclusion: seq([A, B], AST.tensor(A, B)),
        rule: 'tensor_r',
        proven: true,
        premises: [leaf(seq([A, B], A), 'id'), leaf(seq([B], B), 'id')],
      });
      const branch2 = leaf(seq([A, B], A), 'id');
      const tree = new ProofTree({
        conclusion: seq([A, B], goal),
        rule: 'with_r',
        proven: true,
        premises: [branch1, branch2],
      });
      const v = kernel.verifyTree(tree);
      assert.strictEqual(v.valid, false);
    });

    it('flags modeSwitch steps as unverified (bridge steps are opaque)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      // hand-built bridge node: any Δ |- {S} passes shape checks — the
      // kernel cannot re-run the forward engine, so it must FLAG it
      const bridgeTree = new ProofTree({
        conclusion: seq([B], calc.parse('{ A }')),
        rule: 'monad_r',
        proven: true,
        premises: [],
      });
      const v = kernel.verifyTree(bridgeTree);
      assert.strictEqual(v.valid, true);
      assert.deepStrictEqual(v.unverified, ['modeSwitch']);
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
        premises: []
      });
      const v = kernel.verifyTree(tree);
      assert.strictEqual(v.valid, false);
    });
  });
});

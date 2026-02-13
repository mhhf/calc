/**
 * Tests for L2 Generic Prover (search primitives)
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const { createGenericProver, buildRuleSpecs } = require('../lib/v2/prover/generic');
const Seq = require('../lib/v2/kernel/sequent');
const calculus = require('../lib/v2/calculus');
const Context = require('../lib/v2/prover/context');

describe('L2 Generic Prover', () => {
  let calc, AST, generic, specs, alternatives;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    const built = buildRuleSpecs(calc);
    specs = built.specs;
    alternatives = built.alternatives;
    generic = createGenericProver(calc);
  });

  const seq = (linear, succ) => {
    const linearFormulas = linear.map(f => typeof f === 'string' ? calc.parse(f) : f);
    const succFormula = typeof succ === 'string' ? calc.parse(succ) : succ;
    return Seq.fromArrays(linearFormulas, [], succFormula);
  };

  describe('connective', () => {
    it('should return tag for compound formulas', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const t = AST.tensor(A, B);
      assert.strictEqual(generic.connective(t), 'tensor');
    });

    it('should return null for atoms', () => {
      const A = AST.freevar('A');
      assert.strictEqual(generic.connective(A), null);
    });

    it('should return null for named atoms', () => {
      const a = AST.atom('p');
      assert.strictEqual(generic.connective(a), null);
    });
  });

  describe('isPositive / isNegative', () => {
    it('tensor is positive', () => {
      assert.strictEqual(generic.isPositive('tensor'), true);
      assert.strictEqual(generic.isNegative('tensor'), false);
    });

    it('loli is negative', () => {
      assert.strictEqual(generic.isPositive('loli'), false);
      assert.strictEqual(generic.isNegative('loli'), true);
    });

    it('with is negative', () => {
      assert.strictEqual(generic.isPositive('with'), false);
      assert.strictEqual(generic.isNegative('with'), true);
    });

    it('atoms default to positive', () => {
      assert.strictEqual(generic.isPositive('atom'), true);
      assert.strictEqual(generic.isPositive('freevar'), true);
    });
  });

  describe('ruleName', () => {
    it('should compute rule name from formula + side', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const t = AST.tensor(A, B);
      assert.strictEqual(generic.ruleName(t, 'r'), 'tensor_r');
      assert.strictEqual(generic.ruleName(t, 'l'), 'tensor_l');
    });

    it('should return null for atoms', () => {
      const A = AST.freevar('A');
      assert.strictEqual(generic.ruleName(A, 'r'), null);
    });
  });

  describe('ruleIsInvertible', () => {
    it('tensor left is invertible (positive on left)', () => {
      assert.strictEqual(generic.ruleIsInvertible('tensor', 'l'), true);
    });

    it('tensor right is NOT invertible', () => {
      assert.strictEqual(generic.ruleIsInvertible('tensor', 'r'), false);
    });

    it('loli right is invertible (negative on right)', () => {
      assert.strictEqual(generic.ruleIsInvertible('loli', 'r'), true);
    });

    it('loli left is NOT invertible', () => {
      assert.strictEqual(generic.ruleIsInvertible('loli', 'l'), false);
    });

    it('with right is invertible (negative on right)', () => {
      assert.strictEqual(generic.ruleIsInvertible('with', 'r'), true);
    });
  });

  describe('tryIdentity', () => {
    it('should match identical atoms', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = generic.tryIdentity(s, 'R', -1);
      assert.ok(result?.success);
    });

    it('should fail for different atoms', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A], B);
      const result = generic.tryIdentity(s, 'R', -1);
      assert.strictEqual(result, null);
    });

    it('should return remaining delta', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A, B], A);
      const result = generic.tryIdentity(s, 'R', -1);
      assert.ok(result?.success);
      assert.ok(!Context.isEmpty(result.delta_out));
    });

    it('should work with left focus', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = generic.tryIdentity(s, 'L', 0);
      assert.ok(result?.success);
    });
  });

  describe('applyRule', () => {
    it('should apply tensor_l', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const s = seq([AST.tensor(A, B)], C);
      const result = generic.applyRule(s, 'L', 0, specs['tensor_l']);
      assert.ok(result?.success);
      assert.strictEqual(result.premises.length, 1);
    });

    it('should apply loli_r', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([], AST.loli(A, B));
      const result = generic.applyRule(s, 'R', -1, specs['loli_r']);
      assert.ok(result?.success);
      assert.strictEqual(result.premises.length, 1);
      // Premise should have A in linear context
      const premiseLinear = Seq.getContext(result.premises[0], 'linear');
      assert.ok(premiseLinear.includes(A));
    });

    it('should apply one_r (zero premises)', () => {
      const s = seq([], AST.one());
      const result = generic.applyRule(s, 'R', -1, specs['one_r']);
      assert.ok(result?.success);
      assert.strictEqual(result.premises.length, 0);
    });

    it('should return null for null spec', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = generic.applyRule(s, 'R', -1, null);
      assert.strictEqual(result, null);
    });
  });

  describe('applicableRules', () => {
    it('should find identity for A |- A', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const rules = generic.applicableRules(s, specs, alternatives);
      assert.ok(rules.some(r => r.ruleName === 'id'));
    });

    it('should find loli_r for |- A -o B', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([], AST.loli(A, B));
      const rules = generic.applicableRules(s, specs, alternatives);
      assert.ok(rules.some(r => r.ruleName === 'loli_r'));
    });

    it('should find tensor_l for A * B |- C', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const s = seq([AST.tensor(A, B)], C);
      const rules = generic.applicableRules(s, specs, alternatives);
      assert.ok(rules.some(r => r.ruleName === 'tensor_l'));
    });

    it('should find both left and right rules', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([AST.tensor(A, B)], AST.loli(A, B));
      const rules = generic.applicableRules(s, specs, alternatives);
      assert.ok(rules.some(r => r.position === 'L'));
      assert.ok(rules.some(r => r.position === 'R'));
    });

    it('should find alternatives (with_l1, with_l2)', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const C = AST.freevar('C');
      const s = seq([AST.with(A, B)], C);
      const rules = generic.applicableRules(s, specs, alternatives);
      const withRules = rules.filter(r => r.ruleName.startsWith('with_l'));
      assert.ok(withRules.length >= 2, `Expected at least 2 with_l rules, got ${withRules.length}`);
    });

    it('should find no rules for atoms only', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([A], B);
      const rules = generic.applicableRules(s, specs, alternatives);
      // Only identity-like rules (which won't match since A != B)
      assert.ok(!rules.some(r => r.ruleName === 'id'));
    });
  });

  describe('computeChildDelta', () => {
    it('should merge premise linear into delta', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const delta = Context.fromArray([A]);
      const premise = Seq.fromArrays([B], [], A);
      const result = generic.computeChildDelta(premise, delta);
      assert.ok(Context.has(result, A));
      assert.ok(Context.has(result, B));
    });

    it('should return same delta for empty premise linear', () => {
      const A = AST.freevar('A');
      const delta = Context.fromArray([A]);
      const premise = Seq.fromArrays([], [], A);
      const result = generic.computeChildDelta(premise, delta);
      assert.deepStrictEqual(result, delta);
    });
  });

  describe('addDeltaToSequent', () => {
    it('should add delta resources to linear context', () => {
      const A = AST.freevar('A');
      const B = AST.freevar('B');
      const s = seq([], A);
      const delta = Context.fromArray([B]);
      const result = generic.addDeltaToSequent(s, delta);
      const linear = Seq.getContext(result, 'linear');
      assert.ok(linear.includes(B));
    });

    it('should return same sequent for empty delta', () => {
      const A = AST.freevar('A');
      const s = seq([A], A);
      const result = generic.addDeltaToSequent(s, Context.empty());
      assert.strictEqual(result, s);
    });
  });
});

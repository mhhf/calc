/**
 * Tests for rule-interpreter: generic spec builder from rule ASTs
 *
 * Strategy:
 * A. Metadata equivalence (13 rules) - old specs baseline
 * B. makePremises equivalence (13 rules x concrete formulas) - old specs baseline
 * C. extraLinear equivalence (rules that have it) - old specs baseline
 * D. Integration: full proof search - old specs baseline
 * E. New interpreter: metadata match with old
 * F. New interpreter: makePremises match with old
 * G. New interpreter: extraLinear match with old
 * H. New interpreter: proof search integration
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/v2/calculus');
const { buildRuleSpecs } = require('../lib/v2/prover/focused/prover');
const { buildRuleSpecsFromAST } = require('../lib/v2/prover/rule-interpreter');
const Seq = require('../lib/v2/kernel/sequent');
const Store = require('../lib/v2/kernel/store');

describe('Rule Interpreter', () => {
  let calc, AST, oldSpecs, newResult, newSpecs;

  // Atoms for testing
  let p, q, r, s;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    oldSpecs = buildRuleSpecs(calc);
    newResult = buildRuleSpecsFromAST(calc);
    newSpecs = newResult.specs;

    p = AST.atom('p');
    q = AST.atom('q');
    r = AST.atom('r');
    s = AST.atom('s');
  });

  const mkSeq = (linear, succ) => Seq.fromArrays(linear, [], succ);
  const mkSeqCart = (linear, cart, succ) => Seq.fromArrays(linear, cart, succ);

  // Helper: compare premise sequents
  function assertSeqEqual(actual, expected, msg) {
    const aLin = Seq.getContext(actual, 'linear');
    const eLin = Seq.getContext(expected, 'linear');
    const aCart = Seq.getContext(actual, 'cartesian');
    const eCart = Seq.getContext(expected, 'cartesian');
    assert.deepStrictEqual(aLin, eLin, `${msg} linear context`);
    assert.deepStrictEqual(aCart, eCart, `${msg} cartesian context`);
    assert.strictEqual(actual.succedent, expected.succedent, `${msg} succedent`);
  }

  // Helper: compare two specs' premises for a given formula/seq
  function assertPremisesMatch(oldSpec, newSpec, formula, seq, idx, ruleName) {
    const oldP = oldSpec.makePremises(formula, seq, idx);
    const newP = newSpec.makePremises(formula, seq, idx);
    assert.strictEqual(oldP.length, newP.length, `${ruleName}: premise count`);
    for (let i = 0; i < oldP.length; i++) {
      assertSeqEqual(newP[i], oldP[i], `${ruleName} premise ${i}`);
    }
  }

  // =========================================================================
  // A. Metadata equivalence (old specs baseline)
  // =========================================================================
  describe('A. Old specs metadata', () => {
    const RULE_NAMES = [
      'tensor_r', 'tensor_l', 'loli_r', 'loli_l',
      'with_r', 'with_l1', 'with_l2',
      'one_r', 'one_l',
      'bang_r', 'bang_l',
      'absorption', 'copy'
    ];

    for (const name of RULE_NAMES) {
      it(`${name}: numPremises`, () => {
        assert.ok(oldSpecs[name], `spec ${name} exists`);
        assert.strictEqual(typeof oldSpecs[name].numPremises, 'number');
      });
    }

    it('tensor_r metadata', () => {
      const s = oldSpecs.tensor_r;
      assert.strictEqual(s.numPremises, 2);
      assert.strictEqual(s.copyContext, false);
      assert.strictEqual(s.requiresEmptyDelta, undefined);
      assert.strictEqual(s.structural, undefined);
    });

    it('with_r metadata', () => {
      const s = oldSpecs.with_r;
      assert.strictEqual(s.numPremises, 2);
      assert.strictEqual(s.copyContext, true);
    });

    it('bang_r metadata', () => {
      const s = oldSpecs.bang_r;
      assert.strictEqual(s.numPremises, 1);
      assert.strictEqual(s.requiresEmptyDelta, true);
    });

    it('absorption metadata', () => {
      const s = oldSpecs.absorption;
      assert.strictEqual(s.numPremises, 1);
      assert.strictEqual(s.movesToCartesian, true);
    });

    it('copy metadata', () => {
      const s = oldSpecs.copy;
      assert.strictEqual(s.numPremises, 1);
      assert.strictEqual(s.structural, true);
    });
  });

  // =========================================================================
  // B. Old specs makePremises baseline
  // =========================================================================
  describe('B. Old specs makePremises', () => {
    it('tensor_r: |- p * q => [] |- p, [] |- q', () => {
      const formula = AST.tensor(p, q);
      const seq = mkSeq([], formula);
      const premises = oldSpecs.tensor_r.makePremises(formula, seq, -1);
      assert.strictEqual(premises.length, 2);
      assertSeqEqual(premises[0], mkSeq([], p), 'premise 0');
      assertSeqEqual(premises[1], mkSeq([], q), 'premise 1');
    });

    it('tensor_l: p * q |- r => [p, q] |- r', () => {
      const formula = AST.tensor(p, q);
      const seq = mkSeq([formula], r);
      const premises = oldSpecs.tensor_l.makePremises(formula, seq, 0);
      assert.strictEqual(premises.length, 1);
      assertSeqEqual(premises[0], mkSeq([p, q], r), 'premise 0');
    });

    it('loli_l: p -o q |- r => [] |- p, [q] |- r', () => {
      const formula = AST.loli(p, q);
      const seq = mkSeq([formula], r);
      const premises = oldSpecs.loli_l.makePremises(formula, seq, 0);
      assert.strictEqual(premises.length, 2);
      assertSeqEqual(premises[0], mkSeq([], p), 'premise 0');
      assertSeqEqual(premises[1], mkSeq([q], r), 'premise 1');
    });

    it('absorption: !p |- r => []; [p] |- r', () => {
      const formula = AST.bang(p);
      const seq = mkSeq([formula], r);
      const premises = oldSpecs.absorption.makePremises(formula, seq, 0);
      assert.strictEqual(premises.length, 1);
      assertSeqEqual(premises[0], mkSeqCart([], [p], r), 'premise 0');
    });

    it('copy: G,p; [q] |- r => G,p; [q, p] |- r', () => {
      const formula = p;
      const seq = mkSeqCart([q], [formula], r);
      const premises = oldSpecs.copy.makePremises(formula, seq, -1);
      assert.strictEqual(premises.length, 1);
      assertSeqEqual(premises[0], mkSeqCart([q, formula], [formula], r), 'premise 0');
    });
  });

  // =========================================================================
  // C. Old specs extraLinear baseline
  // =========================================================================
  describe('C. Old specs extraLinear', () => {
    it('tensor_l.extraLinear(p * q) = [p, q]', () => {
      const formula = AST.tensor(p, q);
      assert.deepStrictEqual(oldSpecs.tensor_l.extraLinear(formula), [p, q]);
    });

    it('loli_r.extraLinear(p -o q) = [p]', () => {
      const formula = AST.loli(p, q);
      assert.deepStrictEqual(oldSpecs.loli_r.extraLinear(formula), [p]);
    });

    it('loli_l.extraLinear(p -o q, 0) = [], (p -o q, 1) = [q]', () => {
      const formula = AST.loli(p, q);
      assert.deepStrictEqual(oldSpecs.loli_l.extraLinear(formula, 0), []);
      assert.deepStrictEqual(oldSpecs.loli_l.extraLinear(formula, 1), [q]);
    });

    it('with_l1.extraLinear(p & q) = [p]', () => {
      const formula = AST.with(p, q);
      assert.deepStrictEqual(oldSpecs.with_l1.extraLinear(formula), [p]);
    });

    it('with_l2.extraLinear(p & q) = [q]', () => {
      const formula = AST.with(p, q);
      assert.deepStrictEqual(oldSpecs.with_l2.extraLinear(formula), [q]);
    });

    it('bang_l.extraLinear(!p) = [p]', () => {
      const formula = AST.bang(p);
      assert.deepStrictEqual(oldSpecs.bang_l.extraLinear(formula), [p]);
    });
  });

  // =========================================================================
  // D. Integration: proof search with old specs
  // =========================================================================
  describe('D. Old specs proof search', () => {
    let prover;

    before(() => {
      const { createProver } = require('../lib/v2/prover/focused/prover');
      prover = createProver(calc);
    });

    const testProvable = (desc, mkSequent) => {
      it(desc, () => {
        const seq = mkSequent();
        const result = prover.prove(seq, { rules: oldSpecs });
        assert.ok(result.success, `Expected provable: ${desc}`);
      });
    };

    const testNotProvable = (desc, mkSequent) => {
      it(desc, () => {
        const seq = mkSequent();
        const result = prover.prove(seq, { rules: oldSpecs });
        assert.ok(!result.success, `Expected not provable: ${desc}`);
      });
    };

    testProvable('A |- A', () => mkSeq([p], p));
    testProvable('A * B |- B * A', () => {
      const A = AST.atom('a'); const B = AST.atom('b');
      return mkSeq([AST.tensor(A, B)], AST.tensor(B, A));
    });
    testProvable('A -o B, A |- B', () => {
      const A = AST.atom('a'); const B = AST.atom('b');
      return mkSeq([AST.loli(A, B), A], B);
    });
    testProvable('A & B |- A', () => {
      const A = AST.atom('a'); const B = AST.atom('b');
      return mkSeq([AST.with(A, B)], A);
    });
    testProvable('I |- I', () => mkSeq([AST.one()], AST.one()));
    testProvable('|- I', () => mkSeq([], AST.one()));
    testProvable('A -o (B -o C) |- A * B -o C', () => {
      const A = AST.atom('a'); const B = AST.atom('b'); const C = AST.atom('c');
      return mkSeq(
        [AST.loli(A, AST.loli(B, C))],
        AST.loli(AST.tensor(A, B), C)
      );
    });
    testProvable('!A |- A', () => {
      const A = AST.atom('a');
      return mkSeq([AST.bang(A)], A);
    });
    testProvable('!A |- A & A', () => {
      const A = AST.atom('a');
      return mkSeq([AST.bang(A)], AST.with(A, A));
    });

    testNotProvable('A |- B (different atoms)', () => {
      return mkSeq([AST.atom('a')], AST.atom('b'));
    });
    testNotProvable('|- A (empty context)', () => {
      return mkSeq([], AST.atom('a'));
    });
  });

  // =========================================================================
  // E. New interpreter: all 13 specs exist with correct metadata
  // =========================================================================
  describe('E. New interpreter metadata', () => {
    const RULE_NAMES = [
      'tensor_r', 'tensor_l', 'loli_r', 'loli_l',
      'with_r', 'with_l1', 'with_l2',
      'one_r', 'one_l',
      'bang_r', 'bang_l',
      'absorption', 'copy'
    ];

    it('all 13 specs exist', () => {
      for (const name of RULE_NAMES) {
        assert.ok(newSpecs[name], `new spec ${name} exists`);
      }
    });

    for (const name of RULE_NAMES) {
      it(`${name}: numPremises matches`, () => {
        assert.strictEqual(newSpecs[name].numPremises, oldSpecs[name].numPremises,
          `${name} numPremises`);
      });

      it(`${name}: copyContext matches`, () => {
        assert.strictEqual(!!newSpecs[name].copyContext, !!oldSpecs[name].copyContext,
          `${name} copyContext`);
      });
    }

    it('bang_r: requiresEmptyDelta matches', () => {
      assert.strictEqual(!!newSpecs.bang_r.requiresEmptyDelta, true);
    });

    it('absorption: movesToCartesian matches', () => {
      assert.strictEqual(!!newSpecs.absorption.movesToCartesian, true);
    });

    it('copy: structural matches', () => {
      assert.strictEqual(!!newSpecs.copy.structural, true);
    });

    it('tensor_r: no requiresEmptyDelta', () => {
      assert.ok(!newSpecs.tensor_r.requiresEmptyDelta);
    });

    it('tensor_r: no structural', () => {
      assert.ok(!newSpecs.tensor_r.structural);
    });

    it('alternatives map includes absorption under bang_l', () => {
      assert.ok(newResult.alternatives.bang_l, 'bang_l alternatives exists');
      assert.ok(newResult.alternatives.bang_l.includes('absorption'),
        'absorption is bang_l alternative');
    });
  });

  // =========================================================================
  // F. New interpreter: makePremises matches old for all 13 rules
  // =========================================================================
  describe('F. New interpreter makePremises', () => {

    it('tensor_r', () => {
      const formula = AST.tensor(p, q);
      assertPremisesMatch(oldSpecs.tensor_r, newSpecs.tensor_r, formula, mkSeq([], formula), -1, 'tensor_r');
    });

    it('tensor_r with cartesian', () => {
      const formula = AST.tensor(p, q);
      const seq = mkSeqCart([], [r], formula);
      assertPremisesMatch(oldSpecs.tensor_r, newSpecs.tensor_r, formula, seq, -1, 'tensor_r+cart');
    });

    it('tensor_l', () => {
      const formula = AST.tensor(p, q);
      assertPremisesMatch(oldSpecs.tensor_l, newSpecs.tensor_l, formula, mkSeq([formula], r), 0, 'tensor_l');
    });

    it('loli_r', () => {
      const formula = AST.loli(p, q);
      assertPremisesMatch(oldSpecs.loli_r, newSpecs.loli_r, formula, mkSeq([], formula), -1, 'loli_r');
    });

    it('loli_l', () => {
      const formula = AST.loli(p, q);
      assertPremisesMatch(oldSpecs.loli_l, newSpecs.loli_l, formula, mkSeq([formula], r), 0, 'loli_l');
    });

    it('with_r', () => {
      const formula = AST.with(p, q);
      assertPremisesMatch(oldSpecs.with_r, newSpecs.with_r, formula, mkSeq([], formula), -1, 'with_r');
    });

    it('with_l1', () => {
      const formula = AST.with(p, q);
      assertPremisesMatch(oldSpecs.with_l1, newSpecs.with_l1, formula, mkSeq([formula], r), 0, 'with_l1');
    });

    it('with_l2', () => {
      const formula = AST.with(p, q);
      assertPremisesMatch(oldSpecs.with_l2, newSpecs.with_l2, formula, mkSeq([formula], r), 0, 'with_l2');
    });

    it('one_r', () => {
      const formula = AST.one();
      assertPremisesMatch(oldSpecs.one_r, newSpecs.one_r, formula, mkSeq([], formula), -1, 'one_r');
    });

    it('one_l', () => {
      const formula = AST.one();
      assertPremisesMatch(oldSpecs.one_l, newSpecs.one_l, formula, mkSeq([formula], r), 0, 'one_l');
    });

    it('bang_r', () => {
      const formula = AST.bang(p);
      assertPremisesMatch(oldSpecs.bang_r, newSpecs.bang_r, formula, mkSeq([], formula), -1, 'bang_r');
    });

    it('bang_l (dereliction)', () => {
      const formula = AST.bang(p);
      assertPremisesMatch(oldSpecs.bang_l, newSpecs.bang_l, formula, mkSeq([formula], r), 0, 'bang_l');
    });

    it('absorption', () => {
      const formula = AST.bang(p);
      assertPremisesMatch(oldSpecs.absorption, newSpecs.absorption, formula, mkSeq([formula], r), 0, 'absorption');
    });

    it('absorption with existing cartesian', () => {
      const formula = AST.bang(p);
      const seq = mkSeqCart([formula], [s], r);
      assertPremisesMatch(oldSpecs.absorption, newSpecs.absorption, formula, seq, 0, 'absorption+cart');
    });

    it('copy', () => {
      const formula = p;
      const seq = mkSeqCart([], [formula], r);
      assertPremisesMatch(oldSpecs.copy, newSpecs.copy, formula, seq, -1, 'copy');
    });

    it('copy with existing linear', () => {
      const formula = p;
      const seq = mkSeqCart([q], [formula], r);
      assertPremisesMatch(oldSpecs.copy, newSpecs.copy, formula, seq, -1, 'copy+lin');
    });
  });

  // =========================================================================
  // G. New interpreter: extraLinear matches old
  // =========================================================================
  describe('G. New interpreter extraLinear', () => {

    it('tensor_l.extraLinear matches', () => {
      const formula = AST.tensor(p, q);
      assert.deepStrictEqual(newSpecs.tensor_l.extraLinear(formula), oldSpecs.tensor_l.extraLinear(formula));
    });

    it('loli_r.extraLinear matches', () => {
      const formula = AST.loli(p, q);
      assert.deepStrictEqual(newSpecs.loli_r.extraLinear(formula), oldSpecs.loli_r.extraLinear(formula));
    });

    it('loli_l.extraLinear matches for each premise', () => {
      const formula = AST.loli(p, q);
      assert.deepStrictEqual(newSpecs.loli_l.extraLinear(formula, 0), oldSpecs.loli_l.extraLinear(formula, 0));
      assert.deepStrictEqual(newSpecs.loli_l.extraLinear(formula, 1), oldSpecs.loli_l.extraLinear(formula, 1));
    });

    it('with_l1.extraLinear matches', () => {
      const formula = AST.with(p, q);
      assert.deepStrictEqual(newSpecs.with_l1.extraLinear(formula), oldSpecs.with_l1.extraLinear(formula));
    });

    it('with_l2.extraLinear matches', () => {
      const formula = AST.with(p, q);
      assert.deepStrictEqual(newSpecs.with_l2.extraLinear(formula), oldSpecs.with_l2.extraLinear(formula));
    });

    it('bang_l.extraLinear matches', () => {
      const formula = AST.bang(p);
      assert.deepStrictEqual(newSpecs.bang_l.extraLinear(formula), oldSpecs.bang_l.extraLinear(formula));
    });

    it('rules without extraLinear match', () => {
      for (const name of ['tensor_r', 'with_r', 'one_r', 'one_l', 'bang_r', 'absorption', 'copy']) {
        assert.strictEqual(newSpecs[name].extraLinear, undefined,
          `new ${name} should not have extraLinear`);
      }
    });
  });

  // =========================================================================
  // H. New interpreter: proof search integration
  // =========================================================================
  describe('H. New interpreter proof search', () => {
    let prover;

    before(() => {
      const { createProver } = require('../lib/v2/prover/focused/prover');
      prover = createProver(calc);
    });

    const testProvable = (desc, mkSequent) => {
      it(desc, () => {
        const seq = mkSequent();
        const result = prover.prove(seq, { rules: newSpecs });
        assert.ok(result.success, `Expected provable: ${desc}`);
      });
    };

    const testNotProvable = (desc, mkSequent) => {
      it(desc, () => {
        const seq = mkSequent();
        const result = prover.prove(seq, { rules: newSpecs });
        assert.ok(!result.success, `Expected not provable: ${desc}`);
      });
    };

    testProvable('A |- A', () => mkSeq([p], p));
    testProvable('A * B |- B * A', () => {
      const A = AST.atom('a'); const B = AST.atom('b');
      return mkSeq([AST.tensor(A, B)], AST.tensor(B, A));
    });
    testProvable('A -o B, A |- B', () => {
      const A = AST.atom('a'); const B = AST.atom('b');
      return mkSeq([AST.loli(A, B), A], B);
    });
    testProvable('A & B |- A', () => {
      const A = AST.atom('a'); const B = AST.atom('b');
      return mkSeq([AST.with(A, B)], A);
    });
    testProvable('I |- I', () => mkSeq([AST.one()], AST.one()));
    testProvable('|- I', () => mkSeq([], AST.one()));
    testProvable('A -o (B -o C) |- A * B -o C', () => {
      const A = AST.atom('a'); const B = AST.atom('b'); const C = AST.atom('c');
      return mkSeq(
        [AST.loli(A, AST.loli(B, C))],
        AST.loli(AST.tensor(A, B), C)
      );
    });
    testProvable('!A |- A', () => {
      const A = AST.atom('a');
      return mkSeq([AST.bang(A)], A);
    });
    testProvable('!A |- A & A', () => {
      const A = AST.atom('a');
      return mkSeq([AST.bang(A)], AST.with(A, A));
    });

    testNotProvable('A |- B (different atoms)', () => {
      return mkSeq([AST.atom('a')], AST.atom('b'));
    });
    testNotProvable('|- A (empty context)', () => {
      return mkSeq([], AST.atom('a'));
    });
  });
});

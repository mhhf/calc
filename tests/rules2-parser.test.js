/**
 * Tests for .rules2 parser: exhaustive equivalence against .rules pipeline
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/v2/calculus');
const { buildRuleSpecs } = require('../lib/v2/prover/rule-interpreter');
const Seq = require('../lib/v2/kernel/sequent');

describe('.rules2 parser', () => {
  let oldCalc, newCalc;

  before(async () => {
    oldCalc = await calculus.loadILL();
    calculus.clearCache();
    newCalc = await calculus.loadILL2();
  });

  // =========================================================================
  // A. All 14 rules exist
  // =========================================================================
  describe('A. Rule set completeness', () => {
    it('same rule names', () => {
      const oldNames = Object.keys(oldCalc.rules).sort();
      const newNames = Object.keys(newCalc.rules).sort();
      assert.deepStrictEqual(newNames, oldNames);
    });

    it('all 14 rules present', () => {
      assert.strictEqual(Object.keys(newCalc.rules).length, 14);
    });
  });

  // =========================================================================
  // B. Per-rule descriptor equivalence
  // =========================================================================
  describe('B. Descriptor equivalence', () => {
    const RULES = [
      'id', 'tensor_r', 'tensor_l', 'loli_r', 'loli_l',
      'with_r', 'with_l1', 'with_l2',
      'one_r', 'one_l',
      'promotion', 'dereliction', 'absorption', 'copy'
    ];

    for (const name of RULES) {
      it(`${name}: descriptor matches`, () => {
        assert.deepStrictEqual(
          newCalc.rules[name].descriptor,
          oldCalc.rules[name].descriptor
        );
      });
    }
  });

  // =========================================================================
  // C. Per-rule metadata match
  // =========================================================================
  describe('C. Metadata equivalence', () => {
    const FIELDS = ['pretty', 'structural', 'numPremises', 'invertible', 'bridge'];
    const RULES = [
      'id', 'tensor_r', 'tensor_l', 'loli_r', 'loli_l',
      'with_r', 'with_l1', 'with_l2',
      'one_r', 'one_l',
      'promotion', 'dereliction', 'absorption', 'copy'
    ];

    for (const name of RULES) {
      it(`${name}: all metadata fields match`, () => {
        for (const field of FIELDS) {
          assert.deepStrictEqual(
            newCalc.rules[name][field],
            oldCalc.rules[name][field],
            `${name}.${field}`
          );
        }
      });
    }
  });

  // =========================================================================
  // D. Full calculus equivalence
  // =========================================================================
  describe('D. Calculus-level equivalence', () => {
    it('polarity map matches', () => {
      assert.deepStrictEqual(newCalc.polarity, oldCalc.polarity);
    });

    it('invertibility map matches', () => {
      assert.deepStrictEqual(newCalc.invertible, oldCalc.invertible);
    });
  });

  // =========================================================================
  // E. Proof search integration
  // =========================================================================
  describe('E. Proof search with rules2-sourced calculus', () => {
    let AST, specs, alternatives, prover;

    before(() => {
      AST = newCalc.AST;
      const result = buildRuleSpecs(newCalc);
      specs = result.specs;
      alternatives = result.alternatives;
      const { createProver } = require('../lib/v2/prover/focused/prover');
      prover = createProver(newCalc);
    });

    const mkSeq = (linear, succ) => Seq.fromArrays(linear, [], succ);

    const provable = (desc, mk) => it(desc, () => {
      assert.ok(prover.prove(mk(), { rules: specs, alternatives }).success, desc);
    });
    const unprovable = (desc, mk) => it(desc, () => {
      assert.ok(!prover.prove(mk(), { rules: specs, alternatives }).success, desc);
    });

    provable('A |- A', () => {
      const a = AST.atom('a');
      return mkSeq([a], a);
    });
    provable('A * B |- B * A', () => {
      const a = AST.atom('a'), b = AST.atom('b');
      return mkSeq([AST.tensor(a, b)], AST.tensor(b, a));
    });
    provable('A -o B, A |- B', () => {
      const a = AST.atom('a'), b = AST.atom('b');
      return mkSeq([AST.loli(a, b), a], b);
    });
    provable('A & B |- A', () => {
      const a = AST.atom('a'), b = AST.atom('b');
      return mkSeq([AST.with(a, b)], a);
    });
    provable('I |- I', () => mkSeq([AST.one()], AST.one()));
    provable('|- I', () => mkSeq([], AST.one()));
    provable('A -o (B -o C) |- A * B -o C', () => {
      const a = AST.atom('a'), b = AST.atom('b'), c = AST.atom('c');
      return mkSeq([AST.loli(a, AST.loli(b, c))], AST.loli(AST.tensor(a, b), c));
    });
    provable('!A |- A', () => mkSeq([AST.bang(AST.atom('a'))], AST.atom('a')));
    provable('!A |- A & A', () => {
      const a = AST.atom('a');
      return mkSeq([AST.bang(a)], AST.with(a, a));
    });

    unprovable('A |- B', () => mkSeq([AST.atom('a')], AST.atom('b')));
    unprovable('|- A', () => mkSeq([], AST.atom('a')));
  });
});

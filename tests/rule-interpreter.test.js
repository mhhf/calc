/**
 * Tests for rule-interpreter: generic spec builder from rule ASTs
 *
 * A. All 13 specs exist with correct metadata
 * B. makePremises produces correct premise sequents
 * C. Integration: full proof search with generated specs
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/v2/calculus');
const { buildRuleSpecs } = require('../lib/v2/prover/rule-interpreter');
const Seq = require('../lib/v2/kernel/sequent');
const Store = require('../lib/v2/kernel/store');

describe('Rule Interpreter', () => {
  let calc, AST, result, specs;
  let p, q, r, s;

  before(async () => {
    calc = await calculus.loadILL();
    AST = calc.AST;
    result = buildRuleSpecs(calc);
    specs = result.specs;

    p = AST.atom('p');
    q = AST.atom('q');
    r = AST.atom('r');
    s = AST.atom('s');
  });

  const mkSeq = (linear, succ) => Seq.fromArrays(linear, [], succ);
  const mkSeqCart = (linear, cart, succ) => Seq.fromArrays(linear, cart, succ);

  function assertSeqEqual(actual, expected, msg) {
    assert.deepStrictEqual(Seq.getContext(actual, 'linear'), Seq.getContext(expected, 'linear'), `${msg} linear`);
    assert.deepStrictEqual(Seq.getContext(actual, 'cartesian'), Seq.getContext(expected, 'cartesian'), `${msg} cartesian`);
    assert.strictEqual(actual.succedent, expected.succedent, `${msg} succedent`);
  }

  // =========================================================================
  // A. Metadata
  // =========================================================================
  describe('A. Metadata', () => {
    const ALL = [
      'tensor_r', 'tensor_l', 'loli_r', 'loli_l',
      'with_r', 'with_l1', 'with_l2',
      'one_r', 'one_l',
      'bang_r', 'bang_l',
      'absorption', 'copy'
    ];

    it('all 13 specs exist', () => {
      for (const name of ALL)
        assert.ok(specs[name], `spec ${name} exists`);
    });

    it('copyContext: only with_r copies', () => {
      assert.strictEqual(specs.with_r.copyContext, true);
      for (const name of ALL.filter(n => n !== 'with_r'))
        assert.strictEqual(specs[name].copyContext, false, name);
    });

    it('bang_r requires empty delta', () => {
      assert.strictEqual(specs.bang_r.requiresEmptyDelta, true);
      assert.ok(!specs.tensor_r.requiresEmptyDelta);
    });

    it('contextSplit for context-splitting rules', () => {
      assert.strictEqual(specs.tensor_r.contextSplit, true);
      assert.strictEqual(specs.loli_l.contextSplit, true);
      assert.ok(!specs.with_r.contextSplit);
      assert.ok(!specs.tensor_l.contextSplit);
    });

    it('alternatives map: bang_l → [absorption]', () => {
      assert.ok(result.alternatives.bang_l);
      assert.ok(result.alternatives.bang_l.includes('absorption'));
    });

    it('alternatives map: with_l → [with_l1, with_l2]', () => {
      assert.ok(result.alternatives.with_l);
      assert.ok(result.alternatives.with_l.includes('with_l1'));
      assert.ok(result.alternatives.with_l.includes('with_l2'));
    });
  });

  // =========================================================================
  // B. makePremises
  // =========================================================================
  describe('B. makePremises', () => {

    it('tensor_r: |- p * q → |- p, |- q', () => {
      const f = AST.tensor(p, q);
      const premises = specs.tensor_r.makePremises(f, mkSeq([], f), -1);
      assert.strictEqual(premises.length, 2);
      assertSeqEqual(premises[0], mkSeq([], p), 'p0');
      assertSeqEqual(premises[1], mkSeq([], q), 'p1');
    });

    it('tensor_r preserves cartesian', () => {
      const f = AST.tensor(p, q);
      const premises = specs.tensor_r.makePremises(f, mkSeqCart([], [r], f), -1);
      assertSeqEqual(premises[0], mkSeqCart([], [r], p), 'p0');
      assertSeqEqual(premises[1], mkSeqCart([], [r], q), 'p1');
    });

    it('tensor_l: p * q |- r → p, q |- r', () => {
      const f = AST.tensor(p, q);
      const premises = specs.tensor_l.makePremises(f, mkSeq([f], r), 0);
      assert.strictEqual(premises.length, 1);
      assertSeqEqual(premises[0], mkSeq([p, q], r), 'p0');
    });

    it('loli_r: |- p -o q → p |- q', () => {
      const f = AST.loli(p, q);
      const premises = specs.loli_r.makePremises(f, mkSeq([], f), -1);
      assert.strictEqual(premises.length, 1);
      assertSeqEqual(premises[0], mkSeq([p], q), 'p0');
    });

    it('loli_l: p -o q |- r → |- p, q |- r', () => {
      const f = AST.loli(p, q);
      const premises = specs.loli_l.makePremises(f, mkSeq([f], r), 0);
      assert.strictEqual(premises.length, 2);
      assertSeqEqual(premises[0], mkSeq([], p), 'p0');
      assertSeqEqual(premises[1], mkSeq([q], r), 'p1');
    });

    it('with_r: |- p & q → |- p, |- q', () => {
      const f = AST.with(p, q);
      const premises = specs.with_r.makePremises(f, mkSeq([], f), -1);
      assert.strictEqual(premises.length, 2);
      assertSeqEqual(premises[0], mkSeq([], p), 'p0');
      assertSeqEqual(premises[1], mkSeq([], q), 'p1');
    });

    it('with_l1: p & q |- r → p |- r', () => {
      const f = AST.with(p, q);
      const premises = specs.with_l1.makePremises(f, mkSeq([f], r), 0);
      assertSeqEqual(premises[0], mkSeq([p], r), 'p0');
    });

    it('with_l2: p & q |- r → q |- r', () => {
      const f = AST.with(p, q);
      const premises = specs.with_l2.makePremises(f, mkSeq([f], r), 0);
      assertSeqEqual(premises[0], mkSeq([q], r), 'p0');
    });

    it('one_r: |- 1 → (no premises)', () => {
      assert.deepStrictEqual(specs.one_r.makePremises(AST.one(), mkSeq([], AST.one()), -1), []);
    });

    it('one_l: 1 |- r → |- r', () => {
      const f = AST.one();
      const premises = specs.one_l.makePremises(f, mkSeq([f], r), 0);
      assertSeqEqual(premises[0], mkSeq([], r), 'p0');
    });

    it('bang_r (promotion): |- !p → |- p', () => {
      const f = AST.bang(p);
      const premises = specs.bang_r.makePremises(f, mkSeq([], f), -1);
      assertSeqEqual(premises[0], mkSeq([], p), 'p0');
    });

    it('bang_l (dereliction): !p |- r → p |- r', () => {
      const f = AST.bang(p);
      const premises = specs.bang_l.makePremises(f, mkSeq([f], r), 0);
      assertSeqEqual(premises[0], mkSeq([p], r), 'p0');
    });

    it('absorption: !p |- r → ; p |- r', () => {
      const f = AST.bang(p);
      const premises = specs.absorption.makePremises(f, mkSeq([f], r), 0);
      assertSeqEqual(premises[0], mkSeqCart([], [p], r), 'p0');
    });

    it('absorption preserves existing cartesian', () => {
      const f = AST.bang(p);
      const premises = specs.absorption.makePremises(f, mkSeqCart([f], [s], r), 0);
      assertSeqEqual(premises[0], mkSeqCart([], [s, p], r), 'p0');
    });

    it('copy: G,p; |- r → G,p; p |- r', () => {
      const premises = specs.copy.makePremises(p, mkSeqCart([], [p], r), -1);
      assertSeqEqual(premises[0], mkSeqCart([p], [p], r), 'p0');
    });

    it('copy with existing linear: G,p; q |- r → G,p; q, p |- r', () => {
      const premises = specs.copy.makePremises(p, mkSeqCart([q], [p], r), -1);
      assertSeqEqual(premises[0], mkSeqCart([q, p], [p], r), 'p0');
    });
  });

  // =========================================================================
  // C. Integration — proof search
  // =========================================================================
  describe('D. Proof search', () => {
    let prover;

    before(() => {
      const { createProver } = require('../lib/v2/prover/focused/prover');
      prover = createProver(calc);
    });

    const provable = (desc, mk) => it(desc, () => {
      assert.ok(prover.prove(mk(), { rules: specs, alternatives: result.alternatives }).success, desc);
    });
    const unprovable = (desc, mk) => it(desc, () => {
      assert.ok(!prover.prove(mk(), { rules: specs, alternatives: result.alternatives }).success, desc);
    });

    provable('A |- A', () => mkSeq([p], p));
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

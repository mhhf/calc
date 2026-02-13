/**
 * Tests for .rules2 parser: proof search integration
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/v2/calculus');
const { buildRuleSpecs } = require('../lib/v2/prover/rule-interpreter');
const Seq = require('../lib/v2/kernel/sequent');

describe('.rules2 parser', () => {
  describe('Proof search integration', () => {
    let AST, specs, alternatives, prover;

    before(async () => {
      const calc = await calculus.loadILL();
      AST = calc.AST;
      const result = buildRuleSpecs(calc);
      specs = result.specs;
      alternatives = result.alternatives;
      const { createProver } = require('../lib/v2/prover/focused');
      prover = createProver(calc);
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

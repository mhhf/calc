/**
 * Tests for .rules2 parser: proof search integration + direct parser tests
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const calculus = require('../lib/calculus');
const { buildRuleSpecs } = require('../lib/prover/rule-interpreter');
const Seq = require('../lib/kernel/sequent');
const Store = require('../lib/kernel/store');
const { GRADE_W } = require('../lib/engine/grades');

describe('.rules2 parser', () => {
  describe('Proof search integration', () => {
    let AST, specs, alternatives, prover;

    before(async () => {
      const calc = await calculus.loadILL();
      AST = calc.AST;
      const result = buildRuleSpecs(calc);
      specs = result.specs;
      alternatives = result.alternatives;
      const { createProver } = require('../lib/prover/focused');
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
    provable('!A |- A', () => mkSeq([AST.bang(GRADE_W,AST.atom('a'))], AST.atom('a')));
    provable('!A |- A & A', () => {
      const a = AST.atom('a');
      return mkSeq([AST.bang(GRADE_W,a)], AST.with(a, a));
    });

    unprovable('A |- B', () => mkSeq([AST.atom('a')], AST.atom('b')));
    unprovable('|- A', () => mkSeq([], AST.atom('a')));
  });

  describe('Direct parser — rule blocks → flat descriptors', () => {
    let parseRules2, parse;

    before(async () => {
      const calc = await calculus.loadILL();
      parse = (s) => calc.parse(s);
      ({ parseRules2 } = require('../lib/rules/rules2-parser'));
    });

    // Note: .rules2 format uses '.' ONLY to terminate the whole block.
    // Premise lines do NOT end with '.'. The block terminator is '.\n'.

    it('parses simple right rule', () => {
      const text = `@formulas A, B
tensor_r: G ; D |- A * B
  <- G ; D' |- A
  <- G ; D'' |- B.
`;
      const rules = parseRules2(text, parse);
      assert.ok(rules.tensor_r);
      assert.equal(rules.tensor_r.name, 'tensor_r');
      assert.equal(rules.tensor_r.descriptor.connective, 'tensor');
      assert.equal(rules.tensor_r.descriptor.side, 'r');
      assert.equal(rules.tensor_r.descriptor.arity, 2);
      assert.equal(rules.tensor_r.numPremises, 2);
    });

    it('detects context split', () => {
      const text = `@formulas A, B
tensor_r: G ; D |- A * B
  <- G ; D' |- A
  <- G ; D'' |- B.
`;
      const rules = parseRules2(text, parse);
      assert.equal(rules.tensor_r.descriptor.contextSplit, true);
      assert.equal(rules.tensor_r.descriptor.contextFlow, 'split');
    });

    it('detects preserved context (single premise)', () => {
      const text = `@formulas A, B
loli_r: G ; D |- A -o B
  <- G ; D, A |- B.
`;
      const rules = parseRules2(text, parse);
      assert.equal(rules.loli_r.descriptor.contextFlow, 'preserved');
      assert.equal(rules.loli_r.descriptor.side, 'r');
    });

    it('detects left rule principal', () => {
      const text = `@formulas A, B
tensor_l: G ; D, A * B |- C
  <- G ; D, A, B |- C.
`;
      const rules = parseRules2(text, parse);
      assert.equal(rules.tensor_l.descriptor.side, 'l');
      assert.equal(rules.tensor_l.descriptor.connective, 'tensor');
    });

    it('parses zero-premise axiom', () => {
      const text = `@formulas A
one_r: G ; |- I.
`;
      const rules = parseRules2(text, parse);
      assert.equal(rules.one_r.descriptor.contextFlow, 'empty');
      assert.equal(rules.one_r.numPremises, 0);
    });

    it('parses annotations', () => {
      const text = `@formulas A, B
tensor_r: G ; D |- A * B
  <- G ; D' |- A
  <- G ; D'' |- B
  @invertible false
  @pretty "⊗R".
`;
      const rules = parseRules2(text, parse);
      assert.equal(rules.tensor_r.invertible, false);
      assert.equal(rules.tensor_r.pretty, '⊗R');
    });

    it('requires @formulas directive', () => {
      assert.throws(() => parseRules2('no_directive: |- A.', parse), /@formulas directive required/);
    });

    it('parses copy context (all vars in all premises)', () => {
      const text = `@formulas A, B
with_r: G ; D |- A & B
  <- G ; D |- A
  <- G ; D |- B.
`;
      const rules = parseRules2(text, parse);
      assert.equal(rules.with_r.descriptor.contextFlow, 'copy');
      assert.equal(rules.with_r.descriptor.copyContext, true);
    });
  });
});

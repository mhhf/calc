/**
 * Tests for .rules2 parser: proof search integration + direct parser tests
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import calculus from '../lib/calculus/index.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import Seq from '../lib/kernel/sequent.js';
import Store from '../lib/kernel/store.js';
import { gradeW } from '../lib/engine/grades.js';
// Hoisted by tools/esm-hoist.js:
import { createProver } from '../lib/prover/focused.js';
import { parseRules2 as _parseRules2 } from '../lib/rules/rules2-parser.js';
import { loadILL } from '../calculus/ill/index.js';

describe('.rules2 parser', () => {
  describe('Proof search integration', () => {
    let AST, specs, alternatives, prover;

    before(async () => {
      const calc = await loadILL();
      AST = calc.AST;
      const result = buildRuleSpecs(calc);
      specs = result.specs;
      alternatives = result.alternatives;

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
    provable('!A |- A', () => mkSeq([AST.bang(gradeW(),AST.atom('a'))], AST.atom('a')));
    provable('!A |- A & A', () => {
      const a = AST.atom('a');
      return mkSeq([AST.bang(gradeW(),a)], AST.with(a, a));
    });

    unprovable('A |- B', () => mkSeq([AST.atom('a')], AST.atom('b')));
    unprovable('|- A', () => mkSeq([], AST.atom('a')));
  });

  describe('Direct parser — rule blocks → flat descriptors', () => {
    let parseRules2, parse;

    before(async () => {
      const calc = await loadILL();
      parse = (s) => calc.parse(s);
      parseRules2 = _parseRules2;
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

    it('a sequent without a |- turnstile is a clear error, not a bare TypeError (TODO_0272 MINOR 3)', () => {
      const text = `@formulas A\nbad: G ; D A.\n`;
      assert.throws(() => parseRules2(text, parse), /Malformed sequent.*turnstile/);
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

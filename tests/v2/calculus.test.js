/**
 * Tests for v2 Calculus loader
 *
 * Verifies that parser/AST/renderer are GENERATED from spec files,
 * not hardcoded.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calculus = require('../../lib/v2/calculus');

describe('v2 Calculus (generated from spec)', () => {
  let ill;

  before(async () => {
    ill = await calculus.loadILL();
  });

  describe('loading', () => {
    it('should load calculus name from @family directive', () => {
      assert.strictEqual(ill.name, 'lnl');
    });

    it('should load constructors from spec', () => {
      assert.ok(ill.constructors.tensor, 'tensor should be loaded');
      assert.ok(ill.constructors.loli, 'loli should be loaded');
      assert.ok(ill.constructors.bang, 'bang should be loaded');
      assert.ok(ill.constructors.with, 'with should be loaded');
      assert.ok(ill.constructors.one, 'one should be loaded');
      assert.ok(ill.constructors.atom, 'atom should be loaded');
    });

    it('should preserve annotations', () => {
      const tensor = ill.constructors.tensor;
      assert.strictEqual(tensor.annotations.ascii, '_ * _');
      // @polarity removed - now inferred
      assert.strictEqual(tensor.annotations.category, 'multiplicative');
    });

    it('should inherit from lnl.family via @extends', () => {
      assert.ok(ill.constructors.seq, 'seq should be inherited from lnl.family');
      assert.ok(ill.constructors.hyp, 'hyp should be inherited');
      assert.ok(ill.constructors.comma, 'comma should be inherited');
      assert.ok(ill.constructors.empty, 'empty should be inherited');
    });
  });

  describe('AST constructors', () => {
    it('should generate tensor constructor', () => {
      const A = ill.AST.freevar('A');
      const B = ill.AST.freevar('B');
      const t = ill.AST.tensor(A, B);
      assert.strictEqual(t.tag, 'tensor');
      assert.strictEqual(t.children.length, 2);
    });

    it('should generate nullary constructors', () => {
      const one = ill.AST.one();
      assert.strictEqual(one.tag, 'one');
      assert.strictEqual(one.children.length, 0);
    });

    it('should generate unary constructors', () => {
      const A = ill.AST.freevar('A');
      const bangA = ill.AST.bang(A);
      assert.strictEqual(bangA.tag, 'bang');
      assert.strictEqual(bangA.children.length, 1);
    });

    it('should generate sequent constructor from family', () => {
      const G = ill.AST.empty();
      const D = ill.AST.freevar('D');
      const C = ill.AST.freevar('C');
      const s = ill.AST.seq(G, D, C);
      assert.strictEqual(s.tag, 'seq');
      assert.strictEqual(s.children.length, 3);
    });
  });

  describe('parser (generated)', () => {
    it('should parse atoms', () => {
      const ast = ill.parse('p');
      assert.strictEqual(ast.tag, 'atom');
      assert.strictEqual(ast.children[0], 'p');
    });

    it('should parse freevars', () => {
      const ast = ill.parse('A');
      assert.strictEqual(ast.tag, 'freevar');
      assert.strictEqual(ast.children[0], 'A');
    });

    it('should parse tensor from @ascii "_ * _"', () => {
      const ast = ill.parse('A * B');
      assert.strictEqual(ast.tag, 'tensor');
    });

    it('should parse loli from @ascii "_ -o _"', () => {
      const ast = ill.parse('A -o B');
      assert.strictEqual(ast.tag, 'loli');
    });

    it('should parse with from @ascii "_ & _"', () => {
      const ast = ill.parse('A & B');
      assert.strictEqual(ast.tag, 'with');
    });

    it('should parse bang from @ascii "! _"', () => {
      const ast = ill.parse('!A');
      assert.strictEqual(ast.tag, 'bang');
    });

    it('should parse one from @ascii "I"', () => {
      const ast = ill.parse('I');
      assert.strictEqual(ast.tag, 'one');
    });

    it('should respect precedence from @prec', () => {
      // tensor (60) binds tighter than loli (50)
      // "A * B -o C" should be "(A * B) -o C"
      const ast = ill.parse('A * B -o C');
      assert.strictEqual(ast.tag, 'loli');
      assert.strictEqual(ast.children[0].tag, 'tensor');
    });

    it('should handle parentheses', () => {
      const ast = ill.parse('A * (B -o C)');
      assert.strictEqual(ast.tag, 'tensor');
      assert.strictEqual(ast.children[1].tag, 'loli');
    });

    it('should handle complex formulas', () => {
      const ast = ill.parse('!A * B -o C & D');
      // Precedence: ! (80) > * (60) > -o (50) > & (70)
      // Actually & is 70 > -o 50, so it's (!A * B) -o (C & D)
      assert.strictEqual(ast.tag, 'loli');
    });
  });

  describe('renderer (generated)', () => {
    it('should render with @ascii template', () => {
      const ast = ill.AST.tensor(ill.AST.freevar('A'), ill.AST.freevar('B'));
      const str = ill.render(ast, 'ascii');
      assert.strictEqual(str, 'A * B');
    });

    it('should render with @latex template', () => {
      const ast = ill.AST.tensor(ill.AST.freevar('A'), ill.AST.freevar('B'));
      const str = ill.render(ast, 'latex');
      assert.strictEqual(str, 'A \\otimes B');
    });

    it('should render bang correctly', () => {
      const ast = ill.AST.bang(ill.AST.freevar('A'));
      assert.strictEqual(ill.render(ast, 'ascii'), '! A');
    });

    it('should render nullary correctly', () => {
      const ast = ill.AST.one();
      assert.strictEqual(ill.render(ast, 'ascii'), 'I');
    });
  });

  describe('roundtrip', () => {
    it('should parse and render to same AST', () => {
      // Test that parse(render(ast)) === ast
      const formulas = ['A', 'A * B', 'A -o B', '!A', 'I'];
      for (const formula of formulas) {
        const ast1 = ill.parse(formula);
        const rendered = ill.render(ast1, 'ascii');
        const ast2 = ill.parse(rendered);
        // Compare AST structure (normalized)
        assert.strictEqual(JSON.stringify(ast1), JSON.stringify(ast2),
          `Roundtrip failed for: ${formula} -> ${rendered}`);
      }
    });
  });
});

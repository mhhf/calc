/**
 * Tests for v2 AST utilities
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const ast = require('../lib/kernel/ast');
const calculus = require('../lib/calculus');

describe('v2 AST utilities', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('freeVars', () => {
    it('should extract free variable from freevar', () => {
      const f = AST.freevar('A');
      const vars = ast.freeVars(f);
      assert.deepStrictEqual(vars, ['A']);
    });

    it('should extract multiple free variables', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const vars = ast.freeVars(f);
      assert.deepStrictEqual(vars.sort(), ['A', 'B']);
    });

    it('should return unique variables', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('A'));
      const vars = ast.freeVars(f);
      assert.deepStrictEqual(vars, ['A']);
    });

    it('should extract from nested formulas', () => {
      const f = AST.loli(
        AST.tensor(AST.freevar('A'), AST.freevar('B')),
        AST.freevar('C')
      );
      const vars = ast.freeVars(f);
      assert.deepStrictEqual(vars.sort(), ['A', 'B', 'C']);
    });

    it('should return empty for nullary', () => {
      const f = AST.one();
      const vars = ast.freeVars(f);
      assert.deepStrictEqual(vars, []);
    });

    it('should return empty for atom', () => {
      const f = AST.atom('p');
      const vars = ast.freeVars(f);
      assert.deepStrictEqual(vars, []);
    });
  });

  describe('isAtomic', () => {
    it('should return true for atom', () => {
      const f = AST.atom('p');
      assert.strictEqual(ast.isAtomic(f), true);
    });

    it('should return true for freevar', () => {
      const f = AST.freevar('A');
      assert.strictEqual(ast.isAtomic(f), true);
    });

    it('should return false for tensor', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(ast.isAtomic(f), false);
    });

    it('should return false for bang', () => {
      const f = AST.bang(AST.freevar('A'));
      assert.strictEqual(ast.isAtomic(f), false);
    });

    it('should return false for one', () => {
      const f = AST.one();
      assert.strictEqual(ast.isAtomic(f), false);
    });
  });

  describe('connective', () => {
    it('should return tag for formula', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(ast.connective(f), 'tensor');
    });

    it('should return atom for atom', () => {
      const f = AST.atom('p');
      assert.strictEqual(ast.connective(f), 'atom');
    });

    it('should return freevar for freevar', () => {
      const f = AST.freevar('A');
      assert.strictEqual(ast.connective(f), 'freevar');
    });
  });

  describe('copy', () => {
    it('should copy AST (identity for content-addressed terms)', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const f2 = ast.copy(f);
      // Content-addressed: copy is identity (same hash = same immutable term)
      assert.strictEqual(f, f2);
      assert.strictEqual(ast.eq(f, f2), true);
    });

    it('should preserve structure', () => {
      const f = AST.loli(AST.tensor(AST.freevar('A'), AST.freevar('B')), AST.freevar('C'));
      const f2 = ast.copy(f);
      // Content-addressed: use ast.tag/ast.children to inspect structure
      assert.strictEqual(ast.tag(f2), 'loli');
      assert.strictEqual(ast.tag(ast.children(f2)[0]), 'tensor');
      assert.strictEqual(ast.tag(ast.children(f2)[1]), 'freevar');
    });
  });

  describe('eq', () => {
    it('should return true for equal ASTs', () => {
      const f1 = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const f2 = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(ast.eq(f1, f2), true);
    });

    it('should return false for different ASTs', () => {
      const f1 = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const f2 = AST.tensor(AST.freevar('B'), AST.freevar('A'));
      assert.strictEqual(ast.eq(f1, f2), false);
    });
  });

  describe('hash', () => {
    it('should return same hash for equal ASTs', () => {
      const f1 = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const f2 = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(ast.hash(f1), ast.hash(f2));
    });

    it('should return different hash for different ASTs', () => {
      const f1 = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const f2 = AST.loli(AST.freevar('A'), AST.freevar('B'));
      assert.notStrictEqual(ast.hash(f1), ast.hash(f2));
    });
  });

  describe('mapChildren', () => {
    it('should map over children', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      // Content-addressed: children are hashes, use ast.tag/ast.children to inspect
      const f2 = ast.mapChildren(f, c => {
        if (ast.tag(c) === 'freevar' && ast.children(c)[0] === 'A') {
          return AST.freevar('X');
        }
        return c;
      });
      assert.strictEqual(ast.children(ast.children(f2)[0])[0], 'X');
      assert.strictEqual(ast.children(ast.children(f2)[1])[0], 'B');
    });

    it('should return same object if no change', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const f2 = ast.mapChildren(f, c => c);
      assert.strictEqual(f, f2);
    });
  });

  describe('fold', () => {
    it('should fold over AST', () => {
      const f = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const count = ast.fold(f, (acc, node) => acc + 1, 0);
      assert.strictEqual(count, 3); // tensor, freevar(A), freevar(B)
    });
  });
});

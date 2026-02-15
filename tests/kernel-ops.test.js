/**
 * Tests for v2 Kernel (substitute, unify)
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const calculus = require('../lib/calculus');
const Store = require('../lib/kernel/store');
const { sub, apply, eq, copy, occurs } = require('../lib/kernel/substitute');
const { unify, match, isVar } = require('../lib/kernel/unify');

describe('v2 Kernel', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('sub', () => {
    it('should substitute variable', () => {
      const result = sub(AST.freevar('A'), AST.freevar('A'), AST.atom('p'));
      // ASTs are now hashes - use Store.tag to inspect
      assert.strictEqual(Store.tag(result), 'atom');
    });

    it('should not mutate original', () => {
      const ast = AST.freevar('A');
      sub(ast, AST.freevar('A'), AST.atom('p'));
      // Original hash unchanged (immutable by nature)
      assert.strictEqual(Store.tag(ast), 'freevar');
    });

    it('should substitute in nested AST', () => {
      const ast = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const result = sub(ast, AST.freevar('A'), AST.atom('p'));
      // Children are also hashes - use Store to inspect
      assert.strictEqual(Store.tag(Store.child(result, 0)), 'atom');
      assert.strictEqual(Store.tag(Store.child(result, 1)), 'freevar');
    });

    it('should handle multiple via apply', () => {
      const ast = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const theta = [[AST.freevar('A'), AST.atom('p')], [AST.freevar('B'), AST.atom('q')]];
      const result = apply(ast, theta);
      // Nested access via Store
      assert.strictEqual(Store.child(Store.child(result, 0), 0), 'p');
      assert.strictEqual(Store.child(Store.child(result, 1), 0), 'q');
    });
  });

  describe('eq', () => {
    it('should compare equal ASTs', () => {
      const a = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const b = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(eq(a, b), true);
    });

    it('should compare different ASTs', () => {
      const a = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const b = AST.tensor(AST.freevar('B'), AST.freevar('A'));
      assert.strictEqual(eq(a, b), false);
    });
  });

  describe('occurs', () => {
    it('should detect variable in AST', () => {
      const ast = AST.tensor(AST.freevar('A'), AST.atom('p'));
      assert.strictEqual(occurs(AST.freevar('A'), ast), true);
      assert.strictEqual(occurs(AST.freevar('B'), ast), false);
    });
  });

  describe('unify', () => {
    it('should unify identical terms', () => {
      const theta = unify(AST.atom('p'), AST.atom('p'));
      assert.ok(theta !== null);
      assert.strictEqual(theta.length, 0);
    });

    it('should unify metavar with term', () => {
      // Metavars (starting with _) are unification variables
      const theta = unify(AST.freevar('_A'), AST.atom('p'));
      assert.ok(theta !== null);
      assert.strictEqual(theta.length, 1);
    });

    it('should unify nested terms with metavar', () => {
      const t1 = AST.tensor(AST.freevar('_A'), AST.atom('q'));
      const t2 = AST.tensor(AST.atom('p'), AST.atom('q'));
      const theta = unify(t1, t2);
      assert.ok(theta !== null);
      assert.strictEqual(eq(apply(t1, theta), t2), true);
    });

    it('should fail on different constructors', () => {
      assert.strictEqual(unify(AST.tensor(AST.atom('p'), AST.atom('q')),
                               AST.loli(AST.atom('p'), AST.atom('q'))), null);
    });

    it('should fail on different atoms', () => {
      assert.strictEqual(unify(AST.atom('p'), AST.atom('q')), null);
    });

    it('should fail on different freevars', () => {
      // Regular freevars (A, B) are ground - don't unify with each other
      assert.strictEqual(unify(AST.freevar('A'), AST.freevar('B')), null);
    });

    it('should unify same freevar', () => {
      // Same name = same freevar = unifiable (trivially)
      const theta = unify(AST.freevar('A'), AST.freevar('A'));
      assert.ok(theta !== null);
      assert.strictEqual(theta.length, 0);
    });
  });

  describe('match', () => {
    it('should match metavar to term', () => {
      const theta = match(AST.freevar('_A'), AST.atom('p'));
      assert.ok(theta !== null);
      // Flat interleaved theta: [var, val, ...] — 1 binding = length 2
      assert.strictEqual(theta.length, 2);
    });

    it('should check consistent bindings', () => {
      const pattern = AST.tensor(AST.freevar('_A'), AST.freevar('_A'));
      assert.ok(match(pattern, AST.tensor(AST.atom('p'), AST.atom('p'))) !== null);
      assert.strictEqual(match(pattern, AST.tensor(AST.atom('p'), AST.atom('q'))), null);
    });
  });

  describe('isVar', () => {
    it('should identify metavars (not regular freevars)', () => {
      // isVar now only returns true for metavars (unification variables)
      assert.strictEqual(isVar(AST.freevar('_X')), true);
      assert.strictEqual(isVar(AST.freevar('A')), false);  // A is ground
      assert.strictEqual(isVar(AST.atom('p')), false);
    });
  });
});

/**
 * Tests for v2 Sequent
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');

const { seq, hash, eq, hashAST } = require('../../lib/v2/kernel/sequent');
const calculus = require('../../lib/v2/calculus');

describe('v2 Sequent', () => {
  let AST;

  before(async () => {
    const ill = await calculus.loadILL();
    AST = ill.AST;
  });

  describe('hashAST', () => {
    it('should hash same AST to same value', () => {
      const a = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const b = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(hashAST(a), hashAST(b));
    });

    it('should hash different AST to different value', () => {
      const a = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const b = AST.tensor(AST.freevar('B'), AST.freevar('A'));
      assert.notStrictEqual(hashAST(a), hashAST(b));
    });
  });

  describe('seq', () => {
    it('should create sequent', () => {
      const s = seq({ gamma: [AST.freevar('A')] }, AST.freevar('B'));
      assert.ok(s.contexts.gamma);
      assert.strictEqual(s.contexts.gamma.length, 1);
    });
  });

  describe('hash', () => {
    it('should compute hash', () => {
      const s = seq({ gamma: [AST.freevar('A')] }, AST.freevar('B'));
      const h = hash(s);
      assert.ok(typeof h === 'bigint');
    });

    it('should cache hash', () => {
      const s = seq({ gamma: [AST.freevar('A')] }, AST.freevar('B'));
      const h1 = hash(s);
      const h2 = hash(s);
      assert.strictEqual(h1, h2);
    });
  });

  describe('eq', () => {
    it('should compare equal sequents', () => {
      const s1 = seq({ gamma: [AST.freevar('A')] }, AST.freevar('A'));
      const s2 = seq({ gamma: [AST.freevar('A')] }, AST.freevar('A'));
      assert.strictEqual(eq(s1, s2), true);
    });

    it('should compare different sequents', () => {
      const s1 = seq({ gamma: [AST.freevar('A')] }, AST.freevar('A'));
      const s2 = seq({ gamma: [AST.freevar('B')] }, AST.freevar('B'));
      assert.strictEqual(eq(s1, s2), false);
    });

    it('should treat context order as insignificant', () => {
      const s1 = seq({ gamma: [AST.freevar('A'), AST.freevar('B')] }, AST.freevar('C'));
      const s2 = seq({ gamma: [AST.freevar('B'), AST.freevar('A')] }, AST.freevar('C'));
      assert.strictEqual(eq(s1, s2), true);
    });
  });
});

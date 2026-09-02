/**
 * Tests for v2 Sequent
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import { seq, hash, eq } from '../lib/kernel/sequent.js';
import calculus from '../lib/calculus/index.js';
import { loadILL } from '../calculus/ill/index.js';
describe('v2 Sequent', () => {
  let AST;

  before(async () => {
    const ill = await loadILL();
    AST = ill.AST;
  });

  describe('content-addressed identity', () => {
    it('same structure produces same hash', () => {
      const a = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const b = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      assert.strictEqual(a, b);
    });

    it('different structure produces different hash', () => {
      const a = AST.tensor(AST.freevar('A'), AST.freevar('B'));
      const b = AST.tensor(AST.freevar('B'), AST.freevar('A'));
      assert.notStrictEqual(a, b);
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
      // 32-bit FNV-1a returns Number, not BigInt
      assert.ok(typeof h === 'number');
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

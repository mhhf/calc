/**
 * Tests for MDE → Hash conversion
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');

describe('MDE Convert', { timeout: 10000 }, () => {
  describe('parseExpr', () => {
    it('converts atom', async () => {
      const h = await mde.parseExpr('foo');
      assert.strictEqual(Store.tag(h), 'atom');
      assert.deepStrictEqual(Store.children(h), ['foo']);
    });

    it('converts variable', async () => {
      const h = await mde.parseExpr('X');
      assert.strictEqual(Store.tag(h), 'freevar');
      // MDE uppercase variables get _ prefix to become metavars
      assert.deepStrictEqual(Store.children(h), ['_X']);
    });

    it('converts tensor', async () => {
      const h = await mde.parseExpr('A * B');
      assert.strictEqual(Store.tag(h), 'tensor');
      const [a, b] = Store.children(h);
      assert.strictEqual(Store.tag(a), 'freevar');
      assert.strictEqual(Store.tag(b), 'freevar');
    });

    it('converts bang', async () => {
      const h = await mde.parseExpr('!A');
      assert.strictEqual(Store.tag(h), 'bang');
      const [inner] = Store.children(h);
      assert.strictEqual(Store.tag(inner), 'freevar');
    });

    it('converts double bang', async () => {
      const h = await mde.parseExpr('!!A');
      assert.strictEqual(Store.tag(h), 'bang');
      const [inner] = Store.children(h);
      assert.strictEqual(Store.tag(inner), 'bang');
    });

    it('converts arrow', async () => {
      const h = await mde.parseExpr('bin -> bin');
      assert.strictEqual(Store.tag(h), 'arrow');
    });

    it('converts lollipop', async () => {
      const h = await mde.parseExpr('A -o B');
      assert.strictEqual(Store.tag(h), 'loli');
    });

    it('converts monad (forward rule)', async () => {
      const h = await mde.parseExpr('A -o { B }');
      assert.strictEqual(Store.tag(h), 'loli');
      const [ante, conseq] = Store.children(h);
      assert.strictEqual(Store.tag(conseq), 'monad');
    });

    it('converts application', async () => {
      const h = await mde.parseExpr('plus X Y');
      assert.strictEqual(Store.tag(h), 'app');
    });

    it('deduplicates identical subterms', async () => {
      const h = await mde.parseExpr('A * A');
      const [a1, a2] = Store.children(h);
      assert.strictEqual(a1, a2, 'Same hash for identical subterms');
    });
  });

  describe('load', () => {
    it('loads bin.mde', async () => {
      const calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/bin.ill'));

      assert(calc.types.size > 0, 'Should have types');
      assert(calc.clauses.size > 0, 'Should have clauses');
      assert(calc.types.has('bin'), 'Should have bin type');
    });

    it('loads evm.mde with forward rules', async () => {
      const calc = await mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'));

      assert(calc.types.size > 0, 'Should have types');
      assert(calc.forwardRules.length > 0, 'Should have forward rules');
    });
  });

  describe('binlit normalization', () => {
    it('normalizes e to binlit(0n)', async () => {
      const h = await mde.parseExpr('e');
      assert.strictEqual(Store.tag(h), 'binlit');
      assert.deepStrictEqual(Store.children(h), [0n]);
    });

    it('normalizes (i e) to binlit(1n)', async () => {
      const h = await mde.parseExpr('i e');
      assert.strictEqual(Store.tag(h), 'binlit');
      assert.deepStrictEqual(Store.children(h), [1n]);
    });

    it('normalizes (o (i e)) to binlit(2n)', async () => {
      const h = await mde.parseExpr('o (i e)');
      assert.strictEqual(Store.tag(h), 'binlit');
      assert.deepStrictEqual(Store.children(h), [2n]);
    });

    it('normalizes N_75 hex expansion to binlit(117n)', async () => {
      const h = await mde.parseExpr('N_75');
      assert.strictEqual(Store.tag(h), 'binlit');
      assert.deepStrictEqual(Store.children(h), [117n]);
    });

    it('keeps (i X) recursive when X is a metavar', async () => {
      const h = await mde.parseExpr('i X');
      assert.strictEqual(Store.tag(h), 'app', 'Should remain app when child is a metavar');
    });

    it('ee (natural zero) is not normalized', async () => {
      const h = await mde.parseExpr('ee');
      assert.strictEqual(Store.tag(h), 'atom');
      assert.deepStrictEqual(Store.children(h), ['ee']);
    });
  });

  describe('hasMonad', () => {
    it('detects monad in forward rule', async () => {
      const h = await mde.parseExpr('A -o { B }');
      assert(mde.hasMonad(h), 'Should detect monad');
    });

    it('no monad in backward rule', async () => {
      const h = await mde.parseExpr('A -o B');
      assert(!mde.hasMonad(h), 'Should not detect monad');
    });
  });
});

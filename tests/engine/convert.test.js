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
      assert.strictEqual(Store.tag(h), 'metavar');
      // MDE uppercase variables become metavar tag (no _ prefix)
      assert.deepStrictEqual(Store.children(h), ['X']);
    });

    it('converts tensor', async () => {
      const h = await mde.parseExpr('A * B');
      assert.strictEqual(Store.tag(h), 'tensor');
      const [a, b] = Store.children(h);
      assert.strictEqual(Store.tag(a), 'metavar');
      assert.strictEqual(Store.tag(b), 'metavar');
    });

    it('converts bang', async () => {
      const h = await mde.parseExpr('!A');
      assert.strictEqual(Store.tag(h), 'bang');
      const [inner] = Store.children(h);
      assert.strictEqual(Store.tag(inner), 'metavar');
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
      // Flat form: tag is the predicate name, children are the args
      assert.strictEqual(Store.tag(h), 'plus');
      const children = Store.children(h);
      assert.strictEqual(children.length, 2);
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

    it('keeps (i X) as flat pred when X is a metavar', async () => {
      const h = await mde.parseExpr('i X');
      // Flat form: {tag: 'i', children: [X_hash]}
      assert.strictEqual(Store.tag(h), 'i', 'Should be flat pred with tag i');
      assert.strictEqual(Store.children(h).length, 1);
    });

    it('ee (natural zero) is not normalized', async () => {
      const h = await mde.parseExpr('ee');
      assert.strictEqual(Store.tag(h), 'atom');
      assert.deepStrictEqual(Store.children(h), ['ee']);
    });

    it('decimal literal 42 → binlit(42n)', async () => {
      const h = await mde.parseExpr('42');
      assert.strictEqual(Store.tag(h), 'binlit');
      assert.deepStrictEqual(Store.children(h), [42n]);
    });

    it('hex literal 0x60 → binlit(96n)', async () => {
      const h = await mde.parseExpr('0x60');
      assert.strictEqual(Store.tag(h), 'binlit');
      assert.deepStrictEqual(Store.children(h), [96n]);
    });

    it('decimal 0 → binlit(0n), same as e', async () => {
      const h0 = await mde.parseExpr('0');
      const he = await mde.parseExpr('e');
      assert.strictEqual(h0, he, 'decimal 0 and e should produce same hash');
    });

    it('0x60 matches binary (o (o (o (o (o (i (i (e))))))))', async () => {
      const hHex = await mde.parseExpr('0x60');
      const hBin = await mde.parseExpr('o (o (o (o (o (i (i e))))))');
      assert.strictEqual(hHex, hBin, 'hex literal should match binary form');
    });

    it('numeric literal in application: code 0 0x60', async () => {
      const h = await mde.parseExpr('code 0 0x60');
      assert.strictEqual(Store.tag(h), 'code');
      const [pc, opcode] = Store.children(h);
      assert.deepStrictEqual(Store.children(pc), [0n]);
      assert.deepStrictEqual(Store.children(opcode), [96n]);
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

  describe('decomposeQuery — explicit quantifiers', () => {
    const { decomposeQuery } = require('../../lib/engine/convert');

    it('forall X. f(X) — X becomes freevar (eigenvariable)', () => {
      const h = mde.parseExpr('forall X. f X');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 1);
      const fact = keys[0];
      assert.strictEqual(Store.tag(fact), 'f');
      assert.strictEqual(Store.tag(Store.child(fact, 0)), 'freevar',
        'forall-bound variable should become freevar (eigenvariable)');
    });

    it('exists X. f(X) — X stays as metavar (witness variable)', () => {
      const h = mde.parseExpr('exists X. f X');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 1);
      const fact = keys[0];
      assert.strictEqual(Store.tag(fact), 'f');
      assert.strictEqual(Store.tag(Store.child(fact, 0)), 'metavar',
        'exists-bound variable should stay as metavar (witness)');
    });

    it('mixed forall/exists: forall A. exists B. f(A, B)', () => {
      const h = mde.parseExpr('forall A. exists B. f A B');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 1);
      const fact = keys[0];
      assert.strictEqual(Store.tag(fact), 'f');
      assert.strictEqual(Store.tag(Store.child(fact, 0)), 'freevar',
        'forall A → freevar');
      assert.strictEqual(Store.tag(Store.child(fact, 1)), 'metavar',
        'exists B → metavar');
    });

    it('forall distributes over tensor: forall X. f(X) * g(X)', () => {
      const h = mde.parseExpr('forall X. f X * g X');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 2);
      for (const k of keys) {
        const arg = Store.child(k, 0);
        assert.strictEqual(Store.tag(arg), 'freevar',
          'both tensor branches should have freevar for X');
      }
    });

    it('forall with bang: forall X. !eq(X, 0) * f(X)', () => {
      const h = mde.parseExpr('forall X. !eq X 0 * f X');
      const { linear, persistent } = decomposeQuery(h);
      const linKeys = Object.keys(linear).map(Number);
      const perKeys = Object.keys(persistent).map(Number);
      assert.strictEqual(linKeys.length, 1);
      assert.strictEqual(perKeys.length, 1);
      // Both should reference the same freevar for X
      assert.strictEqual(Store.tag(Store.child(linKeys[0], 0)), 'freevar');
      assert.strictEqual(Store.tag(Store.child(perKeys[0], 0)), 'freevar');
    });

    it('nested forall: forall X. forall Y. f(X, Y)', () => {
      const h = mde.parseExpr('forall X. forall Y. f X Y');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 1);
      const fact = keys[0];
      assert.strictEqual(Store.tag(Store.child(fact, 0)), 'freevar');
      assert.strictEqual(Store.tag(Store.child(fact, 1)), 'freevar');
    });

    it('multi-var shorthand: forall X Y. f(X, Y)', () => {
      const h = mde.parseExpr('forall X Y. f X Y');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 1);
      const fact = keys[0];
      assert.strictEqual(Store.tag(Store.child(fact, 0)), 'freevar');
      assert.strictEqual(Store.tag(Store.child(fact, 1)), 'freevar');
    });

    it('concrete query (no variables) works without quantifiers', () => {
      const h = mde.parseExpr('f 0 * g 1');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      assert.strictEqual(keys.length, 2);
      // No metavars → no error
    });

    it('unbound variables throw error', () => {
      const h = mde.parseExpr('f X * g Y');
      assert.throws(
        () => decomposeQuery(h),
        /unbound.*variable/i,
        'Should throw on unbound variables'
      );
    });

    it('partially bound variables throw error', () => {
      const h = mde.parseExpr('forall X. f X * g Y');
      assert.throws(
        () => decomposeQuery(h),
        /unbound.*variable.*Y/i,
        'Should throw for Y but not X'
      );
    });

    it('same freevar hash for same forall variable in different positions', () => {
      const h = mde.parseExpr('forall X. f X * g X');
      const { linear } = decomposeQuery(h);
      const keys = Object.keys(linear).map(Number);
      const arg0 = Store.child(keys[0], 0);
      const arg1 = Store.child(keys[1], 0);
      assert.strictEqual(arg0, arg1,
        'same forall var should produce same freevar hash (content-addressed)');
    });
  });
});

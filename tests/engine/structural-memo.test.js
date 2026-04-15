/**
 * Direct tests for opt/structural-memo.js
 *
 * Covers: control hash computation, memo hit/miss, recordMemo behavior.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { FactSet } = require('../../lib/engine/fact-set');
const { controlHash, createMemoCtx, recordMemo } = require('../../lib/engine/opt/structural-memo');

describe('structural-memo', () => {
  // Load ILL once to register predicate tags (pc, gas, etc.)
  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
  });

  describe('controlHash', () => {
    it('returns a 32-bit unsigned number', () => {
      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent: new FactSet(Store.TAG_NAMES.length) };
      const hash = controlHash(state, {});
      assert.equal(typeof hash, 'number');
      assert.ok(hash >= 0);
      assert.ok(hash <= 0xFFFFFFFF);
    });

    it('same PC + stack depth → same hash', () => {
      const pcVal = Store.put('atom', ['v1']);
      const pc1 = Store.put('pc', [pcVal]);
      const pc2 = Store.put('pc', [pcVal]);
      const tagId = Store.tagId(pc1);

      const fs1 = new FactSet(Store.TAG_NAMES.length);
      fs1.insert(tagId, pc1, null);
      const state1 = { linear: fs1, persistent: new FactSet(Store.TAG_NAMES.length) };

      const fs2 = new FactSet(Store.TAG_NAMES.length);
      fs2.insert(tagId, pc2, null);
      const state2 = { linear: fs2, persistent: new FactSet(Store.TAG_NAMES.length) };

      assert.equal(controlHash(state1, {}), controlHash(state2, {}));
    });

    it('different PC values → different hash', () => {
      const v1 = Store.put('atom', ['val1']);
      const v2 = Store.put('atom', ['val2']);
      const pc1 = Store.put('pc', [v1]);
      const pc2 = Store.put('pc', [v2]);

      const fs1 = new FactSet(Store.TAG_NAMES.length);
      fs1.insert(Store.tagId(pc1), pc1, null);
      const state1 = { linear: fs1, persistent: new FactSet(Store.TAG_NAMES.length) };

      const fs2 = new FactSet(Store.TAG_NAMES.length);
      fs2.insert(Store.tagId(pc2), pc2, null);
      const state2 = { linear: fs2, persistent: new FactSet(Store.TAG_NAMES.length) };

      const h1 = controlHash(state1, {});
      const h2 = controlHash(state2, {});
      assert.notEqual(h1, h2);
    });
  });

  describe('createMemoCtx', () => {
    it('creates fresh context with empty map and zero boundCount', () => {
      const ctx = createMemoCtx();
      assert.equal(ctx.globalControl.size, 0);
      assert.equal(ctx.boundCount, 0);
    });
  });

  describe('recordMemo', () => {
    it('records hash when boundCount unchanged (fully explored)', () => {
      const ctx = createMemoCtx();
      recordMemo(42, 0, ctx);
      assert.equal(ctx.globalControl.has(42), true);
    });

    it('does NOT record when boundCount increased (incomplete)', () => {
      const ctx = createMemoCtx();
      ctx.boundCount = 1;
      recordMemo(42, 0, ctx);
      assert.equal(ctx.globalControl.has(42), false);
    });

    it('records when boundCount matches boundBefore', () => {
      const ctx = createMemoCtx();
      ctx.boundCount = 5;
      recordMemo(99, 5, ctx);
      assert.equal(ctx.globalControl.has(99), true);
    });
  });
});

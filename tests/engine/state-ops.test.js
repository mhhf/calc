/**
 * Direct tests for state-ops.js and delta-bypass.js
 *
 * Covers: consumeLinear, produceLinear, producePersistent, mutateState,
 * and matchDeltaBypass.
 */
const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { FactSet, Arena } = require('../../lib/engine/fact-set');
const { consumeLinear, produceLinear, producePersistent } = require('../../lib/engine/state-ops');
const { matchDeltaBypass } = require('../../lib/engine/delta-bypass');

describe('state-ops', () => {
  // Load ILL to register predicate tags
  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
  });

  describe('consumeLinear', () => {
    it('removes facts from FactSet by hash and count', () => {
      const fs = new FactSet(Store.TAG_NAMES.length);
      const v1 = Store.put('atom', ['v1']);
      const h = Store.put('gas', [v1]);
      const tagId = Store.tagId(h);
      fs.insert(tagId, h, null);
      fs.insert(tagId, h, null);
      assert.equal(fs.count(tagId, h), 2);

      consumeLinear(fs, { [h]: 1 }, null);
      assert.equal(fs.count(tagId, h), 1);
    });

    it('removes multiple different facts', () => {
      const fs = new FactSet(Store.TAG_NAMES.length);
      const h1 = Store.put('pc', [Store.put('atom', ['a'])]);
      const h2 = Store.put('gas', [Store.put('atom', ['b'])]);
      fs.insert(Store.tagId(h1), h1, null);
      fs.insert(Store.tagId(h2), h2, null);

      consumeLinear(fs, { [h1]: 1, [h2]: 1 }, null);
      assert.equal(fs.count(Store.tagId(h1), h1), 0);
      assert.equal(fs.count(Store.tagId(h2), h2), 0);
    });

    it('records undo entries when arena provided', () => {
      const fs = new FactSet(Store.TAG_NAMES.length);
      const arena = new Arena();
      const h = Store.put('gas', [Store.put('atom', ['x'])]);
      const tagId = Store.tagId(h);
      fs.insert(tagId, h, null);

      const cp = arena.cursor;
      consumeLinear(fs, { [h]: 1 }, arena);
      assert.equal(fs.count(tagId, h), 0);
      assert.ok(arena.cursor > cp);
    });
  });

  describe('producePersistent', () => {
    it('inserts new persistent facts', () => {
      const fs = new FactSet(Store.TAG_NAMES.length);
      const h = Store.put('inc', [Store.put('atom', ['a']), Store.put('atom', ['b'])]);
      const tagId = Store.tagId(h);

      producePersistent(fs, [h], [], {}, null, null);
      assert.equal(fs.has(tagId, h), true);
    });

    it('deduplicates — does not double-insert', () => {
      const fs = new FactSet(Store.TAG_NAMES.length);
      const h = Store.put('inc', [Store.put('atom', ['a']), Store.put('atom', ['b'])]);
      const tagId = Store.tagId(h);
      fs.insert(tagId, h, null);

      producePersistent(fs, [h], [], {}, null, null);
      assert.equal(fs.count(tagId, h), 1);
    });
  });

  describe('produceLinear', () => {
    it('inserts linear facts from patterns', () => {
      const fs = new FactSet(Store.TAG_NAMES.length);
      const h = Store.put('gas', [Store.put('atom', ['x'])]);
      const tagId = Store.tagId(h);

      produceLinear(fs, [h], [], {}, null, false, null);
      assert.equal(fs.count(tagId, h), 1);
    });
  });
});

describe('delta-bypass', () => {
  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
  });

  describe('matchDeltaBypass', () => {
    it('returns false when role is not flat delta', () => {
      const pattern = Store.put('gas', [Store.put('atom', ['x'])]);
      const rule = { patternRoles: [null], linearMeta: {} };
      const state = { linear: new FactSet(Store.TAG_NAMES.length) };
      const result = matchDeltaBypass(pattern, 0, rule, state, [], new Map(), new Map(), false, -1);
      assert.equal(result, false);
    });

    it('returns false for preserved patterns', () => {
      const pattern = Store.put('gas', [Store.put('atom', ['x'])]);
      const rule = {
        patternRoles: [{ type: 'delta', flat: true, bindings: [], groundChecks: [] }],
        linearMeta: { [pattern]: { pred: 'gas' } },
      };
      const state = { linear: new FactSet(Store.TAG_NAMES.length) };
      const result = matchDeltaBypass(pattern, 0, rule, state, [], new Map(), new Map(), true, -1);
      assert.equal(result, false);
    });

    it('matches a flat delta pattern and writes theta', () => {
      const child = Store.put('atom', ['val']);
      const fact = Store.put('gas', [child]);
      const tagId = Store.tagId(fact);

      const fs = new FactSet(Store.TAG_NAMES.length);
      fs.insert(tagId, fact, null);

      const mv = Store.put('metavar', ['X']);
      const pattern = Store.put('gas', [mv]);

      const theta = [undefined];
      const consumed = new Map();
      const reserved = new Map();

      const rule = {
        patternRoles: [{ type: 'delta', flat: true, bindings: [{ pos: 0, slot: 0 }], groundChecks: [] }],
        linearMeta: { [pattern]: { pred: 'gas' } },
      };
      const state = { linear: fs, groupForPred: () => fs.group(tagId) };

      const result = matchDeltaBypass(pattern, 0, rule, state, theta, consumed, reserved, false, tagId);
      assert.equal(result, true);
      assert.equal(theta[0], child);
      assert.equal(consumed.get(fact), 1);
    });

    it('respects ground checks', () => {
      const v1 = Store.put('atom', ['a']);
      const v2 = Store.put('atom', ['b']);
      const fact = Store.put('plus', [v1, v2, Store.put('atom', ['c'])]);
      const tagId = Store.tagId(fact);

      const fs = new FactSet(Store.TAG_NAMES.length);
      fs.insert(tagId, fact, null);

      const mv = Store.put('metavar', ['Y']);
      const pattern = Store.put('plus', [v1, mv, Store.put('atom', ['c'])]);

      const theta = [undefined];
      const consumed = new Map();

      const rule = {
        patternRoles: [{
          type: 'delta', flat: true,
          bindings: [{ pos: 1, slot: 0 }],
          groundChecks: [{ pos: 0, value: v1 }, { pos: 2, value: Store.put('atom', ['c']) }],
        }],
        linearMeta: { [pattern]: { pred: 'plus' } },
      };
      const state = { linear: fs, groupForPred: () => fs.group(tagId) };

      const result = matchDeltaBypass(pattern, 0, rule, state, theta, consumed, new Map(), false, tagId);
      assert.equal(result, true);
      assert.equal(theta[0], v2);
    });

    it('fails ground check when value does not match', () => {
      const v1 = Store.put('atom', ['a']);
      const vWrong = Store.put('atom', ['wrong']);
      const v2 = Store.put('atom', ['b']);
      const fact = Store.put('plus', [vWrong, v2, Store.put('atom', ['c'])]);
      const tagId = Store.tagId(fact);

      const fs = new FactSet(Store.TAG_NAMES.length);
      fs.insert(tagId, fact, null);

      const mv = Store.put('metavar', ['Y']);
      const pattern = Store.put('plus', [v1, mv, Store.put('atom', ['c'])]);

      const theta = [undefined];
      const rule = {
        patternRoles: [{
          type: 'delta', flat: true,
          bindings: [{ pos: 1, slot: 0 }],
          groundChecks: [{ pos: 0, value: v1 }],
        }],
        linearMeta: { [pattern]: { pred: 'plus' } },
      };
      const state = { linear: fs, groupForPred: () => fs.group(tagId) };

      const result = matchDeltaBypass(pattern, 0, rule, state, theta, new Map(), new Map(), false, tagId);
      assert.equal(result, false);
    });
  });
});

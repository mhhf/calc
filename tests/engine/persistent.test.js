/**
 * Direct tests for lnl/persistent.js
 *
 * Covers: state lookup path, clause resolution path,
 * multiple goals, hooks — each stage independently.
 */
const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { FactSet } = require('../../lib/engine/fact-set');
const { provePersistentNaive } = require('../../lib/engine/lnl/persistent');

describe('lnl/persistent — provePersistentNaive', () => {
  let calc;

  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    calc = mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
  });

  beforeEach(() => {
    require('../../lib/engine/backward-cache').clearBackwardCache();
  });

  describe('state lookup path', () => {
    it('resolves goal from persistent state via unification', () => {
      // Use a real predicate that exists in ILL (inc)
      const a = Store.put('binlit', [5n]);
      const b = Store.put('binlit', [6n]);
      const fact = Store.put('inc', [a, b]);
      const persistent = new FactSet(Store.TAG_NAMES.length);
      persistent.insert(Store.tagId(fact), fact, null);

      const mv = Store.put('metavar', ['_out']);
      const goal = Store.put('inc', [a, mv]);
      const slots = { [mv]: 0 };
      const theta = [undefined];

      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent };
      const idx = provePersistentNaive([goal], 0, theta, slots, state, null, null, {});
      assert.equal(idx, 1);
      assert.equal(theta[0], b);
    });

    it('fails when fact not in persistent state and no calc', () => {
      const a = Store.put('atom', ['val']);
      const mv = Store.put('metavar', ['X']);
      const goal = Store.put('foo_nonexist', [a, mv]);
      const slots = { [mv]: 0 };
      const theta = [undefined];

      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent: new FactSet(Store.TAG_NAMES.length) };
      const idx = provePersistentNaive([goal], 0, theta, slots, state, null, null, {});
      assert.equal(idx, 0);
    });
  });

  describe('clause resolution path', () => {
    it('resolves inc via backward chaining', () => {
      const five = Store.put('binlit', [5n]);
      const mv = Store.put('metavar', ['_out']);
      const goal = Store.put('inc', [five, mv]);
      const slots = { [mv]: 0 };
      const theta = [undefined];

      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent: new FactSet(Store.TAG_NAMES.length) };
      const matchOpts = {
        ffiParsedModes: calc.ffiContext ? calc.ffiContext.parsedModes : {},
        canonicalize: null,
        backchainUseFFI: false,
      };

      const idx = provePersistentNaive([goal], 0, theta, slots, state, calc, null, matchOpts);
      assert.equal(idx, 1);
      assert.ok(theta[0] !== undefined);
    });
  });

  describe('multiple goals', () => {
    it('proves sequential goals from state', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const factA = Store.put('inc', [a, b]);
      const c = Store.put('binlit', [3n]);
      const d = Store.put('binlit', [4n]);
      const factB = Store.put('inc', [c, d]);

      const persistent = new FactSet(Store.TAG_NAMES.length);
      persistent.insert(Store.tagId(factA), factA, null);
      persistent.insert(Store.tagId(factB), factB, null);

      const mvA = Store.put('metavar', ['A']);
      const mvB = Store.put('metavar', ['B']);
      const goalA = Store.put('inc', [a, mvA]);
      const goalB = Store.put('inc', [c, mvB]);
      const slots = { [mvA]: 0, [mvB]: 1 };
      const theta = [undefined, undefined];

      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent };
      const idx = provePersistentNaive([goalA, goalB], 0, theta, slots, state, null, null, {});
      assert.equal(idx, 2);
      assert.equal(theta[0], b);
      assert.equal(theta[1], d);
    });

    it('stops at first failure', () => {
      const a = Store.put('binlit', [1n]);
      const b = Store.put('binlit', [2n]);
      const factA = Store.put('inc', [a, b]);

      const persistent = new FactSet(Store.TAG_NAMES.length);
      persistent.insert(Store.tagId(factA), factA, null);

      const mvA = Store.put('metavar', ['A']);
      const mvB = Store.put('metavar', ['B']);
      const goalA = Store.put('inc', [a, mvA]);
      const goalB = Store.put('missing_pred_xyz', [mvB]);
      const slots = { [mvA]: 0, [mvB]: 1 };
      const theta = [undefined, undefined];

      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent };
      const idx = provePersistentNaive([goalA, goalB], 0, theta, slots, state, null, null, {});
      assert.equal(idx, 1);
    });
  });

  describe('hooks', () => {
    it('calls onProveSuccess for state lookup', () => {
      const a = Store.put('binlit', [5n]);
      const b = Store.put('binlit', [6n]);
      const fact = Store.put('inc', [a, b]);
      const persistent = new FactSet(Store.TAG_NAMES.length);
      persistent.insert(Store.tagId(fact), fact, null);

      const mv = Store.put('metavar', ['X']);
      const goal = Store.put('inc', [a, mv]);
      const slots = { [mv]: 0 };
      const theta = [undefined];
      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent };

      let hookCalled = false;
      const matchOpts = {
        onProveSuccess: (_, method) => { hookCalled = true; assert.equal(method, 'state'); },
      };
      provePersistentNaive([goal], 0, theta, slots, state, null, null, matchOpts);
      assert.ok(hookCalled);
    });

    it('calls onProveFail when goal exhausted', () => {
      const mv = Store.put('metavar', ['X']);
      const goal = Store.put('no_such_pred_xyz', [mv]);
      const slots = { [mv]: 0 };
      const theta = [undefined];
      const state = { linear: new FactSet(Store.TAG_NAMES.length), persistent: new FactSet(Store.TAG_NAMES.length) };

      let failReason;
      const matchOpts = {
        onProveFail: (_, reason) => { failReason = reason; },
      };
      provePersistentNaive([goal], 0, theta, slots, state, null, null, matchOpts);
      assert.equal(failReason, 'exhausted');
    });
  });
});

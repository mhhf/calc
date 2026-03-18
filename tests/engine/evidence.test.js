/**
 * Tests for evidence collection in the guided execution profile.
 *
 * Tests the evidence pipeline: provePersistentWithFFI → matchLoli → drainPersistentLolis
 * All evidence is collected via mutable collector arrays (evidenceOut).
 * See TODO_0068 §10.5 for the guided profile design.
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const forward = require('../../lib/engine/forward');
const { matchLoli, matchFirstLoli } = require('../../lib/engine/match');
const { provePersistentWithFFI } = require('../../lib/engine/opt/ffi');
const { drainPersistentLolis } = require('../../lib/engine/opt/loli-drain');
const { Arena } = require('../../lib/engine/fact-set');

describe('Evidence collection (TODO_0068 §10.5)', () => {

  describe('provePersistentWithFFI evidence', () => {
    beforeEach(() => { Store.clear(); });

    it('collects state lookup evidence', () => {
      const fact = Store.put('atom', ['myFact']);
      const pattern = Store.put('atom', ['myFact']);
      const state = forward.createState({}, { [fact]: true });

      const theta = new Array(1);
      const slots = {};
      const evidenceOut = [];

      const idx = provePersistentWithFFI([pattern], 0, theta, slots, state, null, evidenceOut);
      assert.strictEqual(idx, 1, 'should prove the goal');
      assert.strictEqual(evidenceOut.length, 1);
      assert.strictEqual(evidenceOut[0].method, 'state');
      assert.strictEqual(evidenceOut[0].fact, fact);
    });

    it('collects FFI evidence for arithmetic', () => {
      // inc(X, Y) with X ground should resolve via FFI
      const val3 = Store.put('binlit', [3n]);
      const X = Store.put('metavar', ['X']);
      const pattern = Store.put('inc', [val3, X]);
      const state = forward.createState({}, {});

      const slots = { [X]: 0 };
      const theta = new Array(1);
      const evidenceOut = [];

      const idx = provePersistentWithFFI([pattern], 0, theta, slots, state, null, evidenceOut);
      assert.strictEqual(idx, 1, 'should prove via FFI');
      assert.strictEqual(evidenceOut.length, 1);
      assert.strictEqual(evidenceOut[0].method, 'ffi');
    });

    it('does not collect evidence when evidenceOut is null', () => {
      const fact = Store.put('atom', ['myFact']);
      const state = forward.createState({}, { [fact]: true });

      const theta = new Array(1);
      const slots = {};

      // null evidenceOut — should not throw
      const idx = provePersistentWithFFI([fact], 0, theta, slots, state, null, null);
      assert.strictEqual(idx, 1);
    });

    it('does not collect evidence when evidenceOut is undefined (backward compat)', () => {
      const fact = Store.put('atom', ['myFact']);
      const state = forward.createState({}, { [fact]: true });

      const theta = new Array(1);
      const slots = {};

      // no evidenceOut argument — backward compatibility
      const idx = provePersistentWithFFI([fact], 0, theta, slots, state, null);
      assert.strictEqual(idx, 1);
    });
  });

  describe('matchLoli evidence', () => {
    beforeEach(() => { Store.clear(); });

    it('returns real theta/slots when evidence requested', () => {
      const X = Store.put('metavar', ['X']);
      const triggerPattern = Store.put('data', [X]);
      const bodyPattern = Store.put('result', [X]);
      const body = Store.put('monad', [bodyPattern]);
      const loli = Store.put('loli', [triggerPattern, body]);

      const val = Store.put('binlit', [42n]);
      const triggerFact = Store.put('data', [val]);

      const state = forward.createState(
        { [loli]: 1, [triggerFact]: 1 },
        {}
      );

      const m = matchLoli(loli, state, null, { evidence: true });
      assert(m, 'should match');
      // With evidence, theta and slots should be populated (not empty)
      assert(Object.keys(m.slots).length > 0, 'slots should be non-empty with evidence');
      assert(m.theta.length > 0, 'theta should be non-empty with evidence');
    });

    it('returns empty theta/slots when evidence NOT requested (backward compat)', () => {
      const trigger = Store.put('atom', ['go']);
      const result = Store.put('atom', ['done']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1, [trigger]: 1 },
        {}
      );

      const m = matchLoli(loli, state, null);
      assert(m, 'should match');
      assert.deepStrictEqual(m.theta, [], 'theta should be empty without evidence');
      assert.deepStrictEqual(m.slots, {}, 'slots should be empty without evidence');
      assert.strictEqual(m.persistentEvidence, undefined, 'no persistentEvidence without evidence');
    });

    it('collects persistent evidence for bang-trigger lolis', () => {
      const guard = Store.put('atom', ['check']);
      const bangGuard = Store.put('bang', [guard]);
      const result = Store.put('atom', ['guarded']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [bangGuard, body]);

      const state = forward.createState(
        { [loli]: 1 },
        { [guard]: true }
      );

      const m = matchLoli(loli, state, null, { evidence: true });
      assert(m, 'should match');
      assert(Array.isArray(m.persistentEvidence), 'should have persistentEvidence array');
      assert.strictEqual(m.persistentEvidence.length, 1, 'should have 1 persistent goal evidence');
      assert.strictEqual(m.persistentEvidence[0].method, 'state');
      assert.strictEqual(m.persistentEvidence[0].fact, guard);
    });

    it('collects persistent evidence for mixed trigger', () => {
      const linTrigger = Store.put('atom', ['resource']);
      const guard = Store.put('atom', ['condition']);
      const bangGuard = Store.put('bang', [guard]);
      const trigger = Store.put('tensor', [linTrigger, bangGuard]);
      const result = Store.put('atom', ['mixed_result']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1, [linTrigger]: 1 },
        { [guard]: true }
      );

      const m = matchLoli(loli, state, null, { evidence: true });
      assert(m, 'should match');
      assert.strictEqual(m.persistentEvidence.length, 1);
      assert.strictEqual(m.persistentEvidence[0].method, 'state');
    });

    it('returns empty persistentEvidence for pure-linear trigger', () => {
      const trigger = Store.put('atom', ['signal']);
      const result = Store.put('atom', ['done']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1, [trigger]: 1 },
        {}
      );

      const m = matchLoli(loli, state, null, { evidence: true });
      assert(m, 'should match');
      assert(Array.isArray(m.persistentEvidence));
      assert.strictEqual(m.persistentEvidence.length, 0, 'no persistent goals = empty evidence');
    });
  });

  describe('matchFirstLoli evidence', () => {
    beforeEach(() => { Store.clear(); });

    it('forwards evidence option to matchLoli', () => {
      const trigger = Store.put('atom', ['go']);
      const result = Store.put('atom', ['done']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [trigger, body]);

      const state = forward.createState(
        { [loli]: 1, [trigger]: 1 },
        {}
      );

      const m = matchFirstLoli(state, { roles: {} }, { evidence: true });
      assert(m, 'should find a match');
      assert(Array.isArray(m.persistentEvidence), 'should have persistentEvidence');
    });
  });

  describe('drainPersistentLolis evidence', () => {
    beforeEach(() => { Store.clear(); });

    it('collects drain evidence for persistent-trigger lolis', () => {
      // Create: !guard -o { result }
      const guard = Store.put('atom', ['check']);
      const bangGuard = Store.put('bang', [guard]);
      const result = Store.put('atom', ['drained']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [bangGuard, body]);

      const state = forward.createState(
        { [loli]: 1 },
        { [guard]: true }
      );

      const linArena = new Arena(256);
      const perArena = new Arena(256);
      const evidenceOut = [];

      drainPersistentLolis(state, linArena, perArena, { roles: {} }, evidenceOut);

      assert.strictEqual(evidenceOut.length, 1, 'should have 1 drain firing');
      assert.strictEqual(evidenceOut[0].loliHash, loli);
      assert(evidenceOut[0].match, 'should have the match result');
      assert(evidenceOut[0].match.consumed[loli], 'loli should be consumed');
    });

    it('does not collect evidence when evidenceOut is null', () => {
      const guard = Store.put('atom', ['check']);
      const bangGuard = Store.put('bang', [guard]);
      const result = Store.put('atom', ['drained']);
      const body = Store.put('monad', [result]);
      const loli = Store.put('loli', [bangGuard, body]);

      const state = forward.createState(
        { [loli]: 1 },
        { [guard]: true }
      );

      const linArena = new Arena(256);
      const perArena = new Arena(256);

      // Should not throw when evidenceOut is null/undefined
      drainPersistentLolis(state, linArena, perArena, { roles: {} }, null);
      drainPersistentLolis(state, linArena, perArena, { roles: {} });
    });

    it('collects multiple drain firings', () => {
      // Two lolis with different persistent guards
      const guard1 = Store.put('atom', ['check1']);
      const guard2 = Store.put('atom', ['check2']);
      const bang1 = Store.put('bang', [guard1]);
      const bang2 = Store.put('bang', [guard2]);
      const result1 = Store.put('atom', ['r1']);
      const result2 = Store.put('atom', ['r2']);
      const body1 = Store.put('monad', [result1]);
      const body2 = Store.put('monad', [result2]);
      const loli1 = Store.put('loli', [bang1, body1]);
      const loli2 = Store.put('loli', [bang2, body2]);

      const state = forward.createState(
        { [loli1]: 1, [loli2]: 1 },
        { [guard1]: true, [guard2]: true }
      );

      const linArena = new Arena(256);
      const perArena = new Arena(256);
      const evidenceOut = [];

      drainPersistentLolis(state, linArena, perArena, { roles: {} }, evidenceOut);

      assert.strictEqual(evidenceOut.length, 2, 'should drain both lolis');
    });
  });
});

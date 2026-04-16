/**
 * Prover-contract consistency tests (TODO_0209 rubric C1-C4).
 *
 * Three implementations of `provePersistent` live in the engine:
 *   - stateProvePersistent  (generic baseline — match.js)
 *   - proveNaive            (LNL — lnl/persistent.js)
 *   - proveWithFFI          (OPT — opt/ffi.js)
 *
 * They MUST agree on:
 *   C1. Signature — same arity and parameter order.
 *   C2. Goal form — hook `goal` is the POST-unification proved form.
 *   C3. Payload shape — every onProveSuccess call emits { ground, hasFfi }.
 *   C4. Method enum — every `method` string is from PROVE_METHODS.
 *
 * This test is mechanical, not integration: it constructs a single
 * persistent fact matching a single pattern, runs all three provers against
 * the same inputs, and asserts each agrees on the contract.
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const forward = require('../../lib/engine/forward');
const {
  stateProvePersistent, PROVE_METHOD, PROVE_METHODS,
} = require('../../lib/engine/match');
const { proveNaive } = require('../../lib/engine/lnl/persistent');
const { proveWithFFI } = require('../../lib/engine/opt/ffi');
const { makeMatchOpts } = require('./_match-opts');

/** Build a minimal state with one persistent fact + one matching pattern. */
function scenario() {
  Store.clear();
  const val = Store.put('atom', ['v']);
  const fact = Store.put('mypred', [val]);
  const pattern = Store.put('mypred', [val]);
  const state = forward.createState({}, { [fact]: true });
  return { fact, pattern, state };
}

/**
 * Minimal FFI context — proveWithFFI dereferences ffiMeta/parsedModes eagerly,
 * so they must be objects (even empty). No arithmetic predicates are
 * involved here; state lookup short-circuits before FFI.
 */
const STUB_FFI = {
  meta: {}, parsedModes: {}, get: () => null, isFFIGround: () => false,
};

/** Parse `function fn(a, b, c = d) { ... }` → ['a', 'b', 'c']. */
function paramNames(fn) {
  const src = fn.toString();
  const m = src.match(/\(([^)]*)\)/);
  if (!m) return [];
  return m[1].split(',').map(s => s.trim().split('=')[0].trim()).filter(Boolean);
}

describe('prover-contract (C1-C4)', () => {
  const PROVERS = [
    { name: 'stateProvePersistent', fn: stateProvePersistent },
    { name: 'proveNaive',           fn: proveNaive           },
    { name: 'proveWithFFI',         fn: proveWithFFI         },
  ];

  describe('C1 — signature (arity & parameter order)', () => {
    // Expected params (ignoring leading underscore "_calc" mark-unused convention).
    const expected = ['patterns', 'startIdx', 'theta', 'slots', 'state', 'calc', 'evidenceOut', 'matchOpts'];
    for (const { name, fn } of PROVERS) {
      it(`${name} has signature (${expected.join(', ')})`, () => {
        const actual = paramNames(fn).map(p => p.replace(/^_/, ''));
        assert.deepStrictEqual(actual, expected,
          `${name} params should match contract exactly (leading underscore tolerated)`);
      });
    }
  });

  describe('C2 — goal reported post-unification', () => {
    beforeEach(() => Store.clear());

    for (const { name, fn } of PROVERS) {
      it(`${name} reports POST-unification goal`, () => {
        const { fact, pattern, state } = scenario();
        // Introduce a metavar to make pre/post-unification forms distinguishable.
        const mv = Store.put('metavar', ['X']);
        const metaPattern = Store.put('mypred', [mv]);
        const slots = { [mv]: 0 };
        const theta = new Array(1);

        let capturedGoal = null;
        const matchOpts = makeMatchOpts({
          ffi: STUB_FFI,
          onProveSuccess: (goal, _method, _payload) => { capturedGoal = goal; },
        });

        const idx = fn([metaPattern], 0, theta, slots, state, null, null, matchOpts);
        assert.equal(idx, 1, `${name} should have proved the pattern`);
        assert.equal(capturedGoal, fact,
          `${name}: goal hash should be the post-unification form (= fact), not the unbound pattern`);
      });
    }
  });

  describe('C3 — hook payload shape { ground, hasFfi }', () => {
    beforeEach(() => Store.clear());

    for (const { name, fn } of PROVERS) {
      it(`${name} emits { ground: boolean, hasFfi: boolean }`, () => {
        const { pattern, state } = scenario();
        const slots = {};
        const theta = [];

        const payloads = [];
        const matchOpts = makeMatchOpts({
          ffi: STUB_FFI,
          onProveSuccess: (_goal, _method, payload) => payloads.push(payload),
        });

        fn([pattern], 0, theta, slots, state, null, null, matchOpts);
        assert.ok(payloads.length >= 1, `${name}: expected at least one onProveSuccess call`);
        for (const p of payloads) {
          assert.ok(p !== undefined && p !== null, `${name}: payload must not be nullish`);
          assert.equal(typeof p.ground, 'boolean', `${name}: payload.ground must be boolean`);
          assert.equal(typeof p.hasFfi, 'boolean', `${name}: payload.hasFfi must be boolean`);
        }
      });
    }

    it('state-lookup path: ground=true, hasFfi=false (uniform across provers)', () => {
      for (const { name, fn } of PROVERS) {
        const { pattern, state } = scenario();
        const slots = {};
        const theta = [];

        let captured = null;
        const matchOpts = makeMatchOpts({
          ffi: STUB_FFI,
          onProveSuccess: (_g, method, payload) => {
            if (method === PROVE_METHOD.STATE) captured = payload;
          },
        });

        fn([pattern], 0, theta, slots, state, null, null, matchOpts);
        assert.ok(captured, `${name}: state method should have fired`);
        assert.equal(captured.ground, true, `${name}: state-lookup payload.ground must be true`);
        assert.equal(captured.hasFfi, false, `${name}: state-lookup payload.hasFfi must be false`);
      }
    });
  });

  describe('C4 — method strings from canonical enum', () => {
    beforeEach(() => Store.clear());

    for (const { name, fn } of PROVERS) {
      it(`${name} emits only PROVE_METHODS values`, () => {
        const { pattern, state } = scenario();
        const slots = {};
        const theta = [];

        const methods = [];
        const matchOpts = makeMatchOpts({
          ffi: STUB_FFI,
          onProveSuccess: (_g, method) => methods.push(method),
        });

        fn([pattern], 0, theta, slots, state, null, null, matchOpts);
        for (const m of methods) {
          assert.ok(PROVE_METHODS.includes(m),
            `${name}: method '${m}' not in PROVE_METHODS (${PROVE_METHODS.join(', ')})`);
        }
      });
    }

    it('PROVE_METHOD enum values are all present in PROVE_METHODS array', () => {
      for (const key of Object.keys(PROVE_METHOD)) {
        assert.ok(PROVE_METHODS.includes(PROVE_METHOD[key]),
          `PROVE_METHOD.${key} = '${PROVE_METHOD[key]}' must be in PROVE_METHODS`);
      }
    });
  });

  describe('return value contract — all provers return a number', () => {
    beforeEach(() => Store.clear());

    for (const { name, fn } of PROVERS) {
      it(`${name} returns a number (patterns.length on full success)`, () => {
        const { pattern, state } = scenario();
        const slots = {};
        const theta = [];
        const matchOpts = makeMatchOpts({ ffi: STUB_FFI });
        const ret = fn([pattern], 0, theta, slots, state, null, null, matchOpts);
        assert.equal(typeof ret, 'number', `${name} must return a number`);
        assert.equal(ret, 1, `${name} must return 1 (=patterns.length) on full success`);
      });
    }
  });
});

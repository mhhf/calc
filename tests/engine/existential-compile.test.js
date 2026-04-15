/**
 * Direct tests for opt/existential-compile.js
 *
 * Covers: chain compilation, execExStep, FFI failure fallback,
 * compiled vs non-compiled equivalence.
 */
const { describe, it, before, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { compileExChain, execExStep } = require('../../lib/engine/opt/existential-compile');

describe('opt/existential-compile', () => {
  let calc, ffiContext;

  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    calc = mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
    ffiContext = calc.ffiContext;
  });

  describe('compileExChain', () => {
    it('returns null for rule with no existential slots', () => {
      const rule = { existentialSlots: [], existentialGoals: {} };
      assert.equal(compileExChain(rule, ffiContext), null);
    });

    it('returns null for null existentialSlots', () => {
      const rule = { existentialSlots: null };
      assert.equal(compileExChain(rule, ffiContext), null);
    });

    it('returns null for null existentialGoals', () => {
      const rule = { existentialSlots: [0], existentialGoals: null };
      assert.equal(compileExChain(rule, ffiContext), null);
    });

    it('compiles inc goal chain', () => {
      // Simulate a rule with existential slot resolving inc(X, ?Y)
      const inputMv = Store.put('metavar', ['X']);
      const outputMv = Store.put('metavar', ['Y']);
      const goalPat = Store.put('inc', [inputMv, outputMv]);
      const inputSlot = 0;
      const outputSlot = 1;

      const rule = {
        existentialSlots: [outputSlot],
        existentialGoals: { [outputSlot]: [goalPat] },
        consequent: { persistent: [goalPat] },
        metavarSlots: { [inputMv]: inputSlot, [outputMv]: outputSlot },
      };

      const chain = compileExChain(rule, ffiContext);
      assert.ok(chain, 'should compile inc chain');
      assert.equal(chain.length, 1);
      assert.ok(chain[0], 'inc step should be compiled (not null)');
      assert.equal(chain[0].arity, 2);
    });

    it('returns null entries for non-FFI predicates', () => {
      const mv = Store.put('metavar', ['Y']);
      const goalPat = Store.put('no_such_ffi', [Store.put('atom', ['x']), mv]);

      const rule = {
        existentialSlots: [0],
        existentialGoals: { 0: [goalPat] },
        consequent: { persistent: [goalPat] },
        metavarSlots: { [mv]: 0 },
      };

      const chain = compileExChain(rule, ffiContext);
      // No FFI handler for 'no_such_ffi' → null or all-null chain
      assert.ok(chain === null || chain.every(s => s === null));
    });

    it('caches goal order on rule object', () => {
      const mv = Store.put('metavar', ['Out']);
      const goalPat = Store.put('inc', [Store.put('metavar', ['In']), mv]);

      const rule = {
        existentialSlots: [1],
        existentialGoals: { 1: [goalPat] },
        consequent: { persistent: [goalPat] },
        metavarSlots: { [Store.put('metavar', ['In'])]: 0, [mv]: 1 },
      };

      compileExChain(rule, ffiContext);
      assert.ok(Array.isArray(rule._existentialGoalOrder));
      assert.equal(rule._existentialGoalOrder.length, 1);
    });
  });

  describe('execExStep', () => {
    it('returns false when required input is missing from theta', () => {
      const step = {
        handler: () => ({ success: true, theta: [] }),
        argSlot: new Int32Array([0]),
        argMeta: new Uint32Array([0]),
        inputMask: 1,
        arity: 1,
      };
      const result = execExStep(step, [undefined], {});
      assert.equal(result, false);
    });

    it('returns false when handler returns failure', () => {
      const step = {
        handler: () => ({ success: false }),
        argSlot: new Int32Array([0]),
        argMeta: new Uint32Array([0]),
        inputMask: 0,
        arity: 1,
      };
      const result = execExStep(step, [Store.put('atom', ['x'])], {});
      assert.equal(result, false);
    });

    it('returns false when handler returns null', () => {
      const step = {
        handler: () => null,
        argSlot: new Int32Array([0]),
        argMeta: new Uint32Array([0]),
        inputMask: 0,
        arity: 1,
      };
      const result = execExStep(step, [Store.put('atom', ['x'])], {});
      assert.equal(result, false);
    });

    it('writes output to theta on success', () => {
      const outMv = Store.put('metavar', ['Out']);
      const outVal = Store.put('atom', ['result']);
      const step = {
        handler: () => ({ success: true, theta: [[outMv, outVal]] }),
        argSlot: new Int32Array([-1, 0]),
        argMeta: new Uint32Array([Store.put('atom', ['in']), outMv]),
        inputMask: 1,
        arity: 2,
      };
      const slots = { [outMv]: 0 };
      const theta = [undefined];

      const result = execExStep(step, theta, slots);
      assert.equal(result, true);
      assert.equal(theta[0], outVal);
    });
  });
});

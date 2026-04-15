/**
 * Direct tests for lnl/existential.js
 *
 * Covers: compiled chain dispatch, provePersistent fallback, freshEvar handling.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { resolveEx } = require('../../lib/engine/lnl/existential');

describe('lnl/existential — resolveEx', () => {
  beforeEach(() => Store.clear());

  it('returns true immediately when no existential slots', () => {
    const rule = { existentialSlots: [] };
    const result = resolveEx([], {}, rule, null, null, {});
    assert.equal(result, true);
  });

  it('returns true when existentialSlots is null', () => {
    const rule = { existentialSlots: null };
    const result = resolveEx([], {}, rule, null, null, {});
    assert.equal(result, true);
  });

  it('fills unbound slots with freshEvar (tag: evar)', () => {
    const mv = Store.put('metavar', ['E']);
    const slot = 0;
    const theta = [undefined];
    const slots = { [mv]: slot };
    const rule = {
      existentialSlots: [slot],
      existentialGoals: {},
      consequent: { persistent: [] },
    };

    const result = resolveEx(theta, slots, rule, null, null, {});
    assert.equal(result, true);
    assert.ok(theta[0] !== undefined, 'slot should be filled');
    assert.equal(Store.tag(theta[0]), 'evar');
  });

  it('calls provePersistent for goals without compiled chain', () => {
    const mv = Store.put('metavar', ['E']);
    const goalPat = Store.put('inc', [Store.put('atom', ['x']), mv]);
    const slot = 0;
    const theta = [undefined];
    const slots = { [mv]: slot };

    let proveCalled = false;
    const resolvedResult = Store.put('atom', ['result']);
    const matchOpts = {
      provePersistent: (goals, startIdx, th) => {
        proveCalled = true;
        th[slot] = resolvedResult;
        return goals.length;
      },
    };

    const rule = {
      existentialSlots: [slot],
      existentialGoals: { [slot]: [goalPat] },
      consequent: { persistent: [goalPat] },
    };

    resolveEx(theta, slots, rule, null, null, matchOpts);
    assert.ok(proveCalled);
    assert.equal(theta[0], resolvedResult);
  });

  it('uses compiled chain when available and useCompiledSteps is true', () => {
    const mv = Store.put('metavar', ['E']);
    const goalPat = Store.put('somepred', [Store.put('atom', ['in']), mv]);
    const slot = 0;
    const theta = [undefined];
    const slots = { [mv]: slot };

    let stepExecuted = false;
    const outVal = Store.put('atom', ['compiled_out']);
    const compiledChain = [{
      handler: () => { stepExecuted = true; return { success: true, theta: [[mv, outVal]] }; },
      argSlot: new Int32Array([-1, slot]),
      argMeta: new Uint32Array([Store.put('atom', ['in']), mv]),
      inputMask: 1,
      arity: 2,
    }];

    const rule = {
      existentialSlots: [slot],
      existentialGoals: { [slot]: [goalPat] },
      consequent: { persistent: [goalPat] },
      _existentialGoalOrder: [goalPat],
      _compiledExChain: compiledChain,
    };

    const matchOpts = { useCompiledSteps: true };

    resolveEx(theta, slots, rule, null, null, matchOpts);
    assert.ok(stepExecuted);
  });

  it('always returns true — exists never blocks', () => {
    const mv = Store.put('metavar', ['E']);
    const slot = 0;
    const theta = [undefined];
    const slots = { [mv]: slot };

    const matchOpts = {
      provePersistent: () => 0, // fails
    };

    const goalPat = Store.put('fail_pred', [mv]);
    const rule = {
      existentialSlots: [slot],
      existentialGoals: { [slot]: [goalPat] },
      consequent: { persistent: [goalPat] },
    };

    const result = resolveEx(theta, slots, rule, null, null, matchOpts);
    assert.equal(result, true);
    assert.ok(theta[0] !== undefined, 'should be filled with freshEvar');
    assert.equal(Store.tag(theta[0]), 'evar');
  });
});

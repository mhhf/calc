/**
 * Tests for engine hooks API (onStep, onProveFail).
 * Validates TODO_0147 Layer 1 — opt-in callbacks for forward/explore.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const mde = require('../../lib/engine');
const { show } = require('../../lib/engine/show');
const { PROVE_METHODS } = require('../../lib/engine/match');

const PROGRAM = path.join(__dirname, '..', '..', 'calculus', 'ill', 'programs', 'evm.ill');

describe('Engine Hooks API', { timeout: 10000 }, () => {
  let calc;
  before(() => {
    calc = mde.load(PROGRAM, { cache: true });
  });

  describe('onStep — forward.run()', () => {
    it('fires with correct shape', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * bytecode [0x00]')
      );
      const steps = [];
      const result = calc.exec(initial, {
        onStep: (payload) => steps.push(payload),
      });

      assert.ok(result.quiescent);
      assert.equal(steps.length, 1);

      const s = steps[0];
      assert.equal(typeof s.step, 'number');
      assert.equal(s.step, 1);
      assert.ok(s.rule);
      assert.equal(typeof s.rule.name, 'string');
      assert.ok(s.consumed);
      assert.ok(Array.isArray(s.theta));
      assert.ok(s.slots);
      assert.ok(s.state);
      // state is a live FactSet reference
      assert.ok(s.state.linear);
      assert.ok(typeof s.state.linear.group === 'function');
    });

    it('consumed and theta are snapshots', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );
      const snapshots = [];
      calc.exec(initial, {
        onStep: ({ consumed, theta }) => {
          snapshots.push({ consumed, theta });
        },
      });

      assert.ok(snapshots.length >= 2, `expected ≥2 steps, got ${snapshots.length}`);
      // Each snapshot is independent — mutating one doesn't affect others
      const c0 = snapshots[0].consumed;
      const c1 = snapshots[1].consumed;
      assert.notDeepStrictEqual(c0, c1, 'different steps consume different facts');
    });

    it('does not fire when not provided', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * bytecode [0x00]')
      );
      // No onStep — should not crash
      const result = calc.exec(initial, {});
      assert.ok(result.quiescent);
      assert.equal(result.steps, 1);
    });

    it('step counter is monotonically increasing', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );
      const steps = [];
      calc.exec(initial, {
        onStep: ({ step }) => steps.push(step),
      });

      for (let i = 1; i < steps.length; i++) {
        assert.ok(steps[i] > steps[i - 1], `step ${steps[i]} should be > ${steps[i - 1]}`);
      }
    });
  });

  describe('onStep — explore()', () => {
    it('fires with correct shape (depth field, not step)', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * bytecode [0x00]')
      );
      const steps = [];
      calc.explore(initial, {
        maxDepth: 10,
        onStep: (payload) => steps.push({ ...payload }),
      });

      assert.ok(steps.length >= 1);
      const s = steps[0];
      assert.equal(typeof s.depth, 'number');
      assert.equal(s.step, undefined, 'explore uses depth, not step');
      assert.ok(s.rule);
      assert.ok(s.consumed);
      assert.ok(Array.isArray(s.theta));
      assert.ok(s.state);
    });

    it('depth represents DFS nesting level', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * bytecode [0x00]')
      );
      const depths = [];
      calc.explore(initial, {
        maxDepth: 10,
        onStep: ({ depth }) => depths.push(depth),
      });

      // First-level matches are at depth 0
      assert.ok(depths.length >= 1);
      assert.equal(depths[0], 0);
    });
  });

  describe('onProveFail', () => {
    it('fires on out-of-gas: checked_sub(0, cost, ?) fails', () => {
      // ADD (0x01, cost 3) with gas 0 — checked_sub(0, 3, ?) is unprovable.
      // The engine tries every step/make variant; those requiring gas > 0 fail.
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0 * stack [0x1, 0x2] * bytecode [0x01]')
      );
      const failures = [];
      calc.exec(initial, {
        maxSteps: 10,
        onProveFail: (goal, reason) => failures.push({ goal: show(goal), reason }),
      });

      assert.ok(failures.length > 0, 'expected onProveFail calls for out-of-gas');
      for (const f of failures) {
        assert.ok(typeof f.goal === 'string');
        assert.ok(['cached_failure', 'external_binding', 'exhausted', 'ffi_mismatch'].includes(f.reason),
          `unknown reason: ${f.reason}`);
      }
      assert.ok(failures.some(f => f.goal.includes('checked_sub')),
        'expected checked_sub failure for out-of-gas');
    });

    it('does not fire when not provided', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * bytecode [0x00]')
      );
      // No onProveFail — should not crash
      const result = calc.exec(initial, {});
      assert.ok(result.quiescent);
    });
  });

  describe('onProveSuccess', () => {
    it('fires with correct shape (goal, method) for FFI path', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );
      const successes = [];
      calc.exec(initial, {
        dangerouslyUseFFI: true,
        onProveSuccess: (goal, method) => successes.push({ goal: show(goal), method }),
      });

      assert.ok(successes.length > 0, 'expected onProveSuccess calls');
      for (const s of successes) {
        assert.equal(typeof s.goal, 'string');
        assert.ok(PROVE_METHODS.includes(s.method),
          `unknown method: ${s.method}`);
      }
      // Hybrid path: goals resolved by compiled dispatch (structural) or FFI (arithmetic)
      assert.ok(successes.every(s => s.method === 'ffi' || s.method === 'compiled'),
        `expected ffi/compiled methods, got: ${[...new Set(successes.map(s => s.method))].join(', ')}`);
    });

    it('fires with cache/clause methods for noFFI path', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );
      const successes = [];
      calc.exec(initial, {
        onProveSuccess: (goal, method) => successes.push({ goal: show(goal), method }),
      });

      assert.ok(successes.length > 0, 'expected onProveSuccess calls');
      const methods = new Set(successes.map(s => s.method));
      // noFFI path should use compiled, cache, and/or clause — never ffi
      assert.ok(!methods.has('ffi'), 'noFFI path should not use ffi method');
      assert.ok(methods.has('compiled') || methods.has('cache') || methods.has('clause'),
        'expected compiled/cache/clause methods in noFFI path');
    });

    it('does not fire when not provided', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * bytecode [0x00]')
      );
      // No onProveSuccess — should not crash
      const result = calc.exec(initial, {});
      assert.ok(result.quiescent);
    });

    it('fires in explore mode', () => {
      const initial = mde.decomposeQuery(
        mde.parseExpr('pc 0 * gas 0xffffff * stack ae * mem empty_mem * memsize 0 * bytecode [0x60, 0x05, 0x00]')
      );
      const successes = [];
      calc.explore(initial, {
        maxDepth: 5,
        dangerouslyUseFFI: true,
        onProveSuccess: (goal, method) => successes.push({ goal: show(goal), method }),
      });

      assert.ok(successes.length > 0, 'expected onProveSuccess calls in explore mode');
      for (const s of successes) {
        assert.equal(typeof s.goal, 'string');
        assert.ok(PROVE_METHODS.includes(s.method));
      }
    });
  });
});

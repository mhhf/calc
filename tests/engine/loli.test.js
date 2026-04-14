/**
 * Direct tests for lnl/loli.js
 *
 * Covers: trigger formula decomposition, linear antecedent match,
 * persistent guard proving.
 */
const { describe, it, before } = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { FactSet } = require('../../lib/engine/fact-set');
const { matchLoli } = require('../../lib/engine/lnl/loli');
const { resolveConnectives } = require('../../lib/engine/compile');

describe('lnl/loli — matchLoli', () => {
  let calc, rc;

  before(() => {
    Store.clear();
    const mde = require('../../lib/engine/index');
    calc = mde.load(path.join(__dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });
    const ccfg = require('../../lib/engine/ill/calculus-config');
    rc = resolveConnectives(ccfg.connectives);
  });

  it('returns null when trigger linear fact not in state', () => {
    const trigger = Store.put('gas', [Store.put('atom', ['x'])]);
    const body = Store.put('pc', [Store.put('atom', ['y'])]);
    const loliHash = Store.put('loli', [trigger, Store.put('monad', [body])]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    // No trigger fact in state → should fail
    const state = {
      linear,
      persistent: new FactSet(Store.TAG_NAMES.length),
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    const result = matchLoli(loliHash, state, calc, { connectives: rc });
    assert.equal(result, null);
  });

  it('matches simple loli with linear trigger in state', () => {
    const val = Store.put('atom', ['v1']);
    const trigger = Store.put('gas', [val]);
    const body = Store.put('pc', [val]);
    const wrappedBody = Store.put('monad', [body]);
    const loliHash = Store.put('loli', [trigger, wrappedBody]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    linear.insert(Store.tagId(trigger), trigger, null);

    const state = {
      linear,
      persistent: new FactSet(Store.TAG_NAMES.length),
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    const result = matchLoli(loliHash, state, calc, { connectives: rc });
    assert.ok(result, 'should match');
    assert.ok(result.consumed[loliHash], 'loli should be consumed');
    assert.ok(result.consumed[trigger], 'trigger should be consumed');
  });

  it('returns result with rule name starting with loli:', () => {
    const val = Store.put('atom', ['v1']);
    const trigger = Store.put('gas', [val]);
    const body = Store.put('pc', [val]);
    const wrappedBody = Store.put('monad', [body]);
    const loliHash = Store.put('loli', [trigger, wrappedBody]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    linear.insert(Store.tagId(trigger), trigger, null);

    const state = {
      linear,
      persistent: new FactSet(Store.TAG_NAMES.length),
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    const result = matchLoli(loliHash, state, calc, { connectives: rc });
    assert.ok(result);
    assert.ok(result.rule.name.startsWith('loli:'));
  });

  it('handles loli with metavar in trigger', () => {
    const mv = Store.put('metavar', ['X']);
    const trigger = Store.put('gas', [mv]);
    const body = Store.put('pc', [mv]);
    const wrappedBody = Store.put('monad', [body]);
    const loliHash = Store.put('loli', [trigger, wrappedBody]);

    const val = Store.put('atom', ['concrete']);
    const triggerFact = Store.put('gas', [val]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    linear.insert(Store.tagId(triggerFact), triggerFact, null);

    const state = {
      linear,
      persistent: new FactSet(Store.TAG_NAMES.length),
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    const result = matchLoli(loliHash, state, calc, { connectives: rc });
    assert.ok(result, 'should match with metavar unification');
  });

  it('returns null when persistent guard cannot be proved', () => {
    const { GRADE_W } = require('../../lib/engine/grades');
    const guard = Store.put('foo_guard', [Store.put('atom', ['k'])]);
    const bangGuard = Store.put('bang', [GRADE_W, guard]);
    const val = Store.put('atom', ['v']);
    const gasF = Store.put('gas', [val]);
    const trigger = Store.put('tensor', [bangGuard, gasF]);
    const body = Store.put('pc', [val]);
    const loliHash = Store.put('loli', [trigger, Store.put('monad', [body])]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    linear.insert(Store.tagId(gasF), gasF, null);

    const state = {
      linear,
      persistent: new FactSet(Store.TAG_NAMES.length), // guard NOT in persistent
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    const result = matchLoli(loliHash, state, null, { connectives: rc });
    assert.equal(result, null, 'should fail: persistent guard not proveable');
  });

  it('matches loli with tensor(!guard, trigger) when guard in persistent state', () => {
    const { GRADE_W } = require('../../lib/engine/grades');
    const guard = Store.put('foo_guard2', [Store.put('atom', ['k2'])]);
    const bangGuard = Store.put('bang', [GRADE_W, guard]);
    const val = Store.put('atom', ['v2']);
    const gasF = Store.put('gas', [val]);
    const trigger = Store.put('tensor', [bangGuard, gasF]);
    const body = Store.put('pc', [val]);
    const loliHash = Store.put('loli', [trigger, Store.put('monad', [body])]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    linear.insert(Store.tagId(gasF), gasF, null);

    const persistent = new FactSet(Store.TAG_NAMES.length);
    persistent.insert(Store.tagId(guard), guard, null);

    const state = {
      linear,
      persistent,
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    const { provePersistentNaive } = require('../../lib/engine/lnl/persistent');
    const result = matchLoli(loliHash, state, null, {
      connectives: rc,
      provePersistent: provePersistentNaive,
    });
    assert.ok(result, 'should match when guard is in persistent state');
    assert.ok(result.consumed[loliHash], 'loli should be consumed');
    assert.ok(result.consumed[gasF], 'linear trigger should be consumed');
    assert.equal(result.consumed[guard], undefined, 'persistent guard must not be consumed');
  });

  it('calls provePersistent with inner formula of !guard', () => {
    const { GRADE_W } = require('../../lib/engine/grades');
    const guard = Store.put('foo_guard3', [Store.put('atom', ['x3'])]);
    const bangGuard = Store.put('bang', [GRADE_W, guard]);
    const val = Store.put('atom', ['w3']);
    const gasF = Store.put('gas', [val]);
    const trigger = Store.put('tensor', [bangGuard, gasF]);
    const loliHash = Store.put('loli', [trigger, Store.put('monad', [Store.put('pc', [val])])]);

    const linear = new FactSet(Store.TAG_NAMES.length);
    linear.insert(Store.tagId(loliHash), loliHash, null);
    linear.insert(Store.tagId(gasF), gasF, null);

    const state = {
      linear,
      persistent: new FactSet(Store.TAG_NAMES.length),
      groupForPred: (pred) => {
        const tid = Store.TAG[pred];
        return (tid !== undefined) ? linear.group(tid) : [];
      },
    };

    let capturedPatterns = null;
    const provePersistent = (patterns, startIdx, theta, slots, _s, _c, _e, _o) => {
      capturedPatterns = patterns.slice();
      return patterns.length; // pretend proved
    };

    const result = matchLoli(loliHash, state, null, {
      connectives: rc,
      provePersistent,
    });

    assert.ok(result, 'should match with stub prover');
    assert.ok(capturedPatterns, 'provePersistent should have been called');
    assert.equal(capturedPatterns.length, 1, 'exactly one persistent pattern');
    assert.equal(capturedPatterns[0], guard, 'inner formula of !guard passed, not bang wrapper');
  });
});

/**
 * Direct tests for compose.js:sortGoals
 *
 * Covers: mode-aware ordering, cycle handling, multiModal scenarios.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { sortGoals } = require('../../lib/engine/compose');

describe('sortGoals', () => {
  beforeEach(() => Store.clear());

  it('returns goals unchanged when single goal', () => {
    const g = Store.put('foo', [Store.put('atom', ['x'])]);
    const result = sortGoals([g], [], () => null);
    assert.deepEqual(result, [g]);
  });

  it('returns goals unchanged when no getModeMeta', () => {
    const g1 = Store.put('foo', [Store.put('atom', ['x'])]);
    const g2 = Store.put('bar', [Store.put('atom', ['y'])]);
    const result = sortGoals([g1, g2], [], null);
    assert.deepEqual(result, [g1, g2]);
  });

  it('sorts by data dependencies (output of first feeds input of second)', () => {
    // goal1: inc(X, ?Y) — X is input (from linear), ?Y is output
    // goal2: plus(?Y, Z, ?R) — ?Y is input (from goal1), Z from linear, ?R is output
    // If placed in wrong order, goal2 can't fire before goal1 resolves ?Y
    const mvX = Store.put('metavar', ['X']);
    const mvY = Store.put('metavar', ['Y']);
    const mvZ = Store.put('metavar', ['Z']);
    const mvR = Store.put('metavar', ['R']);

    const goal1 = Store.put('inc', [mvX, mvY]);
    const goal2 = Store.put('plus', [mvY, mvZ, mvR]);

    // Linear patterns ground X and Z
    const linearPatterns = [
      Store.put('some_pred', [mvX]),
      Store.put('other', [mvZ]),
    ];

    const getModeMeta = (pred) => {
      if (pred === 'inc') return { modes: ['+', '-'], multiModal: false };
      if (pred === 'plus') return { modes: ['+', '+', '-'], multiModal: false };
      return null;
    };

    // goal2 depends on goal1's output (mvY), so goal1 must come first
    const result = sortGoals([goal2, goal1], linearPatterns, getModeMeta);
    assert.equal(result[0], goal1);
    assert.equal(result[1], goal2);
  });

  it('handles cycles — appends remaining in original order', () => {
    // Two goals that each depend on the other's output → cycle
    const mvA = Store.put('metavar', ['A']);
    const mvB = Store.put('metavar', ['B']);

    const goal1 = Store.put('foo', [mvA, mvB]); // needs A, produces B
    const goal2 = Store.put('bar', [mvB, mvA]); // needs B, produces A

    const getModeMeta = () => ({ modes: ['+', '-'], multiModal: false });

    // Neither can be scheduled first → both end up in remaining
    const result = sortGoals([goal1, goal2], [], getModeMeta);
    assert.equal(result.length, 2);
  });

  it('multiModal allows one ungrounded input', () => {
    const mvX = Store.put('metavar', ['X']);
    const mvY = Store.put('metavar', ['Y']);
    const goal = Store.put('gt', [mvX, mvY, Store.put('atom', ['c']), Store.put('metavar', ['R'])]);

    // multiModal: true → allows one ungrounded input
    // X is grounded by linear, Y is not — should still be ready
    const linearPatterns = [Store.put('src', [mvX])];
    const getModeMeta = () => ({ modes: ['+', '+', '+', '-'], multiModal: true });

    const result = sortGoals([goal], linearPatterns, getModeMeta);
    assert.equal(result.length, 1);
    assert.equal(result[0], goal);
  });

  it('conservative: no mode info → all metavars must be grounded', () => {
    const mvX = Store.put('metavar', ['X']);
    const goal = Store.put('unknown_pred', [mvX]);

    const getModeMeta = () => null; // no mode info
    // mvX is not grounded → goal not ready → goes to remaining
    const result = sortGoals([goal], [], getModeMeta);
    assert.equal(result.length, 1);
  });
});

/**
 * Direct tests for constraint-feed.js
 *
 * Covers: feedPersistent (arena → solver), filterAltsBySAT (oplus pruning).
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { FactSet, Arena } = require('../../lib/engine/fact-set');
const { feedPersistent, filterAltsBySAT } = require('../../lib/engine/constraint-feed');

// Minimal EqNeqSolver stub — tracks constraints + SAT state
function makeSolver(satResult = true) {
  const constraints = [];
  let cp = 0;
  return {
    constraints,
    addConstraint(h) { constraints.push(h); },
    checkpoint() { return constraints.length; },
    restore(scp) { constraints.length = scp; },
    checkSAT() { return typeof satResult === 'function' ? satResult() : satResult; },
  };
}

describe('constraint-feed', () => {
  beforeEach(() => Store.clear());

  describe('feedPersistent', () => {
    it('feeds INSERT records from arena into solver', () => {
      const fs = new FactSet();
      const arena = new Arena();
      const h1 = Store.put('atom', ['fact1']);
      const h2 = Store.put('atom', ['fact2']);
      const tagId1 = Store.tagId(h1);
      const tagId2 = Store.tagId(h2);

      const checkpoint = arena.cursor;
      fs.insert(tagId1, h1, arena);
      fs.insert(tagId2, h2, arena);

      const solver = makeSolver();
      feedPersistent(solver, arena, checkpoint);
      assert.equal(solver.constraints.length, 2);
      assert.ok(solver.constraints.includes(h1));
      assert.ok(solver.constraints.includes(h2));
    });

    it('skips records before checkpoint', () => {
      const fs = new FactSet();
      const arena = new Arena();
      const h1 = Store.put('atom', ['old']);
      fs.insert(Store.tagId(h1), h1, arena);

      const checkpoint = arena.cursor;
      const h2 = Store.put('atom', ['new']);
      fs.insert(Store.tagId(h2), h2, arena);

      const solver = makeSolver();
      feedPersistent(solver, arena, checkpoint);
      assert.equal(solver.constraints.length, 1);
      assert.equal(solver.constraints[0], h2);
    });
  });

  describe('filterAltsBySAT', () => {
    it('returns all indices when solver always returns SAT', () => {
      const solver = makeSolver(true);
      const alts = [
        { persistent: [Store.put('atom', ['a'])] },
        { persistent: [Store.put('atom', ['b'])] },
      ];
      const theta = [];
      const slots = {};
      const result = filterAltsBySAT(solver, alts, theta, slots);
      assert.deepEqual(result, [0, 1]);
    });

    it('filters out UNSAT alternatives', () => {
      let callCount = 0;
      const solver = makeSolver(() => {
        callCount++;
        return callCount !== 2; // second alternative is UNSAT
      });
      const alts = [
        { persistent: [Store.put('atom', ['a'])] },
        { persistent: [Store.put('atom', ['b'])] },
        { persistent: [Store.put('atom', ['c'])] },
      ];
      const result = filterAltsBySAT(solver, alts, [], {});
      assert.deepEqual(result, [0, 2]);
    });

    it('restores solver state after each alternative', () => {
      const solver = makeSolver(true);
      const p1 = Store.put('atom', ['p1']);
      const p2 = Store.put('atom', ['p2']);
      const alts = [{ persistent: [p1] }, { persistent: [p2] }];

      const cpBefore = solver.checkpoint();
      filterAltsBySAT(solver, alts, [], {});
      assert.equal(solver.constraints.length, cpBefore);
    });

    it('returns empty array when all alternatives UNSAT', () => {
      const solver = makeSolver(false);
      const alts = [
        { persistent: [Store.put('atom', ['x'])] },
      ];
      const result = filterAltsBySAT(solver, alts, [], {});
      assert.deepEqual(result, []);
    });
  });
});

/**
 * Sort-order machinery (TODO_0011 rung 1) — unit tests for
 * lib/engine/sorts.js: universe derivation, DAG closure, subsort/lub,
 * classifier membership, constraint satisfiability, cycle/hygiene errors.
 *
 * The subsort DAG is a compiled INDEX; the semantics is the sedge facts
 * plus the loader-materialized `subsort` closure — agreement is tested in
 * tests/sorts-fuzz.test.js (table vs prover).
 */

import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../lib/kernel/store.js';
import { buildSortSystem, SORT_PREDS } from '../lib/engine/sorts.js';

const atom = (n) => Store.put('atom', [n]);
const type = () => Store.put('type', []);
const arrow = (a, b) => Store.put('arrow', [a, b]);

/** definitions with the machinery names declared (as sorts.till would). */
function machineryDefs() {
  const d = new Map();
  d.set(SORT_PREDS.SORT, type());
  d.set(SORT_PREDS.EDGE, arrow(atom(SORT_PREDS.SORT), arrow(atom(SORT_PREDS.SORT), type())));
  d.set(SORT_PREDS.SUB, arrow(atom(SORT_PREDS.SORT), arrow(atom(SORT_PREDS.SORT), type())));
  return d;
}

function edgeClause(clauses, sub, sup) {
  clauses.set(`${SORT_PREDS.EDGE}/${sub}/${sup}`, {
    hash: Store.put(SORT_PREDS.EDGE, [atom(sub), atom(sup)]),
    premises: [],
  });
}

describe('sort system construction', () => {
  let defs, clauses;
  beforeEach(() => {
    defs = machineryDefs();
    defs.set('q', type());
    defs.set('bin', type());
    defs.set('delay', type());
    defs.set('e', atom('bin'));
    clauses = new Map();
  });

  it('absent machinery → null system (presence-gated)', () => {
    const sys = buildSortSystem({ definitions: new Map([['go', type()]]), clauses: new Map() });
    assert.equal(sys, null);
  });

  it('builds reflexive-transitive closure from declared edges', () => {
    edgeClause(clauses, 'bin', 'delay');
    edgeClause(clauses, 'delay', 'q');
    const sys = buildSortSystem({ definitions: defs, clauses });
    assert.ok(sys);
    assert.ok(sys.subsort('bin', 'bin'));      // refl
    assert.ok(sys.subsort('bin', 'delay'));    // edge
    assert.ok(sys.subsort('bin', 'q'));        // trans
    assert.ok(!sys.subsort('q', 'bin'));       // no flip
    assert.ok(!sys.subsort('delay', 'bin'));
  });

  it('every declared sort inhabits the meta-sort (term membership, not subsort order)', () => {
    edgeClause(clauses, 'bin', 'q');
    const sys = buildSortSystem({ definitions: defs, clauses });
    assert.ok(sys.isSort('bin'));
    assert.ok(sys.isSort('q'));
    assert.ok(!sys.isSort('e'));            // constructor, not a sort
    assert.ok(!sys.subsort('bin', SORT_PREDS.SORT)); // sort-hood is NOT ≤
  });

  it('classifiers refine the proposition sort; members are collected', () => {
    defs.set('resource', atom(SORT_PREDS.SORT));
    defs.set('wood', atom('resource'));
    defs.set('stone', atom('resource'));
    const sys = buildSortSystem({ definitions: defs, clauses });
    assert.ok(sys.subsort('resource', 'type'));          // classifier ≤ type
    assert.ok(!sys.subsort('bin', 'type'));              // term sorts do NOT
    assert.deepEqual([...sys.membersOf('resource')].sort(), ['stone', 'wood']);
  });

  it('lub: unique least upper bound or a reported failure', () => {
    edgeClause(clauses, 'bin', 'delay');
    edgeClause(clauses, 'bin', 'q');
    edgeClause(clauses, 'delay', 'q');
    defs.set('rat', type());
    edgeClause(clauses, 'rat', 'q');
    const sys = buildSortSystem({ definitions: defs, clauses });
    assert.equal(sys.lub(['bin', 'bin']).sort, 'bin');
    assert.equal(sys.lub(['bin', 'rat']).sort, 'q');
    assert.equal(sys.lub(['bin', 'delay']).sort, 'delay');
    // no common ancestor
    defs.set('resource', atom(SORT_PREDS.SORT));
    const sys2 = buildSortSystem({ definitions: defs, clauses });
    assert.ok(sys2.lub(['bin', 'resource']).error);
  });

  it('constraint satisfiability: ∃ sort below all upper bounds', () => {
    edgeClause(clauses, 'bin', 'delay');
    edgeClause(clauses, 'bin', 'q');
    defs.set('resource', atom(SORT_PREDS.SORT));
    const sys = buildSortSystem({ definitions: defs, clauses });
    assert.ok(sys.satisfiable(new Set(['delay', 'q'])));      // bin fits
    assert.ok(sys.satisfiable(new Set(['bin'])));
    assert.ok(!sys.satisfiable(new Set(['bin', 'resource']))); // disjoint worlds
  });

  it('subsort cycle is a load error', () => {
    edgeClause(clauses, 'bin', 'q');
    edgeClause(clauses, 'q', 'bin');
    assert.throws(() => buildSortSystem({ definitions: defs, clauses }), /cycle/i);
  });

  it('edge operand that is not a declared sort is a load error', () => {
    edgeClause(clauses, 'bin', 'ghost');
    assert.throws(() => buildSortSystem({ definitions: defs, clauses }), /unknown sort 'ghost'/);
  });

  it('edges without the machinery prelude point at the import', () => {
    const bare = new Map([['q', type()], ['bin', type()]]);
    const cl = new Map();
    edgeClause(cl, 'bin', 'q');
    assert.throws(() => buildSortSystem({ definitions: bare, clauses: cl }),
      /sorts prelude/);
  });

  it('calc-level sorts and members merge into the universe', () => {
    edgeClause(clauses, 'delay', 'q');
    const sys = buildSortSystem({
      definitions: defs, clauses,
      calc: {
        edges: [['delay', 'grade'], ['count', 'grade']],
        members: { g0: 'count', gw: 'count' },
      },
    });
    assert.ok(sys.subsort('delay', 'grade'));
    assert.ok(sys.subsort('count', 'grade'));
    assert.equal(sys.leastSortOfName('g0'), 'count');
    assert.ok(sys.subsort('delay', 'q'));   // program edge still there
  });
});

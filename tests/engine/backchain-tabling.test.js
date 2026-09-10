/**
 * Tabling / loop detection in the SLD backchainer (TODO_0009 Axis 3 rung 1).
 *
 * Opt-in (`opts.loopCheck`) path-based cycle detection: a goal that recurs
 * identically on its own root-to-node path is an inductive loop with no
 * finite proof, so the branch fails — detected AT the cycle instead of after
 * grinding to maxDepth. This is the sound half of "loop = success/failure by
 * polarity"; coinductive success on a guarded loop is rung 2 (the global
 * trace condition), deliberately not attempted here.
 *
 * The pins establish: (1) loops are cut precisely and early; (2) valid finite
 * proofs are UNAFFECTED (completeness preserved); (3) it never proves a false
 * goal (soundness); (4) default-off leaves behaviour identical.
 */
import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert/strict';
import Store from '../../lib/kernel/store.js';
import backward from '../../lib/engine/backchain.js';
import { makeILLBackchainOpts } from '../../calculus/ill/lib/backchain-ill.js';

beforeEach(() => { Store.clear(); });
const A = (s) => Store.put('atom', [s]);
const MV = (s) => Store.put('metavar', [s]);
const prove = (goal, clauses, types, opts) =>
  backward.prove(goal, clauses, types, { ...makeILLBackchainOpts(), ...opts });

describe('backchain tabling — inductive loop detection (TODO_0009 rung 1)', () => {
  it('cuts a direct self-loop (p <- p) at the cycle, not at maxDepth', () => {
    const p = A('p');
    const clauses = new Map([['loop', { hash: p, premises: [p] }]]);
    const types = new Map();

    const off = prove(p, clauses, types, { maxDepth: 5000, trace: true });
    const on = prove(p, clauses, types, { maxDepth: 5000, trace: true, loopCheck: true });

    assert.equal(off.success, false, 'unprovable either way (no base case)');
    assert.equal(on.success, false);
    // precision: loopCheck fails after ~1 descent; depth-capping grinds to 5000
    assert.ok(on.trace.length < 10, `loopCheck cut early (${on.trace.length} steps)`);
    assert.ok(off.trace.length > 1000, `depth-cap ground on (${off.trace.length} steps)`);
    assert.ok(on.trace.some(l => /loop on/.test(l)), 'the cycle is reported');
  });

  it('cuts a mutual loop (a <- b, b <- a)', () => {
    const a = A('a'), b = A('b');
    const clauses = new Map([
      ['r1', { hash: a, premises: [b] }],
      ['r2', { hash: b, premises: [a] }],
    ]);
    const r = prove(a, clauses, new Map(), { maxDepth: 5000, loopCheck: true, trace: true });
    assert.equal(r.success, false);
    assert.ok(r.trace.length < 12, 'cut at the a→b→a cycle');
  });

  it('a self-loop clause does not block a base-case clause for the same goal', () => {
    // p has TWO clauses: a looping one (p <- p) and a fact (p). loopCheck must
    // cut only the looping branch and still find the fact → success.
    const p = A('p');
    const clauses = new Map([['loop', { hash: p, premises: [p] }]]);
    const types = new Map([['fact', p]]);   // p is also an axiom
    const r = prove(p, clauses, types, { loopCheck: true });
    assert.equal(r.success, true, 'the base-case axiom still proves p');
  });
});

describe('backchain tabling — completeness preserved (valid proofs unaffected)', () => {
  // nat(e).  nat(s N) <- nat N.   Each recursion is a DISTINCT goal, so no
  // identical loop fires; the proof must still succeed under loopCheck.
  function natProgram() {
    const e = A('e');
    const s = (x) => Store.put('s', [x]);
    const nat = (x) => Store.put('nat', [x]);
    const N = MV('N');
    const types = new Map([['nat/z', nat(e)]]);
    const clauses = new Map([['nat/s', { hash: nat(s(N)), premises: [nat(N)] }]]);
    return { types, clauses, nat, s, e };
  }

  it('a finite recursive proof succeeds identically with loopCheck on and off', () => {
    const { types, clauses, nat, s, e } = natProgram();
    const goal = nat(s(s(s(e))));            // nat(s^3(e))
    assert.equal(prove(goal, clauses, types, {}).success, true);
    assert.equal(prove(goal, clauses, types, { loopCheck: true }).success, true);
  });

  it('a genuinely-unprovable finite goal fails both ways (no false success)', () => {
    const { types, clauses, nat, s, e } = natProgram();
    // odd constructor never introduced — unprovable, and NOT a loop
    const goal = nat(Store.put('bad', [e]));
    assert.equal(prove(goal, clauses, types, {}).success, false);
    assert.equal(prove(goal, clauses, types, { loopCheck: true }).success, false);
  });
});

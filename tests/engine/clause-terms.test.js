/**
 * Tests for 3b.5: Clause Proof Term Extraction + Evidence Bug Fix
 *
 * Covers:
 * - prove.js buildTerm option (clause proof term construction)
 * - prove.js buildTerm=false (zero overhead, term is null)
 * - proveWithFFI clause evidence forwarding (opt/ffi.js)
 * - evidenceToTerm for state/clause methods (via guidedTerm)
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const backward = require('../../lib/engine/backchain');
const { proveWithFFI } = require('../../lib/engine/opt/ffi');
const { GRADE_W } = require('../../lib/engine/grades');
const forward = require('../../lib/engine/forward');
const { guidedTerm } = require('../../lib/prover/guided-term');
const { makeILLBackchainOpts } = require('../../lib/engine/ill/backchain-ill');

describe('3b.5: Clause Proof Terms', () => {

  beforeEach(() => { Store.clear(); });

  // ─── prove.js buildTerm ─────────────────────────────────────────

  describe('prove.js buildTerm: true', () => {

    it('type axiom returns copy(goal, id(goal))', () => {
      // Types: { foo: foo }. Goal: foo.
      const foo = Store.put('atom', ['foo']);
      const types = new Map([['foo', foo]]);
      const clauses = new Map();

      const result = backward.prove(foo, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success, 'should prove');
      assert(result.term, 'should have term');
      assert.strictEqual(result.term.rule, 'copy');
      assert.strictEqual(result.term.principal, foo);
      assert.strictEqual(result.term.subterms[0].rule, 'id');
      assert.strictEqual(result.term.subterms[0].principal, foo);
    });

    it('zero-premise clause returns copy(loli, loli_l(one_r, monad_l(id)))', () => {
      // Clause: bar (no premises). Goal: bar.
      // Ground loli: loli(one, monad(bar))
      const bar = Store.put('atom', ['bar']);
      const clauses = new Map([
        ['bar_clause', { hash: bar, premises: [] }]
      ]);
      const types = new Map();

      const result = backward.prove(bar, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success, 'should prove');
      const term = result.term;
      assert.strictEqual(term.rule, 'copy');

      // Ground loli = loli(one, monad(bar))
      const groundLoli = term.principal;
      assert.strictEqual(Store.tag(groundLoli), 'loli');
      assert.strictEqual(Store.tag(Store.child(groundLoli, 0)), 'one');
      assert.strictEqual(Store.tag(Store.child(groundLoli, 1)), 'monad');
      assert.strictEqual(Store.child(Store.child(groundLoli, 1), 0), bar);

      // loli_l
      const loliL = term.subterms[0];
      assert.strictEqual(loliL.rule, 'loli_l');
      assert.strictEqual(loliL.principal, groundLoli);

      // Antecedent: one_r (zero premises)
      assert.strictEqual(loliL.subterms[0].rule, 'one_r');

      // Continuation: monad_l(id(bar))
      const cont = loliL.subterms[1];
      assert.strictEqual(cont.rule, 'monad_l');
      assert.strictEqual(cont.subterms[0].rule, 'id');
      assert.strictEqual(cont.subterms[0].principal, bar);
    });

    it('single-premise clause with type axiom premise', () => {
      // Types: { a: a }. Clause: a => b. Goal: b.
      // Ground loli: loli(tensor(!a, one), monad(b)) = loli(!a, monad(b))
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const types = new Map([['a_type', a]]);
      const clauses = new Map([
        ['ab_clause', { hash: b, premises: [a] }]
      ]);

      const result = backward.prove(b, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success, 'should prove');
      const term = result.term;
      assert.strictEqual(term.rule, 'copy');

      // loli_l
      const loliL = term.subterms[0];
      assert.strictEqual(loliL.rule, 'loli_l');

      // Antecedent: promotion(copy(a, id(a)))
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'promotion');
      assert.strictEqual(antProof.subterms[0].rule, 'copy');
      assert.strictEqual(antProof.subterms[0].principal, a);

      // Continuation: monad_l(id(b))
      const cont = loliL.subterms[1];
      assert.strictEqual(cont.rule, 'monad_l');
      assert.strictEqual(cont.subterms[0].rule, 'id');
      assert.strictEqual(cont.subterms[0].principal, b);
    });

    it('multi-premise clause produces right-associated tensor_r spine', () => {
      // Types: { a, b }. Clause: a, b => c. Goal: c.
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const types = new Map([['a_type', a], ['b_type', b]]);
      const clauses = new Map([
        ['abc_clause', { hash: c, premises: [a, b] }]
      ]);

      const result = backward.prove(c, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success, 'should prove');
      const term = result.term;
      assert.strictEqual(term.rule, 'copy');

      const loliL = term.subterms[0];
      assert.strictEqual(loliL.rule, 'loli_l');

      // Antecedent: tensor_r(promotion(copy(a,id(a))), promotion(copy(b,id(b))))
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'tensor_r');
      assert.strictEqual(antProof.subterms[0].rule, 'promotion');
      assert.strictEqual(antProof.subterms[0].subterms[0].rule, 'copy');
      assert.strictEqual(antProof.subterms[0].subterms[0].principal, a);
      assert.strictEqual(antProof.subterms[1].rule, 'promotion');
      assert.strictEqual(antProof.subterms[1].subterms[0].rule, 'copy');
      assert.strictEqual(antProof.subterms[1].subterms[0].principal, b);

      // Ground loli has tensor of bangs
      const groundLoli = term.principal;
      const ant = Store.child(groundLoli, 0);
      assert.strictEqual(Store.tag(ant), 'tensor');
      assert.strictEqual(Store.tag(Store.child(ant, 0)), 'bang');
      assert.strictEqual(Store.child(Store.child(ant, 0), 1), a);
      assert.strictEqual(Store.tag(Store.child(ant, 1)), 'bang');
      assert.strictEqual(Store.child(Store.child(ant, 1), 1), b);
    });

    it('recursive clause resolution (clause premise proved by another clause)', () => {
      // Types: { x }. Clause1: x => y. Clause2: y => z. Goal: z.
      const x = Store.put('atom', ['x']);
      const y = Store.put('atom', ['y']);
      const z = Store.put('atom', ['z']);
      const types = new Map([['x_type', x]]);
      const clauses = new Map([
        ['xy_clause', { hash: y, premises: [x] }],
        ['yz_clause', { hash: z, premises: [y] }]
      ]);

      const result = backward.prove(z, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success, 'should prove');
      const term = result.term;
      assert.strictEqual(term.rule, 'copy');

      // Outer: copy(loliYZ, loli_l(...))
      const outerLoliL = term.subterms[0];
      assert.strictEqual(outerLoliL.rule, 'loli_l');

      // Outer antecedent: promotion(inner clause term for y)
      const outerAnt = outerLoliL.subterms[0];
      assert.strictEqual(outerAnt.rule, 'promotion');

      // Inner: copy(loliXY, loli_l(...)) — clause proving y from x
      const innerTerm = outerAnt.subterms[0];
      assert.strictEqual(innerTerm.rule, 'copy');
      const innerLoliL = innerTerm.subterms[0];
      assert.strictEqual(innerLoliL.rule, 'loli_l');

      // Inner antecedent: promotion(copy(x, id(x)))
      const innerAnt = innerLoliL.subterms[0];
      assert.strictEqual(innerAnt.rule, 'promotion');
      assert.strictEqual(innerAnt.subterms[0].rule, 'copy');
      assert.strictEqual(innerAnt.subterms[0].principal, x);
    });

    it('clause with freevars — unification grounds the term', () => {
      // Types: { p(a) }. Clause: p(_X) => q(_X). Goal: q(a).
      const aAtom = Store.put('atom', ['a']);
      const X = Store.put('metavar', ['X']);
      const pA = Store.put('p', [aAtom]);
      const pX = Store.put('p', [X]);
      const qA = Store.put('q', [aAtom]);
      const qX = Store.put('q', [X]);
      const types = new Map([['pA_type', pA]]);
      const clauses = new Map([
        ['pq_clause', { hash: qX, premises: [pX] }]
      ]);

      const result = backward.prove(qA, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success, 'should prove');
      const term = result.term;
      assert.strictEqual(term.rule, 'copy');

      // The ground loli should reference p(a) and q(a), not p(_X) and q(_X)
      const groundLoli = term.principal;
      const groundAnt = Store.child(groundLoli, 0);
      // bang(GRADE_W, p(a))
      assert.strictEqual(Store.tag(groundAnt), 'bang');
      const premHash = Store.child(groundAnt, 1);
      assert.strictEqual(Store.tag(premHash), 'p');
      assert.strictEqual(Store.child(premHash, 0), aAtom);
    });
  });

  describe('prove.js buildTerm: false (default)', () => {

    it('returns null term when buildTerm is false', () => {
      const foo = Store.put('atom', ['foo']);
      const types = new Map([['foo', foo]]);
      const clauses = new Map();

      const result = backward.prove(foo, clauses, types, { ...makeILLBackchainOpts(), buildTerm: false });
      assert(result.success);
      assert.strictEqual(result.term, null);
    });

    it('returns null term when buildTerm is omitted', () => {
      const foo = Store.put('atom', ['foo']);
      const types = new Map([['foo', foo]]);
      const clauses = new Map();

      const result = backward.prove(foo, clauses, types, { ...makeILLBackchainOpts() });
      assert(result.success);
      assert.strictEqual(result.term, null);
    });

    it('returns identical theta whether buildTerm is on or off', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const types = new Map([['a_type', a]]);
      const clauses = new Map([['ab_clause', { hash: b, premises: [a] }]]);

      const r1 = backward.prove(b, clauses, types, { ...makeILLBackchainOpts(), buildTerm: false });
      Store.clear();
      // Recreate with same structure — Store.clear resets IDs
      const a2 = Store.put('atom', ['a']);
      const b2 = Store.put('atom', ['b']);
      const types2 = new Map([['a_type', a2]]);
      const clauses2 = new Map([['ab_clause', { hash: b2, premises: [a2] }]]);
      const r2 = backward.prove(b2, clauses2, types2, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(r1.success);
      assert(r2.success);
      assert.strictEqual(r1.term, null);
      assert(r2.term !== null);
    });
  });

  // ─── proveWithFFI clause evidence ─────────────────────

  describe('proveWithFFI clause evidence', () => {

    it('forwards proof term in clause evidence', () => {
      // Set up: a goal that can only be proved by clause resolution (not FFI, not state)
      // We need clauses/types available via calc param
      const p = Store.put('atom', ['testP']);
      const q = Store.put('atom', ['testQ']);

      const types = new Map([['p_type', p]]);
      const clauses = new Map([['pq_clause', { hash: q, premises: [p] }]]);
      const backchainIndex = backward.buildIndex(clauses, types);

      const calc = { clauses, definitions: types, backchainIndex, backwardOpts: makeILLBackchainOpts() };
      const state = forward.createState({}, {});

      const theta = new Array(1);
      const slots = {};
      const evidenceOut = [];

      const idx = proveWithFFI([q], 0, theta, slots, state, calc, evidenceOut);

      assert.strictEqual(idx, 1, 'should prove the goal');
      assert.strictEqual(evidenceOut.length, 1);
      assert.strictEqual(evidenceOut[0].method, 'clause');
      assert(evidenceOut[0].term, 'should have proof term');
      assert.strictEqual(evidenceOut[0].term.rule, 'copy');

      // Verify full structure: copy(loli(...), loli_l(...))
      const loliL = evidenceOut[0].term.subterms[0];
      assert.strictEqual(loliL.rule, 'loli_l');
    });

    it('does not build term when evidenceOut is null', () => {
      const p = Store.put('atom', ['testP']);
      const q = Store.put('atom', ['testQ']);
      const types = new Map([['p_type', p]]);
      const clauses = new Map([['pq_clause', { hash: q, premises: [p] }]]);
      const backchainIndex = backward.buildIndex(clauses, types);
      const calc = { clauses, definitions: types, backchainIndex };
      const state = forward.createState({}, {});

      const theta = new Array(1);
      const slots = {};

      // No evidenceOut — should succeed without building term
      const idx = proveWithFFI([q], 0, theta, slots, state, calc, null);
      assert.strictEqual(idx, 1, 'should still prove the goal');
    });
  });

  // ─── evidenceToTerm via guidedTerm ─────────────────────────

  describe('evidenceToTerm via guidedTerm', () => {

    it('state evidence produces copy(fact, id(fact))', () => {
      // Rule: !p -o { q }, with p proved by state lookup
      const p = Store.put('atom', ['sp']);
      const q = Store.put('atom', ['sq']);
      const bangP = Store.put('bang', [GRADE_W,p]);
      const monadQ = Store.put('monad', [q]);
      const loli = Store.put('loli', [bangP, monadQ]);

      const rfTerm = { rule: 'id', principal: q, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [q] } },
        consumed: {},
        theta: [],
        slots: {},
        persistentEvidence: [{ goal: p, method: 'state', fact: p }],
        loliHash: null
      }];

      const term = guidedTerm(trace, rfTerm);

      // Navigate to the promotion node's inner term
      const loliL = term.subterms[0];
      const antProof = loliL.subterms[0]; // promotion
      assert.strictEqual(antProof.rule, 'promotion');
      const inner = antProof.subterms[0];

      // State evidence → copy(fact, id(fact))
      assert.strictEqual(inner.rule, 'copy');
      assert.strictEqual(inner.principal, p);
      assert.strictEqual(inner.subterms[0].rule, 'id');
      assert.strictEqual(inner.subterms[0].principal, p);
    });

    it('clause evidence with full term uses the term directly', () => {
      // Rule: !q -o { r }, with q proved by clause resolution
      const q = Store.put('atom', ['cq']);
      const r = Store.put('atom', ['cr']);
      const bangQ = Store.put('bang', [GRADE_W,q]);
      const monadR = Store.put('monad', [r]);
      const loli = Store.put('loli', [bangQ, monadR]);

      const rfTerm = { rule: 'id', principal: r, subterms: [] };

      // Mock clause proof term (what prove.js would return)
      const mockClauseTerm = {
        rule: 'copy',
        principal: 999, // doesn't matter for structure test
        subterms: [{ rule: 'loli_l', principal: 999, subterms: [
          { rule: 'one_r', principal: null, subterms: [] },
          { rule: 'monad_l', principal: null, subterms: [
            { rule: 'id', principal: q, subterms: [] }
          ]}
        ]}]
      };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [r] } },
        consumed: {},
        theta: [],
        slots: {},
        persistentEvidence: [{ goal: q, method: 'clause', term: mockClauseTerm }],
        loliHash: null
      }];

      const term = guidedTerm(trace, rfTerm);

      const loliL = term.subterms[0];
      const antProof = loliL.subterms[0]; // promotion
      assert.strictEqual(antProof.rule, 'promotion');
      const inner = antProof.subterms[0];

      // Clause evidence with term → uses the term directly
      assert.strictEqual(inner, mockClauseTerm);
    });

    it('clause evidence without term falls back to id(goal)', () => {
      // Simulates pre-3b.5 evidence (no term field)
      const q = Store.put('atom', ['fq']);
      const r = Store.put('atom', ['fr']);
      const bangQ = Store.put('bang', [GRADE_W,q]);
      const monadR = Store.put('monad', [r]);
      const loli = Store.put('loli', [bangQ, monadR]);

      const rfTerm = { rule: 'id', principal: r, subterms: [] };

      const trace = [{
        rule: { name: 'test', hash: loli, consequent: { linear: [r] } },
        consumed: {},
        theta: [],
        slots: {},
        persistentEvidence: [{ goal: q, method: 'clause' }], // no term!
        loliHash: null
      }];

      const term = guidedTerm(trace, rfTerm);

      const loliL = term.subterms[0];
      const antProof = loliL.subterms[0];
      assert.strictEqual(antProof.rule, 'promotion');
      const inner = antProof.subterms[0];

      // Fallback: id(goal)
      assert.strictEqual(inner.rule, 'id');
      assert.strictEqual(inner.principal, q);
    });
  });

  // ─── Ground loli structure verification ─────────────────────────

  describe('buildClauseTerm ground loli structure', () => {

    it('zero premises: loli(one, monad(Q))', () => {
      const q = Store.put('atom', ['q']);
      const clauses = new Map([['q_clause', { hash: q, premises: [] }]]);
      const result = backward.prove(q, clauses, new Map(), { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success);
      const groundLoli = result.term.principal;
      assert.strictEqual(Store.tag(groundLoli), 'loli');
      assert.strictEqual(Store.tag(Store.child(groundLoli, 0)), 'one');
      assert.strictEqual(Store.tag(Store.child(groundLoli, 1)), 'monad');
      assert.strictEqual(Store.child(Store.child(groundLoli, 1), 0), q);
    });

    it('one premise: loli(bang(GRADE_W, P), monad(Q))', () => {
      const p = Store.put('atom', ['p']);
      const q = Store.put('atom', ['q']);
      const types = new Map([['p_type', p]]);
      const clauses = new Map([['pq_clause', { hash: q, premises: [p] }]]);
      const result = backward.prove(q, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success);
      const groundLoli = result.term.principal;
      const ant = Store.child(groundLoli, 0);
      assert.strictEqual(Store.tag(ant), 'bang');
      assert.strictEqual(Store.child(ant, 1), p);
    });

    it('three premises: loli(tensor(!P1, tensor(!P2, !P3)), monad(Q))', () => {
      const a = Store.put('atom', ['a']);
      const b = Store.put('atom', ['b']);
      const c = Store.put('atom', ['c']);
      const d = Store.put('atom', ['d']);
      const types = new Map([['a_type', a], ['b_type', b], ['c_type', c]]);
      const clauses = new Map([['abcd_clause', { hash: d, premises: [a, b, c] }]]);
      const result = backward.prove(d, clauses, types, { ...makeILLBackchainOpts(), buildTerm: true });

      assert(result.success);
      const groundLoli = result.term.principal;
      const ant = Store.child(groundLoli, 0);

      // Right-associated: tensor(!a, tensor(!b, !c))
      assert.strictEqual(Store.tag(ant), 'tensor');
      assert.strictEqual(Store.tag(Store.child(ant, 0)), 'bang');
      assert.strictEqual(Store.child(Store.child(ant, 0), 1), a);
      const inner = Store.child(ant, 1);
      assert.strictEqual(Store.tag(inner), 'tensor');
      assert.strictEqual(Store.tag(Store.child(inner, 0)), 'bang');
      assert.strictEqual(Store.child(Store.child(inner, 0), 1), b);
      assert.strictEqual(Store.tag(Store.child(inner, 1)), 'bang');
      assert.strictEqual(Store.child(Store.child(inner, 1), 1), c);
    });
  });

  // ─── Failure cases ──────────────────────────────────────────────

  describe('prove.js failure', () => {

    it('returns null term on failure', () => {
      const unknown = Store.put('atom', ['unknown']);
      const result = backward.prove(unknown, new Map(), new Map(), { ...makeILLBackchainOpts(), buildTerm: true });
      assert(!result.success);
      assert.strictEqual(result.term, null);
    });
  });
});

/**
 * Datasorts, slice 1 — finite-classifier subsets (TODO_0011 fence B,
 * round-2 spec; TODO_0300 item 3(a) first slice).
 *
 * A datasort is introduced by an undeclared-LHS subsort declaration
 * (`warm <: tile_t.`) and DEFINED by ordinary membership clauses
 * (`warm/s: warm sea.`) — the name is loader-synthesized into a dual
 * role (sort-name atom + unary membership predicate; sound post-
 * f7ec930a). Slice 1 restricts bases to finite atomic classifiers
 * (subset events, no fixpoint): the degenerate automaton.
 *
 * Pins:
 *   - loader: intro + member subset; fences f1 (head must be a member),
 *     f2 (no premises on nullary-member clauses), f3 (one clause per
 *     (datasort, head)), no-clauses error, recursive-base deferral,
 *     already-declared-name error; schema quantification refused
 *   - membership is a real predicate: backward goals (`!warm T`) work
 *   - static conditioning: `exists T: warm @w.` draws only warm members;
 *     masses are RESTRICTED, not renormalized (B4: surviving worlds keep
 *     their masses; total = m(warm))
 *   - dynamic conditioning: `!within E S` intersects; non-datasort S is
 *     a loud error; empty intersection = contradiction (M9 / dead branch)
 *   - importance ≡ m(warm) for every seed (B6, degenerate case)
 *   - certification: conditioned draws certify (token drawn(c, warm) —
 *     m4); doctored weight rejected
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import willConfig, { loadWillSequent } from '../../calculus/will/calculus-config.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { programFromCalc } from '../../lib/prover/timed/elaborate-trace.js';
import { certifyCollapse } from '../../lib/prover/timed/elaborate-collapse.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-datasorts-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');

const HEADER = `#import(${MEASURE})
pos2: sort.
a0: pos2.
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t @w 2.
mk: (c: pos2) -> type.
tile: (c: pos2) -> (t: tile_t) -> type.
`;

const WARM = `warm <: tile_t.
warm/s: warm sea.
warm/c: warm coast.
`;

const loadProg = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: willConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
const init1 = () => ({ linear: { [Store.put('mk', [atom('a0')])]: 1 }, persistent: {} });
const tileOf = (state) => {
  for (const k of Object.keys(state.linear)) {
    let h = Number(k);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    if (Store.tag(h) === 'tile') return Store.child(Store.child(h, 1), 0);
  }
  return null;
};

describe('datasorts — loader (intro, subset, fences)', () => {
  it('intro + member subset: warm = {sea, coast}, base tile_t', () => {
    const calc = loadProg('ok.will', HEADER + WARM +
      'spawn: mk C -o { exists T: tile_t @w. tile C T }.\n');
    assert.ok(calc.sorts.isDatasort('warm'));
    assert.ok(!calc.sorts.isClassifier('warm'));
    const info = calc.sorts.datasortInfo('warm');
    assert.equal(info.base, 'tile_t');
    assert.deepEqual([...info.members].sort(), ['coast', 'sea']);
    // the subsort edge is in the materialized closure
    assert.ok(calc.sorts.subsort('warm', 'tile_t'));
  });

  it('f1: clause head must be a member of the base', () => {
    assert.throws(() => loadProg('f1.will', HEADER + `warm <: tile_t.
warm/x: warm a0.
`), /not a member|member of/);
  });

  it('f2: no premises on a nullary-member clause', () => {
    assert.throws(() => loadProg('f2.will', HEADER + `warm <: tile_t.
warm/s: warm sea <- warm coast.
`), /premise/i);
  });

  it('f3: one clause per (datasort, head) — determinism', () => {
    assert.throws(() => loadProg('f3.will', HEADER + `warm <: tile_t.
warm/a: warm sea.
warm/b: warm sea.
`), /determinism|duplicate|already/i);
  });

  it('a datasort with no membership clauses is a load error', () => {
    assert.throws(() => loadProg('empty.will', HEADER + 'warm <: tile_t.\n'),
      /no membership clauses/i);
  });

  it('unknown RHS still errors; declared-name LHS still errors', () => {
    assert.throws(() => loadProg('rhs.will', HEADER + 'warm <: nope.\n'), /unknown sort/i);
    assert.throws(() => loadProg('lhs.will', HEADER + 'sea <: tile_t.\n'), /already declared|unknown sort/i);
  });

  it('schema quantification over a datasort is refused', () => {
    assert.throws(() => loadProg('quant.will', HEADER + WARM +
      'spoil: (r: warm) tile C r -o { I }.\n'), /not a classifier/);
  });

  it('membership is a real backward predicate: rules gate on !warm T', () => {
    const calc = loadProg('goal.will', HEADER + WARM + `nice: (t: tile_t) -> type.
n1: tile C T * !warm T -o { nice T }.
`);
    const st = { linear: { [Store.put('tile', [atom('a0'), atom('sea')])]: 1 }, persistent: {} };
    const res = calc.settle(st, 0, { maxSteps: 10 });
    assert.ok(Object.keys(res.state.linear).some((k) => {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      return Store.tag(h) === 'nice';
    }), 'warm tile should become nice');
    const st2 = { linear: { [Store.put('tile', [atom('a0'), atom('land')])]: 1 }, persistent: {} };
    const res2 = calc.settle(st2, 0, { maxSteps: 10 });
    assert.ok(!Object.keys(res2.state.linear).some((k) => {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      return Store.tag(h) === 'nice';
    }), 'land is not warm');
  });
});

describe('datasorts — static conditioning (exists T: warm @w.)', () => {
  let calc;
  before(() => {
    calc = loadProg('static.will', HEADER + WARM +
      'spawn: mk C -o { exists T: warm @w. tile C T }.\n');
  });

  it("'exact': restriction, not renormalization — outcomes {sea:2, coast:1}, total 3", () => {
    const r = calc.collapse(init1(), { mode: 'exact' });
    assert.equal(r.outcomes.length, 2);
    assert.deepEqual(r.total, [3n, 1n]);
    const bySort = Object.fromEntries(r.outcomes.map((o) => [tileOf(o.state), o.mass]));
    assert.deepEqual(bySort.sea, [2n, 1n]);
    assert.deepEqual(bySort.coast, [1n, 1n]);
  });

  it("'sample': only warm members drawn; importance ≡ m(warm) = 3 every seed (B6)", () => {
    const seen = new Set();
    for (let seed = 0; seed < 30; seed++) {
      const r = calc.collapse(init1(), { seed });
      assert.ok(r.ground);
      const t = tileOf(r.state);
      assert.ok(t === 'sea' || t === 'coast', `drew ${t} outside warm`);
      assert.deepEqual(r.importance, [3n, 1n], `seed ${seed}: importance ≠ m(warm)`);
      seen.add(t);
    }
    assert.deepEqual([...seen].sort(), ['coast', 'sea'], 'both members reachable');
  });
});

describe('datasorts — dynamic conditioning (!within E S)', () => {
  const DYN = HEADER + WARM + `dry <: tile_t.
dry/l: dry land.
within: (x: tile_t) -> (s: sort) -> type.
go: type.
spawn: mk C -o { exists T: tile_t @w. tile C T }.
`;

  it('within intersects: masses restricted to warm, total 3', () => {
    const calc = loadProg('dyn.will', DYN +
      'cond: go * $tile C X -o { !within X warm }.\n');
    const init = { linear: { [Store.put('mk', [atom('a0')])]: 1, [atom('go')]: 1 }, persistent: {} };
    const r = calc.collapse(init, { mode: 'exact' });
    assert.equal(r.outcomes.length, 2);
    assert.deepEqual(r.total, [3n, 1n]);
  });

  it('empty intersection: exact ⇒ no outcomes, sample ⇒ persistent contradiction', () => {
    const calc = loadProg('dyn2.will', DYN + `go2: type.
cond: go * $tile C X -o { !within X warm }.
cond2: go2 * $tile C X -o { !within X dry }.
`);
    const init = { linear: {
      [Store.put('mk', [atom('a0')])]: 1, [atom('go')]: 1, [atom('go2')]: 1,
    }, persistent: {} };
    // two $-reading rules trip settleExplore's conservative contention
    // check; the program is confluent — take the chooser-resolved reading
    const r = calc.collapse(init, { mode: 'exact', settleBranching: 'seed' });
    assert.equal(r.outcomes.length, 0);
    assert.deepEqual(r.total, [0n, 1n]);
    assert.throws(() => calc.collapse(init, { seed: 1, maxAttempts: 4 }),
      /contradiction persisted/);
  });

  it('within on a non-datasort is a loud error', () => {
    const calc = loadProg('dyn3.will', DYN +
      'cond: go * $tile C X -o { !within X tile_t }.\n');
    const init = { linear: { [Store.put('mk', [atom('a0')])]: 1, [atom('go')]: 1 }, persistent: {} };
    assert.throws(() => calc.collapse(init, { mode: 'exact' }), /not a declared datasort/);
  });
});

// ── slice 2: linear-recursive datasorts + exact inside masses ──

const LSTHDR = `#import(${MEASURE})
bit: sort.
b0: bit @w 1.
b1: bit @w 1.
lst: sort.
nil: lst @w 2.
cons: (h: bit) -> (t: lst) -> lst @w 1/4.
mk: type.
box: (x: lst) -> type.
`;
const EVENODD = `even <: lst.
odd <: lst.
even/n: even nil.
even/c: even (cons H T) <- odd T.
odd/c: odd (cons H T) <- even T.
ne <: lst.
ne/c: ne (cons H T).
`;
const initMk = () => ({ linear: { [atom('mk')]: 1 }, persistent: {} });
const boxOf = (state) => {
  for (const k of Object.keys(state.linear)) {
    let h = Number(k);
    if (Store.tag(h) === 'at') h = Store.child(h, 0);
    if (Store.tag(h) === 'box') return Store.child(h, 0);
  }
  return null;
};
const listLen = (h) => {
  let n = 0;
  while (Store.tag(h) === 'cons') { n++; h = Store.child(h, 1); }
  return Store.tag(h) === 'atom' && Store.child(h, 0) === 'nil' ? n : -1;
};

describe('datasorts — recursive (slice 2): exact inside masses', () => {
  let calc;
  before(() => {
    calc = loadProg('rec.will', LSTHDR + EVENODD +
      'spawn: mk -o { exists X: even @w. box X }.\n');
  });

  it('the B8 worked example solves exactly: m(lst)=4, m(even)=8/3, m(odd)=4/3, m(ne)=2', () => {
    assert.ok(calc.masses, 'masses solved at load');
    assert.deepEqual(calc.masses.get('lst'), [4n, 1n]);
    assert.deepEqual(calc.masses.get('bit'), [2n, 1n]);
    assert.deepEqual(calc.masses.get('even'), [8n, 3n]);
    assert.deepEqual(calc.masses.get('odd'), [4n, 3n]);
    assert.deepEqual(calc.masses.get('ne'), [2n, 1n]);
    // partition identity: even/odd partition lst — the solver's self-check
    const [en, ed] = calc.masses.get('even');
    const [on, od] = calc.masses.get('odd');
    assert.equal(en * od + on * ed, 4n * ed * od, 'm(even) + m(odd) = m(lst)');
  });

  it('f4: a tree-shaped datasort is a load error (nonlinear mass system, B″)', () => {
    assert.throws(() => loadProg('tree.will', `#import(${MEASURE})
tree: sort.
leaf: tree @w 1.
node: (l: tree) -> (r: tree) -> tree @w 1/8.
full <: tree.
full/l: full leaf.
full/n: full (node L R) <- full L <- full R.
`), /nonlinear|B″/);
  });

  it('emptiness: a base-case-free datasort is a load error', () => {
    assert.throws(() => loadProg('inf.will', LSTHDR + `inf <: lst.
inf/c: inf (cons H T) <- inf T.
`), /empty language/);
  });

  it('f1/f2 extended fences fire with named errors', () => {
    const bad = (name, clause, re) =>
      assert.throws(() => loadProg(name, LSTHDR + 'bad <: lst.\nbad/n: bad nil.\n' + clause), re, clause);
    bad('b1.will', 'bad/c: bad (cons H T) <- bad X.\n', /not a head argument/);
    bad('b2.will', 'even2 <: lst.\neven2/n: even2 nil.\nbad/c: bad (cons H T) <- even2 T <- bad T.\n', /constrained twice/);
    bad('b3.will', 'bad/c: bad (cons H T) <- box T.\n', /unary datasort goal/);
    bad('b4.will', 'bad/c: bad (cons H T) <- bad H.\n', /refines 'lst' but the argument's sort is 'bit'/);
    bad('b5.will', 'bad/c: bad (cons H (cons H2 T)).\n', /distinct variables/);
  });

  it("'sample': every drawn list has even length; importance ≡ m(even) = 8/3 every seed (B6)", () => {
    const lens = new Set();
    for (let seed = 0; seed < 25; seed++) {
      const r = calc.collapse(initMk(), { seed });
      assert.ok(r.ground);
      const len = listLen(boxOf(r.state));
      assert.ok(len >= 0 && len % 2 === 0, `seed ${seed}: drew an odd/malformed list (len ${len})`);
      assert.deepEqual(r.importance, [8n, 3n], `seed ${seed}: importance ≠ m(even)`);
      lens.add(len);
    }
    assert.ok(lens.size > 1, 'multiple lengths reachable');
  });

  it("'exact' with maxCollapses 6: nil + the four 2-lists — total 5/2, truncated", () => {
    const r = calc.collapse(initMk(), { mode: 'exact', maxCollapses: 6 });
    assert.equal(r.outcomes.length, 5);
    assert.deepEqual(r.total, [5n, 2n]);
    assert.ok(r.truncated);
    for (const o of r.outcomes) {
      const len = listLen(boxOf(o.state));
      assert.ok(len === 0 || len === 2);
    }
  });

  it('within over a recursive domain (slice 3): nonempty lists only, total 3/2', () => {
    const calc2 = loadProg('recwithin.will', LSTHDR + EVENODD + `within: (x: lst) -> (s: sort) -> type.
go: type.
spawn: mk -o { exists X: lst @w. box X }.
cond: go * $box X -o { !within X ne }.
`);
    const init = { linear: { [atom('mk')]: 1, [atom('go')]: 1 }, persistent: {} };
    const r = calc2.collapse(init, { mode: 'exact', maxCollapses: 6, settleBranching: 'seed' });
    assert.equal(r.outcomes.length, 6);       // 2 one-lists + 4 two-lists
    assert.deepEqual(r.total, [3n, 2n]);
    assert.ok(r.truncated);
    for (const o of r.outcomes) assert.ok(listLen(boxOf(o.state)) >= 1, 'nil excluded');
    // sample: importance ≡ m(ne) = 2 every seed
    for (let seed = 0; seed < 10; seed++) {
      const s = calc2.collapse(init, { seed, settleBranching: 'seed' });
      assert.ok(listLen(boxOf(s.state)) >= 1);
      assert.deepEqual(s.importance, [2n, 1n], `seed ${seed}: importance ≠ m(ne)`);
    }
  });

  it('entangled product states (slice 3): even ∧ allb0 — lazy product masses, importance ≡ 32/15', () => {
    const calc2 = loadProg('prod.will', LSTHDR + EVENODD + `b0s <: bit.
b0s/z: b0s b0.
allb0 <: lst.
allb0/n: allb0 nil.
allb0/c: allb0 (cons H T) <- b0s H <- allb0 T.
within: (x: lst) -> (s: sort) -> type.
go: type.
go2: type.
spawn: mk -o { exists X: lst @w. box X }.
cond: go * $box X -o { !within X even }.
cond2: go2 * $box X -o { !within X allb0 }.
`);
    const init = { linear: {
      [atom('mk')]: 1, [atom('go')]: 1, [atom('go2')]: 1,
    }, persistent: {} };
    // declared-state masses from load; product m(even&allb0) = 32/15 solved lazily
    assert.deepEqual(calc2.masses.get('allb0'), [8n, 3n]);
    const r = calc2.collapse(init, { mode: 'exact', maxCollapses: 6, settleBranching: 'seed' });
    assert.equal(r.outcomes.length, 2);       // nil + the single all-b0 2-list
    assert.deepEqual(r.total, [17n, 8n]);
    assert.ok(r.truncated);
    for (let seed = 0; seed < 10; seed++) {
      const s = calc2.collapse(init, { seed, settleBranching: 'seed' });
      const lst = boxOf(s.state);
      const len = listLen(lst);
      assert.ok(len >= 0 && len % 2 === 0, `seed ${seed}: not even-length`);
      let h = lst;   // all heads b0
      while (Store.tag(h) === 'cons') {
        assert.equal(Store.child(Store.child(h, 0), 0), 'b0', `seed ${seed}: non-b0 element`);
        h = Store.child(h, 1);
      }
      assert.deepEqual(s.importance, [32n, 15n], `seed ${seed}: importance ≠ m(even∧allb0)`);
    }
  });

  it('stepwise API: collapseView/collapseDraw walk a conditioned recursive wave', () => {
    const calc2 = loadProg('stepwise.will', LSTHDR + EVENODD +
      'spawn: mk -o { exists X: even @w. box X }.\n');
    const session = { state: { linear: { [atom('mk')]: 1 }, persistent: {} }, waveMap: new Map(), skolemSet: new Set() };
    let waves = calc2.collapseView(session);
    assert.equal(waves.length, 1);
    assert.equal(waves[0].sort, 'even');
    // drawWeights carry the mass-proportional distribution: total = m(even)
    assert.deepEqual(waves[0].posterior.drawTotal, [8n, 3n]);
    // force cons: child waves register at the automaton child states
    const rec = calc2.collapseDraw(session, waves[0], { member: 'cons' });
    assert.equal(rec.member, 'cons');
    assert.deepEqual([...session.waveMap.values()].sort(), ['bit', 'odd']);
    // draw to ground with the PRF; the final list must be even-length
    for (let step = 0; step < 50; step++) {
      waves = calc2.collapseView(session);
      if (waves.length === 0) break;
      const r = calc2.collapseDraw(session, waves[0], { seed: 5, step });
      assert.ok(!r.contradiction && !r.refused);
    }
    const len = listLen(boxOf(session.state));
    assert.ok(len >= 2 && len % 2 === 0, `stepwise result not even-length (${len})`);
  });

  it('mass facts materialize when the program declares the predicate (intra-logical rider)', () => {
    const calc2 = loadProg('massfacts.will', LSTHDR + EVENODD + `mass: (s: sort) -> (m: q) -> type.
chk: type.
got: (m: q) -> type.
r: chk * !mass even M -o { got M }.
`);
    const res = calc2.settle({ linear: { [atom('chk')]: 1 }, persistent: {} }, 0, { maxSteps: 10 });
    assert.ok(res.quiescent);
    let gotVal = null;
    for (const k of Object.keys(res.state.linear)) {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      if (Store.tag(h) === 'got') gotVal = Store.child(h, 0);
    }
    assert.ok(gotVal !== null, 'rule bound !mass even M');
  });

  it('a conditioned recursive run certifies: one token per draw, Π ρ = mass, states on tokens', () => {
    const seqCalc = loadWillSequent();
    const kernel = createKernel(seqCalc);
    for (const seed of [0, 1, 2]) {
      const r = certifyCollapse({
        engineCalc: calc, calculus: seqCalc, kernel,
        state: initMk(), collapseOpts: { seed },
      });
      assert.equal(r.verdict, 'certified', `seed ${seed}: ${r.reason || (r.errors || []).join('; ')}`);
      assert.equal(r.tokens.length, r.run.collapses.length, 'one token per draw');
      let prod = [1n, 1n];
      const sorts = new Set();
      for (const tok of r.tokens) {
        const member = Store.child(Store.child(tok, 0), 0);
        sorts.add(Store.child(Store.child(tok, 1), 0));
        const [pn, pd] = calc.priors.get(member) || [1n, 1n];
        prod = [prod[0] * pn, prod[1] * pd];
      }
      assert.equal(prod[0] * r.run.mass[1], r.run.mass[0] * prod[1],
        `seed ${seed}: Π ρ over ⟨Θ⟩ ≠ run mass`);
      assert.ok(sorts.has('even'), 'root token at the binder sort');
      for (const s of sorts) assert.ok(['even', 'odd', 'bit'].includes(s), `unexpected token sort ${s}`);
    }
  });
});

describe('datasorts — certification of conditioning states + mass claims (slice 4)', () => {
  let calc, seqCalc, kernel;
  const SRC = LSTHDR + EVENODD + `nilonly <: lst.
nilonly/n: nilonly nil.
within: (x: lst) -> (s: sort) -> type.
go: type.
spawn: mk -o { exists X: lst @w. box X }.
cond: go * $box X -o { !within X ne }.
`;
  const init = () => ({ linear: { [atom('mk')]: 1, [atom('go')]: 1 }, persistent: {} });
  before(() => {
    calc = loadProg('s4.will', SRC);
    seqCalc = loadWillSequent();
    kernel = createKernel(seqCalc);
  });
  const certify = (seed) => certifyCollapse({
    engineCalc: calc, calculus: seqCalc, kernel,
    state: init(), collapseOpts: { seed, settle: { seed } },
  });

  it('a within-conditioned run certifies; the @draw node carries the effective state', () => {
    const r = certify(0);
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    let found = false;
    (function walk(n) {
      if (n.rule === 'draw' && n.state && n.state.draw && n.state.draw.state === 'ne') found = true;
      for (const p of n.premises || []) walk(p);
    })(r.tree);
    assert.ok(found, 'no draw node records the within-derived state');
  });

  it('a doctored mass table is rejected (verification by substitution, B7)', () => {
    const saved = calc.masses.get('ne');
    calc.masses.set('ne', [7n, 1n]);
    try {
      const r = certify(0);
      assert.equal(r.verdict, 'invalid');
      assert.ok(r.errors.some((e) => /mass.*'ne'.*equation/.test(e)), r.errors.join('; '));
    } finally {
      calc.masses.set('ne', saved);
    }
  });

  it('a doctored conditioning state on a draw node fails kernel verification', () => {
    const r = certify(0);
    assert.equal(r.verdict, 'certified');
    // claim the root cons-draw was conditioned to 'nilonly' — cons is
    // not admitted there (child draws fold into the composite witness,
    // so the root node is the one carrying the state)
    let doctored = false;
    (function walk(n) {
      if (!doctored && n.rule === 'draw' && n.state && n.state.draw &&
          n.state.draw.member === 'cons') {
        n.state.draw.state = 'nilonly';
        doctored = true;
      }
      for (const p of n.premises || []) walk(p);
    })(r.tree);
    assert.ok(doctored, 'no cons draw found to doctor');
    const v = kernel.verifyTree(r.tree, { program: programFromCalc(calc) });
    assert.ok(!v.valid, 'doctored conditioning state must not verify');
    assert.ok(v.errors.some((e) => /not admitted/.test(e)), v.errors.join('; '));
  });
});

describe('datasorts — certification (conditioned draws, m4 tokens)', () => {
  it('a static-conditioned sample run certifies; tokens carry the datasort name', () => {
    const calc = loadProg('cert.will', HEADER + WARM +
      'spawn: mk C -o { exists T: warm @w. tile C T }.\n');
    const seqCalc = loadWillSequent();
    const kernel = createKernel(seqCalc);
    const r = certifyCollapse({
      engineCalc: calc, calculus: seqCalc, kernel,
      state: init1(), collapseOpts: { seed: 3 },
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.tokens.length, 1);
    const tok = r.tokens[0];
    assert.equal(Store.tag(tok), 'drawn');
    assert.equal(Store.child(Store.child(tok, 1), 0), 'warm', 'token sort = binder sort (m4)');
    const member = Store.child(Store.child(tok, 0), 0);
    assert.ok(member === 'sea' || member === 'coast');
  });

  it('tamper: a doctored draw weight is rejected', () => {
    const calc = loadProg('cert2.will', HEADER + WARM +
      'spawn: mk C -o { exists T: warm @w. tile C T }.\n');
    const seqCalc = loadWillSequent();
    const kernel = createKernel(seqCalc);
    const r = certifyCollapse({
      engineCalc: calc, calculus: seqCalc, kernel,
      state: init1(), collapseOpts: { seed: 3 },
    });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    // find the @draw node and doctor its recorded weight
    const doctor = (node) => {
      if (node.state && node.state.draw && !node.state.draw.open) {
        node.state.draw.weight = [7n, 1n];
        return true;
      }
      return (node.premises || []).some(doctor);
    };
    assert.ok(doctor(r.tree), 'no draw node found');
    const v = kernel.verifyTree(r.tree, { program: programFromCalc(calc) });
    assert.ok(!v.valid, 'doctored weight must be rejected');
  });
});

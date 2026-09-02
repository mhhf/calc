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

/**
 * T2-applicability certifier — TODO_0293 (a), settle-optimality §11.
 *
 * The engine certifies contention-freedom instead of assuming it:
 *   - structural tier: the one-shot-edge discipline (depot-style graph
 *     programs) certifies with no state at all;
 *   - relaxation tier: the monotone relaxation's firing set + pairwise
 *     independence — E1 (choice-free, contended) is refused, and E2's
 *     deferred producer is refused EXACTLY BECAUSE the relaxation sees
 *     demand that no run state ever co-exhibits (the paper's central
 *     correction);
 *   - the read-relaxation twin (measure, don't consume) certifies;
 *   - unsupported shapes refuse with a reason, never guess.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import tillConfig from '../../calculus/till/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'timed-certify-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const load = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: tillConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
const S = (m) => ({ linear: Object.fromEntries(Object.entries(m).map(([k, v]) => [atom(k), v])), persistent: {} });

describe('T2-applicability certifier', () => {
  it('structural: one-shot-edge graph program certifies with no state', () => {
    const calc = load('graph.till', `
n0: type.  n1: type.  n2: type.  e0: type.  e1: type.
hop0: read n0 * e0 -o { n1 }@3.
hop1: read n1 * e1 -o { n2 }@4.
`);
    const r = calc.certifyContention(S({ n0: 1, e0: 1, e1: 1 }), '10');
    assert.deepEqual(r, { certified: true, method: 'structural' });
  });

  it('E1 (choice-free, contended): refused — demand overlap on the token', () => {
    const calc = load('e1.till', `
a: type.  b: type.  tok: type.  won_a: type.  won_b: type.
r1: a * tok -o { won_a }@1.
r2: b * tok -o { won_b }@1.
`);
    const r = calc.certifyContention(S({ a: 1, tok: 1, b: 1 }), '10');
    assert.equal(r.certified, false);
    assert.equal(r.method, 'relaxation');
    assert.ok(r.contended.some(c => /tok/.test(c.why) || (c.a !== c.b)),
      JSON.stringify(r.contended));
  });

  it('E2 (deferred producer): the relaxation sees what no run state shows', () => {
    const calc = load('e2.till', `
a: type.  b: type.  c: type.  tok: type.  won_a: type.  won_b: type.
r1: a * tok -o { won_a }@1.
r2: b * tok -o { won_b }@1.
mk: c -o { b }@5.
`);
    // b arrives only at 5 — every run E(s) is a singleton, yet the
    // relaxation fires r2 and exposes the shared demand on tok
    const r = calc.certifyContention(S({ a: 1, tok: 1, c: 1 }), '10');
    assert.equal(r.certified, false);
    const pair = r.contended.find(c =>
      (c.a === 'r1' && c.b === 'r2') || (c.a === 'r2' && c.b === 'r1'));
    assert.ok(pair, `expected the (r1,r2) pair: ${JSON.stringify(r.contended)}`);
  });

  it('read twin: measuring instead of consuming certifies', () => {
    const calc = load('twin.till', `
a: type.  b: type.  rtok: type.  won_a: type.  won_b: type.
r1: a * read rtok -o { won_a }@1.
r2: b * read rtok -o { won_b }@1.
`);
    const r = calc.certifyContention(S({ a: 1, b: 1, rtok: 1 }), '10');
    assert.equal(r.certified, true, JSON.stringify(r));
  });

  it('unsupported shapes refuse with a reason (whole-bind)', () => {
    const calc = load('wb.till', `
g: type.  w: bin -> type.
all: !_W g -o { w W }@1.
`);
    const r = calc.certifyContention(S({ g: 3 }), '10');
    assert.equal(r.certified, false);
    assert.match(r.reason, /whole-bind/);
  });

  // ---- audit witnesses (TODO_0296 P0): four demonstrated unsound
  // certifications, each now refused. Every rule below was chosen because
  // the pre-fix certifier CERTIFIED it.

  it('same-rule multi-instance contention refuses (non-ground premise)', () => {
    // r[X:=1] and r[X:=2] are co-enabled and share the single g — outcome
    // q 1 vs q 2, confluence fails. Structural refuses (non-ground consumed
    // premise); the relaxation must enumerate BOTH bindings (the
    // undoRestore-arity fix) and flag the demand overlap.
    const calc = load('mv.till', `
p: bin -> type.  g: type.  q: bin -> type.
r: p X * g -o { q X }@1.
`);
    const bin = (n) => Store.put('binlit', [BigInt(n)]);
    const pOf = (n) => Store.put('p', [bin(n)]);
    const st = { linear: { [pOf(1)]: 1, [pOf(2)]: 1, [atom('g')]: 1 }, persistent: {} };
    const r = calc.certifyContention(st, '10');
    assert.equal(r.certified, false, JSON.stringify(r));
    assert.equal(r.method, 'relaxation');
    assert.equal(r.firings, 2, 'stale theta must not hide the second binding');
    assert.match(r.structural, /non-ground consumed premise/);
    assert.ok(r.contended.some(c => /demand overlap/.test(c.why)), JSON.stringify(r.contended));
  });

  it('consume/read conflict refuses (structural clause-2 blindness)', () => {
    // consume_p fires and removes p; read_p starves. The structural tier
    // skipped reads entirely and certified — now it refuses to the
    // relaxation, whose readStarve check flags the pair.
    const calc = load('rc.till', `
p: type.  q: type.  r: type.  s: type.
consume_p: p -o { q }@1.
read_p: read p * r -o { s }@1.
`);
    const res = calc.certifyContention(S({ p: 1, r: 1 }), '10');
    assert.equal(res.certified, false, JSON.stringify(res));
    assert.match(res.structural, /read starvation possible/);
    assert.ok(res.contended.some(c => /read starvation/.test(c.why)), JSON.stringify(res));
  });

  it('implicit zero-delay (delayless rule) never certifies structurally', () => {
    // `mk: a -o { b }.` IS zero-delay in settle's semantics, but carried no
    // r.delay.ground for the old guard to see (and `@0` normalizes to
    // no-delay before the certifier). Clause 3 must stay vacuous at the
    // structural tier, so delayless refuses; the relaxation flags the
    // instant feed into `use`.
    const calc = load('zd.till', `
a: type.  b: type.  c: type.
mk: a -o { b }.
use: b -o { c }@1.
`);
    const res = calc.certifyContention(S({ a: 1 }), '10');
    assert.notEqual(res.method, 'structural');
    assert.match(res.structural, /no ground delay/);
    assert.equal(res.certified, false, JSON.stringify(res));
    assert.ok(res.contended.some(c => /instant feed/.test(c.why)), JSON.stringify(res));
  });

  it('horizon bounds the relaxation: late contention outside H certifies', () => {
    const calc = load('late.till', `
a: type.  b: type.  c: type.  tok: type.  won_a: type.  won_b: type.
r1: a * tok -o { won_a }@1.
r2: b * tok -o { won_b }@1.
mk: c -o { b }@50.
`);
    // b arrives at 50; below horizon 10 the relaxation never fires r2
    const r = calc.certifyContention(S({ a: 1, tok: 1, c: 1 }), '10');
    assert.equal(r.certified, true, JSON.stringify(r));
  });
});

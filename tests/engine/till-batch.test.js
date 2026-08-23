/**
 * Cohort firing — batched fire at multiplicity k (TODO_0278 B1).
 *
 * A unique candidate whose intermediate fires provably cannot change the
 * instant's candidate landscape fires ONCE at multiplicity k = min over
 * consumed refs of floor((count − reserved) / take). The batch equals the
 * sequential k-prefix EXACTLY (state-identical incl. Zobrist); the event
 * list becomes an RLE (per-fire facts + `multiplicity`, expansion ≡ the
 * sequential event multiset). Default ON; `batch: false` opts out.
 *
 * Pins:
 *  - the motivating case: a 10^6-item spoilage sweep is ONE firing step
 *  - differential: batch ≡ batch:false, state-identical + RLE-exact, on
 *    chains, preserved machines, counted takes, reads, PP2 kiln w/ draws
 *  - serialized machines: k same-stamp machines batch k-parallel and
 *    stagger the next round via the reproduced copies (no special case)
 *  - fences: ties, zero-delay feeding, persistent production, weighted
 *    consequents never batch; a self-feeding Zeno loop cannot batch past
 *    the instant guard; the I32 produce fence throws loudly
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import { loadTill as load, atom, initQuery, stampedStr, traceKey } from './till-helpers.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';

const PP2 = path.join(import.meta.dirname, '../../calculus/till/game/PP2.till');
const PRELUDE = path.join(import.meta.dirname, '../../calculus/till/prelude/rat.ill');
const lin = (obj) => ({ linear: obj, persistent: {} });

let _dir = null;
function prog(text) {
  if (!_dir) _dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-b1-'));
  const f = path.join(_dir, `p${fs.readdirSync(_dir).length}.ill`);
  fs.writeFileSync(f, `#import(${PRELUDE})\n${text}`);
  return load(f);
}

/** RLE expansion: the batched event list unrolled to per-fire records. */
const expand = (events) =>
  events.flatMap(e => Array((e.multiplicity || 1)).fill(e));
const maxMult = (events) => Math.max(...events.map(e => e.multiplicity || 1));

/** Full differential: batched run ≡ per-item run (state, next, events). */
function differential(calc, mkState, T, opts = {}) {
  const on = calc.settle(mkState(), T, opts);
  const off = calc.settle(mkState(), T, { ...opts, batch: false });
  assert.equal(stampedStr(on.state), stampedStr(off.state), 'state-identical');
  assert.deepEqual(
    on.next === null ? null : ratParts(on.next),
    off.next === null ? null : ratParts(off.next), 'same pending schedule');
  if (on.events && off.events) {
    assert.equal(traceKey(expand(on.events)), traceKey(off.events),
      'RLE expansion reproduces the sequential event multiset');
  }
  return { on, off };
}

describe('till cohort firing — the motivating case (B1)', () => {
  it('a 10^6-item spoilage sweep is ONE firing step', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
wood: type.

spoil: wood@Q * after (Q+20) -o { I }.
`);
    // One run-length cohort; per-item this is 10^6 events and would trip
    // any per-instant guard — batched it is one step under a TINY guard.
    const r = calc.settle(lin({ [atom('wood')]: 1000000 }), '30',
      { maxInstantSteps: 5, events: false });
    assert.equal(r.steps, 1);
    assert.equal(r.quiescent, true);
    assert.equal(r.eventTotals.spoil, 1000000);   // totals count fires (rider 4)
  });

  it('onEvent and onStep carry the multiplicity; events are RLE records', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
w: type.

sweep: w@Q * after (Q+1) -o { I }.
`);
    const seen = [];
    const stepped = [];
    const r = calc.settle(lin({ [atom('w')]: 7 }), '5', {
      onEvent: (e) => seen.push(e.multiplicity),
      onStep: (s) => stepped.push(s.multiplicity),
    });
    assert.equal(r.steps, 1);
    assert.deepEqual(seen, [7]);
    assert.deepEqual(stepped, [7]);
    assert.equal(r.events[0].multiplicity, 7);
  });
});

describe('till cohort firing — differential (batch ≡ per-item, B1 rider 3)', () => {
  it('production chain with parcels, a preserved machine, and spoilage', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
junk: type.
wood: type.
plank: type.
saw: type.

gen: junk -o { !_5 wood }@1.
mill: $saw * !_2 wood -o { plank }@3.
spoil: plank@Q * after (Q+10) -o { I }.
`);
    const mk = () => lin({ [atom('junk')]: 4, [atom('saw')]: 2 });
    const { on } = differential(calc, mk, '60');
    assert.ok(maxMult(on.events) > 1, 'batches must actually occur');
  });

  it('serialized machines: k same-stamp machines batch k-parallel, then stagger', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
wood: type.
plank: type.
saw: type.

mill: $saw * wood -o { plank }@2.
`);
    const mk = () => lin({ [atom('saw')]: 3, [atom('wood')]: 10 });
    const { on } = differential(calc, mk, '20');
    // 3 machines: rounds of multiplicity 3 (then the 10-wood tail)
    assert.equal(on.events[0].multiplicity, 3);
    assert.equal(on.quiescent, true);
  });

  it('read arcs subtract from the batch pool (k·take + reserve ≤ count)', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
w: type.

burn: read w * w -o { I }@1.
`);
    // Each fire reads one w AND consumes one w from the same cohort:
    // 10 copies support exactly 9 fires (the last copy stays readable).
    const mk = () => lin({ [atom('w')]: 10 });
    const { on } = differential(calc, mk, '50');
    assert.equal(on.events[0].multiplicity, 9);
    assert.equal(on.steps, 1);
  });

  it('multi-cohort spread takes never mis-batch', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
a: type.
a2: type.
b: type.

mk: a -o { !_3 b }@1.
mk2: a2 -o { !_2 b }@2.
eat: !_2 b -o { I }@1.
`);
    differential(calc, () => lin({ [atom('a')]: 1, [atom('a2')]: 1 }), '20');
  });

  it('PP2 kiln — real draws, parcels, coalescing: state-identical', () => {
    const calc = load(PP2);
    const mk = () => {
      const s = initQuery(calc, 'expect_shell_start');
      s.linear[atom('kiln')] = 1;
      return s;
    };
    const on = calc.settle(mk(), '4000', { coalesce: true, seed: 7, events: false });
    const off = calc.settle(mk(), '4000', { coalesce: true, seed: 7, events: false, batch: false });
    assert.equal(stampedStr(on.state), stampedStr(off.state));
  });

  it('acceleration composes with batching (jump, state, certificate parity)', () => {
    // A preserved machine drives an eternal produce/spoil orbit: both
    // modes must certify the SAME orbit, jump, and land state-identical.
    const calc = prog(`
% tokens (closed-world sort checking)
mill: type.
wood: type.

tick: $mill -o { wood }@2.
spoil: wood@Q * after (Q+5) -o { I }.
`);
    const mk = () => lin({ [atom('mill')]: 1 });
    const on = calc.settle(mk(), '5000', { accelerate: true, seed: 7, events: false });
    const off = calc.settle(mk(), '5000', { accelerate: true, seed: 7, events: false, batch: false });
    assert.equal(stampedStr(on.state), stampedStr(off.state));
    assert.ok(on.accelerated.length >= 1, 'batched run must jump');
    assert.ok(off.accelerated.length >= 1, 'per-item run must jump');
    assert.ok(on.certificate && off.certificate, 'both modes mint');
    assert.equal(on.certificate.sigKey, off.certificate.sigKey);
    assert.deepEqual(on.certificate.period, off.certificate.period);
  });

  it('settleChunked composes with batching (E5 — an instant never splits)', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
junk: type.
wood: type.
plank: type.
saw: type.

gen: junk -o { !_5 wood }@1.
mill: $saw * !_2 wood -o { plank }@3.
spoil: plank@Q * after (Q+10) -o { I }.
`);
    const mk = () => lin({ [atom('junk')]: 4, [atom('saw')]: 2 });
    const single = calc.settle(mk(), '60');
    const chunked = calc.settleChunked(mk(), '60', { chunk: '7' });
    assert.equal(stampedStr(chunked.state), stampedStr(single.state));
    assert.equal(chunked.steps, single.steps);
    assert.equal(traceKey(chunked.events), traceKey(single.events));
  });
});

describe('till cohort firing — fences (B1 rider 1)', () => {
  it('an equal-activation tie never batches; the draw stream is untouched', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
a: type.

r1: a -o { I }@1.
r2: a -o { I }@1.
`);
    const mk = () => lin({ [atom('a')]: 10 });
    const { on, off } = differential(calc, mk, '50', { seed: 7 });
    assert.equal(maxMult(on.events), 1, 'tied candidates fire per-item');
    assert.equal(on.steps, off.steps);
  });

  it('zero-delay outputs that feed a rule never batch; a delayed window consumer does', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
a: type.
b: type.

gen: a -o { b }@0.
eat: b@Q * after (Q+1) -o { I }.
`);
    const mk = () => lin({ [atom('a')]: 6 });
    const { on } = differential(calc, mk, '10');
    for (const e of on.events) {
      if (e.rule === 'gen') assert.equal(e.multiplicity, undefined, 'gen feeds the instant');
    }
    const eat = on.events.find(e => e.rule === 'eat');
    assert.equal(eat.multiplicity, 6, 'the window consumer batches the whole cohort');
  });

  it('persistent production never batches (timeless facts are instantly visible)', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
a: type.
know: bin -> type.

learn: a -o { !know 1 }@5.
`);
    const mk = () => lin({ [atom('a')]: 4 });
    const { on } = differential(calc, mk, '10');
    assert.equal(maxMult(on.events), 1);
    assert.equal(on.steps, 4);
  });

  it('weighted consequents never batch (each fire draws its own alt)', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
a: type.
win: type.
lose: type.

fight: a -o { woplus 1/2 win lose }@1.
`);
    const mk = () => lin({ [atom('a')]: 8 });
    const { on, off } = differential(calc, mk, '10', { seed: 5 });
    assert.equal(maxMult(on.events), 1);
    assert.equal(on.steps, off.steps);
  });

  it('a zero-delay output only a possessed loli consumes never batches', () => {
    // The instant-feeding tables must include STATE-loli antecedents, not
    // just the static rule list (audit 2026-08-23): wood has no static
    // consumer, so pre-fix grow batched past the loli and the grow/loli
    // tie draw vanished from the PRF stream (trace order diverged).
    const calc = prog(`
% tokens (closed-world sort checking)
trigger: type.
seed: type.
wood: type.
plank: type.

mint: trigger -o { (wood -o { plank }@0) }@0.
grow: seed -o { wood }@0.
`);
    const mk = () => lin({ [atom('trigger')]: 1, [atom('seed')]: 3 });
    for (const seed of [0, 7, 23]) {
      const { on } = differential(calc, mk, '10', { seed });
      // The FIRST grow always fires with the loli still possessed (the
      // loli needs wood, which only grow makes) — it must stay per-item.
      // Once the loli is CONSUMED the remaining grows may batch soundly:
      // the guard is per-firing and recomputes as the state mutates.
      const grow0 = on.events.find(e => e.rule === 'grow');
      assert.equal(grow0.multiplicity, undefined, "grow feeds the loli's instant");
    }
  });

  it('a self-feeding loop cannot batch past the Zeno guard', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
z: type.

loop: z -o { z }@0.
`);
    assert.throws(
      () => calc.settle(lin({ [atom('z')]: 5 }), '10', { maxInstantSteps: 50 }),
      /Zeno/);
  });

  it('the batched-produce I32 fence throws loudly', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
w: type.
sand: type.

dup: w -o { !_30000 sand }@1.
`);
    assert.throws(
      () => calc.settle(lin({ [atom('w')]: 100000 }), '5', { events: false }),
      /Int32/);
  });
});

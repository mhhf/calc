/**
 * Catch-up at scale (TODO_0278 A2) — Zeno redefinition, event suppression,
 * settleChunked.
 *
 * Pins:
 *   - Zeno guard (D16 redefined): true Zeno is NO TIME PROGRESS — the guard
 *     counts firings at ONE instant (maxInstantSteps). A dense-but-finite
 *     schedule runs to completion; flat maxSteps is an opt-in hard cap.
 *   - Event suppression: { events: false } skips the events array (the
 *     week-scale OOM), keeps count + per-rule totals; onEvent streams the
 *     full records either way.
 *   - settleChunked ≡ settle: E5 composability IS the proof — bit-exact in
 *     exact mode (including PRF draws: the chooser is horizon-split
 *     invariant), drop-in result contract (next/rebase in the caller's
 *     frame), certificate threading (one validated jump per slice on a
 *     proven orbit), total maxSteps budget, onChunk progress.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';
import { FIX, loadTill as load, atom, initQuery, stampedStr, bagStr, traceKey } from './till-helpers.js';

const PP2 = path.join(import.meta.dirname, '../../calculus/till/game/PP2.till');

const lin = (obj) => ({ linear: obj, persistent: {} });
const skippedOf = (r) => (r.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
const resumedJump = (r) => (r.accelerated || []).find(a => a.resumed);

describe('till Zeno guard — zero time progress, not step count (A2 rider 4)', () => {
  const calc = load(FIX('till-zeno.ill'));
  const unitCalc = load(FIX('till-unit-conseq.ill'));
  const ping = load(FIX('till-ping.ill'));

  it('zero-delay cycle trips the instant guard with NO maxSteps (default)', () => {
    assert.throws(() => calc.settle(lin({ [atom('a')]: 1 }), '0', {}), /Zeno/);
  });

  it('maxInstantSteps bounds firings at one instant and names it', () => {
    assert.throws(
      () => calc.settle(lin({ [atom('a')]: 1 }), '0', { maxInstantSteps: 50 }),
      (e) => /Zeno/.test(e.message) && /instant/.test(e.message) && /maxInstantSteps=50/.test(e.message));
  });

  it('a dense-but-finite instant runs to completion (it is not Zeno)', () => {
    // Per-item (batch: false): 500 same-instant firings never trip the
    // instant guard — dense-but-finite is not Zeno (the A2 rider-4 intent).
    const r = unitCalc.settle(lin({ [atom('junk')]: 500 }), '10', { batch: false });
    assert.equal(r.steps, 500);
    assert.equal(r.quiescent, true);
    // Default (B1 cohort firing): the whole cohort is ONE firing step —
    // the instant guard bound now measures rule progress, not tokens.
    const b = unitCalc.settle(lin({ [atom('junk')]: 500 }), '10', { maxInstantSteps: 5 });
    assert.equal(b.steps, 1);
    assert.equal(b.events[0].multiplicity, 500);
    assert.equal(b.quiescent, true);
  });

  it('many events across many instants never trip the instant guard', () => {
    // 601 firings, one per second — under the OLD flat default this class of
    // catch-up threw; per-instant it is trivially productive.
    const r = ping.settle(lin({ [atom('pa')]: 1 }), '600', { maxInstantSteps: 5 });
    assert.equal(r.steps, 601);
  });

  it('flat maxSteps survives as an opt-in hard cap with its own message', () => {
    assert.throws(
      () => ping.settle(lin({ [atom('pa')]: 1 }), '600', { maxSteps: 50 }),
      (e) => /maxSteps=50/.test(e.message) && !/Zeno/.test(e.message));
  });
});

describe('till event suppression — { events: false } and onEvent (A2 rider 5)', () => {
  const calc = load(PP2);
  const mk = () => lin({ [atom('lumberjack')]: 1, [atom('quarry')]: 1 });

  it('suppressed run: same state and step count, totals instead of records', () => {
    const full = calc.settle(mk(), '300', { seed: 7 });
    const slim = calc.settle(mk(), '300', { seed: 7, events: false });
    assert.equal(slim.events, null);
    assert.equal(slim.steps, full.steps);
    assert.equal(stampedStr(slim.state), stampedStr(full.state));
    const fromFull = {};
    for (const e of full.events) fromFull[e.rule] = (fromFull[e.rule] || 0) + 1;
    assert.deepEqual({ ...slim.eventTotals }, fromFull);   // null-prototype by design
    assert.equal(Object.values(slim.eventTotals).reduce((a, b) => a + b, 0), slim.steps);
  });

  it('onEvent streams the full records even when the array is suppressed', () => {
    const full = calc.settle(mk(), '300', { seed: 7 });
    const seen = [];
    const slim = calc.settle(mk(), '300', { seed: 7, events: false, onEvent: (e) => seen.push(e) });
    assert.equal(slim.events, null);
    assert.equal(traceKey(seen), traceKey(full.events));
    assert.deepEqual(seen[0].produced, full.events[0].produced);
  });

  it('accelerated catch-up with suppression: jumps report, no event array', () => {
    const r = calc.settle(mk(), '100000', { accelerate: true, seed: 7, events: false });
    assert.ok(skippedOf(r) > 0, 'orbit must certify');
    assert.equal(r.events, null);
    assert.ok(Object.keys(r.eventTotals).length > 0);
  });
});

describe('till settleChunked — bounded slices, E5-exact (A2)', () => {
  const calc = load(PP2);
  const duel = load(FIX('till-duel.ill'));
  const mk = () => lin({ [atom('lumberjack')]: 1, [atom('quarry')]: 1 });
  const mkS = () => initQuery(calc, 'expect_shell_start');

  it('requires a positive chunk', () => {
    assert.throws(() => calc.settleChunked(mk(), '100', {}), /chunk/);
    assert.throws(() => calc.settleChunked(mk(), '100', { chunk: '0' }), /chunk/);
  });

  it('chunked ≡ single settle bit-exact in exact mode (state, events, next)', () => {
    const single = calc.settle(mk(), '400', { seed: 7 });
    const chunked = calc.settleChunked(mk(), '400', { seed: 7, chunk: '37' });
    assert.ok(chunked.chunks > 5, `expected many slices, got ${chunked.chunks}`);
    assert.equal(stampedStr(chunked.state), stampedStr(single.state));
    assert.equal(chunked.steps, single.steps);
    assert.equal(traceKey(chunked.events), traceKey(single.events));
    assert.deepEqual(ratParts(chunked.next), ratParts(single.next));
    assert.equal(chunked.quiescent, single.quiescent);
  });

  it('PRF draws replay identically across slice boundaries (woplus)', () => {
    const S = () => lin({ [atom('rockd')]: 3, [atom('scid')]: 3 });
    const single = duel.settle(S(), '10', { seed: 5 });
    const chunked = duel.settleChunked(S(), '10', { seed: 5, chunk: '2' });
    assert.equal(stampedStr(chunked.state), stampedStr(single.state));
    assert.equal(traceKey(chunked.events), traceKey(single.events));
  });

  it('quiescence ends the slicing early', () => {
    const unitCalc = load(FIX('till-unit-conseq.ill'));
    const r = unitCalc.settleChunked(lin({ [atom('junk')]: 3 }), '1000', { chunk: '10' });
    assert.equal(r.quiescent, true);
    assert.equal(r.next, null);
    assert.equal(r.steps, 1);           // B1: the 3-cohort batches into one step
    assert.equal(r.events[0].multiplicity, 3);
    assert.ok(r.chunks <= 4, `expected early quiescence, got ${r.chunks} chunks`);
  });

  it('onChunk reports monotone progress in the caller frame', () => {
    const seen = [];
    calc.settleChunked(mk(), '400', { seed: 7, chunk: '37', onChunk: (p) => seen.push(p) });
    assert.ok(seen.length > 5);
    let prev = null;
    for (const p of seen) {
      const t = ratParts(p.settledTo);
      if (prev) assert.ok(t[0] * prev[1] >= prev[0] * t[1], 'settledTo must be nondecreasing');
      prev = t;
      assert.equal(typeof p.chunks, 'number');
      assert.equal(typeof p.steps, 'number');
    }
    assert.deepEqual(ratParts(seen[seen.length - 1].settledTo), [400n, 1n]);
  });

  it('maxSteps is a TOTAL budget across slices', () => {
    const ping = load(FIX('till-ping.ill'));
    assert.throws(
      () => ping.settleChunked(lin({ [atom('pa')]: 1 }), '600', { chunk: '100', maxSteps: 150 }),
      /maxSteps/);
  });

  it('event suppression composes: merged per-rule totals', () => {
    const full = calc.settleChunked(mk(), '400', { seed: 7, chunk: '37' });
    const slim = calc.settleChunked(mk(), '400', { seed: 7, chunk: '37', events: false });
    assert.equal(slim.events, null);
    assert.equal(stampedStr(slim.state), stampedStr(full.state));
    const fromFull = {};
    for (const e of full.events) fromFull[e.rule] = (fromFull[e.rule] || 0) + 1;
    assert.deepEqual({ ...slim.eventTotals }, fromFull);
  });

  it('certificate threading: a saved orbit resumes as one jump per slice', () => {
    const save = calc.settle(mkS(), '3000', { accelerate: true, seed: 7 });
    assert.ok(save.certificate, 'precondition: save mints');
    const chunked = calc.settleChunked(save.state, '9000', {
      certificate: save.certificate, seed: 7, chunk: '2000',
    });
    assert.ok(resumedJump(chunked), 'expected a certificate-resumed jump');
    assert.ok(chunked.chunks >= 2);
    assert.ok(chunked.certificate, 'final slice re-mints');
    const plainFull = calc.settle(mkS(), '9000', { coalesce: true, seed: 7 });
    assert.equal(stampedStr(chunked.state), stampedStr(plainFull.state));
    assert.equal(save.events.length + skippedOf(save) + chunked.steps + skippedOf(chunked),
      plainFull.events.length);
  });

  it('rebase accumulates across slices; the absolute continuation agrees', () => {
    const single = calc.settle(mk(), '400', { seed: 7, coalesce: true, rebase: true });
    const chunked = calc.settleChunked(mk(), '400', { seed: 7, coalesce: true, rebase: true, chunk: '37' });
    assert.ok(chunked.rebase !== undefined);
    const cb = ratParts(chunked.rebase), sb = ratParts(single.rebase);
    assert.equal(cb[1], 1n); assert.equal(sb[1], 1n);   // integral shifts
    // next reported in the CALLER's frame — drop-in for settle's contract
    if (single.next !== null) {
      assert.deepEqual(ratParts(chunked.next), ratParts(single.next));
    }
    // Dead (coalesced) stamps are frame-relative by design, so absolute
    // stamp equality is only owed to LIVE facts — pin via the observable
    // continuation to a common absolute time (PP2 idle is draw-free).
    const c2 = calc.settle(chunked.state, String(800n - cb[0]), { seed: 7, coalesce: true });
    const s2 = calc.settle(single.state, String(800n - sb[0]), { seed: 7, coalesce: true });
    assert.equal(c2.steps, s2.steps);
    assert.equal(bagStr(c2.state), bagStr(s2.state));
  });
});

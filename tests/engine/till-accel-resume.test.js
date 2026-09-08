/**
 * Orbit-certificate persistence (TODO_0278 A1) — accel.js mint/resume.
 *
 * A settle that PROVES a periodic orbit and exits inside it mints a
 * certificate: { fingerprint, sigKey, period, sinkDelta, cycleEvents }.
 * A later settle on the saved state accepts the certificate and jumps the
 * elapsed cycles in O(state) instead of re-detecting (or re-firing).
 *
 * Pins:
 *   - mint condition: certificate only at a horizon exit covered by a
 *     proven, draw-free, deadline-clear orbit — never otherwise
 *   - resume exactness (E5): save + certificate-resume reaches the SAME
 *     stamped multiset as one uninterrupted run; events fully accounted
 *   - validation is exact: tampered signature or foreign fingerprint falls
 *     back to in-run re-detection, result unchanged
 *   - 'verify' mode: honest O(one-period) re-proof instead of trust
 *   - deadlines: resume jump capped below ground before-bounds; a horizon
 *     past the crossing never mints with the stale period
 *   - rebase: mint/resume operate in the rebased frame
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import { ratParts } from '../../lib/kernel/rat-term.js';
import { loadTill as load, atom, initQuery, stampedStr, bagStr } from './till-helpers.js';

const PP2 = path.join(import.meta.dirname, '../../calculus/till/game/PP2.till');

let _dir = null;
function prog(text) {
  if (!_dir) _dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-resume-'));
  const f = path.join(_dir, `p${fs.readdirSync(_dir).length}.ill`);
  fs.writeFileSync(f, text);
  return load(f);
}

const skippedOf = (r) => (r.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);
const resumedJump = (r) => (r.accelerated || []).find(a => a.resumed);

describe('till orbit certificates — mint (A1)', () => {
  const calc = load(PP2);
  const mk = () => ({ linear: { [atom('lumberjack')]: 1, [atom('quarry')]: 1 }, persistent: {} });

  it('proven orbit at exit mints a JSON-safe certificate', () => {
    const r = calc.settle(mk(), '1000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.ok(skippedOf(r) > 0, 'precondition: the orbit must certify in-run');
    const c = r.certificate;
    assert.ok(c, 'expected a certificate at the horizon exit');
    assert.equal(c.v, 1);
    assert.equal(typeof c.sigKey, 'string');
    assert.equal(typeof c.fingerprint, 'string');
    assert.equal(c.fingerprint, calc.bundleFingerprint);
    assert.ok(calc.verifyFingerprint(c.fingerprint));
    assert.equal(c.period.length, 2);
    assert.ok(BigInt(c.period[0]) > 0n && BigInt(c.period[1]) > 0n);
    assert.ok(Number.isInteger(c.cycleEvents) && c.cycleEvents >= 1);
    assert.ok(Array.isArray(c.sinkDelta));
    // survives a save file round-trip bit-exactly
    assert.deepEqual(JSON.parse(JSON.stringify(c)), c);
  });

  it('no proven orbit → no certificate (too few events)', () => {
    const r = calc.settle(mk(), '3', { accelerate: true, seed: 7 });
    assert.equal(skippedOf(r), 0);
    assert.equal(r.certificate, undefined);
  });

  it('woplus draws void every window → no certificate', () => {
    const c2 = prog('wa: type.\nwb: type.\nwc: type.\n' +
      'flip: wa -o { woplus 1/2 wb wc }@1.\n' +
      'rb: wb -o { wa }@1.\n' +
      'rc: wc -o { wa }@1.\n');
    const r = c2.settle({ linear: { [atom('wa')]: 1 }, persistent: {} }, '300',
      { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.equal(r.certificate, undefined);
  });

  it('quiescent-forever exit (nothing pending) mints nothing', () => {
    const c2 = prog('wood: type.\nplank: type.\n' +
      'once: wood -o { plank }@1.\n');
    const r = c2.settle({ linear: { [atom('wood')]: 1 }, persistent: {} }, '10',
      { accelerate: true, seed: 7 });
    assert.equal(r.next, null);
    assert.equal(r.certificate, undefined);
  });
});

describe('till orbit certificates — resume (A1)', () => {
  const calc = load(PP2);
  const mk = () => ({ linear: { [atom('lumberjack')]: 1, [atom('quarry')]: 1 }, persistent: {} });

  it('resume jump: state identical to the uninterrupted run, events fully accounted (E5)', () => {
    const plainFull = calc.settle(mk(), '5000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    const save = calc.settle(mk(), '1000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.ok(save.certificate, 'precondition: save mints');
    const cert = JSON.parse(JSON.stringify(save.certificate));
    const resume = calc.settle(save.state, '5000',
      { accelerate: true, certificate: cert, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(resume.state), stampedStr(plainFull.state));
    const j = resumedJump(resume);
    assert.ok(j, 'expected the certificate jump to apply');
    assert.ok(j.cycles >= 1);
    assert.equal(save.events.length + skippedOf(save) + resume.events.length + skippedOf(resume),
      plainFull.events.length, 'every elided event accounted for across the save/resume seam');
  });

  it('resume re-mints at its own exit — chained saves keep working', () => {
    const save = calc.settle(mk(), '1000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    const r1 = calc.settle(save.state, '5000',
      { accelerate: true, certificate: save.certificate, seed: 7, maxSteps: 10000000 });
    assert.ok(r1.certificate, 'certificate-resumed settle must re-mint');
    const r2 = calc.settle(r1.state, '20000',
      { accelerate: true, certificate: r1.certificate, seed: 7, maxSteps: 10000000 });
    assert.ok(resumedJump(r2));
    const scratch = calc.settle(mk(), '20000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(r2.state), stampedStr(scratch.state));
  });

  it('full PP2 shell state: save at 3000, certificate-resume to 8000 exact', () => {
    const mkS = () => initQuery(calc, 'expect_shell_start');
    const plainFull = calc.settle(mkS(), '8000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    const save = calc.settle(mkS(), '3000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.ok(save.certificate, 'shell idle orbit must mint');
    const resume = calc.settle(save.state, '8000',
      { accelerate: true, certificate: save.certificate, seed: 7, maxSteps: 10000000 });
    assert.ok(resumedJump(resume), 'certificate must apply on the shell state');
    assert.equal(stampedStr(resume.state), stampedStr(plainFull.state));
    assert.equal(save.events.length + skippedOf(save) + resume.events.length + skippedOf(resume),
      plainFull.events.length);
  });

  it('tampered sigKey: refused, falls back to re-detection, result unchanged', () => {
    const save = calc.settle(mk(), '1000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    const bad = { ...save.certificate, sigKey: save.certificate.sigKey + 'x' };
    const r = calc.settle(save.state, '5000',
      { accelerate: true, certificate: bad, seed: 7, maxSteps: 10000000 });
    assert.equal(resumedJump(r), undefined, 'tampered certificate must not apply');
    const truth = calc.settle(mk(), '5000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(r.state), stampedStr(truth.state));
    assert.ok(skippedOf(r) > 0, 'in-run re-detection must still accelerate');
  });

  it('foreign fingerprint: refused, result unchanged', () => {
    const save = calc.settle(mk(), '1000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    const bad = { ...save.certificate, fingerprint: 'ev=deadbeef;n=1;c=1;s=1;b=0;a=0;t=1;d=deadbeef' };
    const r = calc.settle(save.state, '5000',
      { accelerate: true, certificate: bad, seed: 7, maxSteps: 10000000 });
    assert.equal(resumedJump(r), undefined);
    const truth = calc.settle(mk(), '5000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(r.state), stampedStr(truth.state));
  });

  it("'verify' mode: one-period honest re-proof, then jumps", () => {
    const save = calc.settle(mk(), '1000', { accelerate: true, seed: 7, maxSteps: 10000000 });
    const r = calc.settle(save.state, '5000',
      { accelerate: true, certificate: save.certificate, certificateMode: 'verify',
        seed: 7, maxSteps: 10000000 });
    assert.equal(resumedJump(r), undefined, 'verify mode must not trust-jump');
    assert.ok(skippedOf(r) > 0, 'verify mode must still certify and jump');
    const truth = calc.settle(mk(), '5000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(r.state), stampedStr(truth.state));
  });
});

describe('till orbit certificates — deadlines and rebase (A1)', () => {
  it('ground before-deadline: resume capped below it, crossing replayed exactly', () => {
    const calc = prog('lumber: type.\nwood: type.\n' +
      'lj: lumber -o { lumber * wood }@1.\n' +
      'mk: wood * before 200 -o { I }.\n');
    const mk = () => ({ linear: { [atom('lumber')]: 1 }, persistent: {} });
    const save = calc.settle(mk(), '100', { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.ok(save.certificate, 'pre-deadline orbit must mint (deadline still ahead)');
    const resume = calc.settle(save.state, '1000',
      { accelerate: true, certificate: save.certificate, seed: 7, maxSteps: 10000000 });
    assert.ok(resumedJump(resume), 'certificate must apply, capped below t=200');
    const truth = calc.settle(mk(), '1000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(resume.state), stampedStr(truth.state));
  });

  it('horizon past the crossing: the stale pre-deadline period is never minted', () => {
    const calc = prog('lumber: type.\nwood: type.\n' +
      'lj: lumber -o { lumber * wood }@1.\n' +
      'mk: wood * before 200 -o { I }.\n');
    const mk = () => ({ linear: { [atom('lumber')]: 1 }, persistent: {} });
    // 210: the last jump was proven pre-crossing; the crossing fired in the
    // remainder and no post-crossing orbit re-certified — mint must refuse.
    const r = calc.settle(mk(), '210', { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.ok(skippedOf(r) > 0, 'precondition: pre-deadline jump happened');
    assert.equal(r.certificate, undefined,
      'a certificate across a crossed deadline would carry a stale period');
  });

  it('rebase: certificate minted in the rebased frame resumes correctly', () => {
    const calc = load(PP2);
    const mk = () => ({ linear: { [atom('lumberjack')]: 1, [atom('quarry')]: 1 }, persistent: {} });
    const save = calc.settle(mk(), '1000',
      { accelerate: true, rebase: true, seed: 7, maxSteps: 10000000 });
    assert.ok(save.certificate, 'rebased exit must still mint');
    const [bn, bd] = ratParts(save.rebase);
    assert.equal(bd, 1n, 'rebase shift is floored to an integer');
    const T2 = String(5000n - bn);
    const withCert = calc.settle(save.state, T2,
      { accelerate: true, certificate: save.certificate, seed: 7, maxSteps: 10000000 });
    assert.ok(resumedJump(withCert), 'certificate must apply in the rebased frame');
    const noCert = calc.settle(save.state, T2,
      { accelerate: true, seed: 7, maxSteps: 10000000 });
    assert.equal(stampedStr(withCert.state), stampedStr(noCert.state));
    const plainFull = calc.settle(mk(), '5000', { coalesce: true, seed: 7, maxSteps: 10000000 });
    assert.equal(bagStr(withCert.state), bagStr(plainFull.state),
      'stamp-blind counts at the same absolute time must agree');
  });
});

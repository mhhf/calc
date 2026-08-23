/**
 * Covariant tie-PRF — draw-tolerant acceleration (TODO_0278 A3a).
 *
 * A tie whose candidates bind no stamp terms draws from a translation-
 * covariant PRF input (seed + relative candidate identities), so an exact
 * orbit recurrence forces the draw to replay — tie-poisoned cycles (any
 * built kiln: !_W wood racing the sawmill's wood) certify with no loss of
 * exactness. Pins:
 *   - the kiln state CERTIFIES and jumps (formerly: every window voided)
 *   - exactness: accelerated ≡ coalesced run, state-identical, same seed
 *   - deep time is O(1) in elapsed time (steps stay bounded)
 *   - certificates mint and resume on the kiln state
 *   - the covariance fence: stamp-BINDING ties still void the window
 *     (no certification), and the run stays correct
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import { loadTill as load, atom, initQuery, stampedStr } from './till-helpers.js';

const PP2 = path.join(import.meta.dirname, '../../calculus/till/game/PP2.till');

let _dir = null;
function prog(text) {
  if (!_dir) _dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-a3a-'));
  const f = path.join(_dir, `p${fs.readdirSync(_dir).length}.ill`);
  fs.writeFileSync(f, text);
  return load(f);
}

const jumpsOf = (r) => (r.accelerated || []).length;
const skippedOf = (r) => (r.accelerated || []).reduce((s, a) => s + a.skippedEvents, 0);

describe('till covariant tie-PRF — kiln orbits certify (A3a)', () => {
  const calc = load(PP2);
  const mkKiln = () => {
    const s = initQuery(calc, 'expect_shell_start');
    s.linear[atom('kiln')] = 1;
    return s;
  };

  it('the tie-poisoned kiln state certifies and jumps', () => {
    const r = calc.settle(mkKiln(), '50000', { accelerate: true, seed: 7 , events: false });
    assert.ok(jumpsOf(r) >= 1, 'expected at least one certified jump');
    assert.ok(skippedOf(r) > 0);
  });

  it('acceleration is state-identical to the coalesced run (exactness)', () => {
    const plain = calc.settle(mkKiln(), '4000', { coalesce: true, seed: 7, events: false });
    const fast = calc.settle(mkKiln(), '4000', { accelerate: true, seed: 7, events: false });
    assert.equal(stampedStr(fast.state), stampedStr(plain.state));
  });

  it('deep time is O(1): elapsed x40 leaves fired steps flat', () => {
    const r1 = calc.settle(mkKiln(), '50000', { accelerate: true, seed: 7, events: false });
    const r2 = calc.settle(mkKiln(), '2000000', { accelerate: true, seed: 7, events: false });
    assert.ok(jumpsOf(r2) >= 1);
    // without certification 2M horizon ≈ 26M events; with jumps the fired
    // remainder stays within a small multiple of the warmup
    assert.ok(r2.steps < r1.steps * 3,
      `steps must not scale with elapsed time (${r1.steps} -> ${r2.steps})`);
  });

  it('certificates mint and resume on the kiln state', () => {
    const save = calc.settle(mkKiln(), '30000', { accelerate: true, seed: 7, events: false });
    assert.ok(save.certificate, 'kiln exit inside a proven orbit must mint');
    const resume = calc.settle(save.state, '200000',
      { certificate: save.certificate, seed: 7, events: false });
    const rj = (resume.accelerated || []).find(a => a.resumed);
    assert.ok(rj, 'expected a certificate-resumed jump');
    const truth = calc.settle(mkKiln(), '200000', { accelerate: true, seed: 7, events: false });
    assert.equal(stampedStr(resume.state), stampedStr(truth.state));
  });

  it('draw replay is verbatim under the deterministic chooser too', () => {
    const r = calc.settle(mkKiln(), '50000',
      { accelerate: true, chooser: 'deterministic', events: false });
    assert.ok(jumpsOf(r) >= 1, 'covariant deterministic ties must certify');
  });
});

describe('till covariance fence — stamp-binding ties still void (A3a)', () => {
  it('a tie that binds cohort stamps never certifies, and stays correct', () => {
    const calc = prog(`
% tokens (closed-world sort checking)
src: type.
a: type.

gen: src -o { src * a }@5.
r1: a@Q -o { I }.
r2: a@Q -o { I }.
`);
    const S = { linear: { [atom('src')]: 1 }, persistent: {} };
    const r = calc.settle(S, '2000', { accelerate: true, seed: 7 });
    assert.equal(jumpsOf(r), 0, 'stamp-binding tie must void every window');
    // periodic source, fired plainly: 401 gens (t = 0, 5, …, 2000) plus
    // 400 eats (the last a lands at 2005, beyond the horizon)
    assert.equal(r.steps, 801);
  });
});

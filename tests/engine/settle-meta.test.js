/**
 * till metamorphic settle laws over RANDOM ground timed states — TODO_0265
 * Phase 5 (infrastructure map: settle-meta).
 *
 * The composability law settle(settle(S,T₁),T₂) ≡ settle(S,T₂) (E5) and
 * idempotence settle(settle(S,T),T) ≡ settle(S,T) are pinned on hand-built
 * scenarios in till-settle.test.js; here they are checked METAMORPHICALLY:
 * for each executable-spec program, randomized initial multisets (random
 * counts × random stamps of the program's own atoms) and randomized split
 * points, all under one fixed seed (the D17 stateless PRF makes mid-flight
 * resumption replay-identical, so the laws hold on conflicting states too).
 *
 * One fixed master seed drives everything — failures reproduce exactly.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { ratParts } from '../../lib/engine/theories/ratlit-theory.js';

const SPEC = (f) => path.join(import.meta.dirname, '../../calculus/till/tests/forward', f);
const load = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });

// program → its atom alphabet (facts the rules mention)
const PROGRAMS = [
  ['schedule.ill', ['sawmill', 'wood']],
  ['spoilage.ill', ['food', 'meal_order', 'bakery']],
  ['grades.ill', ['log', 'wood', 'sawmill']],
  ['read.ill', ['chopper', 'tree', 'manual', 'x', 'late', 'wood']],
  ['economy.ill', ['sawmill', 'smith', 'wood', 'plank', 'stone']],
];
const STAMPS = [null, [1n, 1n], [1n, 2n], [2n, 1n]];   // null = unstamped (D11 → 0)
const HORIZONS = ['0', '1/2', '1', '2', '5'];
const STATES_PER_PROGRAM = 8;
const SEED = 3;

let rngState = 0xBEEF | 1;
const rand = () => {
  rngState ^= rngState << 13; rngState ^= rngState >>> 17; rngState ^= rngState << 5;
  return (rngState >>> 0) / 0x100000000;
};
const pick = (xs) => xs[Math.floor(rand() * xs.length)];
const randInt = (n) => Math.floor(rand() * n);

function randomState(atoms) {
  const linear = {};
  let tokens = 0;
  for (const a of atoms) {
    const h = Store.put('atom', [a]);
    for (const st of STAMPS) {
      if (rand() < 0.45) continue;
      const c = 1 + randInt(2);
      const fact = st === null ? h : Store.put('at', [h, putRat(...st)]);
      linear[fact] = (linear[fact] || 0) + c;
      tokens += c;
    }
  }
  if (tokens === 0) linear[Store.put('atom', [atoms[0]])] = 1;
  return { linear, persistent: {} };
}

/** Canonical 'inner@n/d'×count string of a timed state. */
function stamped(state) {
  const out = {};
  for (const [hStr, c] of Object.entries(state.linear)) {
    const h = Number(hStr);
    const isAt = Store.tag(h) === 'at';
    const inner = isAt ? Store.child(h, 0) : h;
    const [n, d] = isAt ? ratParts(Store.child(h, 1)) : [0n, 1n];
    const key = `${Store.tag(inner) === 'atom' ? Store.child(inner, 0) : Store.tag(inner)}@${n}/${d}`;
    out[key] = (out[key] || 0) + c;
  }
  return Object.entries(out).sort().map(([k, v]) => `${k}x${v}`).join(',');
}

describe('till settle metamorphic laws (E5) over random states', () => {
  for (const [file, atoms] of PROGRAMS) {
    it(`${file}: composability + idempotence on ${STATES_PER_PROGRAM} random states`, () => {
      const calc = load(SPEC(file));
      for (let i = 0; i < STATES_PER_PROGRAM; i++) {
        const S = randomState(atoms);
        const T = pick(HORIZONS.slice(1));            // final horizon > 0
        const splits = new Set(['0', T, pick(HORIZONS), pick(HORIZONS)]);
        const direct = calc.settle(S, T, { seed: SEED }).state;
        for (const t1 of splits) {
          if (cmpHz(t1, T) > 0) continue;             // only splits ≤ T are meaningful
          const mid = calc.settle(S, t1, { seed: SEED }).state;
          const resumed = calc.settle(mid, T, { seed: SEED }).state;
          assert.equal(stamped(resumed), stamped(direct),
            `${file} state#${i} split ${t1} of ${T}\nstate: ${stamped(S)}`);
        }
        const once = calc.settle(S, T, { seed: SEED }).state;
        assert.equal(stamped(calc.settle(once, T, { seed: SEED }).state), stamped(once),
          `${file} state#${i} idempotence at ${T}`);
      }
    });
  }
});

/** Compare two horizon strings as exact rationals. */
function cmpHz(a, b) {
  const parse = (s) => (s.includes('/') ? s.split('/').map(BigInt) : [BigInt(s), 1n]);
  const [an, ad] = parse(a); const [bn, bd] = parse(b);
  const l = an * bd, r = bn * ad;
  return l < r ? -1 : l > r ? 1 : 0;
}

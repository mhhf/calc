/**
 * Constructor priors @w + Chi–Geman lint (TODO_0297 P1; 0292 D5/M6/M7).
 *
 * Pins:
 *   - `name: sort @w Q.` parses in program files (nat and fraction),
 *     lands on calc.priors as exact [n,d]; unannotated members absent
 *     (default weight 1 is the CONSUMER's rule, not table content)
 *   - the parse is regex-narrow: stamp positions (`food@Q`, `{...}@3`)
 *     are untouched (a timed rule in the same file still loads)
 *   - @w on a non-classifier-member is a LOAD error (loud, not dropped)
 *   - checkPriors computes Chi–Geman m over recursive arities: a
 *     supercritical synthetic sort yields the advisory (rung-1 programs
 *     can't declare recursive members yet, so this is unit-level)
 *   - priors survive the precompile → loadPrecompiled round-trip
 */

import { describe, it, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import { checkPriors } from '../../lib/engine/priors.js';
import willConfig from '../../calculus/will/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-priors-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');

const write = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, `#import(${MEASURE})\n` + src);
  return f;
};
const load = (f) => mde.load(f, { calculusConfig: willConfig, cache: false });

describe('@w constructor priors (D5/M6)', () => {
  it('parses nat and fraction weights into calc.priors; stamps untouched', () => {
    const calc = load(write('ok.will', `
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t.
land: tile_t @w 1/2.
food: type.
rotten: type.
spoil: food@Q * after (Q + 2) -o { rotten }.
`));
    assert.deepEqual([...calc.priors].sort(), [['land', [1n, 2n]], ['sea', [2n, 1n]]]);
    assert.equal(calc.priorLint.length, 0);
    assert.ok(calc.forwardRules.some((r) => r.name === 'spoil'), 'timed rule loads beside @w');
  });

  it('@w on a non-member is a load error', () => {
    assert.throws(
      () => load(write('bad.will', `
foo: type.
bar: foo @w 2.
`)),
      /@w prior on a non-member/);
  });

  it('priors survive the precompile round-trip', () => {
    const src = write('cached.will', `
tile_t: sort.
sea: tile_t @w 3.
coast: tile_t.
`);
    const bin = path.join(tmp, 'cached.bin');
    mde.precompile(src, bin, { calculusConfig: willConfig });
    const calc = mde.loadPrecompiled(bin, { calculusConfig: willConfig });
    assert.deepEqual([...calc.priors], [['sea', [3n, 1n]]]);
  });
});

describe('Chi–Geman subcriticality (T2, M7 advisory)', () => {
  // Rung 1 forbids recursive members, so the supercritical case is
  // exercised at the unit level with a synthetic sort system — the
  // formula arms itself when P3 datasorts land.
  const sortSys = (members) => ({
    leastSortOfName: (n) => (n in members ? 'lst' : null),
    isClassifier: (c) => c === 'lst',
    membersOf: (c) => (c === 'lst' ? new Set(Object.keys(members)) : new Set()),
    subsort: () => false,
  });
  const atom = (n) => Store.put('atom', [n]);
  const arrow = (a, b) => Store.put('arrow', [a, b]);

  it('binary recursive constructor at 3:1 is supercritical (m = 1.5)', () => {
    const defs = new Map([
      ['leaf', atom('lst')],
      ['node', arrow(atom('lst'), arrow(atom('lst'), atom('lst')))],
    ]);
    const { errors, advice } = checkPriors(
      new Map([['node', [3n, 1n]], ['leaf', [1n, 1n]]]),
      sortSys({ leaf: 1, node: 1 }), defs);
    assert.equal(errors.length, 0);
    assert.equal(advice.length, 1);
    assert.equal(advice[0].kind, 'supercritical-prior');
    assert.ok(Math.abs(advice[0].m - 1.5) < 1e-9);
  });

  it('unary recursive constructor with terminating mass is subcritical', () => {
    const defs = new Map([
      ['nil', atom('lst')],
      ['cons', arrow(atom('lst'), atom('lst'))],
    ]);
    const { advice } = checkPriors(
      new Map([['cons', [17n, 2n]], ['nil', [3n, 2n]]]),   // m = 8.5/10 = 0.85
      sortSys({ nil: 1, cons: 1 }), defs);
    assert.equal(advice.length, 0);
  });
});

/**
 * Cross-program predicate/atom name collision (found 2026-09-01 via the
 * THY_0028 evidence pins; root-fixed in compile.js linearMeta.predTag +
 * the tag-aware group resolution).
 *
 * Store.TAG is GLOBAL: once any loaded program interns a name as a
 * predicate tag (unary+ declaration), a name-based group lookup routes
 * that name to the tag group forever — in every other program of the
 * same process. A program using the same name as a NULLARY atom then
 * had its facts filed in the atom group but its rules matched against
 * the (empty) tag group: an enabled rule silently never fired, in both
 * the timed and untimed engines. The fix dispatches on the PATTERN's
 * own compiled head tag (linearMeta.predTag; tryStateLookup and loli
 * triggers use the pattern hash directly), and presence pre-filters
 * (hasPredicate) take UNION semantics.
 *
 * The test loads the poisoning program FIRST (unary `probe`), then a
 * victim program with atom `probe`, and asserts the victim's rules fire
 * under exec, settle, and a persistent-goal state lookup.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../lib/engine/index.js';
import tillConfig from '../../calculus/till/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'pred-atom-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

const load = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: tillConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);

describe('cross-program predicate/atom name collision', () => {
  before(() => {
    // POISON: intern `probe` as a unary predicate tag, globally
    load('poison.till', `
thing: type.
x0: thing.
probe: (t: thing) -> type.
seen: type.
p1: probe X -o { seen }.
`);
    assert.ok(Store.TAG['probe'] >= Store.PRED_BOUNDARY, 'poison interned the tag');
  });

  it('a nullary `probe` atom still fires rules (timed settle)', () => {
    const calc = load('victim-settle.till', `
probe: type.
won: type.
r: probe -o { won }.
`);
    const res = calc.settle({ linear: { [atom('probe')]: 1 }, persistent: {} }, 0, { maxSteps: 10 });
    assert.ok(res.quiescent);
    const names = Object.keys(res.state.linear).map((k) => {
      let h = Number(k);
      if (Store.tag(h) === 'at') h = Store.child(h, 0);
      return Store.tag(h) === 'atom' ? Store.child(h, 0) : Store.tag(h);
    });
    assert.deepEqual(names, ['won'], `rule did not fire: state = ${names.join(',')}`);
  });

  it('a nullary `probe` atom still fires rules (untimed exec)', () => {
    const calc = load('victim-exec.ill', `
probe: type.
won: type.
r: probe -o { won }.
`);
    const res = calc.exec({ linear: { [atom('probe')]: 1 }, persistent: {} }, { maxSteps: 10 });
    const names = Object.keys(res.state.linear).map((k) => {
      const h = Number(k);
      return Store.tag(h) === 'atom' ? Store.child(h, 0) : Store.tag(h);
    });
    assert.deepEqual(names, ['won']);
  });

  it('a persistent `probe` atom is found by goal lookup', () => {
    const calc = load('victim-pers.ill', `
probe: type.
go: type.
won: type.
r: go * !probe -o { won }.
`);
    const res = calc.exec(
      { linear: { [atom('go')]: 1 }, persistent: { [atom('probe')]: 1 } },
      { maxSteps: 10 });
    const names = Object.keys(res.state.linear).map((k) => {
      const h = Number(k);
      return Store.tag(h) === 'atom' ? Store.child(h, 0) : Store.tag(h);
    });
    assert.deepEqual(names, ['won']);
  });
});

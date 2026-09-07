/**
 * Eager eigenvariable introduction (TODO_0307).
 *
 * A consequent-∃ goal has two lawful readings: compute the witness when it
 * is FORCED (inputs ground, resolution deterministic), or defer — fresh
 * eigenvariable + the goal as a flat constraint fact. There is no third
 * reading: an unforced goal must never be answered by pattern-matching an
 * arbitrary stored fact.
 *
 * The hazard these tests pin (b1588c6e regression): resolveEx freshened
 * unbound ∃-slots only AFTER attempting every goal, so a failed goal's
 * output was a BLANK PATTERN SLOT during later goals' resolution. A blank
 * matches anything — tier-1 state lookup answered `to256 C C'` with an
 * unrelated `to256(0,0)` fact, binding the symbolic sum to 0 and asserting
 * the unsatisfiable constraint `plus(x, K, 0)`. Downstream comparisons went
 * concrete and the 31-path multisig tree collapsed to 2 corrupted leaves.
 *
 * Fix: freshen a failed goal's ∃-outputs immediately. Evars are opaque
 * leaves — every tier then treats them correctly for free (lookup: no
 * match; FFI: not ground; clauses: no structural unify). Independent goals
 * (disjoint variables) still resolve — the fused-rule win of b1588c6e.
 */

import { describe, it, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { show } from '../../lib/engine/show.js';
import { getAllLeaves, countNodes } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'ex-eigen-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

// The repro imports bin.ill by relative path — write it next to a symlinked
// prelude so #import resolves against the real programs directory.
const PROGRAMS = path.join(import.meta.dirname, '../../calculus/ill/programs');
const load = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src.replace('#import(bin.ill)',
    `#import(${path.join(PROGRAMS, 'bin.ill')})`));
  return mde.load(f, { cache: false });
};

const leafFacts = (leaf, re) => {
  const o = toObject(leaf.state);
  return {
    linear: Object.keys(o.linear).map(Number).map(h => show(h)).filter(s => re.test(s)),
    persistent: Object.keys(o.persistent).map(Number).map(h => show(h)).filter(s => re.test(s)),
  };
};

describe('eager eigenvariable introduction (TODO_0307)', () => {
  it('a dependent chain goal never resolves against an unrelated stored fact', () => {
    // Seed to256(0,0) into the state, then run a symbolic add through the
    // plus/to256 chain — the exact hijack shape.
    const calc = load('repro.ill', `
#import(bin.ill)

start: type.
s2: type.
a: (x: bin) -> type.
b: (x: bin) -> type.
r: (x: bin) -> type.

seed: start -o { exists S. ( !to256 0x0 S * s2 ) }.
mk:   s2 * b X -o { exists V. ( !and X 0x80 V * a V ) }.
add3: a X -o { exists C. exists C'. ( !plus X 0x3 C * !to256 C C' * r C' ) }.

#symex [Q] start * b Q.
`);
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const tree = calc.explore(state, { maxDepth: 20, dangerouslyUseFFI: true });
    const leaves = getAllLeaves(tree);
    assert.equal(leaves.length, 1);
    const { linear, persistent } = leafFacts(leaves[0], /^(r\(|plus|to256)/);
    // r carries a symbolic result, never the hijacked 0
    assert.match(linear.find(s => s.startsWith('r(')), /^r\(evar\(\d+\)\)$/,
      `expected r(evar), got ${linear.join(', ')}`);
    // both chain constraints are deferred with evars; no unsatisfiable
    // plus(_, 0x3, 0x0) fact exists
    assert.ok(persistent.some(s => /^plus\(evar\(\d+\), 0x3, evar\(\d+\)\)$/.test(s)),
      `plus constraint not deferred: ${persistent.join(' ; ')}`);
    assert.ok(persistent.some(s => /^to256\(evar\(\d+\), evar\(\d+\)\)$/.test(s)),
      `to256 constraint not deferred: ${persistent.join(' ; ')}`);
    assert.ok(!persistent.some(s => /^plus\(.*0x0\)$/.test(s)),
      `unsatisfiable constraint asserted: ${persistent.join(' ; ')}`);
  });

  it('independent ∃-goals still resolve past an earlier failure (fused-rule win)', () => {
    const calc = load('indep.ill', `
#import(bin.ill)

start: type.
b: (x: bin) -> type.
r: (u: bin) -> (v: bin) -> type.

mk: b X -o { exists U. exists V. ( !plus X 0x1 U * !plus 0x2 0x3 V * r U V ) }.

#symex [Q] start * b Q.
`);
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const tree = calc.explore(state, { maxDepth: 20, dangerouslyUseFFI: true });
    const { linear } = leafFacts(getAllLeaves(tree)[0], /^r\(/);
    // U defers (symbolic input), V computes (ground, forced): r(evar, 0x5)
    assert.match(linear[0], /^r\(evar\(\d+\), 0x5\)$/,
      `expected r(evar, 0x5), got ${linear[0]}`);
  });
});

describe('mode equivalence — observation must not change semantics (TODO_0307)', () => {
  // The multisig symbolic tree is identical across every observation mode:
  // compiled fast path, evidence, hooks, FFI-off. 1987 nodes / 31 leaves
  // (the 31 feasible control-flow paths; forks only at jumpi).
  const PROGRAM = path.join(PROGRAMS, 'multisig_nocall_solc_symbolic.ill');
  const MODES = {
    fast: { maxDepth: 500, dangerouslyUseFFI: true },
    evidence: { maxDepth: 500, evidence: true, dangerouslyUseFFI: true },
    hooks: { maxDepth: 500, dangerouslyUseFFI: true, onProveSuccess: () => {} },
    'ffi-off': { maxDepth: 500 },
  };

  for (const [name, opts] of Object.entries(MODES)) {
    it(`${name}: 1987 nodes, 31 leaves`, () => {
      Store.clear();
      const calc = mde.load(PROGRAM, { cache: false });
      const state = mde.normalizeQuery(calc.queries.get('symex'));
      const tree = calc.explore(state, opts);
      assert.equal(countNodes(tree), 1987);
      assert.equal(getAllLeaves(tree).length, 31);
    });
  }
});

/**
 * D16 productivity lint — TODO_0265 Phase 5 (round-13 residue).
 *
 * Conservative load-time WARNING on zero-delay rule cycles: sound as a
 * warning (self-covering rules and token-non-decreasing pred cycles), NOT
 * complete (windows/depletion can break a flagged cycle — the runtime
 * Zeno guard stays). Precision pins: token-DECREASING programs (the duel),
 * positive-delay self-loops (productivity.ill), instant-feeding DAGs and
 * unknowable counts (!_W) must all stay QUIET.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { SPEC, FIX, GAME, loadTill as load } from './till-helpers.js';

describe('till D16 productivity lint', () => {
  it('flags a zero-delay self-cycle (till-zeno)', () => {
    const calc = load(FIX('till-zeno.ill'));
    assert.equal(calc.timedLint.length, 1);
    assert.deepEqual(calc.timedLint[0], { kind: 'self-cycle', rule: 'ping0' });
  });

  it('flags a two-rule zero-delay cycle via the pred graph', () => {
    const calc = load(FIX('till-cycle2.ill'));
    assert.equal(calc.timedLint.length, 1);
    assert.equal(calc.timedLint[0].kind, 'cycle');
    assert.deepEqual([...calc.timedLint[0].rules].sort(), ['r1', 'r2']);
  });

  it('stays quiet on token-decreasing races (the duel depletes)', () => {
    // fight consumes {rock, sci}, produces one of them — every alternative
    // is token-decreasing, so the "cycle" rock→rock terminates by depletion.
    assert.deepEqual(load(FIX('till-duel.ill')).timedLint, []);
  });

  it('stays quiet on winner-return duels (self-edges are tier 1 territory)', () => {
    // The combat duel returns the winner: 2-in/2-out per alternative (NOT
    // token-decreasing), but each alt strictly depletes the opposing side —
    // tier 1's pointwise-cover test correctly clears it, and tier 2 must not
    // re-flag it through the red→red self-edge (Phase 6 false positive).
    assert.deepEqual(load(FIX('till-duel-dyn.ill')).timedLint, []);
  });

  it('stays quiet on positive-delay self-loops (productive, D16)', () => {
    assert.deepEqual(load(SPEC('productivity.ill')).timedLint, []);
  });

  it('stays quiet on zero-delay DAGs and !_W cohort binds', () => {
    assert.deepEqual(load(FIX('till-instant-enable.ill')).timedLint, []);
    assert.deepEqual(load(FIX('till-instant-transfer.ill')).timedLint, []);
  });

  it('stays quiet on the spec programs (economy, schedule, spoilage, read, grades)', () => {
    for (const f of ['economy.ill', 'schedule.ill', 'spoilage.ill', 'read.ill', 'grades.ill']) {
      assert.deepEqual(load(SPEC(f)).timedLint, [], f);
    }
  });
});

describe('C1 chain-collapse advisory (timedAdvice)', () => {
  it('advises exactly the unconditional intermediates, vetoes the rest', () => {
    // till-chain.ill: bb and kk are collapsible; mm (guarded consumer),
    // ss (two consumers), vv (stamp-observed), ww (read arc), xx (!_W
    // bind), yy (loli-minted consumer) each trip one disqualifier.
    const calc = load(FIX('till-chain.ill'));
    const cc = calc.timedAdvice.filter(f => f.kind === 'chain-collapse');
    assert.deepEqual(cc.map(f => f.pred).sort(), ['bb', 'kk']);
    assert.deepEqual(calc.timedAdvice.find(f => f.pred === 'bb'),
      { kind: 'chain-collapse', pred: 'bb', producers: ['mk'], consumer: 'use' });
    assert.deepEqual(calc.timedAdvice.find(f => f.pred === 'kk'),
      { kind: 'chain-collapse', pred: 'kk', producers: ['mkk'], consumer: 'usek' });
  });

  it('is gated on a productivity-clean rule set (fix Zeno first)', () => {
    assert.deepEqual(load(FIX('till-cycle2.ill')).timedAdvice, []);
  });

  it('chain-collapse stays quiet on PP2 and the specs; C2/C3 speak honestly', () => {
    const pp2 = load(GAME('PP2.till')).timedAdvice;
    assert.deepEqual(pp2.filter(f => f.kind === 'chain-collapse'), []);
    // C2 (Hypothesis S): PP2's only !-conclusions are unlock MENUS — the
    // external-choice exemption keeps it silent (the corpus statement of
    // settle-optimality §1.3, machine-checked)
    assert.deepEqual(pp2.filter(f => f.kind === 'persistent-conclusion'), []);
    // C3 (whole-bind arrivals): the DOCUMENTED PP2 §3b starvation family —
    // !_W premises whose predicates keep arriving
    assert.deepEqual(
      pp2.filter(f => f.kind === 'whole-bind-arrivals')
        .map(f => `${f.rule}|${f.pred}`).sort(),
      ['kiln|wood', 'merge_space|space', 'spoil|food']);
    for (const f of ['economy.ill', 'schedule.ill', 'spoilage.ill', 'grades.ill']) {
      assert.deepEqual(load(SPEC(f)).timedAdvice.filter(x => x.kind === 'chain-collapse'), [], f);
    }
  });

  it('finds the real collapse in read.ill (eat_wood is an unconditional sink)', () => {
    // chop -o {wood}@4 feeds eat_wood: wood -o {eaten} — sole premise, no
    // window, no read of wood, stamp unobserved by any rule. The spec file
    // keeps the pair for its in-flight-atomicity gate; the advice is sound.
    assert.deepEqual(load(SPEC('read.ill')).timedAdvice,
      [{ kind: 'chain-collapse', pred: 'wood', producers: ['chop'], consumer: 'eat_wood' }]);
  });
});

describe('C2 Hypothesis-S + C3 whole-bind advisories (TODO_0293 b/c)', () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'till-lint-'));
  const mk = (name, src) => { const f = path.join(tmp, name); fs.writeFileSync(f, src); return f; };

  it('C2 flags a plain !-conclusion; external-choice menus are exempt', () => {
    const calc = load(mk('s.till', `
a: type.  b: type.  g: type.  m1: type.  m2: type.
learn: a -o { b * !g }@1.
menu: b -o { !(m1 & m2) }@1.
`));
    const c2 = calc.timedAdvice.filter(f => f.kind === 'persistent-conclusion');
    assert.deepEqual(c2, [{ kind: 'persistent-conclusion', rule: 'learn', via: 'conclusion', pred: 'g' }]);
  });

  it('C2 sees through minted possessed rules (loli with a !-conclusion)', () => {
    const calc = load(mk('s2.till', `
a: type.  b: type.  g: type.
mint: a -o { (b -o { !g }@1) }@1.
`));
    const c2 = calc.timedAdvice.filter(f => f.kind === 'persistent-conclusion');
    assert.deepEqual(c2, [{ kind: 'persistent-conclusion', rule: 'mint', via: 'minted loli', pred: 'g' }]);
  });

  it('C3 flags whole-bind with producers, quiet without', () => {
    const withProd = load(mk('w1.till', `
g: type.  w: bin -> type.  a: type.
farm: a -o { g }@1.
all: !_W g -o { w W }@1.
`));
    assert.deepEqual(withProd.timedAdvice.filter(f => f.kind === 'whole-bind-arrivals'),
      [{ kind: 'whole-bind-arrivals', rule: 'all', pred: 'g', producers: ['farm'] }]);
    const noProd = load(mk('w2.till', `
g: type.  w: bin -> type.
all: !_W g -o { w W }@1.
`));
    assert.deepEqual(noProd.timedAdvice.filter(f => f.kind === 'whole-bind-arrivals'), []);
  });
});

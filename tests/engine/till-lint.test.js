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
    assert.deepEqual(calc.timedAdvice.map(f => f.pred).sort(), ['bb', 'kk']);
    assert.deepEqual(calc.timedAdvice.find(f => f.pred === 'bb'),
      { kind: 'chain-collapse', pred: 'bb', producers: ['mk'], consumer: 'use' });
    assert.deepEqual(calc.timedAdvice.find(f => f.pred === 'kk'),
      { kind: 'chain-collapse', pred: 'kk', producers: ['mkk'], consumer: 'usek' });
  });

  it('is gated on a productivity-clean rule set (fix Zeno first)', () => {
    assert.deepEqual(load(FIX('till-cycle2.ill')).timedAdvice, []);
  });

  it('stays quiet on PP2 (every intermediate is building-guarded) and the specs', () => {
    assert.deepEqual(load(GAME('PP2.till')).timedAdvice, []);
    for (const f of ['economy.ill', 'schedule.ill', 'spoilage.ill', 'grades.ill']) {
      assert.deepEqual(load(SPEC(f)).timedAdvice, [], f);
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

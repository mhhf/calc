/**
 * Zone threading with a NON-default contextStructure (audit 2026-09-02).
 *
 * Every real calculus derives zone names identical to
 * DEFAULT_CONTEXT_STRUCTURE ('linear'/'cartesian'), so a hardcoded zone
 * key anywhere in lib/ passes all integration tests. These tests exercise
 * the two seams the audit flagged with synthetic zone names:
 *
 *   - bridge.sequentToState: consumableZone → state.linear,
 *     copySource → state.persistent (engine keys are STATE_ZONES constants)
 *   - generic.addDelta: reads AND writes the consumable zone
 *     (the write side was the one hardcoded-'linear' site the 0086
 *     sweep missed — regression pin)
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { sequentToState } from '../lib/prover/bridge.js';
import { createGenericProver } from '../lib/prover/generic.js';
import Seq from '../lib/kernel/sequent.js';
import Context from '../lib/prover/context.js';
import Store from '../lib/kernel/store.js';

const atom = (n) => Store.put('atom', [n]);

const CS = Object.freeze({
  zones: ['zk', 'zc'],
  properties: {
    zk: { exchange: true, contraction: false, weakening: false },
    zc: { exchange: true, contraction: true, weakening: true },
  },
  consumableZone: 'zk',
  copySource: 'zc',
  copyTarget: 'zk',
});

describe('sequentToState zone mapping', () => {
  it('maps a synthetic consumableZone/copySource onto state.linear/persistent', () => {
    const a = atom('zma'), b = atom('zmb'), c = atom('zmc');
    const seq = Seq.seq({ zk: [a, a], zc: [b] }, c);
    const state = sequentToState(seq, CS);
    assert.deepEqual(state.linear, { [a]: 2 });
    assert.deepEqual(state.persistent, { [b]: 1 });
  });

  it('defaults to DEFAULT_CONTEXT_STRUCTURE without a ctxStruct', () => {
    const a = atom('zma'), b = atom('zmb'), c = atom('zmc');
    const seq = Seq.fromArrays([a], [b], c);
    const state = sequentToState(seq);
    assert.deepEqual(state.linear, { [a]: 1 });
    assert.deepEqual(state.persistent, { [b]: 1 });
  });
});

describe('generic prover addDelta zone threading', () => {
  it('writes delta additions to the calculus consumable zone, not "linear"', () => {
    const prover = createGenericProver({ contextStructure: CS, rules: {} });
    const a = atom('zma'), b = atom('zmb'), c = atom('zmc');
    const seq = Seq.seq({ zk: [a], zc: [] }, c);
    const out = prover.addDelta(seq, Context.fromArray([b]));
    assert.deepEqual([...Seq.getContext(out, 'zk')].sort(), [a, b].sort(),
      'delta must land in the consumable zone');
    assert.equal(out.contexts.linear, undefined,
      'no spurious "linear" zone may appear');
  });

  it('is the identity on an empty delta', () => {
    const prover = createGenericProver({ contextStructure: CS, rules: {} });
    const a = atom('zma'), c = atom('zmc');
    const seq = Seq.seq({ zk: [a], zc: [] }, c);
    assert.equal(prover.addDelta(seq, Context.empty()), seq);
  });
});

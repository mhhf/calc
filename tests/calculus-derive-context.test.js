/**
 * deriveContextStructure unit tests (TODO_0086 follow-up, audit 2026-09-02).
 *
 * The derivation is otherwise MASKED in every integration test: the lnl
 * family derives a structure value-identical to DEFAULT_CONTEXT_STRUCTURE,
 * so a derivation bug that returns null (or even swaps the zones) would be
 * invisible behind the `|| DEFAULT_CONTEXT_STRUCTURE` fallback. These tests
 * pin the derived VALUES on the real spec and every loud-error branch on
 * synthetic specs.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import calculus, { deriveContextStructure } from '../lib/calculus/index.js';
import generator from '../lib/meta-parser/loader.js';
import Seq from '../lib/kernel/sequent.js';

const ILL_CALC = path.join(import.meta.dirname, '../calculus/ill/ill.calc');
const MINIMAL_PROP = path.join(import.meta.dirname, 'fixtures/minimal-prop.calc');

/** Synthetic spec: two zones with the given per-zone structural properties. */
function specWith(structural, positionModes = 'zoneA zoneB zoneB') {
  return {
    directives: { family: 'synthetic' },
    constructors: {
      seq: {
        annotations: { role: 'sequent', position_modes: positionModes },
        argTypes: ['structure', 'structure', 'structure'],
      },
    },
    structural,
  };
}

describe('deriveContextStructure', () => {
  it('derives the real values from the lnl chain (not the fallback)', () => {
    const spec = generator.loadChain(ILL_CALC);
    const cs = deriveContextStructure(spec);
    // Must be a real derivation, not null-then-fallback.
    assert.ok(cs, 'lnl spec must derive a context structure');
    assert.equal(cs.consumableZone, 'linear');
    assert.equal(cs.copySource, 'cartesian');
    assert.equal(cs.copyTarget, 'linear');
    assert.deepEqual(cs.zones, ['linear', 'cartesian']);
    assert.equal(cs.properties.linear.contraction, false);
    assert.equal(cs.properties.linear.exchange, true);
    assert.equal(cs.properties.cartesian.contraction, true);
    // And the loaded calculus carries exactly this derivation.
    calculus.clearCache();
    const ill = calculus.load(ILL_CALC);
    assert.deepEqual(ill.contextStructure, cs);
  });

  it('falls back to DEFAULT_CONTEXT_STRUCTURE for a bare calculus', () => {
    const spec = generator.loadChain(MINIMAL_PROP);
    assert.equal(deriveContextStructure(spec), null,
      'bare calculus declares no zone structure');
    calculus.clearCache();
    const prop = calculus.load(MINIMAL_PROP);
    assert.deepEqual(prop.contextStructure, Seq.DEFAULT_CONTEXT_STRUCTURE);
  });

  it('throws when no zone lacks contraction (no consumable zone)', () => {
    const spec = specWith([
      { name: 'a_contr', property: 'contraction', position: 1 },
      { name: 'b_contr', property: 'contraction', position: 2 },
    ]);
    assert.throws(() => deriveContextStructure(spec), /no consumable zone/);
  });

  it('throws when a second no-contraction zone has no wrapper constructor', () => {
    // TODO_0285: further no-contraction zones are AUX consumable zones;
    // membership is wrapper-routed, so a wrapperless aux zone is dead.
    const spec = specWith([
      { name: 'a_ex', property: 'exchange', position: 1 },
      { name: 'b_ex', property: 'exchange', position: 2 },
    ]);
    assert.throws(() => deriveContextStructure(spec), /no wrapper constructor/);
  });

  it('throws when an aux zone declares weakening (unsupported aux policy)', () => {
    const spec = specWith([
      { name: 'a_ex', property: 'exchange', position: 1 },
      { name: 'b_ex', property: 'exchange', position: 2 },
      { name: 'b_weak', property: 'weakening', position: 2 },
    ]);
    spec.constructors.wrap = {
      annotations: { category: 'zoneB' },
      argTypes: ['formula', 'formula'],
    };
    assert.throws(() => deriveContextStructure(spec), /declares weakening/);
  });

  it('derives an aux consumable zone with its wrapper (TODO_0285)', () => {
    // Three-zone family: cartesian-style zoneA, primary zoneB, aux zoneC
    // whose wrapper is the `wrap` connective (@category zoneC).
    const spec = specWith([
      { name: 'a_contr', property: 'contraction', position: 1 },
      { name: 'b_ex', property: 'exchange', position: 2 },
      { name: 'c_ex', property: 'exchange', position: 3 },
    ], 'zoneA zoneB zoneC zoneB');
    spec.constructors.wrap = {
      annotations: { category: 'zoneC' },
      argTypes: ['formula', 'formula'],
    };
    const cs = deriveContextStructure(spec);
    assert.equal(cs.consumableZone, 'zoneB',
      'primary consumable = FIRST no-contraction zone in position order');
    assert.deepEqual(cs.consumableZones, ['zoneB', 'zoneC']);
    assert.equal(cs.copySource, 'zoneA');
    assert.deepEqual(cs.wrapperZoneByTag, { wrap: 'zoneC' });
    assert.deepEqual(cs.zones, ['zoneB', 'zoneA', 'zoneC']);
  });

  it('throws when an aux zone name shadows a reserved @category', () => {
    // A zone named 'monad' would make its wrapper the computation
    // connective too (buildCalculus finds it by the same @category scan)
    // — spurious monad_r/monad_l injection on a wrapper. Fenced loudly.
    const spec = specWith([
      { name: 'a_contr', property: 'contraction', position: 1 },
      { name: 'b_ex', property: 'exchange', position: 2 },
      { name: 'c_ex', property: 'exchange', position: 3 },
    ], 'zoneA zoneB monad zoneB');
    spec.constructors.wrap = {
      annotations: { category: 'monad' },
      argTypes: ['formula', 'formula'],
    };
    assert.throws(() => deriveContextStructure(spec), /reserved @category/);
  });

  it('throws on a structural @position outside the context zones', () => {
    // Position 3 is the succedent slot; in lnl-style modes it shares the
    // consumable zone's NAME, so silently applying it would pollute that
    // zone's properties.
    const spec = specWith([
      { name: 'a_contr', property: 'contraction', position: 1 },
      { name: 'bad', property: 'weakening', position: 3 },
    ]);
    assert.throws(() => deriveContextStructure(spec), /does not index a context zone/);
  });

  it('derives a NON-default structure faithfully (zone names thread through)', () => {
    const cs = deriveContextStructure(specWith([
      { name: 'a_contr', property: 'contraction', position: 1 },
      { name: 'a_weak', property: 'weakening', position: 1 },
      { name: 'b_ex', property: 'exchange', position: 2 },
    ]));
    assert.equal(cs.consumableZone, 'zoneB');
    assert.equal(cs.copySource, 'zoneA');
    assert.equal(cs.copyTarget, 'zoneB');
    assert.deepEqual(cs.zones, ['zoneB', 'zoneA']);
    assert.deepEqual(cs.properties.zoneA,
      { exchange: false, contraction: true, weakening: true });
    assert.deepEqual(cs.properties.zoneB,
      { exchange: true, contraction: false, weakening: false });
  });
});

/**
 * sill sequent calculus — the located zone as calculus data (TODO_0285).
 *
 * sill declares a THIRD sequent zone (Γ ; Δ ; Λ ⊢ C) purely in
 * sill.calc: a 4-ary @role sequent constructor's @position_modes plus
 * per-position @structural rules. The engine derives the structure
 * (deriveContextStructure), routes membership by the zone's wrapper
 * connective (loc, @category located), and threads ONE union pool
 * through search and kernel — the pool plumbing is zone-count-agnostic,
 * so ADDING the zone took declarations alone (the 0285 P4 acceptance,
 * pinned here).
 *
 * Pins:
 *   - the derived contextStructure (zones, consumableZones, wrapper map)
 *   - wrapper routing at parse/premise boundaries (columns materialize)
 *   - per-fiber identity, cross-zone tensor splitting, per-fiber
 *     linearity (no cross-fiber unification, no silent weakening)
 *   - copy from the cartesian zone into the located column (routing)
 *   - every found derivation passes the L1 kernel checker CLEAN
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import { createManualProofAPI } from '../lib/prover/strategy/manual.js';
import { loadSillSequent } from '../calculus/sill/calculus-config.js';

describe('sill sequent calculus — located zone (TODO_0285)', () => {
  let calc, specs, alternatives, prover, kernel, cs;

  before(() => {
    calc = loadSillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
    cs = calc.contextStructure;
  });

  const atom = (n) => Store.put('atom', [n]);
  const loc = (f, p) => Store.put('loc', [f, atom(p)]);
  const tensor = (a, b) => Store.put('tensor', [a, b]);
  const loli = (a, b) => Store.put('loli', [a, b]);

  const prove = (consumables, succ, cart = []) => {
    const seq = Seq.seq(
      { ...Seq.routeContexts(cs, consumables), [cs.copySource]: cart },
      succ
    );
    return prover.prove(seq, { rules: specs, alternatives });
  };

  const proveVerified = (consumables, succ, cart = []) => {
    const r = prove(consumables, succ, cart);
    if (!r.success) return r;
    const v = kernel.verifyTree(r.proofTree);
    assert.ok(v.valid, `kernel: ${JSON.stringify(v.errors)}`);
    assert.ok(!v.unverified, `unverified: ${v.unverified}`);
    return r;
  };

  it('derives the three-zone structure from sill.calc alone', () => {
    assert.deepEqual(cs.zones, ['linear', 'cartesian', 'located']);
    assert.deepEqual(cs.consumableZones, ['linear', 'located']);
    assert.equal(cs.copySource, 'cartesian');
    assert.deepEqual(cs.wrapperZoneByTag, { loc: 'located' });
    assert.deepEqual(cs.properties.located,
      { exchange: true, contraction: false, weakening: false });
  });

  it('routes located formulas into the located column', () => {
    const contexts = Seq.routeContexts(cs, [atom('a'), loc(atom('crop'), 'l00')]);
    assert.deepEqual(contexts.linear, [atom('a')]);
    assert.deepEqual(contexts.located, [loc(atom('crop'), 'l00')]);
  });

  it('identity within a fiber', () => {
    const c = loc(atom('crop'), 'l00');
    assert.ok(proveVerified([c], c).success);
  });

  it('refutes cross-fiber identity (crop@@l00 |- crop@@l01)', () => {
    const r = prove([loc(atom('crop'), 'l00')], loc(atom('crop'), 'l01'));
    assert.ok(!r.success);
  });

  it('refutes leftover located resources (no silent weakening in Λ)', () => {
    const c = loc(atom('crop'), 'l00');
    const r = prove([c, c], c);
    assert.ok(!r.success);
  });

  it('tensor splits across zones (mixed linear + located)', () => {
    const c = loc(atom('crop'), 'l00');
    const g = loc(atom('gold'), 'l01');
    const a = atom('a');
    assert.ok(proveVerified([a, c, g], tensor(c, tensor(g, a))).success);
  });

  it('loli consumes a located hypothesis (dynamic-rule shape)', () => {
    const c = loc(atom('crop'), 'l00');
    const g = loc(atom('good'), 'l00');
    assert.ok(proveVerified([c, loli(c, g)], g).success);
  });

  it('copy routes a located formula from the cartesian zone', () => {
    const c = loc(atom('crop'), 'l00');
    assert.ok(proveVerified([], c, [c]).success);
  });

  it('premise columns materialize the located zone (routing, not CZ)', () => {
    const c = loc(atom('crop'), 'l00');
    const g = loc(atom('gold'), 'l01');
    const r = proveVerified([c, g], tensor(c, g));
    // Root conclusion carries both located facts in the located column.
    const root = r.proofTree.conclusion;
    assert.equal(Seq.getContext(root, 'located').length, 2);
    assert.equal(Seq.getContext(root, 'linear').length, 0);
  });

  it('with_r shares the located column across branches (Λ additive sharing)', () => {
    // Both branches consume the SAME located resource — provable.
    const c = loc(atom('crop'), 'l00');
    const withT = (a, b) => Store.put('with', [a, b]);
    assert.ok(proveVerified([c], withT(c, c)).success);
    // Branches cannot SPLIT located resources (each branch must consume
    // its full context; no weakening in Λ) — unprovable.
    const g = loc(atom('gold'), 'l01');
    assert.ok(!prove([c, g], withT(c, g)).success);
  });

  it('manual proof API premises keep the located column (routing, not CZ reads)', () => {
    // Pins the c623227f review fix: fullPremises reads the POOL and
    // rebuilds columns by routing — a CZ-only read drops located
    // formulas from the returned premise sequents.
    const manual = createManualProofAPI(calc);
    const c = loc(atom('crop'), 'l00');
    const withT = (a, b) => Store.put('with', [a, b]);
    const seq = Seq.seq(
      { ...Seq.routeContexts(cs, [c]), [cs.copySource]: [] },
      withT(c, c)
    );
    const state = manual.createProofState(seq);
    const actions = manual.getApplicableActions(state, { mode: 'unfocused' });
    const withR = actions.find((a) => a.name === 'with_r');
    assert.ok(withR, `with_r applicable (got: ${actions.map((a) => a.name).join(', ')})`);
    for (const p of withR.premises) {
      assert.equal(Seq.getContext(p, 'located').length, 1, 'located column survives');
      assert.equal(Seq.getContext(p, 'linear').length, 0);
    }
  });
});

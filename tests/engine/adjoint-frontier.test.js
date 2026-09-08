/**
 * The adjoint frontier, pinned (TODO_0309 P5, THY_0038).
 *
 * deriveContextStructure realizes a FRAGMENT of the mode-preorder
 * space (THY_0032's reframing): which mode structures derive today and
 * which are refused — loudly, by design — is the exact boundary the
 * adjoint bridge (big_next branch 2) would move. These pins make
 * THY_0038's frontier claims executable:
 *
 *   INSIDE:  LNL (C > L), single-mode (sax: L only, copySource null),
 *            multi-zone with linear-policy aux (sill: C > L, L_loc).
 *   OUTSIDE: an affine aux zone (weakening without contraction — the
 *            would-be A mode of U ≥ A ≥ L), and a second contraction
 *            zone (two cartesian-like modes). Both refuse loudly.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { deriveContextStructure } from '../../lib/calculus/index.js';

// Synthetic family specs (the derivation's actual input shape).
function spec(positionModes, structural, extraCtors = {}) {
  return {
    directives: { family: 'probe' },
    constructors: {
      seq: { annotations: { role: 'sequent', position_modes: positionModes } },
      ...extraCtors,
    },
    structural,
  };
}
const rule = (name, property, position) => ({ name, property, position });

describe('the adjoint frontier (TODO_0309 P5, THY_0038)', () => {
  it('INSIDE: LNL — the two-mode preorder C > L derives', () => {
    const cs = deriveContextStructure(spec('cartesian linear linear', [
      rule('c_x', 'exchange', 1), rule('c_c', 'contraction', 1), rule('c_w', 'weakening', 1),
      rule('l_x', 'exchange', 2),
    ]));
    assert.equal(cs.consumableZone, 'linear');
    assert.equal(cs.copySource, 'cartesian');
  });

  it('INSIDE: the single-mode instance — copySource null (the sax shape)', () => {
    const cs = deriveContextStructure(spec('linear linear', [
      rule('x', 'exchange', 1),
    ]));
    assert.equal(cs.consumableZone, 'linear');
    assert.equal(cs.copySource, null);
  });

  it('INSIDE: linear-policy aux zones — n consumable modes, wrapper-routed (the sill shape)', () => {
    const cs = deriveContextStructure(spec('cartesian linear located linear', [
      rule('c_c', 'contraction', 1), rule('c_w', 'weakening', 1),
      rule('l_x', 'exchange', 2), rule('loc_x', 'exchange', 3),
    ], {
      loc: { annotations: { category: 'located' } },
    }));
    assert.equal(cs.consumableZone, 'linear');
    assert.deepEqual(cs.consumableZones, ['linear', 'located']);
  });

  it('FRONTIER: an affine aux zone (weakening, no contraction) is refused loudly', () => {
    // The would-be middle mode of U ≥ A ≥ L: weakening-only. This is the
    // exact refusal an adjoint Stage A would lift — and note the engine
    // ALREADY hand-rolls affine discharge for one token class (will's
    // drawn_l2 ghost, "@affine ... weakening restricted to the token
    // class"): the mode exists in the wild, ad hoc.
    assert.throws(() => deriveContextStructure(spec('cartesian linear affine linear', [
      rule('c_c', 'contraction', 1), rule('c_w', 'weakening', 1),
      rule('l_x', 'exchange', 2),
      rule('a_x', 'exchange', 3), rule('a_w', 'weakening', 3),
    ], {
      affwrap: { annotations: { category: 'affine' } },
    })), /aux zone 'affine' declares weakening/);
  });

  it('FRONTIER: a second contraction zone (two cartesian-like modes) is refused loudly', () => {
    assert.throws(() => deriveContextStructure(spec('cartesian valid linear linear', [
      rule('c_c', 'contraction', 1), rule('c_w', 'weakening', 1),
      rule('v_c', 'contraction', 2), rule('v_w', 'weakening', 2),
      rule('l_x', 'exchange', 3),
    ])), /at most one copy source/);
  });
});

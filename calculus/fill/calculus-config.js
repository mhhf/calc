/**
 * fill Calculus Configuration — single assembly point.
 *
 * fill = ILL + μ/ν fixed points (fill.calc @extends ill). This config
 * COMPOSES ILL's config: every ILL-specific layer (family, init, theories,
 * backward, FFI, compose, EVM domain) is REFERENCED, never copied — fill
 * inherits ILL's whole machinery and adds only the fixpoint surface. The two
 * fill-OWN overrides:
 *   - connectives: derived from fill.calc's @extends-ill chain (ILL's table +
 *     mu/nu). The @category fixpoint declarations are what arm the generic
 *     cyclic-proof engine via deriveRoles() → roles.lfp/roles.gfp.
 *   - loader.buildParser: fill's forward parser (ILL's + the μ/ν binders).
 *   - compile.cacheEpoch: 'fill' — compiled rules must not collide with ILL's.
 *
 * illConfig is referenced field-by-field (NOT spread): its `connectives`
 * getter calls calculus.load(ill.calc), which side-effect-allocates Store
 * atoms and must not run at fill's import time (Store bit-identity — see
 * connectives.js). Only the lazy getters below trigger it, on first use.
 */

'use strict';

import path from 'path';
import illConfig from '../ill/calculus-config.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { makeCalcTables } from '../kit.js';
import { grade0 } from '../../lib/engine/grades.js';
import { buildForwardParser as buildFillForwardParser } from './lib/forward-parser.js';

const FILL_CALC = path.join(import.meta.dirname, 'fill.calc');

// Connective table from fill.calc's OWN chain (= ILL's surface via @extends
// ill, plus mu/nu). Same derivation as ILL's illConnectives() — @category +
// @polarity annotations — resolved over the merged chain. Lazy + memoized.
const { connectives: fillConnectives } = makeCalcTables(FILL_CALC, {});

const fillCalculusConfig = {
  // ── Structural family: LNL — inherited from ILL (via @extends lnl) ──
  family: illConfig.family,

  // ── L0: Kernel Init — shared with ILL (same atoms + theories) ──
  init: illConfig.init,

  // ── L1: Structural ── fill-OWN table (ILL + mu/nu) ──
  get connectives() { return fillConnectives(); },
  typeCheck: illConfig.typeCheck,
  wellModed: illConfig.wellModed,
  theories: illConfig.theories,
  gradeUnit: illConfig.gradeUnit,

  // ── L2: Loader ── fill-OWN parser (ILL's + μ/ν binders) ──
  loader: {
    buildParser: buildFillForwardParser,
    get connTags() {
      if (!this._ct) this._ct = connTagsFrom(fillConnectives());
      return this._ct;
    },
    grade0,
    timed: false,
  },

  // ── L2: Compile ── shared with ILL, own cache epoch ──
  compile: { ...illConfig.compile, cacheEpoch: 'fill' },

  // ── L3: Backward ── shared with ILL ──
  backward: illConfig.backward,

  // ── L4: FFI ── shared with ILL ──
  ffi: illConfig.ffi,

  // ── L5: Compose ── shared with ILL ──
  compose: illConfig.compose,

  // ── L6: Domain (EVM) ── shared with ILL ──
  domain: illConfig.domain,
};

export { fillCalculusConfig, fillConnectives };
export default fillCalculusConfig;

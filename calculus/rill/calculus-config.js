/**
 * rill Calculus Configuration — single assembly point.
 *
 * rill = fill + ○ (rill.calc @extends fill). This config COMPOSES fill's config:
 * every fill/ILL layer (family, init, theories, backward, FFI, compose, EVM
 * domain) is REFERENCED, never copied — rill inherits the whole μMALL machinery
 * and adds only the ○ surface. The two rill-OWN overrides:
 *   - connectives: derived from rill.calc's @extends-fill chain (ILL + mu/nu + ○).
 *   - loader.buildParser: rill's forward parser (fill's + the ○ prefix operator).
 *   - compile.cacheEpoch: 'rill' — compiled rules must not collide with fill's.
 *
 * fillConfig is referenced field-by-field (NOT spread): its `connectives` getter
 * loads a .calc chain that side-effect-allocates Store atoms and must not run at
 * rill's import time (Store bit-identity). Only the lazy getters below trigger it.
 */

'use strict';

import path from 'path';
import fillConfig from '../fill/calculus-config.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { makeCalcTables } from '../kit.js';
import { grade0 } from '../../lib/engine/grades.js';
import { buildForwardParser as buildRillForwardParser } from './lib/forward-parser.js';

const RILL_CALC = path.join(import.meta.dirname, 'rill.calc');

// Connective table from rill.calc's OWN chain (= fill's surface via @extends
// fill, plus circle). Same derivation as fill's — @category + @polarity
// annotations resolved over the merged chain. Lazy + memoized.
const { connectives: rillConnectives } = makeCalcTables(RILL_CALC, {});

const rillCalculusConfig = {
  // ── Structural family: LNL — inherited from fill/ILL (via @extends lnl) ──
  family: fillConfig.family,

  // ── L0: Kernel Init — shared with fill/ILL (same atoms + theories) ──
  init: fillConfig.init,

  // ── L1: Structural ── rill-OWN table (ILL + mu/nu + ○) ──
  get connectives() { return rillConnectives(); },
  typeCheck: fillConfig.typeCheck,
  wellModed: fillConfig.wellModed,
  theories: fillConfig.theories,
  gradeUnit: fillConfig.gradeUnit,

  // ── L2: Loader ── rill-OWN parser (fill's + the ○ prefix operator) ──
  loader: {
    buildParser: buildRillForwardParser,
    get connTags() {
      if (!this._ct) this._ct = connTagsFrom(rillConnectives());
      return this._ct;
    },
    grade0,
    timed: false,
  },

  // ── L2: Compile ── shared with fill, own cache epoch ──
  compile: { ...fillConfig.compile, cacheEpoch: 'rill' },

  // ── L3: Backward ── shared with fill/ILL ──
  backward: fillConfig.backward,

  // ── L4: FFI ── shared with fill/ILL ──
  ffi: fillConfig.ffi,

  // ── L5: Compose ── shared with fill/ILL ──
  compose: fillConfig.compose,

  // ── L6: Domain (EVM) ── shared with fill/ILL ──
  domain: fillConfig.domain,
};

export { rillCalculusConfig, rillConnectives };
export default rillCalculusConfig;

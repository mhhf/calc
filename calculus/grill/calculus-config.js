/**
 * grill Calculus Configuration — graded μMALL (gill + μ/ν).
 *
 * grill COMPOSES gill's config: every gill/till/ILL layer (family, init,
 * theories, grades, grade registry, backward, FFI, timing) is REFERENCED, never
 * copied — grill inherits gill's whole graded machinery and adds only the μ/ν
 * fixpoint surface. The grill-OWN overrides:
 *   - connectives / sorts: derived from grill.calc's @extends-gill chain (gill's
 *     graded surface + mu/nu). @category fixpoint arms deriveRoles' lfp/gfp.
 *   - loader.buildParser + loadGrillSequent: gill's parser plus the μ/ν binders.
 *   - compile.cacheEpoch: 'grill' — compiled rules must not collide with gill's.
 *
 * gillCalculusConfig is referenced field-by-field (NOT spread): its `connectives`
 * / `sorts` getters load a .calc chain that side-effect-allocates Store atoms and
 * must not run at grill's import time. Only the lazy getters below trigger it.
 */

'use strict';

import path from 'path';
import gillConfig, { gillFences, gillFFIFace } from '../gill/calculus-config.js';
import { tillGradeUnit } from '../till/calculus-config.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { grade0 } from '../../lib/engine/grades.js';
import { makeCalcTables, makeForwardParserBuilder, makeSequentLoader, makeTheory } from '../kit.js';

const GRILL_CALC = path.join(import.meta.dirname, 'grill.calc');
const GILL_RULES = path.join(import.meta.dirname, '../gill/gill.rules');
const GRILL_RULES = path.join(import.meta.dirname, 'grill.rules');
const GILL_PRELUDE = path.join(import.meta.dirname, '../gill/prelude/num.gill');

// NOTE ON BINDERS: mu/nu are de-Bruijn PREFIX binders (`mu A`, `nu A` — the body
// is the whole argument, like fill's). The sequent-rules parser AUTO-DERIVES them
// from @category fixpoint (arity-1 formula→formula), so loadGrillSequent must NOT
// pass an explicit `binders` map — an explicit {mu,nu} makes the rules parser
// expect the quantifier form `mu X. body` and reject `mu A` (a real trap; the
// forward parser, parserFromTables, treats explicit {mu,nu} correctly, but the
// sequent-rules parser does not — the two parser paths diverge here).

// Connective + sort tables from grill.calc's OWN chain (gill's graded surface
// via @extends gill, plus mu/nu). Same fences as gill (grade value checks).
const { connectives: grillConnectives, sorts: grillSorts } =
  makeCalcTables(GRILL_CALC, { fences: gillFences });

// The FORWARD / query parser DOES take explicit {mu,nu} binders (parserFromTables
// reads the named-binder form `nu X. body` and de-Bruijn-encodes it, matching the
// rules' auto-derived `nu A`). This is the fill pattern for its forward parser.
const grillBuildParser = makeForwardParserBuilder(GRILL_CALC, tillGradeUnit,
  { binders: { exists: 'exists', forall: 'forall', mu: 'mu', nu: 'nu' } });

const grillCalculusConfig = {
  // ── Structural family + kernel init — shared with gill/till/ILL ──
  family: gillConfig.family,
  init: gillConfig.init,

  // ── L1: Structural ── grill-OWN table (gill's graded surface + mu/nu) ──
  get connectives() { return grillConnectives(); },
  typeCheck: gillConfig.typeCheck,
  theories: gillConfig.theories,
  gradeUnit: gillConfig.gradeUnit,
  get sorts() { return grillSorts(); },

  // ── Grade algebras — shared with gill (grill inherits the grade sorts) ──
  grades: gillConfig.grades,
  gradeRegistry: gillConfig.gradeRegistry,
  gradeAlgebraFor: gillConfig.gradeAlgebraFor,
  factSetPolicy: gillConfig.factSetPolicy,
  stampTag: gillConfig.stampTag,
  shiftOps: gillConfig.shiftOps,
  scheduler: gillConfig.scheduler,

  // ── L2: Compile ── shared with gill, own cache epoch ──
  compile: { ...gillConfig.compile, cacheEpoch: 'grill' },

  // ── L3/L4: Backward + FFI — shared with gill ──
  backward: gillConfig.backward,
  ffi: gillConfig.ffi,

  // ── L6: Domain — shared with gill ──
  domain: gillConfig.domain,

  // ── Loader ── grill-OWN parser (gill's + μ/ν binders) ──
  loader: {
    ...gillConfig.loader,
    buildParser: grillBuildParser,
    get connTags() {
      if (!this._ct) this._ct = connTagsFrom(grillConnectives());
      return this._ct;
    },
    grade0,
  },
};

// grill's OWN theory engine (numeric premises resolve over gill's num.gill).
// It must bind grill's config, NOT gill's: makeTheory loads the prelude with
// getConfig()'s parser, and gill's parser lacks the μ/ν binders, so a
// gill-bound theory chokes when the loader re-checks grill's mu/nu rules.
const grillTheory = makeTheory({
  preludeFile: GILL_PRELUDE,
  META: gillFFIFace.META,
  getConfig: () => grillCalculusConfig,
});

/** Sequent-level grill calculus: grill.calc + [gill.rules, grill.rules] with
 *  grill's theory engine (numeric premises resolve over prelude/num.gill) and the
 *  μ/ν binders. The four fixpoint rules are grade-agnostic; gill's graded rules
 *  handle the modalities inside the unfolded body. */
const loadGrillSequent = makeSequentLoader({
  calcFile: GRILL_CALC,
  rulesFile: [GILL_RULES, GRILL_RULES],
  gradeUnit: tillGradeUnit,
  theory: grillTheory,
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub' },
  // no `parser.binders`: mu/nu auto-derive from @category fixpoint (see above).
});

export { grillCalculusConfig, grillConnectives, loadGrillSequent };
export default grillCalculusConfig;

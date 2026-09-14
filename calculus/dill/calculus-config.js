/**
 * dill Calculus Configuration — governance ILL (gill + principal possession).
 *
 * dill COMPOSES gill's config field-by-field (the grill/trill pattern): every
 * gill/till/ILL layer — family, init, theories, grades, grade registry,
 * backward, FFI, timing — is REFERENCED, never copied. dill adds only the
 * principal-indexed possession modality `poss` ([K] A). The dill-OWN overrides:
 *   - connectives / sorts: from dill.calc's @extends-gill chain (gill's graded
 *     surface + poss).
 *   - loader.buildParser + loadDillSequent: gill's parser; rules = [gill.rules,
 *     dill.rules] (gill's fragment by reference + the two poss rules).
 *   - compile.cacheEpoch: 'dill' — compiled rules must not collide with gill's.
 *
 * No new grade algebra is registered: poss's index rides gill's `count` sort
 * (a numeric identity tag), and no-cross-principal-collapse is enforced by the
 * poss_l index unification, not by a grade operation — so the partial-⊕ stays
 * calculus-local and touches no shared engine code for backward cut. See
 * THY_0045/THY_0046 and calculus/dill/dill.{calc,rules}.
 */

'use strict';

import path from 'path';
import gillConfig, { gillFences, gillFFIFace } from '../gill/calculus-config.js';
import { tillGradeUnit } from '../till/calculus-config.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { grade0 } from '../../lib/engine/grades.js';
import { makeCalcTables, makeForwardParserBuilder, makeSequentLoader, makeTheory } from '../kit.js';

const DILL_CALC = path.join(import.meta.dirname, 'dill.calc');
const GILL_RULES = path.join(import.meta.dirname, '../gill/gill.rules');
const DILL_RULES = path.join(import.meta.dirname, 'dill.rules');
const GILL_PRELUDE = path.join(import.meta.dirname, '../gill/prelude/num.gill');

// Connective + sort tables from dill.calc's OWN chain (gill's graded surface via
// @extends gill, plus poss). Same fences as gill (grade value checks).
const { connectives: dillConnectives, sorts: dillSorts } =
  makeCalcTables(DILL_CALC, { fences: gillFences });

const dillBuildParser = makeForwardParserBuilder(DILL_CALC, tillGradeUnit);

const dillCalculusConfig = {
  // ── Structural family + kernel init — shared with gill/till/ILL ──
  family: gillConfig.family,
  init: gillConfig.init,

  // ── L1: Structural ── dill-OWN table (gill's graded surface + poss) ──
  get connectives() { return dillConnectives(); },
  typeCheck: gillConfig.typeCheck,
  theories: gillConfig.theories,
  gradeUnit: gillConfig.gradeUnit,
  get sorts() { return dillSorts(); },

  // ── Grade algebras — shared with gill (poss rides the `count` sort) ──
  grades: gillConfig.grades,
  gradeRegistry: gillConfig.gradeRegistry,
  gradeAlgebraFor: gillConfig.gradeAlgebraFor,
  factSetPolicy: gillConfig.factSetPolicy,
  stampTag: gillConfig.stampTag,
  shiftOps: gillConfig.shiftOps,
  scheduler: gillConfig.scheduler,

  // ── L2: Compile ── shared with gill, own cache epoch ──
  compile: { ...gillConfig.compile, cacheEpoch: 'dill' },

  // ── L3/L4: Backward + FFI — shared with gill ──
  backward: gillConfig.backward,
  ffi: gillConfig.ffi,

  // ── L6: Domain — shared with gill ──
  domain: gillConfig.domain,

  // ── Loader ── dill-OWN parser (gill's surface + poss) ──
  loader: {
    ...gillConfig.loader,
    buildParser: dillBuildParser,
    get connTags() {
      if (!this._ct) this._ct = connTagsFrom(dillConnectives());
      return this._ct;
    },
    grade0,
  },
};

// dill's OWN theory engine (numeric premises of the inherited gill rules resolve
// over gill's num.gill). Binds dill's config (makeTheory loads the prelude with
// getConfig()'s parser) — the grill pattern.
const dillTheory = makeTheory({
  preludeFile: GILL_PRELUDE,
  META: gillFFIFace.META,
  getConfig: () => dillCalculusConfig,
});

/** Sequent-level dill calculus: dill.calc + [gill.rules, dill.rules] with dill's
 *  theory engine. poss carries no theory premise; gill's graded rules discharge
 *  the numeric premises of the inherited fragment. */
const loadDillSequent = makeSequentLoader({
  calcFile: DILL_CALC,
  rulesFile: [GILL_RULES, DILL_RULES],
  gradeUnit: tillGradeUnit,
  theory: dillTheory,
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub' },
});

export { dillCalculusConfig, dillConnectives, loadDillSequent };
export default dillCalculusConfig;

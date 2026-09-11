/**
 * trill Calculus Configuration — graded reactive μMALL (grill + ○).
 *
 * trill = grill + the ○ next-time modality (trill.calc @extends grill). It is to
 * grill exactly what rill is to fill: the ○ fork. This config COMPOSES gill's
 * config field-by-field (the same base grill composes: family, init, theories,
 * grades, grade registry, backward, FFI, timing are REFERENCED, never copied) and
 * adds only the ○ surface on top of grill's graded-fixpoint surface. trill-OWN:
 *   - connectives / sorts: from trill.calc's @extends-grill chain (gill's graded
 *     surface + μ/ν + ○). @category fixpoint arms lfp/gfp; @category modality (○)
 *     gets NO role; grade sorts inherited — all three axes coexist as data.
 *   - loader.buildParser + loadTrillSequent: grill's parser (μ/ν binders + grades)
 *     plus the ○ prefix operator (auto-derived from trill.calc's @ascii "O #1").
 *   - compile.cacheEpoch: 'trill' — compiled rules must not collide with grill's.
 *
 * The ○ tick rule is grade- AND fixpoint-agnostic (the generic @tick machinery):
 * no engine change, the axes simply compose.
 */

'use strict';

import path from 'path';
import gillConfig, { gillFences, gillFFIFace } from '../gill/calculus-config.js';
import { tillGradeUnit } from '../till/calculus-config.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { grade0 } from '../../lib/engine/grades.js';
import { makeCalcTables, makeForwardParserBuilder, makeSequentLoader, makeTheory } from '../kit.js';

const TRILL_CALC = path.join(import.meta.dirname, 'trill.calc');
const GILL_RULES = path.join(import.meta.dirname, '../gill/gill.rules');
const GRILL_RULES = path.join(import.meta.dirname, '../grill/grill.rules');
const TRILL_RULES = path.join(import.meta.dirname, 'trill.rules');
const GILL_PRELUDE = path.join(import.meta.dirname, '../gill/prelude/num.gill');

// BINDERS: as in grill, mu/nu auto-derive from @category fixpoint in the SEQUENT
// rules parser, so loadTrillSequent must NOT pass an explicit `binders` map
// (explicit {mu,nu} makes the rules parser expect `mu X. body` and reject `mu A`).
// The FORWARD/query parser DOES take {mu,nu} (parserFromTables reads `nu X. body`).
// ○ is NOT a binder — its prefix operator auto-derives from the constructor table.

const { connectives: trillConnectives, sorts: trillSorts } =
  makeCalcTables(TRILL_CALC, { fences: gillFences });

const trillBuildParser = makeForwardParserBuilder(TRILL_CALC, tillGradeUnit,
  { binders: { exists: 'exists', forall: 'forall', mu: 'mu', nu: 'nu' } });

const trillCalculusConfig = {
  // ── Structural family + kernel init — shared with grill/gill/till/ILL ──
  family: gillConfig.family,
  init: gillConfig.init,

  // ── L1: Structural ── trill-OWN table (gill's graded surface + μ/ν + ○) ──
  get connectives() { return trillConnectives(); },
  typeCheck: gillConfig.typeCheck,
  theories: gillConfig.theories,
  gradeUnit: gillConfig.gradeUnit,
  get sorts() { return trillSorts(); },

  // ── Grade algebras — shared with gill/grill ──
  grades: gillConfig.grades,
  gradeRegistry: gillConfig.gradeRegistry,
  gradeAlgebraFor: gillConfig.gradeAlgebraFor,
  factSetPolicy: gillConfig.factSetPolicy,
  stampTag: gillConfig.stampTag,
  shiftOps: gillConfig.shiftOps,
  scheduler: gillConfig.scheduler,

  // ── L2: Compile ── shared with gill, own cache epoch ──
  compile: { ...gillConfig.compile, cacheEpoch: 'trill' },

  // ── L3/L4: Backward + FFI — shared with gill ──
  backward: gillConfig.backward,
  ffi: gillConfig.ffi,

  // ── L6: Domain — shared with gill ──
  domain: gillConfig.domain,

  // ── Loader ── trill-OWN parser (grill's μ/ν + grades, plus the ○ prefix) ──
  loader: {
    ...gillConfig.loader,
    buildParser: trillBuildParser,
    get connTags() {
      if (!this._ct) this._ct = connTagsFrom(trillConnectives());
      return this._ct;
    },
    grade0,
  },
};

// trill's OWN theory engine — must bind trill's config (its parser has the μ/ν
// binders AND the ○ operator; a gill/grill-bound theory would choke re-checking
// trill's rules). Same pattern as grill's theory.
const trillTheory = makeTheory({
  preludeFile: GILL_PRELUDE,
  META: gillFFIFace.META,
  getConfig: () => trillCalculusConfig,
});

/** Sequent-level trill calculus: trill.calc + [gill.rules, grill.rules, trill.rules]
 *  with trill's theory engine and the μ/ν binders. The ○ tick rule is grade- and
 *  fixpoint-agnostic; gill's graded rules and grill's unfold rules handle the body. */
const loadTrillSequent = makeSequentLoader({
  calcFile: TRILL_CALC,
  rulesFile: [GILL_RULES, GRILL_RULES, TRILL_RULES],
  gradeUnit: tillGradeUnit,
  theory: trillTheory,
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub' },
  // no `parser.binders`: mu/nu auto-derive from @category fixpoint (see above).
});

export { trillCalculusConfig, trillConnectives, loadTrillSequent };
export default trillCalculusConfig;

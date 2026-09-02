/**
 * will Calculus Configuration — single assembly point (TODO_0292/0297 P0).
 *
 * Weighted ILL: the measure-class calculus. will's surface IS gill's
 * (will.calc @extends gill — the first cross-calculus @extends chain;
 * loadChain merges the constructor/sort-edge tables), so this config
 * COMPOSES gill's exported layer pieces (M2: data extends data in .calc,
 * config composes config here — the altitude at which gill composes
 * till's) and derives its own tables from will.calc, one source of truth
 * per calculus. Shared layers are REFERENCED (init, backward, ffi,
 * domain, the FFI face, the fences, the by-sort grade registry), never
 * copied; will-own layers are written out — no blind spread (the config
 * literal is the visible layer table, 0284 M10).
 *
 * Will-OWN semantics arrive with the later phases: @w constructor priors
 * and the entropy chooser (P1), the wave table + decimation driver (P2),
 * the ∃_ρ graded existential (P3). At P0 the active scheduling axis stays
 * TIME (D1 — one algebra schedules a run): the measure axis is an
 * execution MODE over whole derivations, never a stamp scheduler —
 * buildTimedConfig rejects weightGrades loudly (0284 P1b), and the
 * decimation driver, not the settle loop, will realize sum/sample.
 */

'use strict';

import path from 'path';
import { grade0 } from '../../lib/engine/grades.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { tillGrades, tillFactSetPolicy, tillGradeUnit } from '../till/calculus-config.js';
import { gillCalculusConfig, gillGradeRegistry, gillFences, gillFFIFace } from '../gill/calculus-config.js';
import { makeCalcTables, makeTheory, makeForwardParserBuilder, makeSequentLoader } from '../kit.js';
import datasortMass from './lib/datasort-mass.js';
import { DECIMATE_PREDS } from '../../lib/engine/decimate.js';

const WILL_CALC = path.join(import.meta.dirname, 'will.calc');
const WILL_PRELUDE = path.join(import.meta.dirname, 'prelude/measure.will');
// The backward fragment is inherited BY REFERENCE: .rules files have no
// @extends mechanism, so calculus.load takes the LIST [gill.rules,
// will.rules] — gill's fragment verbatim plus the will-own ∃_ρ rules
// (drawn_l/drawn_l2/superpose_l/draw — TODO_0298 item 1, THY_0027).
const GILL_RULES = path.join(import.meta.dirname, '../gill/gill.rules');
const WILL_RULES = path.join(import.meta.dirname, 'will.rules');

// Tables derived from will.calc's OWN chain (= gill's surface via
// @extends); the literal fences are gill's, referenced (weight stays
// [0,1] — D5: unnormalized masses are @w priors, not weight literals).
const { connectives: willConnectives, sorts: willSorts } = makeCalcTables(WILL_CALC, {
  fences: gillFences,
});

/** Grade-algebra routing over will's sort tables and gill's registry
 *  (woplus: weight → weightGrades, monad: delay → time, haul: dist). */
function gradeAlgebraFor(conn) {
  const argSorts = willSorts().connArgSorts[conn];
  const gs = argSorts && argSorts.find((s) => s !== 'formula');
  return (gs && gillGradeRegistry.bySort[gs]) || gillGradeRegistry.default;
}

// Theory engine over will's prelude chain (measure.will → num.gill → rat.ill
// → bin.ill — min/max, q-ops, and the sorts machinery all resolve there).
const willTheory = makeTheory({
  preludeFile: WILL_PRELUDE,
  META: gillFFIFace.META,
  getConfig: () => willCalculusConfig,
});

// binderSorts: the ∃_ρ sorted binder (`exists X: s @w. A`) — will-only
// grammar opt-in (M1); till/gill parsers are untouched.
const willBuildParser = makeForwardParserBuilder(WILL_CALC, tillGradeUnit, { binderSorts: true });

const willCalculusConfig = {
  // ── Structural family: LNL (via gill's layer table) ──────────
  family: gillCalculusConfig.family,

  // ── L0: Kernel init — shared with gill (same Store tags + theories) ──
  init: gillCalculusConfig.init,

  // ── L1: Structural ───────────────────────────────────────────
  get connectives() { return willConnectives(); },
  typeCheck: 'strict',
  theories: gillCalculusConfig.theories,
  gradeUnit: tillGradeUnit,
  get sorts() { return willSorts(); },

  // Active axis = time (D1); the registry routes per-connective reading.
  grades: tillGrades,
  gradeRegistry: gillGradeRegistry,
  gradeAlgebraFor,
  // will-own (fence B): the inside-mass solver for recursive datasorts —
  // oracle machinery bound HERE, not in the core (the driver reaches it
  // through the calc; calculi without the binding structurally lack the
  // concept, and recursive datasorts under them are a load error).
  datasortMasses: datasortMass,
  // C2/Hypothesis-S lint exemption: bias facts are the decimation
  // driver's machinery — persistent conclusions are their purpose.
  lintExempt: [DECIMATE_PREDS.BIAS],
  factSetPolicy: tillFactSetPolicy,
  stampTag: 'at',
  shiftOps: gillCalculusConfig.shiftOps,
  // will-own default (M5/D6): the least-entropy tie policy — H=0 rules
  // (propagation, forced moves) before weighted draws, tighter draws
  // before wider (WFC decimation order). Semantics-free tuning: any
  // chooser reaches the same outcome set; per-run override via settle
  // opts.chooser.
  scheduler: { chooser: 'entropy', seed: 0, cohort: 'fifo' },

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    getModes: gillFFIFace.getModes,
    getModeMeta: gillFFIFace.getModeMeta,
    discriminatorPreds: [],
    cacheEpoch: 'will',
  },

  // ── L3: Backward — shared with gill (same META, same normalizer) ──
  backward: gillCalculusConfig.backward,

  // ── L4: FFI — shared with gill ───────────────────────────────
  ffi: gillCalculusConfig.ffi,

  // ── L5: Compose ── deliberately absent (till discipline) ─────

  // ── L6: Domain — shared with gill ────────────────────────────
  domain: gillCalculusConfig.domain,

  // ── Loader (convert.js) ──────────────────────────────────────
  loader: {
    buildParser: willBuildParser,
    get connTags() { return connTagsFrom(willConnectives()); },
    grade0,
    timed: true,
    qexprPreds: gillCalculusConfig.loader.qexprPreds,
  },
};

/** Sequent-level will calculus: will.calc + the inherited backward
 *  fragment + the ∃_ρ rules, with will's theory engine, the shared
 *  @fire wiring (delay/dist stamp axes — the additive ⊕/⊖ residual
 *  shape), and the @draw checker (TODO_0298 item 1b). The parser gains
 *  binders: the ∃_ρ rule patterns match binder bodies (`exists X. A`). */
const loadWillSequent = makeSequentLoader({
  calcFile: WILL_CALC, rulesFile: [GILL_RULES, WILL_RULES],
  gradeUnit: tillGradeUnit, theory: willTheory,
  parser: { binders: { exists: 'exists', forall: 'forall' } },
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub' },
  draw: { stampTag: 'at' },
});

export { willCalculusConfig, willConnectives, willTheory, loadWillSequent, gradeAlgebraFor };
export default willCalculusConfig;

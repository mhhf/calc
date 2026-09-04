/**
 * sill Calculus Configuration — single assembly point (TODO_0285 P5).
 *
 * Spatial ILL: gill's graded surface plus the located modality `A @@ L`
 * and the three-zone sequent discipline Γ ; Δ ; Λ ⊢ C (sill.calc — the
 * zones-as-data acceptance artifact). sill's surface IS gill's (@extends
 * gill, the will precedent), so this config COMPOSES gill's exported
 * layer pieces exactly as will's does: shared layers are REFERENCED
 * (init, backward, ffi, domain, the FFI face, the fences, the by-sort
 * grade registry), sill-own layers are written out — no blind spread.
 *
 * sill-OWN: the connective/sort tables derived from sill.calc (place
 * index sort + loc), the theory over prelude/spatial.sill (gill's tower
 * verbatim), and the `place` fence — a place is a bare identifier
 * (torsor: no numerals; the grammar's one auxiliary chain would happily
 * parse `A @@ 3/2`, the sort checker must not).
 *
 * The active scheduling axis at P5 is TIME (D1 — one algebra schedules
 * a run); the product (time × dist) axis is P6a and lands here as a
 * grades override when it does.
 */

'use strict';

import path from 'path';
import { grade0 } from '../../lib/engine/grades.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import Store from '../../lib/kernel/store.js';
import { tillGrades, tillFactSetPolicy, tillGradeUnit } from '../till/calculus-config.js';
import { gillCalculusConfig, gillGradeRegistry, gillFences, gillFFIFace } from '../gill/calculus-config.js';
import { makeCalcTables, makeTheory, makeForwardParserBuilder, makeSequentLoader } from '../kit.js';

const SILL_CALC = path.join(import.meta.dirname, 'sill.calc');
const SILL_PRELUDE = path.join(import.meta.dirname, 'prelude/spatial.sill');
// Backward fragment inherited BY REFERENCE (.rules have no @extends):
// gill's fragment verbatim. loc has NO sequent rules — it is a synthetic
// atom at search level (identity only), and the located zone's discipline
// is derived from sill.calc's @structural declarations.
const GILL_RULES = path.join(import.meta.dirname, '../gill/gill.rules');

// Tables derived from sill.calc's OWN chain (= gill's surface via
// @extends). The place fence: a place value is a non-numeric identifier
// (atom) — torsor discipline at the value level.
const sillFences = {
  ...gillFences,
  place: (h) => Store.tag(h) === 'atom',
};
const { connectives: sillConnectives, sorts: sillSorts } = makeCalcTables(SILL_CALC, {
  fences: sillFences,
});

/** Grade-algebra routing over sill's sort tables and gill's registry. */
function gradeAlgebraFor(conn) {
  const argSorts = sillSorts().connArgSorts[conn];
  const gs = argSorts && argSorts.find((s) => s !== 'formula');
  return (gs && gillGradeRegistry.bySort[gs]) || gillGradeRegistry.default;
}

// Theory engine over sill's prelude chain (spatial.sill → num.gill →
// rat.ill → bin.ill).
const sillTheory = makeTheory({
  preludeFile: SILL_PRELUDE,
  META: gillFFIFace.META,
  getConfig: () => sillCalculusConfig,
});

const sillBuildParser = makeForwardParserBuilder(SILL_CALC, tillGradeUnit);

const sillCalculusConfig = {
  // ── Structural family: LNL (via gill's layer table) ──────────
  family: gillCalculusConfig.family,

  // ── L0: Kernel init — shared with gill (same Store tags + theories) ──
  init: gillCalculusConfig.init,

  // ── L1: Structural ───────────────────────────────────────────
  get connectives() { return sillConnectives(); },
  typeCheck: 'strict',
  theories: gillCalculusConfig.theories,
  gradeUnit: tillGradeUnit,
  get sorts() { return sillSorts(); },

  // Active axis = time (D1); the registry routes per-connective reading.
  grades: tillGrades,
  gradeRegistry: gillGradeRegistry,
  gradeAlgebraFor,
  factSetPolicy: tillFactSetPolicy,
  stampTag: 'at',
  shiftOps: gillCalculusConfig.shiftOps,
  scheduler: gillCalculusConfig.scheduler,

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    getModes: gillFFIFace.getModes,
    getModeMeta: gillFFIFace.getModeMeta,
    discriminatorPreds: [],
    cacheEpoch: 'sill',
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
    buildParser: sillBuildParser,
    get connTags() { return connTagsFrom(sillConnectives()); },
    grade0,
    timed: true,
    qexprPreds: gillCalculusConfig.loader.qexprPreds,
  },
};

/** Sequent-level sill calculus: sill.calc (three-zone contextStructure
 *  derived from its declarations) + gill's backward fragment by
 *  reference, with sill's theory engine and the shared @fire wiring. */
const loadSillSequent = makeSequentLoader({
  calcFile: SILL_CALC, rulesFile: GILL_RULES,
  gradeUnit: tillGradeUnit, theory: sillTheory,
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub' },
});

export { sillCalculusConfig, sillConnectives, sillTheory, loadSillSequent, gradeAlgebraFor, sillFences };
export default sillCalculusConfig;

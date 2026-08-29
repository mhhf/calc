/**
 * gill Calculus Configuration — single assembly point (TODO_0284 P2).
 *
 * Graded ILL: the laboratory where a grade algebra is DATA. gill's surface
 * is till's graded surface plus the transport comonad (gill.calc — shared
 * Store tags, one numeric prelude), scheduled by whichever grade algebra
 * this config plugs in. The grade algebras are a BY-SORT REGISTRY (P3):
 * delay → tillGrades (imported READ-ONLY from till's config — the time
 * instance is shared, not copied), dist → distGrades (the (min,+)
 * transport reading); cc.grades stays the active axis (D1: one algebra
 * schedules a run). Also gill-own: the connective/sort tables derived
 * from gill.calc (dist grade sort + value fence, haul), the numeric
 * theory over prelude/num.gill (till's tower + the collapsed min/max
 * instances), and the FFI meta routing min/max onto the tower
 * dispatchers (num.min/num.max) — ILL's meta keeps the bin-only
 * handlers, till's meta is frozen pre-P2, gill's meta is where the
 * collapse is complete.
 *
 * Mirrors calculus/till/calculus-config.js layer-for-layer.
 */

'use strict';

import path from 'path';
import { setTheories } from '../../lib/kernel/unify.js';
import { defaultTheories } from '../../lib/kernel/eq-theory.js';
import { binlitTheory } from '../../lib/engine/ill/binlit-theory.js';
import { ratlitTheory, ratParts, installRatlitTheory } from '../../lib/engine/theories/ratlit-theory.js';
import { grade0 } from '../../lib/engine/grades.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import backchainIll from '../../lib/engine/ill/backchain-ill.js';
import * as ffi from '../../lib/engine/ill/ffi/index.js';
import { mul as ratMul, div as ratDiv, cmp as ratCmp } from '../../lib/rat.js';
import { tillGrades, tillFactSetPolicy, tillGradeUnit } from '../till/calculus-config.js';
import { makeCalcTables, makeFFIFace, makeTheory, makeForwardParserBuilder, makeSequentLoader, ratCanon } from '../kit.js';

const GILL_CALC = path.join(import.meta.dirname, 'gill.calc');
const GILL_RULES = path.join(import.meta.dirname, 'gill.rules');
const GILL_PRELUDE = path.join(import.meta.dirname, 'prelude/num.gill');

// Connective + sort tables DERIVED from gill.calc (kit.js — the till
// discipline: one source of truth, a connective exists iff declared with
// @category). Value fences are per-sort VALUE checks; dist shares delay's
// fence shape (a transport cost is any nonnegative rational). Sort EDGES
// on the numeric tower live in logic files (prelude/num.gill), never here.
const _fp = (h) => ratParts(h);
const { connectives: gillConnectives, sorts: gillSorts } = makeCalcTables(GILL_CALC, {
  fences: {
    delay: (h) => { const p = _fp(h); return !!p && p[0] >= 0n; },
    count: (h) => { const p = _fp(h); return !!p && p[0] >= 0n && p[1] === 1n; },
    weight: (h) => { const p = _fp(h); return !!p && p[0] >= 0n && p[0] <= p[1]; },
    dist: (h) => { const p = _fp(h); return !!p && p[0] >= 0n; },
  },
});

// ── distGrades — the (min,+) transport-cost instance (TODO_0284 P3) ──
// Time's tropical twin: the SAME operations (ℚ≥0 carrier, ⊗ = + cost
// accumulation, ⊔ = 'join', ⊕ = order/min-prune), a different PHYSICAL
// READING (stamp = accumulated haul cost, horizon = cost budget, rule
// delay = segment cost). The operational identity is the audit's central
// point: shortest path needs NO join swap — the scheduler's B&B already
// minimizes completion, so distance is a reading of the one tropical
// algebra, selected by grade sort. A distinct frozen object (not an
// alias) so registry resolution, conformance, and buildTimedConfig
// acceptance pin a second instance. merge stays 'join' — R2: the
// principled availability reading (Petricek–Orchard–Mycroft dataflow
// coeffect); single-input hauls never exercise it, and R2 pins it
// BEFORE any multi-input haul may land. The slot list is EXPLICIT (no
// blind spread — 0284 audit): the shared tropical value algebra is
// aliased knowingly, and nothing else rides along.
const distGrades = Object.freeze({
  values: tillGrades.values,           // the one tropical ℚ algebra (frozen, shared)
  isStamp: tillGrades.isStamp,
  parseStamp: tillGrades.parseStamp,
  canonStamp: tillGrades.canonStamp,
  aggregate: tillGrades.aggregate,
});

// ── weightGrades — the MEASURE-class instance (TODO_0284 P3b; the
// 0292/will handoff). The unnormalized measure semiring (THY_0026):
// carrier ℚ≥0 masses, ⊗ compose = · (weights multiply along one
// derivation), ⊔ merge = · (co-consumed independent premises multiply —
// T4-d), ⊕ aggregate = + realized EXACTLY ('sum') or by PRF draw
// ('sample', prf.js sampleIndex). A measure algebra never discards an
// alternative (M1 mass conservation — the ⊕ prune is order-class only,
// and contract-fixed there) and carries NO scheduler boundary slots
// (parseStamp etc.): buildTimedConfig rejects this algebra loudly (the
// P1b fence; measure aggregation over whole derivations is an execution
// mode, arriving with will/0292).
//
// The values face keeps the label-algebra slot NAMES with measure
// semantics: `add` IS the ⊗ slot (· here, + for time), `sub` IS the ⊖
// residual (exact division; rat.div = null at mass 0 — the fence).
// merge is a value-level FUNCTION slot — the non-idempotent path the
// StampTable interns through (w ⊔ w = w², never the join shortcut).
// Representation slots (canon/parse/reify/float/mix/key) are the shared
// ℚ codec, reused from till's value algebra — and ONLY those: no prunes
// (a measure algebra has none), no scale/floorDiv (time-semantics
// acceleration slots — loud absence beats silently wrong mass math).
const weightGrades = Object.freeze({
  values: Object.freeze({
    unit: [1n, 1n],
    canon: tillGrades.values.canon,
    parse: tillGrades.values.parse,
    reify: tillGrades.values.reify,
    float: tillGrades.values.float,
    mix: tillGrades.values.mix,
    key: tillGrades.values.key,
    cmp: ratCmp,                       // index order ONLY — never a prune direction
    add: (a, b) => ratMul(a, b),       // ⊗ = ·
    sub: (a, b) => ratDiv(a, b),       // ⊖ = exact ÷; null at mass 0
    merge: (a, b) => ratMul(a, b),     // ⊔ = · (function slot, non-idempotent)
  }),
  aggregate: Object.freeze({ class: 'measure', realizations: ['sum', 'sample'] }),
});

// ── Grade registry keyed by grade SORT (P3/P3b): a modality = a mode +
// a grade algebra + its rules, all data. The algebra a connective runs
// under is selected by the sort of its grade argument (gill.calc):
// monad: delay → time, haul: dist → distGrades, woplus: weight →
// weightGrades. count is STRUCTURAL (parcel peeling is engine-owned,
// not a scheduler algebra). D1 single-axis: ONE algebra schedules a run
// — cc.grades below stays the active axis (time); the registry is the
// routing table, and only order-class entries are schedulable (the
// measure entry is data for will's execution mode).
const gillGradeRegistry = Object.freeze({
  bySort: Object.freeze({ delay: tillGrades, dist: distGrades, weight: weightGrades }),
  default: tillGrades,
});

/** Resolve the grade algebra selected by a connective's grade argument
 *  (the resolveConn/sort-routing face of the registry). */
function gradeAlgebraFor(conn) {
  const argSorts = gillSorts().connArgSorts[conn];
  const gs = argSorts && argSorts.find((s) => s !== 'formula');
  return (gs && gillGradeRegistry.bySort[gs]) || gillGradeRegistry.default;
}

// ── FFI meta: till's collapsed tower names PLUS min/max (TODO_0284 P2).
// min/max agree with the bin instance on the overlap (order-theoretic
// selection; n ↦ n/1 is order-preserving), so the coherence law admits
// them to the shared set — the clause face is bin.ill's min/max + the /q
// instances in prelude/num.gill. qsub/qdiv stay split (checked/field).
const _face = makeFFIFace({
  plus: { ffi: 'num.plus', mode: '+ + -', multiModal: true },
  mul: { ffi: 'num.mul', mode: '+ + -' },
  lt: { ffi: 'num.lt', mode: '+ +' },
  le: { ffi: 'num.le', mode: '+ +' },
  eq: { ffi: 'num.eq', mode: '+ +' },
  neq: { ffi: 'num.neq', mode: '+ +' },
  eq_bool: { ffi: 'num.eq_bool', mode: '+ + -' },
  min: { ffi: 'num.min', mode: '+ + -' },
  max: { ffi: 'num.max', mode: '+ + -' },
});
const GILL_FFI_META = _face.META;

// ── Theory engine (TODO_0273 discipline, kit.js): discharges template
// theory premises over gill's numeric prelude (min/max resolve there).
const gillTheory = makeTheory({
  preludeFile: GILL_PRELUDE,
  META: GILL_FFI_META,
  getConfig: () => gillCalculusConfig,
});

const gillBuildParser = makeForwardParserBuilder(GILL_CALC, tillGradeUnit);

const gillCalculusConfig = {
  // ── L0: Kernel init (same Store tags + theories as till) ─────
  init() {
    backchainIll.initILL();
    setTheories([...defaultTheories, binlitTheory, ratlitTheory]);
    installRatlitTheory();
  },

  // ── L1: Structural ───────────────────────────────────────────
  get connectives() { return gillConnectives(); },
  typeCheck: 'strict',
  theories: [binlitTheory, ratlitTheory],
  gradeUnit: tillGradeUnit,
  get sorts() { return gillSorts(); },

  // The grade ALGEBRA slot = the ACTIVE AXIS (D1: a run is scheduled by
  // ONE algebra). Time is gill's default axis; the by-sort registry
  // (gradeRegistry/gradeAlgebraFor) routes per-connective grade reading.
  grades: tillGrades,
  gradeRegistry: gillGradeRegistry,
  gradeAlgebraFor,
  factSetPolicy: tillFactSetPolicy,
  stampTag: 'at',
  shiftOps: { plus: 'add', qplus: 'add', qsub: 'sub', mul: 'scale', qdiv: 'scale' },
  scheduler: { chooser: 'random', seed: 0, cohort: 'fifo' },

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    getModes: _face.getModes,
    getModeMeta: _face.getModeMeta,
    discriminatorPreds: [],
    cacheEpoch: 'gill',
  },

  // ── L3: Backward ─────────────────────────────────────────────
  backward: {
    normalize: ratCanon,
    tryFFI: backchainIll.tryFFI,
    getFFIMeta: () => GILL_FFI_META,
    buildClauseTerm: backchainIll.buildClauseTerm,
    buildFFITerm: backchainIll.buildFFITerm,
    buildTypeTerm: backchainIll.buildTypeTerm,
  },

  // ── L4: FFI ──────────────────────────────────────────────────
  ffi: {
    meta: GILL_FFI_META,
    parsedModes: _face.PARSED,
    get: ffi.get,
    isFFIGround: ffi.convert.isGround,
  },

  // ── L5: Compose ── deliberately absent (till discipline) ─────

  // ── L6: Domain ───────────────────────────────────────────────
  domain: {
    memoControlTags: [],
  },

  // ── Loader (convert.js) ──────────────────────────────────────
  loader: {
    buildParser: gillBuildParser,
    get connTags() { return connTagsFrom(gillConnectives()); },
    grade0,
    timed: true,
    qexprPreds: { qexpr_add: 'plus', qexpr_sub: 'qsub', qexpr_mul: 'mul', qexpr_div: 'qdiv' },
  },
};

/** Sequent-level gill calculus: gill.calc + gill.rules with the gill
 *  theory engine (min/max resolve over prelude/num.gill). */
const loadGillSequent = makeSequentLoader({
  calcFile: GILL_CALC, rulesFile: GILL_RULES,
  gradeUnit: tillGradeUnit, theory: gillTheory,
  // @fire wiring (TODO_0296 P2 — the verification face's genericity
  // proof): gill's settleable stamp axes (delay, dist) share till's
  // additive ⊕/⊖ residual shape, so the same checker names apply.
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub' },
});

export { gillCalculusConfig, gillConnectives, gillTheory, loadGillSequent, distGrades, weightGrades, gillGradeRegistry, gradeAlgebraFor };
export default gillCalculusConfig;

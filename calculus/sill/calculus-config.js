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
 * (opaque index sort: no numerals; the grammar's one auxiliary chain would happily
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
import { putRat } from '../../lib/kernel/rat-term.js';
import { ratParts } from '../../lib/kernel/rat-term.js';
import { cmp as ratCmp, add as ratAdd, sub as ratSub } from '../../lib/rat.js';
import { tillGrades, tillFactSetPolicy, tillGradeUnit } from '../till/calculus-config.js';
import { gillCalculusConfig, gillGradeRegistry, gillFences, gillFFIFace } from '../gill/calculus-config.js';
import { makeCalcTables, makeTheory, makeForwardParserBuilder, makeSequentLoader, ratCanon } from '../kit.js';

const SILL_CALC = path.join(import.meta.dirname, 'sill.calc');
const SILL_PRELUDE = path.join(import.meta.dirname, 'prelude/spatial.sill');
// Backward fragment inherited BY REFERENCE (.rules have no @extends):
// gill's fragment verbatim. loc has NO sequent rules — it is a synthetic
// atom at search level (identity only), and the located zone's discipline
// is derived from sill.calc's @structural declarations.
const GILL_RULES = path.join(import.meta.dirname, '../gill/gill.rules');

// Tables derived from sill.calc's OWN chain (= gill's surface via
// @extends). The place fence: a place value is a non-numeric identifier
// (atom) — the opaque-index discipline at the value level.
const sillFences = {
  ...gillFences,
  place: (h) => Store.tag(h) === 'atom',
};
const { connectives: sillConnectives, sorts: sillSorts } = makeCalcTables(SILL_CALC, {
  fences: sillFences,
});

// ── productGrades — the (time × dist) product axis (TODO_0285 P6a) ──
//
// One stamp carries BOTH axes: value = [tn, td, dn, dd] (two normalized
// BigInt rational halves — time first). Componentwise tropical: ⊗ add
// and ⊔ join act per axis (availability: the conclusion waits for the
// last input in time AND carries the dearest accumulated cost); the
// scheduler's TOTAL order is LEXICOGRAPHIC (time primary, dist
// tie-break) — every settle-loop comparison, the heap, the B&B prune
// and the FIFO invariants run unchanged on it. The committed run
// realizes the lex-least completion; the Pareto frontier lives in the
// exploration layer (settleFrontier), never in the committed loop.
//
// Term face: a scalar grade IS time-only — dist-0 values REIFY back to
// the scalar term (canonical collapse), so till/gill programs ride in
// bit-identically; `(T ~ D)` pair terms (tpair) carry a dist half. The
// dist half admits +∞ ([1n, 0n], term face `tinf`) for HORIZONS only:
// a scalar horizon T means the down-set "time ≤ T, any dist" — pairs
// with time exactly T must not be cut off by the lex tie-break.
//
// Deliberately ABSENT slots (the weightGrades discipline — loud absence
// beats silently wrong math): scale / floorDiv / floor, so accelerate,
// coalesce and rebase reject sill runs instead of mis-shifting the dist
// axis. Zeno note: lex progress includes dist-only progress at a fixed
// instant — a 0-time dist-accumulating loop advances the frontier and
// evades maxInstantSteps; maxSteps is the bound that catches it.
const _half = (h, allowInf) => {
  if (Store.tag(h) === 'atom' && Store.child(h, 0) === 'tinf') {
    // ∞ is a DIST-axis sentinel (horizons); an infinite time half has no
    // reading in the lex order or the tropical ops — fence at the boundary.
    if (allowInf) return [1n, 0n];
    throw new Error('sill: tinf is a dist-axis sentinel — the time half of a stamp must be finite');
  }
  const p = ratParts(ratCanon(h));
  if (p === null) throw new Error(`sill: not a rational stamp half: ${Store.tag(h)}`);
  return p;
};
const _isInf = (v, i) => v[i + 1] === 0n;
const _tinf = () => Store.put('atom', ['tinf']);
const productValues = Object.freeze({
  unit: [0n, 1n, 0n, 1n],
  canon: (v) => {
    const t = tillGrades.values.canon([v[0], v[1]]);
    const d = v[3] === 0n ? [1n, 0n] : tillGrades.values.canon([v[2], v[3]]);
    return [t[0], t[1], d[0], d[1]];
  },
  parse: (h) => {
    if (Store.tag(h) === 'tpair') {
      const t = _half(Store.child(h, 0));
      const d = _half(Store.child(h, 1), true);
      return [t[0], t[1], d[0], d[1]];
    }
    const t = _half(h);
    return [t[0], t[1], 0n, 1n];
  },
  reify: (v) => {
    if (_isInf(v, 2)) return Store.put('tpair', [putRat(v[0], v[1]), _tinf()]);
    if (v[2] === 0n) return putRat(v[0], v[1]);            // dist 0 → scalar (canonical collapse)
    return Store.put('tpair', [putRat(v[0], v[1]), putRat(v[2], v[3])]);
  },
  // LEX: time first, dist breaks ties (∞ above every finite dist).
  cmp: (a, b) => {
    const t = ratCmp([a[0], a[1]], [b[0], b[1]]);
    if (t !== 0) return t;
    const ai = _isInf(a, 2), bi = _isInf(b, 2);
    if (ai || bi) return ai && bi ? 0 : (ai ? 1 : -1);
    return ratCmp([a[2], a[3]], [b[2], b[3]]);
  },
  // ⊗ compose: componentwise + (∞ absorbs on the dist axis).
  add: (a, b) => {
    const t = ratAdd([a[0], a[1]], [b[0], b[1]]);
    if (_isInf(a, 2) || _isInf(b, 2)) return [t[0], t[1], 1n, 0n];
    const d = ratAdd([a[2], a[3]], [b[2], b[3]]);
    return [t[0], t[1], d[0], d[1]];
  },
  // ⊖ residual: componentwise − (signed, like the scalar face; the
  // derived effect.residual guards negativity by cmp against unit —
  // lex catches negative time; negative dist under nonnegative time
  // cannot arise from fenced nonneg grades). ∞ absorbs on the left;
  // subtracting ∞ from a finite dist has no lawful reading — loud.
  sub: (a, b) => {
    const t = ratSub([a[0], a[1]], [b[0], b[1]]);
    if (_isInf(a, 2)) return [t[0], t[1], 1n, 0n];
    if (_isInf(b, 2)) throw new Error('sill: ⊖ with an infinite dist subtrahend');
    const d = ratSub([a[2], a[3]], [b[2], b[3]]);
    return [t[0], t[1], d[0], d[1]];
  },
  // ⊔ join of co-consumed labels: COMPONENTWISE max (a lex max would
  // drop the dearer dist of an earlier input) — hence a function slot,
  // not the 'join' shortcut.
  merge: (a, b) => {
    const t = ratCmp([a[0], a[1]], [b[0], b[1]]) >= 0 ? [a[0], a[1]] : [b[0], b[1]];
    let d;
    if (_isInf(a, 2) || _isInf(b, 2)) d = [1n, 0n];
    else d = ratCmp([a[2], a[3]], [b[2], b[3]]) >= 0 ? [a[2], a[3]] : [b[2], b[3]];
    return [t[0], t[1], d[0], d[1]];
  },
  // Monotone float approximation of the LEX order = the TIME float
  // (t_a < t_b ⟹ a <lex b; time ties fall through to cmp).
  float: (v) => tillGrades.values.float([v[0], v[1]]),
  mix: (v) => {
    const mt = tillGrades.values.mix([v[0], v[1]]);
    const md = tillGrades.values.mix([v[2], v[3]]);
    return (mt ^ Math.imul(md, 0x85ebca6b)) >>> 0;
  },
  key: (v) => v[0] + '/' + v[1] + '|' + (_isInf(v, 2) ? 'inf' : v[2] + '/' + v[3]),
});
const productGrades = Object.freeze({
  // A usable GROUND stamp: scalar literal, or a pair whose halves are
  // literals (or the ∞ sentinel). A tpair with metavar children (a
  // rule's variable delay, resolved at fire time) is NOT a stamp yet —
  // exactly till's semantics, where a variable delay's tag fails the
  // literal check.
  isStamp: (h) => {
    const t = Store.tag(h);
    if (t === 'ratlit' || t === 'binlit') return true;
    if (t !== 'tpair') return false;
    // Positional: ∞ (tinf) is admitted on the DIST half only — an
    // infinite time half is rejected here (and _half throws on the
    // strict parse path with the descriptive fence).
    const half = (c, allowInf) => {
      const ct = Store.tag(c);
      return ct === 'ratlit' || ct === 'binlit' ||
        (allowInf && ct === 'atom' && Store.child(c, 0) === 'tinf');
    };
    return half(Store.child(h, 0), false) && half(Store.child(h, 1), true);
  },
  // Tolerant by try/catch (unlike till's ratCanon, which returns
  // non-matching forms unchanged and never throws, productValues.parse
  // THROWS on non-rational halves): a NON-GROUND stamp term (metavar
  // children in a rule's delay — resolved at fire time) passes through
  // unchanged for isStamp to reject; the StampTable's values.parse
  // stays strict.
  canonStamp: (h) => {
    try { return productValues.reify(productValues.parse(h)); }
    catch { return h; }
  },
  /** Threshold input (horizon, view bounds): scalar forms delegate to
   *  till's parser, then WIDEN to the down-set (T, ∞) — a time horizon
   *  admits any accumulated dist at time ≤ T. A pair hash passes
   *  through { stamp: h }. */
  parseStamp(x) {
    if (x && typeof x === 'object' && typeof x.stamp === 'number' && productGrades.isStamp(x.stamp)) {
      return x.stamp;
    }
    const t = tillGrades.parseStamp(x);
    const p = ratParts(t);
    return productValues.reify([p[0], p[1], 1n, 0n]);
  },
  /** Extent input (chunk widths — durations, never thresholds): the
   *  scalar embedding (c, 0), NO widening — a widened width would
   *  absorb ∞ into fact stamps through settleChunked's accumulator. */
  parseExtent(x) {
    if (x && typeof x === 'object' && typeof x.stamp === 'number' && productGrades.isStamp(x.stamp)) {
      return x.stamp;
    }
    return tillGrades.parseStamp(x);
  },
  values: productValues,
  aggregate: Object.freeze({ class: 'order', realizations: ['prune'] }),
});

// By-sort grade registry (the will/gill named-const pattern — no forward
// self-reference through the config object): delay routes to the product
// axis; the rest inherit gill's.
const sillGradeRegistry = Object.freeze({
  bySort: Object.freeze({ ...gillGradeRegistry.bySort, delay: productGrades }),
  default: productGrades,
});

/** Grade-algebra routing over sill's sort tables. */
function gradeAlgebraFor(conn) {
  const argSorts = sillSorts().connArgSorts[conn];
  const gs = argSorts && argSorts.find((s) => s !== 'formula');
  return (gs && sillGradeRegistry.bySort[gs]) || sillGradeRegistry.default;
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

  // Active axis = the PRODUCT (time × dist) — P6a: one stamp carries
  // both; scalar grades embed as time-only (dist 0).
  grades: productGrades,
  gradeRegistry: sillGradeRegistry,
  gradeAlgebraFor,
  // till's policy with the label-column algebra swapped to the product
  // values — the StampTable interns (time, dist) pairs as single ids.
  factSetPolicy: { ...tillFactSetPolicy, labels: productValues },
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
  // join: 'sjoin' — under the PRODUCT order the componentwise join may
  // equal no single input, so the checker derives activation = ⊔ inputs
  // through the declared join clauses (spatial.sill) instead of the
  // total-order attainment shortcut.
  fire: { stampTag: 'at', le: 'le', lt: 'lt', sub: 'qsub', join: 'sjoin' },
});

export { sillCalculusConfig, sillConnectives, sillTheory, loadSillSequent, gradeAlgebraFor, sillFences, productGrades };
export default sillCalculusConfig;

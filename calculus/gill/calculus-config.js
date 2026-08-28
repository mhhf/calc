/**
 * gill Calculus Configuration — single assembly point (TODO_0284 P2).
 *
 * Graded ILL: the laboratory where a grade algebra is DATA. gill's surface
 * is till's graded surface (gill.calc — shared Store tags, one numeric
 * prelude), scheduled by whichever grade algebra this config plugs in.
 * P2 plugs in the TIME instance — `tillGrades` imported READ-ONLY from
 * till's config (the todo's own P3 plan references it as the delay entry
 * of the by-sort registry `{ bySort: { delay: tillGrades, dist: distGrades,
 * … } }`, which replaces the single `grades` slot here). What is gill-own
 * today: the connective/sort tables derived from gill.calc (incl. the
 * `dist` grade sort + its value fence), the numeric theory over
 * prelude/num.gill (till's tower + the collapsed min/max instances), and
 * the FFI meta routing min/max onto the tower dispatchers (num.min/
 * num.max) — ILL's meta keeps the bin-only handlers, till's meta is
 * frozen pre-P2, gill's meta is where the collapse is complete.
 *
 * Mirrors calculus/till/calculus-config.js layer-for-layer; divergence
 * begins at P3 (grade registry by sort, haul), not here.
 */

'use strict';

import path from 'path';
import Store from '../../lib/kernel/store.js';
import calculus from '../../lib/calculus/index.js';
import { buildParser } from '../../lib/calculus/builders.js';
import { setTheories } from '../../lib/kernel/unify.js';
import { defaultTheories } from '../../lib/kernel/eq-theory.js';
import { binlitTheory } from '../../lib/engine/ill/binlit-theory.js';
import { ratlitTheory, ratParts, installRatlitTheory } from '../../lib/engine/theories/ratlit-theory.js';
import { grade0 } from '../../lib/engine/grades.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { apply } from '../../lib/kernel/substitute.js';
import { predHead } from '../../lib/kernel/ast.js';
import { collectMetavars } from '../../lib/engine/pattern-utils.js';
import mde from '../../lib/engine/index.js';
import backward from '../../lib/engine/backchain.js';
import backchainIll from '../../lib/engine/ill/backchain-ill.js';
import * as ffi from '../../lib/engine/ill/ffi/index.js';
import { tillGrades, tillFactSetPolicy, tillGradeUnit } from '../till/calculus-config.js';

const GILL_CALC = path.join(import.meta.dirname, 'gill.calc');
const GILL_RULES = path.join(import.meta.dirname, 'gill.rules');
const GILL_PRELUDE = path.join(import.meta.dirname, 'prelude/num.gill');

/** The one numeric canonicalizer (same tower as till: structural i/o/e
 *  chains and rat(N,D) forms fold onto canonical literals). */
const _ratCanon = (h) => ratlitTheory.canonicalize(binlitTheory.canonicalize(h));

// Connective table DERIVED from gill.calc (the till discipline: one source
// of truth — a connective exists iff declared there with @category).
let _gillConnectives = null;
function gillConnectives() {
  if (_gillConnectives) return _gillConnectives;
  const cs = calculus.load(GILL_CALC).constructors;
  const table = {};
  for (const [name, c] of Object.entries(cs)) {
    const ann = c.annotations || {};
    if (c.returnType !== 'formula' || !ann.category) continue;
    table[name] = {
      category: ann.category, arity: c.argTypes.length,
      ...(ann.polarity ? { polarity: ann.polarity } : {}),
    };
  }
  _gillConnectives = table;
  return table;
}

// ── Sorts (TODO_0011 rung 1): calc-derived sort data + literal
// classification. Value fences are per-sort VALUE checks; dist shares
// delay's fence shape (a transport cost is any nonnegative rational).
// Sort EDGES on the numeric tower live in logic files (prelude/num.gill),
// never here.
let _gillSorts = null;
function gillSorts() {
  if (_gillSorts) return _gillSorts;
  const spec = calculus.load(GILL_CALC);
  const edges = spec.sortEdges || [];
  const calcSortNames = new Set(edges.flat());
  const members = {};
  const connArgSorts = {};
  for (const [name, c] of Object.entries(spec.constructors)) {
    if (c.argTypes.length === 0 && calcSortNames.has(c.returnType)) {
      members[name] = c.returnType;
    }
    if (c.returnType === 'formula' && c.argTypes.length > 0) {
      connArgSorts[name] = c.argTypes;
    }
  }
  const _p = (h) => ratParts(h);
  _gillSorts = {
    calc: { edges, members },
    connArgSorts,
    formulaSort: 'formula',
    lit: {
      literals: { binlit: 'bin', ratlit: 'q', strlit: 'string' },
      fences: {
        delay: (h) => { const p = _p(h); return !!p && p[0] >= 0n; },
        count: (h) => { const p = _p(h); return !!p && p[0] >= 0n && p[1] === 1n; },
        weight: (h) => { const p = _p(h); return !!p && p[0] >= 0n && p[0] <= p[1]; },
        dist: (h) => { const p = _p(h); return !!p && p[0] >= 0n; },
      },
    },
  };
  return _gillSorts;
}

// ── FFI meta: till's collapsed tower names PLUS min/max (TODO_0284 P2).
// min/max agree with the bin instance on the overlap (order-theoretic
// selection; n ↦ n/1 is order-preserving), so the coherence law admits
// them to the shared set — the clause face is bin.ill's min/max + the /q
// instances in prelude/num.gill. qsub/qdiv stay split (checked/field).
const GILL_FFI_META = {
  ...ffi.defaultMeta,
  plus: { ffi: 'num.plus', mode: '+ + -', multiModal: true },
  mul: { ffi: 'num.mul', mode: '+ + -' },
  lt: { ffi: 'num.lt', mode: '+ +' },
  le: { ffi: 'num.le', mode: '+ +' },
  eq: { ffi: 'num.eq', mode: '+ +' },
  neq: { ffi: 'num.neq', mode: '+ +' },
  eq_bool: { ffi: 'num.eq_bool', mode: '+ + -' },
  min: { ffi: 'num.min', mode: '+ + -' },
  max: { ffi: 'num.max', mode: '+ + -' },
};
const GILL_PARSED_MODES = { ...ffi.parsedModes };
for (const k of ['plus', 'mul', 'lt', 'le', 'eq', 'neq', 'eq_bool', 'min', 'max']) {
  GILL_PARSED_MODES[k] = ffi.mode.parseMode(GILL_FFI_META[k].mode);
}
const gillGetModes = (p) => GILL_PARSED_MODES[p] || null;
const gillGetModeMeta = (p) => {
  const meta = GILL_FFI_META[p];
  if (!meta) return null;
  return { modes: GILL_PARSED_MODES[p], multiModal: !!meta.multiModal };
};

// ── Theory engine (TODO_0273 discipline, till's shape): discharges
// template theory premises over gill's numeric prelude. FFI fast path
// first (advisory on decode failure), clause resolution as the semantics;
// CALC_NOFFI=1 disables the fast path AND FFI inside clause resolution.
const _noFFI = () => process.env.CALC_NOFFI === '1';
let _theoryEc = null, _theoryOpts = null, _theoryPreds = null;
Store.onClear(() => { _theoryEc = null; _theoryPreds = null; });
function _theoryEngine() {
  if (!_theoryEc) {
    gillCalculusConfig.init();
    _theoryEc = mde.load(GILL_PRELUDE, { calculusConfig: gillCalculusConfig, cache: false });
    _theoryOpts = {
      ...backchainIll.makeILLBackchainOpts({
        theories: [...defaultTheories, binlitTheory, ratlitTheory],
        normalize: _ratCanon,
        getFFIMeta: () => GILL_FFI_META,
      }),
      maxDepth: 20000, allBuckets: true, useFFI: true,
    };
  }
  return _theoryEc;
}
const gillTheory = {
  prove(goal) {
    if (!_noFFI()) {
      const fast = backchainIll.tryFFI(goal, GILL_FFI_META);
      if (fast) {
        if (fast.success) return fast.theta || [];
        if (fast.reason !== 'conversion_failed') return null;
      }
    }
    const ec = _theoryEngine();
    const opts = _noFFI() ? { ..._theoryOpts, useFFI: false } : _theoryOpts;
    const res = backward.prove(goal, ec.clauses, ec.definitions, opts);
    if (!res.success) return null;
    const vars = new Set();
    collectMetavars(goal, vars);
    const out = [];
    for (const v of vars) {
      const val = _ratCanon(apply(v, res.theta));
      const rem = new Set();
      collectMetavars(val, rem);
      if (rem.size) return null;
      out.push([v, val]);
    }
    return out;
  },
  has(pred) {
    if (pred in GILL_FFI_META) return true;
    if (!_theoryPreds) {
      const ec = _theoryEngine();
      _theoryPreds = new Set();
      for (const [, cl] of ec.clauses) _theoryPreds.add(predHead(cl.hash));
      for (const [, h] of ec.definitions) _theoryPreds.add(predHead(h));
      _theoryPreds.delete(null);
    }
    return _theoryPreds.has(pred);
  },
};

function gillBuildParser() {
  return buildParser(calculus.load(GILL_CALC).constructors, {
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
    gradeUnit: tillGradeUnit,
  });
}

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

  // The grade ALGEBRA slot: P2 = the time instance, read-only from till.
  // P3 replaces this with the by-sort registry (delay/count/dist/weight).
  grades: tillGrades,
  factSetPolicy: tillFactSetPolicy,
  stampTag: 'at',
  shiftOps: { plus: 'add', qplus: 'add', qsub: 'sub', mul: 'scale', qdiv: 'scale' },
  scheduler: { chooser: 'random', seed: 0, cohort: 'fifo' },

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    getModes: gillGetModes,
    getModeMeta: gillGetModeMeta,
    discriminatorPreds: [],
    cacheEpoch: 'gill',
  },

  // ── L3: Backward ─────────────────────────────────────────────
  backward: {
    normalize: _ratCanon,
    tryFFI: backchainIll.tryFFI,
    getFFIMeta: () => GILL_FFI_META,
    buildClauseTerm: backchainIll.buildClauseTerm,
    buildFFITerm: backchainIll.buildFFITerm,
    buildTypeTerm: backchainIll.buildTypeTerm,
  },

  // ── L4: FFI ──────────────────────────────────────────────────
  ffi: {
    meta: GILL_FFI_META,
    parsedModes: GILL_PARSED_MODES,
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
function loadGillSequent() {
  return calculus.load(GILL_CALC, GILL_RULES, {
    parser: {
      multiCharFreevars: true,
      numbers: true,
      gradeUnit: tillGradeUnit,
    },
    theory: gillTheory,
  });
}

export { gillCalculusConfig, gillConnectives, gillTheory, loadGillSequent };
export default gillCalculusConfig;

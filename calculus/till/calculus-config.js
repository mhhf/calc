/**
 * till Calculus Configuration — single assembly point (TODO_0265 Phase 4).
 *
 * Timed ILL: exact-rational stamps (D3/D14), the tropical grade algebra
 * (⊕ = max on availability, ⊗ = + on duration), the stamp-sorted FactSet
 * index policy (D5 — the FIFO cohort order), and the scheduler policies
 * (D12: fifo cohort sampler, PRF conflict chooser; D17 seed).
 *
 * Mirrors lib/engine/ill/calculus-config.js layer-for-layer; this file is
 * the ONLY place till-specific choices live — the engine (timed.js) reads
 * everything through the config record (D13).
 */

'use strict';

import path from 'path';
import Store from '../../lib/kernel/store.js';
import calculus from '../../lib/calculus/index.js';
import { buildParser } from '../../lib/calculus/builders.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import { setTheories } from '../../lib/kernel/unify.js';
import { defaultTheories } from '../../lib/kernel/eq-theory.js';
import { binlitTheory } from '../../lib/engine/ill/binlit-theory.js';
import { ratlitTheory, ratParts, installRatlitTheory } from '../../lib/engine/theories/ratlit-theory.js';
import { grade0 } from '../../lib/engine/grades.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { cmp as ratCmp, add as ratAdd, sub as ratSub } from '../../lib/rat.js';
import backchainIll from '../../lib/engine/ill/backchain-ill.js';
import * as ffi from '../../lib/engine/ill/ffi/index.js';

const TILL_CALC = path.join(import.meta.dirname, 'till.calc');
const TILL_RULES = path.join(import.meta.dirname, 'till.rules');

// Connective table DERIVED from till.calc — one source of truth: a
// connective exists iff it is declared there with a @category annotation
// (the former hand-written duplicate required every addition twice —
// with/Phase 6 needed edits in BOTH places, which is how tables drift).
// tensor/loli/one/bang share ILL's store tags (one Store, shared numeric
// prelude); monad is till's own 2-ary monad (D6 — ILL's unary {A} untouched).
let _tillConnectives = null;
function tillConnectives() {
  if (_tillConnectives) return _tillConnectives;
  const cs = calculus.load(TILL_CALC).constructors;
  const table = {};
  for (const [name, c] of Object.entries(cs)) {
    const ann = c.annotations || {};
    if (c.returnType !== 'formula' || !ann.category) continue;
    table[name] = {
      category: ann.category, arity: c.argTypes.length,
      ...(ann.polarity ? { polarity: ann.polarity } : {}),
    };
  }
  _tillConnectives = table;
  return table;
}

/** Unit of the duration monoid = stamp 0 = the D11 default stamp.
 *  `{B}` (bare braces) elides this grade; rules carrying it stay untimed. */
const tillGradeUnit = () => putRat(0n, 1n);

// ── Stamp algebra (the tropical instance over canonical ℚ hashes) ──
// Stamps are canonical putRat forms: binlit for integers, ratlit otherwise.
// canonStamp folds clause-derived shapes (i/o/e chains, structural rat(N,D))
// so the noFFI path yields the same hashes the FFI path does.

const _parts = (h) => {
  const p = ratParts(h);
  if (p === null) throw new Error(`till: not a rational stamp: ${Store.tag(h)}`);
  return p;
};

const tillGrades = {
  availability: {
    cmp: (a, b) => (a === b ? 0 : ratCmp(_parts(a), _parts(b))),
  },
  effect: {
    unit: tillGradeUnit,
    compose: (s, d) => putRat(...ratAdd(_parts(s), _parts(d))),
    sub: (a, b) => putRat(...ratSub(_parts(a), _parts(b))),
  },
  isStamp: (h) => {
    const t = Store.tagId(h);
    return t === Store.TAG.ratlit || t === Store.TAG.binlit;
  },
  canonStamp: (h) => ratlitTheory.canonicalize(binlitTheory.canonicalize(h)),
  /** Horizon/stamp input: integer Number, "a/b" / "d.f" / "n" string
   *  (digit-wise exact — never through a float, D3), or an existing stamp
   *  hash wrapped as { stamp: h } — numbers are always VALUES, so a raw
   *  hash can never be misread as an integer horizon (or vice versa). */
  parseStamp(x) {
    // Stamps and horizons are ℚ≥0 in v1 (time starts at 0) — negatives are
    // rejected here even though ratlit STORAGE is signed (D14).
    const nonNeg = (n, d) => {
      if (n < 0n) throw new Error(`till.parseStamp: stamps are non-negative in v1 (got ${x})`);
      return putRat(n, d);
    };
    if (typeof x === 'number') {
      if (!Number.isInteger(x)) throw new Error(`till.parseStamp(${x}): non-integer Number — pass a string ("${x}") for exactness (D3)`);
      return nonNeg(BigInt(x), 1n);
    }
    if (typeof x === 'string') {
      const s = x.trim();
      let m;
      if ((m = s.match(/^(-?\d+)\/(\d+)$/))) return nonNeg(BigInt(m[1]), BigInt(m[2]));
      if ((m = s.match(/^(-?)(\d+)\.(\d+)$/))) {
        return nonNeg(BigInt(m[1] + m[2] + m[3]), 10n ** BigInt(m[3].length));
      }
      if (/^-?\d+$/.test(s)) return nonNeg(BigInt(s), 1n);
      throw new Error(`till.parseStamp: cannot parse '${x}'`);
    }
    if (x && typeof x === 'object' && typeof x.stamp === 'number' && tillGrades.isStamp(x.stamp)) {
      return x.stamp;
    }
    throw new Error('till.parseStamp: expected an integer Number, an exact string, or { stamp: hash }');
  },
};

// ── FactSet index policy (D5): group at(A, t) under A's predicate tag,
// order within the group by stamp then hash — the FIFO cohort index.
// "The index is optimization, the multiset is semantics" (D13): this may
// never change WHICH matches exist, only how candidates are enumerated.

const _ZERO = [0n, 1n];
const _stampParts = (h) => (Store.tag(h) === 'at' ? _parts(Store.child(h, 1)) : _ZERO);

const tillFactSetPolicy = {
  groupKey: (h) => (Store.tag(h) === 'at' ? Store.tagId(Store.child(h, 0)) : Store.tagId(h)),
  cmp: (a, b) => {
    const c = ratCmp(_stampParts(a), _stampParts(b));
    return c !== 0 ? c : (a - b);
  },
};

// ── Sorts (TODO_0011 rung 1): the till instance of the refinement-sort
// machinery. The MACHINERY is generic (lib/engine/sorts.js + the prelude
// logic file calculus/till/prelude/sorts.till); this record carries the
// only till-specific pieces JS may hold: calc-level sort data DERIVED from
// till.calc (grade sorts + connective signatures — one declaration, two
// consumers: grammar and checker), and literal classification with value
// fences (a numeral's membership in a refinement sort is a VALUE check —
// nonneg at 'delay', integer at 'count', [0,1] at 'weight'). Sort EDGES
// on the numeric tower live in logic files (prelude/rat.ill), never here.
let _tillSorts = null;
function tillSorts() {
  if (_tillSorts) return _tillSorts;
  const spec = calculus.load(TILL_CALC);
  const edges = spec.sortEdges || [];
  const calcSortNames = new Set(edges.flat());
  const members = {};
  const connArgSorts = {};
  for (const [name, c] of Object.entries(spec.constructors)) {
    if (c.argTypes.length === 0 && calcSortNames.has(c.returnType)) {
      members[name] = c.returnType;                    // g0/gw : count
    }
    if (c.returnType === 'formula' && c.argTypes.length > 0) {
      connArgSorts[name] = c.argTypes;                 // monad: [delay, formula], …
    }
  }
  const _p = (h) => ratParts(h);                       // [num, den] bigints | null
  _tillSorts = {
    calc: { edges, members },
    connArgSorts,
    formulaSort: 'formula',
    lit: {
      literals: { binlit: 'bin', ratlit: 'q', strlit: 'string' },
      fences: {
        delay: (h) => { const p = _p(h); return !!p && p[0] >= 0n; },
        count: (h) => { const p = _p(h); return !!p && p[0] >= 0n && p[1] === 1n; },
        weight: (h) => { const p = _p(h); return !!p && p[0] >= 0n && p[0] <= p[1]; },
      },
    },
  };
  return _tillSorts;
}

// ── Numeric-namespace collapse (TODO_0011 §3 — the dispatch rider) ──
// plus/mul/lt/le/eq/neq/eq_bool are ONE predicate each across the numeric
// tower: bin.ill's clauses are the bin instance, rat.ill's /q clauses the
// instance at the bound. The FFI face dispatches the same way (num.*
// handlers: bin fast path, rational fallback). This overlay is till's
// interface declaration for those names — ILL keeps the shared bin-only
// defaults untouched. `plus` narrows from the bin family's multi-modal
// '+ + +' to '+ + -' (the shape window lowering emits; multiModal stays
// on, so the bin fast path still solves other modes). qsub/qdiv stay
// SPLIT names: checked-vs-monus and field-vs-Euclidean disagree on the
// shared subsort — the coherence law forbids sharing (Integral/Fractional).
const TILL_FFI_META = {
  ...ffi.defaultMeta,
  plus: { ffi: 'num.plus', mode: '+ + -', multiModal: true },
  mul: { ffi: 'num.mul', mode: '+ + -' },
  lt: { ffi: 'num.lt', mode: '+ +' },
  le: { ffi: 'num.le', mode: '+ +' },
  eq: { ffi: 'num.eq', mode: '+ +' },
  neq: { ffi: 'num.neq', mode: '+ +' },
  eq_bool: { ffi: 'num.eq_bool', mode: '+ + -' },
};
const TILL_PARSED_MODES = { ...ffi.parsedModes };
for (const k of ['plus', 'mul', 'lt', 'le', 'eq', 'neq', 'eq_bool']) {
  TILL_PARSED_MODES[k] = ffi.mode.parseMode(TILL_FFI_META[k].mode);
}
const tillGetModes = (p) => TILL_PARSED_MODES[p] || null;
const tillGetModeMeta = (p) => {
  const meta = TILL_FFI_META[p];
  if (!meta) return null;
  return { modes: TILL_PARSED_MODES[p], multiModal: !!meta.multiModal };
};

function tillBuildParser() {
  return buildParser(calculus.load(TILL_CALC).constructors, {
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

const tillCalculusConfig = {
  // ── L0: Kernel init ──────────────────────────────────────────
  // initILL registers the bin atoms/tags (the numeric prelude is shared);
  // till additionally needs the ratlit theory in the GLOBAL unifier or the
  // forward engine can never cross-tag match ratlit ↔ rat(N,D) (B6).
  init() {
    backchainIll.initILL();
    setTheories([...defaultTheories, binlitTheory, ratlitTheory]);
    installRatlitTheory();
  },

  // ── L1: Structural ───────────────────────────────────────────
  get connectives() { return tillConnectives(); },
  // Closed-world sort checking: undeclared symbols in rules/clauses FAIL
  // the load (Phase 6 post-mortem — the open-world checker let every typo
  // self-introduce a resource).
  typeCheck: 'strict',
  theories: [binlitTheory, ratlitTheory],
  gradeUnit: tillGradeUnit,

  // Refinement sorts (TODO_0011 rung 1) — presence-gated: the slot enables
  // the machinery; a program without sort declarations still loads through
  // the sortless string checker.
  get sorts() { return tillSorts(); },

  // The grade ALGEBRA slot (D2) — timed.js reads stamps/durations through
  // this record only; availability.cmp doubles as the index comparator.
  grades: tillGrades,
  factSetPolicy: tillFactSetPolicy,

  // Scheduler policies (D12/D17): within-instant conflict chooser (P5 PRF,
  // seedable) and cohort sampler ('fifo' = index order, 'lifo' reversed).
  scheduler: { chooser: 'random', seed: 0, cohort: 'fifo' },

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    // q-family + bin modes from the shared FFI registry — MANDATORY for
    // till: without q-op modes, existential-output detection falls back to
    // the last-arg convention (round-12 residue, checked by tests).
    getModes: tillGetModes,
    getModeMeta: tillGetModeMeta,
    discriminatorPreds: [],        // fingerprint layer is not theory-aware (r12)
    cacheEpoch: 'till',
  },

  // ── L3: Backward ─────────────────────────────────────────────
  // Clause resolution over the numeric prelude (bin.ill + prelude/rat.ill).
  // Reuses ILL's backchain defaults with a ratlit-aware normalizer.
  backward: {
    normalize: (h) => ratlitTheory.canonicalize(binlitTheory.canonicalize(h)),
    tryFFI: backchainIll.tryFFI,
    getFFIMeta: () => TILL_FFI_META,
    buildClauseTerm: backchainIll.buildClauseTerm,
    buildFFITerm: backchainIll.buildFFITerm,
    buildTypeTerm: backchainIll.buildTypeTerm,
  },

  // ── L4: FFI ──────────────────────────────────────────────────
  // The shared registry carries bin + rat handlers (FFI is optimization;
  // prelude clauses are the semantics — FFI-off must agree hash-for-hash).
  ffi: {
    meta: TILL_FFI_META,
    parsedModes: TILL_PARSED_MODES,
    get: ffi.get,
    isFFIGround: ffi.convert.isGround,
  },

  // ── L5: Compose ──────────────────────────────────────────────
  // Deliberately absent: till v1 is grade-0-free (compose.js still
  // hardcodes ILL tags — recorded residue, rides with 0157/merge-back).

  // ── L6: Domain ───────────────────────────────────────────────
  domain: {
    memoControlTags: [],
  },

  // ── Loader (convert.js) ──────────────────────────────────────
  loader: {
    buildParser: tillBuildParser,
    get connTags() { return connTagsFrom(tillConnectives()); },
    grade0,
    timed: true,
    // Window arithmetic lowers onto the COLLAPSED numeric names (add/mul);
    // sub/div stay q-specific (checked / field — never collapsed).
    qexprPreds: { qexpr_add: 'plus', qexpr_sub: 'qsub', qexpr_mul: 'mul', qexpr_div: 'qdiv' },
  },
};

/**
 * Sequent-level till calculus (Phase 6b Stage 1): till.calc + till.rules,
 * the graded-syntax parser, and THE tillGrades record — the same algebra
 * the timed scheduler reads (D13: one grade algebra, two faces). Backward
 * provability over the graded fragment only; settle stays the execution
 * semantics, and the timed judgment (stamps) is Stage 2.
 */
function loadTillSequent() {
  return calculus.load(TILL_CALC, TILL_RULES, {
    parser: {
      multiCharFreevars: true,
      numbers: true,
      gradeUnit: tillGradeUnit,
    },
    grades: tillGrades,
  });
}

export { tillCalculusConfig, tillGrades, tillFactSetPolicy, tillGradeUnit, tillConnectives, loadTillSequent };
export default tillCalculusConfig;

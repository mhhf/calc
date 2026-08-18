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

// tensor/loli/one/bang share ILL's store tags (one Store, shared numeric
// prelude); gmonad is till's own 2-ary monad (D6 — ILL's unary {A} untouched).
const TILL_CONNECTIVES = {
  tensor: { category: 'multiplicative', arity: 2, polarity: 'positive' },
  loli:   { category: 'multiplicative', arity: 2, polarity: 'negative' },
  one:    { category: 'multiplicative', arity: 0, polarity: 'positive' },
  bang:   { category: 'exponential',    arity: 2 },
  gmonad: { category: 'monad',          arity: 2, polarity: 'negative' },
  // Weighted internal choice `woplus Q A B` (Phase 4b) — resolveConn maps
  // (additive, arity 3, positive) to roles.weightedChoice.
  woplus: { category: 'additive',       arity: 3, polarity: 'positive' },
};

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
    if (typeof x === 'number') {
      if (!Number.isInteger(x)) throw new Error(`till.parseStamp(${x}): non-integer Number — pass a string ("${x}") for exactness (D3)`);
      return putRat(BigInt(x), 1n);
    }
    if (typeof x === 'string') {
      const s = x.trim();
      let m;
      if ((m = s.match(/^(-?\d+)\/(\d+)$/))) return putRat(BigInt(m[1]), BigInt(m[2]));
      if ((m = s.match(/^(-?)(\d+)\.(\d+)$/))) {
        return putRat(BigInt(m[1] + m[2] + m[3]), 10n ** BigInt(m[3].length));
      }
      if (/^-?\d+$/.test(s)) return putRat(BigInt(s), 1n);
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

function tillBuildParser() {
  return buildParser(calculus.load(TILL_CALC).constructors, {
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
    timedAnnotations: true,
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
  connectives: TILL_CONNECTIVES,
  theories: [binlitTheory, ratlitTheory],
  gradeUnit: tillGradeUnit,

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
    getModes: ffi.getModes,
    getModeMeta: ffi.getModeMeta,
    discriminatorPreds: [],        // fingerprint layer is not theory-aware (r12)
    cacheEpoch: 'till',
  },

  // ── L3: Backward ─────────────────────────────────────────────
  // Clause resolution over the numeric prelude (bin.ill + prelude/rat.ill).
  // Reuses ILL's backchain defaults with a ratlit-aware normalizer.
  backward: {
    normalize: (h) => ratlitTheory.canonicalize(binlitTheory.canonicalize(h)),
    tryFFI: backchainIll.tryFFI,
    getFFIMeta: backchainIll.getFFIMeta,
    buildClauseTerm: backchainIll.buildClauseTerm,
    buildFFITerm: backchainIll.buildFFITerm,
    buildTypeTerm: backchainIll.buildTypeTerm,
  },

  // ── L4: FFI ──────────────────────────────────────────────────
  // The shared registry carries bin + rat handlers (FFI is optimization;
  // prelude clauses are the semantics — FFI-off must agree hash-for-hash).
  ffi: {
    meta: ffi.defaultMeta,
    parsedModes: ffi.parsedModes,
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
    connTags: connTagsFrom(TILL_CONNECTIVES),
    grade0,
    timed: true,
  },
};

export { tillCalculusConfig, tillGrades, tillFactSetPolicy, tillGradeUnit, TILL_CONNECTIVES };
export default tillCalculusConfig;

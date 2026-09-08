/**
 * Shared assembly kit for the ILL-family timed calculi (till, gill, and
 * will after it — TODO_0284 audit). A calculus config is a DATA file: it
 * names its .calc/.rules/prelude files, its grade algebras, its FFI meta
 * rows, and its literal fences. The MECHANICAL loaders live here once:
 * connective/sort tables derived from the .calc (one source of truth — a
 * connective exists iff declared with @category), the theory engine
 * (TODO_0273 discipline), the forward parser, the sequent loader, and the
 * numeric canonicalizer. The L0-L6 config literal stays in each calculus
 * file — it is the visible layer table (0284 M10), not something a
 * factory should hide.
 */

'use strict';

import Store from '../lib/kernel/store.js';
import { fireChecker } from '../lib/prover/timed/fire-check.js';
import { drawChecker } from '../lib/prover/draw-check.js';
import calculus from '../lib/calculus/index.js';
import { buildParser } from '../lib/calculus/builders.js';
import { defaultTheories } from '../lib/kernel/eq-theory.js';
import { binlitTheory } from './ill/lib/binlit-theory.js';
import { ratlitTheory } from './till/lib/ratlit-theory.js';
import { apply } from '../lib/kernel/substitute.js';
import { predHead } from '../lib/kernel/ast.js';
import { collectMetavars } from '../lib/engine/pattern-utils.js';
import mde from '../lib/engine/index.js';
import backward from '../lib/engine/backchain.js';
import backchainIll from './ill/lib/backchain-ill.js';
import * as ffi from './ill/lib/ffi/index.js';

/** The one numeric canonicalizer (folds structural i/o/e chains and
 *  rat(N,D) forms onto canonical literals) — shared by stamp algebras,
 *  theory engines, and backchain normalizers. */
const ratCanon = (h) => ratlitTheory.canonicalize(binlitTheory.canonicalize(h));

/**
 * Lazy connective + sort tables derived from one .calc file.
 * `fences` is calculus data: per-grade-sort literal VALUE checks
 * (a numeral's membership in a refinement sort is a value question).
 * The caches hold only names/closures — no Store hashes — so they
 * survive Store.clear.
 */
function makeCalcTables(calcFile, { fences }) {
  let conn = null, sorts = null;
  return {
    connectives() {
      if (conn) return conn;
      const cs = calculus.load(calcFile).constructors;
      const table = {};
      for (const [name, c] of Object.entries(cs)) {
        const ann = c.annotations || {};
        if (c.returnType !== 'formula' || !ann.category) continue;
        table[name] = {
          category: ann.category, arity: c.argTypes.length,
          ...(ann.polarity ? { polarity: ann.polarity } : {}),
        };
      }
      conn = table;
      return table;
    },
    sorts() {
      if (sorts) return sorts;
      const spec = calculus.load(calcFile);
      const edges = spec.sortEdges || [];
      const calcSortNames = new Set(edges.flat());
      const members = {};
      const connArgSorts = {};
      for (const [name, c] of Object.entries(spec.constructors)) {
        if (c.argTypes.length === 0 && calcSortNames.has(c.returnType)) {
          members[name] = c.returnType;                  // g0/gw : count, …
        }
        if (c.returnType === 'formula' && c.argTypes.length > 0) {
          connArgSorts[name] = c.argTypes;               // monad: [delay, formula], …
        }
      }
      sorts = {
        calc: { edges, members },
        connArgSorts,
        formulaSort: 'formula',
        lit: {
          literals: { binlit: 'bin', ratlit: 'q', strlit: 'string' },
          fences,
        },
      };
      return sorts;
    },
  };
}

/** FFI face: the shared registry defaults plus the calculus's rows, with
 *  parsed modes and the compile-layer accessors. */
function makeFFIFace(extraMeta) {
  const META = { ...ffi.defaultMeta, ...extraMeta };
  const PARSED = { ...ffi.parsedModes };
  for (const k of Object.keys(extraMeta)) PARSED[k] = ffi.mode.parseMode(META[k].mode);
  return {
    META,
    PARSED,
    getModes: (p) => PARSED[p] || null,
    getModeMeta: (p) => (META[p] ? { modes: PARSED[p], multiModal: !!META[p].multiModal } : null),
  };
}

/**
 * Theory engine (TODO_0273): discharges template theory premises over the
 * calculus's numeric prelude. FFI fast path first — the rational face is
 * TOTAL on decodable numerics, so a non-conversion failure IS the
 * decision; decode failures stay advisory and fall through to clause
 * resolution (the semantics; FFI principle). CALC_NOFFI=1 skips the fast
 * path AND disables FFI inside clause resolution. `getConfig` is lazy —
 * the config object references the theory and vice versa.
 */
function makeTheory({ preludeFile, META, getConfig }) {
  const noFFI = () => process.env.CALC_NOFFI === '1';
  let ec = null, opts = null, preds = null;
  Store.onClear(() => { ec = null; preds = null; });    // cached hashes die with the Store
  const engine = () => {
    if (!ec) {
      const cfg = getConfig();
      cfg.init();
      ec = mde.load(preludeFile, { calculusConfig: cfg, cache: false });
      opts = {
        ...backchainIll.makeILLBackchainOpts({
          theories: [...defaultTheories, binlitTheory, ratlitTheory],
          normalize: ratCanon,
          getFFIMeta: () => META,
        }),
        maxDepth: 20000, allBuckets: true, useFFI: true,
      };
    }
    return ec;
  };
  return {
    /** popts.useFFI: false forces the SEMANTICS path — no tryFFI fast
     *  path, no FFI inside clause resolution. The certified checkers
     *  (fire-check) prove their stamp judgments this way, keeping
     *  rat-ffi/lib-rat OUT of the verification trust base (TODO_0296 P1);
     *  the engine's hot path keeps the FFI-first default. */
    prove(goal, popts) {
      const clauseOnly = noFFI() || (popts && popts.useFFI === false);
      if (!clauseOnly) {
        const fast = backchainIll.tryFFI(goal, META);
        if (fast) {
          if (fast.success) return fast.theta || [];
          if (fast.reason !== 'conversion_failed') return null;
        }
      }
      const e = engine();
      const o = clauseOnly ? { ...opts, useFFI: false } : opts;
      const res = backward.prove(goal, e.clauses, e.definitions, o);
      if (!res.success) return null;
      const vars = new Set();
      collectMetavars(goal, vars);
      const out = [];
      for (const v of vars) {
        // backward.prove resolves slot chains before returning theta —
        // one apply reaches the value
        const val = ratCanon(apply(v, res.theta));
        const rem = new Set();
        collectMetavars(val, rem);
        if (rem.size) return null;      // outputs must be fully determined
        out.push([v, val]);
      }
      return out;
    },
    /** Can the theory speak about `pred`? The loader uses this to reject
     *  typo'd theory premises LOUDLY at load time (TODO_0274 item 1). */
    has(pred) {
      if (pred in META) return true;
      if (!preds) {
        const e = engine();
        preds = new Set();
        for (const [, cl] of e.clauses) preds.add(predHead(cl.hash));
        for (const [, h] of e.definitions) preds.add(predHead(h));
        preds.delete(null);
      }
      return preds.has(pred);
    },
  };
}

/** Forward-rule parser over a .calc constructor table (graded syntax).
 *  `extraOpts` = per-calculus grammar opt-ins (will: binderSorts — the
 *  ∃_ρ sorted binder). */
function makeForwardParserBuilder(calcFile, gradeUnit, extraOpts = {}) {
  return () => buildParser(calculus.load(calcFile).constructors, {
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true,
    numbers: true,
    application: true,
    arrows: true,
    forwardRules: true,
    binaryNormalization: true,
    gradeUnit,
    ...extraOpts,
  });
}

/** Sequent-level loader: .calc + .rules (a path or a LIST of paths —
 *  later files extend earlier ones, TODO_0298) with the theory engine.
 *  `parser` adds per-calculus parser opt-ins (will: binders — the ∃_ρ
 *  rules pattern-match binder bodies); `draw` binds the @draw checker. */
function makeSequentLoader({ calcFile, rulesFile, gradeUnit, theory, fire = null, draw = null, parser = null }) {
  return () => {
    const calc = calculus.load(calcFile, rulesFile, {
      parser: { multiCharFreevars: true, numbers: true, gradeUnit, ...(parser || {}) },
      theory,
    });
    // step-checker wiring (TODO_0294/0298): predicate/tag names for the
    // @fire/@draw checkers plus the rule-name → checker bindings — all
    // declared here at the assembly point, never defaulted engine-side
    // (the kernel only routes calculus.stepCheckers; `unit` is the
    // grade-unit thunk)
    const checkers = {};
    if (fire) {
      const { ruleName = 'fire', ...names } = fire;
      calc.fire = Object.freeze({ unit: gradeUnit, ...names });
      checkers[ruleName] = fireChecker;
    }
    if (draw) {
      const { ruleName = 'draw', ...names } = draw;
      calc.draw = Object.freeze({ ...names });
      checkers[ruleName] = drawChecker;
    }
    if (Object.keys(checkers).length) calc.stepCheckers = Object.freeze(checkers);
    return calc;
  };
}

export { ratCanon, makeCalcTables, makeFFIFace, makeTheory, makeForwardParserBuilder, makeSequentLoader };
export default { ratCanon, makeCalcTables, makeFFIFace, makeTheory, makeForwardParserBuilder, makeSequentLoader };

// @ts-check
/**
 * The calculus-config PORT (RES_0143 F1).
 *
 * `cc` is the engine's ports-and-adapters boundary: every piece of
 * calculus knowledge the generic engine consumes arrives through it.
 * This module is the DECLARED contract — one entry per key the engine
 * (lib/engine + the timed/measure layers) reads, with its type, whether
 * it is required, WHO consumes it, and what absence means. Validated
 * fail-fast at the composition root (_requireConfig): a typo'd or
 * unknown key is a load error naming this file, not a silent fallback
 * discovered three layers deep.
 *
 * This replaces the audit's hand-maintained "socket inventory"
 * (RES_0143 §cc socket inventory) with an executable one. Keep the two
 * in sync by keeping only this one.
 *
 * Validation depth is deliberately shallow: top-level presence + types,
 * plus the few nested fields whose absence used to surface as a
 * TypeError mid-load (loader.buildParser, compile.cacheEpoch). Deep
 * shapes are documented here and typed in lib/types.d.ts (F5); runtime
 * enforcement of every nested field would re-implement a type checker.
 */

'use strict';

// type: expected typeof (getters are evaluated — configs memoize).
// required: load fails when absent.
// private: not read by the engine — a calculus-side composition helper
//   allowed to ride the cc object (cross-calculus config reuse).
// consumer/absent: documentation — the living socket inventory.
const CC_SCHEMA = {
  connectives: {
    type: 'object', required: true,
    consumer: 'index/compile/compose/timed',
    doc: 'tag → { category, arity, polarity } from the .calc table',
  },
  loader: {
    type: 'object', required: true,
    consumer: 'convert.js',
    doc: '{ buildParser*, connTags, grade0, timed, qexprPreds } — buildParser is required (the engine holds no parser); timed:true additionally requires qexprPreds',
  },
  compile: {
    type: 'object', required: true,
    consumer: 'index.js (_compileOpts, cache keys)',
    doc: '{ getModes, getModeMeta, discriminatorPreds, cacheEpoch*, profile? } — cacheEpoch namespaces caches; profile overrides the default optimizer profile',
  },
  family: {
    type: 'object',
    consumer: 'index/match (cc.family.engine hooks as data)',
    absent: 'state-lookup-only persistent proving, no dynamic rules/existentials',
    doc: '{ name, engine: { proveNaive, matchDynamicRule, drainDynamicRules, resolveEx } } — each hook nullable',
  },
  init: {
    type: 'function',
    consumer: 'index.js (once per build)',
    absent: 'no kernel-level registration (atoms, theory install)',
  },
  typeCheck: {
    type: 'string',
    consumer: 'index.js',
    absent: 'open-world sort checking',
    doc: "'strict' = closed world; load fails on sort errors",
  },
  theories: {
    type: 'object', // arrays are typeof 'object'
    consumer: 'index.js → kernel setTheories',
    absent: 'kernel defaults only (strlit)',
    doc: 'equational theory list (binlit, ratlit, ...); theories may declare classTags for over-approximation clients',
  },
  gradeUnit: {
    type: 'function',
    consumer: 'compile.js / compose.js',
    absent: 'SELL zero (monadUnit, binlit 0) — the documented shared default',
  },
  gradeConfig: {
    type: 'object',
    consumer: 'index/formula-utils/type-check (resolveConn, deriveGradeMeta)',
    absent: "engine {0,1,ω} atoms (grades.js defaultGradeConfig)",
    doc: '{ grade0: () => hash, gradeOmega: () => hash }',
  },
  backward: {
    type: 'object',
    consumer: 'index.js (backchain opts)',
    absent: 'no calculus backchain bindings (normalize/tryFFI/term builders)',
  },
  ffi: {
    type: 'object',
    consumer: 'index.js (FFI context; opts.dangerouslyUseFFI paths)',
    absent: 'clause-only persistent proving',
    doc: '{ meta, parsedModes, get, isFFIGround, ... }',
  },
  compose: {
    type: 'object',
    consumer: 'index.js (composeOpts)',
    absent: 'grade-0 erasure without fusion/SROA/residual-resolution bindings',
    doc: '{ chainConfigs, sroaConfig, linearFusionPredicate, residualResolver }',
  },
  domain: {
    type: 'object',
    consumer: 'index/forward/explore (display, solver, memo, bytecode hooks)',
    absent: 'no domain policies: solver off, memo off, no bytecode API',
    doc: '{ evalNumeric, constraintPreds, sumPreds, orderDomain, memoControlTags, classifyLeafPolicy, showExclude, loadBytecode, bytecodeToTrie, trieNav, lookupArrayValue, ... }',
  },
  sorts: {
    type: 'object',
    consumer: 'materialize.js',
    absent: 'no refinement-sort system (sortless calculus)',
  },
  datasortMasses: {
    type: 'object',
    consumer: 'materialize.js',
    absent: 'recursive datasorts are a load error (the solver is calculus-bound oracle machinery)',
    doc: 'the mass-solver module record (solveMasses, ...) — calculus/will/lib/datasort-mass.js',
  },
  grades: {
    type: 'object',
    consumer: 'lib/timed (buildTimedConfig gate)',
    absent: 'NO timed API (settle/views/game absent) — the presence gate',
    doc: '{ values*, aggregate, availability, effect, isStamp, parseStamp, parseExtent, canonStamp }',
  },
  factSetPolicy: {
    type: 'object',
    consumer: 'lib/timed (effective policy; stampTable added there)',
    absent: 'default unlabeled FactSet layout',
  },
  stampTag: {
    type: 'string',
    consumer: 'index/compile/lib/timed/lib/measure',
    absent: "'at' (kernel-reserved boundary wrapper)",
  },
  shiftOps: {
    type: 'object',
    consumer: 'lib/timed (covariance/rebase)',
    absent: 'covariance analysis skipped; rebase rejects loudly',
  },
  scheduler: {
    type: 'object',
    consumer: 'lib/timed',
    absent: 'PRF chooser + fifo defaults',
  },
  lintExempt: {
    type: 'object',
    consumer: 'lib/timed (timed-lint machinery predicates)',
    absent: 'no lint exemption set',
  },
  apiExtensions: {
    type: 'object', // array
    consumer: 'index.js (API attacher list, F6)',
    absent: 'no calculus-specific api methods',
    doc: 'array of attach({ api, cc, calc }) → partial-api | null',
  },
  wellModed: {
    type: 'string',
    consumer: 'index.js (well-moded.js enforcement, task #81 / P7)',
    absent: "warn-first: violations land on calc.wellModedLint. 'strict' flips them to a load error (THY_0039 §6)",
  },
  // ── calculus-private keys (never read by the engine; allowed to ride
  // the cc object for cross-calculus config composition) ──
  gradeRegistry: { type: 'object', private: true,
    doc: 'gill: by-sort grade algebra registry (composed by will/sill)' },
  gradeAlgebraFor: { type: 'function', private: true,
    doc: 'gill: sort → grade algebra lookup (composed by will/sill)' },
};

/**
 * Fail-fast validation at the composition root. Checks: unknown
 * top-level keys (typo defense), required keys present, present keys
 * type-correct, and the two nested fields whose absence historically
 * surfaced as mid-load TypeErrors.
 *
 * @param {Object} cc - calculus config
 * @param {string} site - caller label for the error message
 */
function validateCalculusConfig(cc, site) {
  const errors = [];
  for (const key of Object.keys(cc)) {
    if (!CC_SCHEMA[key]) {
      errors.push(`unknown key '${key}' — not a port the engine reads ` +
        `(known: ${Object.keys(CC_SCHEMA).join(', ')}); a calculus-private ` +
        `key must be declared in lib/engine/cc-schema.js`);
    }
  }
  for (const [key, spec] of Object.entries(CC_SCHEMA)) {
    const v = cc[key];
    if (v === undefined || v === null) {
      if (spec.required) errors.push(`missing required key '${key}' (${spec.doc || spec.consumer})`);
      continue;
    }
    if (typeof v !== spec.type) {
      errors.push(`key '${key}': expected ${spec.type}, got ${typeof v}`);
    }
  }
  if (cc.loader && typeof cc.loader === 'object' && typeof cc.loader.buildParser !== 'function') {
    errors.push(`loader.buildParser must be a function — the engine holds no default parser`);
  }
  if (cc.compile && typeof cc.compile === 'object' && typeof cc.compile.cacheEpoch !== 'string') {
    errors.push(`compile.cacheEpoch must be a string — caches are epoch-namespaced per calculus`);
  }
  // family.engine: the four hook slots by exact name (audit periphery —
  // a typo'd hook key, e.g. 'engin' or 'provNaive', silently loses the
  // family's machinery and surfaces as a mid-run TypeError or wrong
  // fallback semantics; the record is small enough to check exactly).
  if (cc.family && typeof cc.family === 'object') {
    const eng = cc.family.engine;
    const HOOKS = ['proveNaive', 'matchDynamicRule', 'drainDynamicRules', 'resolveEx'];
    if (!eng || typeof eng !== 'object') {
      errors.push(`family.engine must be an object carrying the four hook slots (${HOOKS.join('/')} — null for unused)`);
    } else {
      for (const h of HOOKS) {
        if (!(h in eng)) errors.push(`family.engine.${h} is missing — declare it (null for unused)`);
        else if (eng[h] !== null && typeof eng[h] !== 'function') {
          errors.push(`family.engine.${h} must be a function or null`);
        }
      }
      for (const k of Object.keys(eng)) {
        if (!HOOKS.includes(k)) {
          errors.push(`family.engine.${k} is not a hook slot (typo? the slots are ${HOOKS.join('/')})`);
        }
      }
    }
  }
  if (errors.length > 0) {
    throw new Error(`${site}: invalid calculusConfig —\n  ` + errors.join('\n  ') +
      `\n  (the port contract lives in lib/engine/cc-schema.js)`);
  }
  return cc;
}

export { CC_SCHEMA, validateCalculusConfig };
export default { CC_SCHEMA, validateCalculusConfig };

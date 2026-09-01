/**
 * MDE Module - Load and work with MDE/Celf files
 *
 * Minimal API following Unix philosophy:
 * - load(filePath) - load MDE file, returns { definitions, clauses, forwardRules }
 * - parseExpr(src) - parse expression string to hash
 * - prove(goal) - backward chaining proof search
 * - exec(state, rules) - run forward chaining
 */

/**
 * The plug-in calculus contract (round-15 F7). A logic is assembled
 * ENTIRELY from this record — the engine core is calculus-agnostic (D13).
 * Reference instances: lib/engine/ill/calculus-config.js (ILL) and
 * calculus/till/calculus-config.js (till, the timed instance).
 *
 * REQUIRED for any forward logic:
 * @typedef {Object} CalculusConfig
 * @property {Object} connectives   tag → { category, arity, polarity } —
 *   drives resolveConn role derivation (product/implication/choices/
 *   exponential/computation)
 * @property {Object} compile       { getModes, getModeMeta?,
 *   discriminatorPreds, cacheEpoch } — mode table for FFI/existential
 *   output detection; epoch namespaces the compile cache per calculus
 * @property {Object} loader        { buildParser, connTags, grade0?,
 *   timed? } — parser factory + the tag names convert.js decomposes with
 *
 * REQUIRED additionally for a TIMED logic (presence of `grades` gates the
 * settle/choose/menuStatus API):
 * @property {Object} [grades]      { availability: {cmp, join}, effect:
 *   {unit, compose, sub}, isStamp, parseStamp, canonStamp? } — the ONE
 *   grade algebra both the scheduler and the sequent prover read (D13:
 *   one algebra, two faces)
 * @property {Function} [gradeUnit] () → hash — the `{B}` sugar grade
 * @property {Object} [factSetPolicy] { groupKey, cmp } — linear-zone
 *   index policy (stamp-sorted FIFO for till); the index is optimization,
 *   the multiset is semantics
 * @property {Object} [scheduler]   { chooser, seed, cohort } — D12/D17
 *   within-instant policies (defaults: PRF chooser, fifo)
 *
 * OPTIONAL (defaults apply):
 * @property {Function} [init]      global setup: Store atoms, setTheories,
 *   classifier installs — MUST register any equational theories the
 *   forward matcher needs (B6)
 * @property {Array}   [theories]   equational theories (cross-tag match)
 * @property {Object}  [gradeConfig] { grade0, gradeOmega } grade atoms
 * @property {string}  [typeCheck]  'strict' → closed-world sort checking
 * @property {Object}  [backward]   backchainer hooks { normalize, tryFFI,
 *   getFFIMeta, buildClauseTerm, buildFFITerm, buildTypeTerm }
 * @property {Object}  [ffi]        FFI registry { meta, parsedModes, get,
 *   isFFIGround } — optimization only; clauses are the semantics
 * @property {Object}  [compose]    grade-0 staging pipeline (ILL-only
 *   until 0157 — compose.js still hardcodes ILL tags)
 * @property {Object}  [domain]     display/memo policy { memoControlTags,
 *   classifyLeaf, showExclude, ... }
 */

import convert from './convert.js';
import forward from './forward.js';
import explore from './explore.js';
import timed from './timed/timed.js';
import { lintProductivity, lintChainCollapse, lintHypothesisS, lintWholeBind } from './timed/timed-lint.js';
import { certifyContention } from './timed/certify.js';
import game from './timed/timed-game.js';
import views from './timed/timed-views.js';
import backward from './backchain.js';
import Store from '../kernel/store.js';
import { serialize, deserialize, compact } from './store-binary.js';
import { hashCombine, hashString } from '../hash.js';
import { profile, engine } from './optimizer.js';
import { engineVersion } from './engine-version.js';
import { cacheFlagFingerprint } from './cache-flags.js';
import { ensureVersionTag, lruEvict, DEFAULT_MAX_BYTES } from './cache-evict.js';
import crypto from 'crypto';
import zlib from 'zlib';
import fs from 'fs';
import path from 'path';
import os from 'os';
import _defaultCalcConfig from './ill/calculus-config.js';
// Hoisted by tools/esm-hoist.js:
import { compilePS as _compilePS, execPS as _execPS } from './opt/ffi.js';
import { buildTheoryLookup, buildCanonicalizer, defaultTheories as _defaultTh } from '../kernel/eq-theory.js';
import { compose0 } from './compose.js';
import { checkAll } from './type-check.js';
import { buildSortSystem, SORT_PREDS } from './sorts.js';
import { checkPriors } from './priors.js';
import { putRat } from '../kernel/rat-term.js';
import decimate from './decimate.js';
import { resolve as resolveAll } from './resolve-all.js';
import { _validateArity } from './opt/ffi.js';
import { clauseDispatch } from './opt/compiled-clauses.js';
import { compileExChain, execExStep as _execExStep } from './opt/existential-compile.js';
import { resolveConn as _resolveConn } from './formula-utils.js';
import _match from './match.js';
import { drainLolis as _drainLolis } from './lnl/loli-drain.js';
import { matchLoli as _matchLoli } from './lnl/loli.js';
import { resolveEx as _resolveEx } from './lnl/existential.js';
import { proveNaive as _proveNaive } from './lnl/persistent.js';
import { proveWithFFI as _proveWithFFI, ffiDirect as _ffiDirect } from './opt/ffi.js';
import { tryCCDispatch as _tryCCDispatch } from './opt/compiled-clauses.js';
import { predictNext as _predictNext } from './opt/prediction.js';
import _structuralMemoFns from './opt/structural-memo.js';
import { fpDetect as _fpDetect, fpLayer as _fpLayer, attachPred as _attachPred } from './opt/fingerprint.js';
import { createRequire } from 'module';

// Bytecode loader (EVM domain) is loaded lazily — only when the caller
// passes opts.bytecode. require(ESM) is synchronous (Node >= 22), which
// keeps load() sync while decoupling the module graph from ill/ for
// non-bytecode callers (TODO_0265 Phase 2b).
const _require = createRequire(import.meta.url);
let _bytecodeLoader = null;
function _getBytecodeLoader() {
  if (!_bytecodeLoader) _bytecodeLoader = _require('./ill/bytecode-loader.js');
  return _bytecodeLoader;
}

/**
 * Rule-compilation opts derived from a calculus config (TODO_0265 Phase 3,
 * B3: every compile site threads the ACTIVE config — the former
 * _illCompileOpts constant silently compiled non-ILL loads as ILL).
 */
function _compileOpts(cc) {
  return {
    connectives: cc.connectives,
    getModes: cc.compile.getModes,
    discriminatorPreds: cc.compile.discriminatorPreds,
    cacheEpoch: cc.compile.cacheEpoch,
    gradeConfig: cc.gradeConfig,
    // Stamp wrapper tag (timed calculi); undefined ⇒ compile defaults to 'at'.
    stampTag: cc.stampTag,
    // Unit of the computation grade — grades equal to it compile to NO
    // delay slot (a graded-but-undelayed rule stays untimed, Phase 4).
    gradeUnit: cc.gradeUnit,
  };
}

// ─── Compose disk cache ─────────────────────────────────────────────────────
//
// Persists full post-compose Store snapshot to disk using store-binary format.
// On cache hit, Store.restore() replaces parsing AND compose — cold E2E becomes
// ~40ms (restore + compileRule) instead of ~210ms (parse + compile + compose).
//
// Cache key: SHA-256(canonical string of tree hashes, bytecode hex, opts,
// engineVersion, cache-flag fingerprint, snapshot-format version).
// Snapshot metadata contains definitions, clauses, queries, final rule list,
// and SELL infrastructure so _buildCalc can run with skipCompose: true.

const COMPOSE_DISK_VERSION = 3;

// Read a snapshot file: open, gunzip-if-gzipped (magic 0x1f 0x8b), deserialize.
// Caller is responsible for Store.restore() and metadata validation.
function _readSnapshotFile(filePath) {
  let buf = fs.readFileSync(filePath);
  if (buf[0] === 0x1f && buf[1] === 0x8b) buf = zlib.gunzipSync(buf);
  return deserialize(buf);
}

/**
 * Compute compose disk cache key.
 *
 * Closes hazards H7 (bytecode API — content-hash of hex bytes, no
 * caller-declared scopeGuard ID), H8 (flag registry — cacheFlagFingerprint),
 * H9 (engine version — content-hash of lib/).
 *
 * @param {Map} treeHashes      manifest[path → contentHash]
 * @param {string} absPath      root file absolute path
 * @param {string|null} bcHex   bytecode hex (or null if no bytecode input)
 * @param {Object} flagOpts     compose-affecting opts (fuseBasicBlocks, cacheVersion)
 */
function _composeCacheKey(treeHashes, absPath, bcHex, flagOpts) {
  const parts = [
    'ev=' + engineVersion(),
    'file=' + String(treeHashes.get(absPath) | 0),
  ];
  if (bcHex) {
    const bcH = crypto.createHash('sha256').update(bcHex).digest('hex').slice(0, 16);
    parts.push('bc=' + bcH);
  }
  parts.push(cacheFlagFingerprint(flagOpts || {}));
  parts.push('v=' + COMPOSE_DISK_VERSION);
  return crypto.createHash('sha256').update(parts.join(';')).digest('hex').slice(0, 16);
}

// Priors table (BigInt pairs) ↔ JSON ('n/d' strings) for cache metadata.
const _serPriors = (m) => (m && m.size)
  ? Object.fromEntries([...m].map(([k, [n, d]]) => [k, `${n}/${d}`])) : {};
const _desPriors = (o) => new Map(Object.entries(o || {}).map(([k, v]) => {
  const [n, d] = v.split('/');
  return [k, [BigInt(n), BigInt(d)]];
}));

/**
 * Save full post-compose Store snapshot to disk.
 * Includes all metadata needed to reconstruct the calc context without
 * reparsing or recomposing.
 */
function _saveCSnap(cachePath, calc, definitions, clauses, queries,
    argNamesTable, querySettings, splitQueries, moduleDecls, rootLabel, labelDeps, sortVarsTable) {
  try {
    const metadata = {
      _composeCache: COMPOSE_DISK_VERSION,
      sortVarsTable: sortVarsTable ? Object.fromEntries(sortVarsTable) : {},
      types: Object.fromEntries(definitions),
      clauses: Object.fromEntries(
        Array.from(clauses.entries()).map(([k, v]) => [k, v])
      ),
      // Final rule list (post-compose): name + hash + sourceLabel
      forwardRules: calc._compiledRules.map(r => ({
        name: r.name, hash: r.hash, sourceLabel: r.sourceLabel || null
      })),
      queries: Object.fromEntries(queries),
      argNamesTable: argNamesTable ? Object.fromEntries(argNamesTable) : {},
      querySettings: querySettings
        ? Object.fromEntries([...querySettings].map(([k, v]) => [k, v])) : {},
      splitQueries: splitQueries
        ? Object.fromEntries([...splitQueries].map(([k, v]) => [k, v])) : {},
      moduleDecls: moduleDecls || [],
      rootLabel: rootLabel || null,
      priors: _serPriors(calc.priors),
      labelDeps: labelDeps
        ? Object.fromEntries([...labelDeps].map(([k, v]) => [k, [...v]])) : {}
    };
    const snap = Store.snapshot(metadata);
    const bin = compact(snap);
    const buf = serialize(bin);
    fs.mkdirSync(path.dirname(cachePath), { recursive: true });
    // Atomic write: tmpfile + rename. Prevents partial-write corruption when
    // concurrent readers race with a writer (rename() is atomic on POSIX).
    const tmpPath = `${cachePath}.tmp.${process.pid}.${Date.now()}`;
    fs.writeFileSync(tmpPath, buf);
    fs.renameSync(tmpPath, cachePath);
  } catch (e) {
    // Non-fatal — fresh parse+compose on next load
  }
}

/**
 * Load post-compose Store snapshot from disk.
 * Returns calc context or null on miss/corruption.
 */
function _loadCSnap(cachePath, sellOpts) {
  try {
    if (!fs.existsSync(cachePath)) return null;
    const data = _readSnapshotFile(cachePath);
    if (!data.metadata || data.metadata._composeCache !== COMPOSE_DISK_VERSION) return null;
    Store.restore(data);

    const meta = data.metadata;
    const definitions = new Map(Object.entries(meta.types));
    const clauses = new Map(Object.entries(meta.clauses));
    const queries = new Map(Object.entries(meta.queries));
    const argNamesTable = meta.argNamesTable
      ? new Map(Object.entries(meta.argNamesTable)) : new Map();
    const sortVarsTable = meta.sortVarsTable
      ? new Map(Object.entries(meta.sortVarsTable)) : new Map();
    const querySettings = meta.querySettings
      ? new Map(Object.entries(meta.querySettings)) : new Map();
    const splitQueries = meta.splitQueries
      ? new Map(Object.entries(meta.splitQueries)) : new Map();
    const moduleDecls = meta.moduleDecls || [];
    const rootLabel = meta.rootLabel || (sellOpts && sellOpts.rootLabel) || null;
    const labelDeps = meta.labelDeps
      ? new Map(Object.entries(meta.labelDeps).map(([k, v]) => [k, new Set(v)]))
      : (sellOpts && sellOpts.labelDeps) || new Map();

    // Reconstruct raw forward rules from stored name+hash pairs
    const forwardRules = meta.forwardRules.map(r => ({
      name: r.name,
      hash: r.hash,
      antecedent: Store.child(r.hash, 0),
      consequent: Store.child(r.hash, 1),
      sourceLabel: r.sourceLabel || null
    }));

    // Call _buildCalc with skipCompose — compose is already baked into forwardRules
    return _buildCalc(definitions, clauses, forwardRules, queries, {
      argNamesTable, sortVarsTable, rootLabel, labelDeps, querySettings, splitQueries, moduleDecls,
      priorsTable: _desPriors(meta.priors),
      skipCompose: true
    });
  } catch (e) {
    // Corrupted — delete and fall through to fresh load
    try { fs.unlinkSync(cachePath); } catch {}
    return null;
  }
}

/**
 * Verify that cold and cached loads agree on the compose output. Compares rule
 * names (rule order + identity) — the structural contract the cache depends on.
 * Hash equality is not required because restore may renumber Store IDs after
 * compact(); the rule-name sequence is the invariant.
 */
function _verifyEq(cold, cached) {
  const coldNames = cold._compiledRules.map(r => r.name);
  const cachedNames = cached._compiledRules.map(r => r.name);
  if (coldNames.length !== cachedNames.length) {
    throw new Error(`CALC_CACHE_VERIFY: rule count divergence — cold=${coldNames.length} cached=${cachedNames.length}`);
  }
  for (let i = 0; i < coldNames.length; i++) {
    if (coldNames[i] !== cachedNames[i]) {
      throw new Error(`CALC_CACHE_VERIFY: rule[${i}] name divergence — cold='${coldNames[i]}' cached='${cachedNames[i]}'`);
    }
  }
}

// ─── Shared helpers ─────────────────────────────────────────────────────────

/**
 * Build calc context from loaded data (shared by all load paths)
 * @param {Object} [opts]
 * @param {Array} [opts.compiledRules] - pre-compiled rules from cache
 * @param {string} [opts.rootLabel] - label for the root file (D3: always participates)
 * @param {Map} [opts.labelDeps] - label → Set<label> transitive deps
 * @param {Map} [opts.querySettings] - directive settings per query kind
 * @param {Map} [opts.splitQueries] - separated queries (|- or =>) per directive kind
 * @param {Array} [opts.moduleDecls] - @module declarations to resolve
 */
function _buildCalc(definitions, clauses, forwardRules, queries, opts = {}) {
  const onPhase = opts.onPhase || null;
  const _phaseStart = () => onPhase ? performance.now() : 0;
  const _phaseEnd = (name, t, meta) => { if (onPhase) onPhase(name, performance.now() - t, meta); };

  const cc = opts.calculusConfig || _defaultCalcConfig;
  const connectives = opts.connectives || cc.connectives;

  const argNamesTable = opts.argNamesTable || new Map();
  const sortVarsTable = opts.sortVarsTable || new Map();
  const querySettings = opts.querySettings || new Map();
  const splitQueries = opts.splitQueries || new Map();

  // Initialize calculus-specific atoms + equational theories (idempotent)
  if (cc.init) cc.init();

  // Use cached compiled rules or compile from scratch
  // Derive canonicalize + theoryLookup from calculus config theories

  const _allTheories = [..._defaultTh, ...(cc.theories || [])];
  const canonicalize = buildCanonicalizer(_allTheories);

  const _tRuleCompile = _phaseStart();
  const _preCompiled = !!opts.compiledRules;
  let compiledRules = opts.compiledRules || forwardRules.map(r => forward.compileRule(r, _compileOpts(cc)));
  _phaseEnd('load/rule-compile', _tRuleCompile, {
    rules: compiledRules.length,
    rawRules: forwardRules.length,
    preCompiled: _preCompiled,
  });

  // Grade-0 cut elimination: compose grade-0 rules before runtime (THY_0015)
  // skipCompose: set by compose disk cache when restoring pre-composed rules
  if (!opts.skipCompose) {
    const hasGrade0Rules = compiledRules.some(r => r.hasGrade0);
    const hasGrade0Clauses = clauses && [...clauses.values()].some(c => c.grade0);
    if (hasGrade0Rules || hasGrade0Clauses || opts.extraGrade0Facts) {

      // A config without a compose slot can still reach this branch via
      // grade-0 content — degrade gracefully instead of TypeError
      // (audit round 12, F3). NOTE: compose's rule-hash builder still
      // hardcodes ILL tags (loli/bang/monad/tensor) — a non-ILL calculus
      // with grade-0 rules is NOT yet supported (recorded residue).
      const _ccCompose = cc.compose || {};
      const composeOpts = {};
      if (opts.residualResolver) {
        composeOpts.residualResolver = opts.residualResolver;
      } else if (opts.extraGrade0Facts) {
        composeOpts.residualResolver = _ccCompose.residualResolver;
      }
      // Compose pipeline config from calculus config
      if (opts.fuseBasicBlocks) composeOpts.fuseBasicBlocks = opts.fuseBasicBlocks;
      if (opts.fusionBarriers) composeOpts.fusionBarriers = opts.fusionBarriers;
      if (opts.skipSpecialize) composeOpts.skipSpecialize = true;
      composeOpts.chainFusionPredicates = opts.chainFusionPredicates || _ccCompose.chainConfigs;
      composeOpts.linearFusionPredicate = opts.linearFusionPredicate || _ccCompose.linearFusionPredicate;
      composeOpts.sroaConfig = opts.sroaConfig || _ccCompose.sroaConfig;
      composeOpts.canonicalize = canonicalize;
      composeOpts.backchainOpts = { theories: _allTheories };
      // FFI fast path for tabling's ground goals (le/lt/plus/inc/...).
      // Without this, every ground arithmetic goal in a grade-0 clause's
      // premises falls through to backward.prove (~120 µs/call) instead of
      // the O(1) FFI handler (<1 µs/call).
      if (cc.ffi) {
        composeOpts.ffiContext = {
          meta: cc.ffi.meta,
          parsedModes: cc.ffi.parsedModes,
          get: cc.ffi.get,
          isFFIGround: cc.ffi.isFFIGround,
        };
        composeOpts.ffiDirect = _ffiDirect;
      }
      if (onPhase) composeOpts.onPhase = onPhase;
      const _tCompose = _phaseStart();
      const composeResult = compose0(compiledRules, connectives, cc.compile.getModeMeta, clauses, definitions, opts.extraGrade0Facts || null, opts.scopeGuard || null, composeOpts);
      const _d = composeResult.diagnostics || {};
      _phaseEnd('load/compose', _tCompose, {
        composedRules: (composeResult.composedRules || []).length,
        removedRules: composeResult.removedNames ? composeResult.removedNames.size : 0,
        pairsAttempted: _d.pairsAttempted || 0,
        pairsSucceeded: _d.pairsSucceeded || 0,
        pairsSkipped: _d.pairsSkipped || 0,
        specializations: _d.specializations || 0,
        tablings: _d.tablings || 0,
        scopeGuarded: _d.scopeGuarded || 0,
        residualResolutions: _d.residualResolutions || 0,
        fusedRuleReduction: _d.fusedRuleReduction || 0,
        fuseChainLengths: _d.fuseChainLengths || [],
        sroaTransformed: _d.sroaTransformed || 0,
        mccarthyNormalized: _d.mccarthyNormalized || 0,
        grade0Predicates: (_d.grade0Predicates || []).length,
        errors: (_d.errors || []).length,
      });
      if (composeResult.diagnostics.errors.length > 0) {
        for (const e of composeResult.diagnostics.errors) {
          if (typeof process !== 'undefined') process.stderr.write(`compose: ${e}\n`);
          else console.error(`compose: ${e}`);
        }
        if (opts.strict) throw new Error(`Grade-0 composition failed: ${composeResult.diagnostics.errors.length} error(s)`);
      }
      if (composeResult.composedRules.length > 0) {
        const _cOpts = _compileOpts(cc);
        const composedCompiled = composeResult.composedRules.map(
          r => forward.compileRule(r, _cOpts)
        );
        compiledRules = [...compiledRules, ...composedCompiled];
      }
      if (composeResult.removedNames && composeResult.removedNames.size > 0) {
        compiledRules = compiledRules.filter(r => !composeResult.removedNames.has(r.name));
      }
    }
  }

  // Sort-check declarations + rules (load-time only, zero runtime cost)

  // Refinement-sort system (TODO_0011 rung 1) — presence-gated twice:
  // the CALCULUS opts in via cc.sorts (till), and the PROGRAM opts in by
  // declaring sort content (subsorts/classifiers/sort variables). Absent
  // on either side ⇒ the sortless string checker, bit-identical to before.
  const _tSorts = _phaseStart();
  let sortSystem = null;
  if (cc.sorts) {
    sortSystem = buildSortSystem({
      definitions, clauses, sortVarsTable,
      calc: cc.sorts.calc, lit: cc.sorts.lit,
      connArgSorts: cc.sorts.connArgSorts, formulaSort: cc.sorts.formulaSort,
    });
  } else if (Store.TAG[SORT_PREDS.EDGE] !== undefined) {
    for (const [cname, c] of clauses) {
      if (Store.tagId(c.hash) === Store.TAG[SORT_PREDS.EDGE]) {
        throw new Error(`'${cname}': subsort declarations need a calculus with a sorts config (cc.sorts) — this calculus is sortless`);
      }
    }
  }
  // Materialized closure (TODO_0011 §4): inject every strict subsort pair
  // as a ground `subsort a b` fact. With `subsort/refl` in the prelude,
  // in-logic queries (`!subsort X resource` premises) are answered totally
  // by fact lookup — the committed-choice completeness caveat of a
  // recursive closure clause is gone, not worked around. Runs BEFORE
  // checkAll (facts get sort-checked like sedge facts) and before
  // buildIndex (queries see them); idempotent on cache-restore re-entry
  // (same names, same content-addressed hashes).
  if (sortSystem && definitions.has(SORT_PREDS.SUB)) {
    for (const [a, b] of sortSystem.closurePairs()) {
      // Separator is `/` (not `_`): sort names can't contain `/`, so the key
      // is collision-free even for underscore-named sorts — `(foo, bar_x)` and
      // `(foo_bar, x)` would both key to `subsort/foo_bar_x` under `_`, silently
      // dropping one materialized closure fact.
      clauses.set(`${SORT_PREDS.SUB}/${a}/${b}`, {
        hash: Store.put(SORT_PREDS.SUB,
          [Store.put('atom', [a]), Store.put('atom', [b])]),
        premises: [],
      });
    }
  }
  _phaseEnd('load/sort-system', _tSorts, {
    present: !!sortSystem,
    sorts: sortSystem ? sortSystem.sorts.size : 0,
    edges: sortSystem ? sortSystem.edges.length : 0,
    classifiers: sortSystem ? sortSystem.classifiers.size : 0,
  });

  // Constructor priors `name: sort @w Q.` (TODO_0292 D5/M6, will P1):
  // validated against the sort system; Chi–Geman subcriticality (T2) is
  // a load-time ADVISORY (M7 — the decimation driver, not the loader,
  // hard-errors on supercritical priors without a depth bound).
  const priorsTable = opts.priorsTable || new Map();
  let priorAdvice = [];
  if (priorsTable.size > 0) {
    const pr = checkPriors(priorsTable, sortSystem, definitions);
    if (pr.errors.length > 0) {
      throw new Error(`Priors: ${pr.errors.join('; ')}`);
    }
    priorAdvice = pr.advice;
    for (const a of priorAdvice) {
      console.warn(`priors lint (T2): sort '${a.sort}' is supercritical (m = ${a.m.toFixed(3)} > 1) — lazy collapse over it diverges with positive probability (Chi–Geman); rebalance @w or pass the driver an explicit depth bound`);
    }
  }
  // Materialized priors (TODO_0298 item 1b): mirror the subsort closure —
  // for every classifier TOUCHED by @w (checkPriors's discipline), every
  // member's ratio (default 1: totality over the touched sort, matching
  // the decimation consumer) becomes a ground `prior s c ρ` fact, so
  // in-logic `!prior S C W` premises and the clause-only draw
  // verification path are total fact lookups. Presence-gated twice: the
  // PROGRAM declares the predicate (the bias discipline — machinery
  // predicates are program-declared with the program's own sorts) AND
  // annotates at least one member of the sort (`m: s @w 1.` opts an
  // otherwise-unannotated sort in). Runs before checkAll — facts get
  // sort-checked like sedge facts.
  if (sortSystem && definitions.has('prior') && priorsTable.size > 0) {
    for (const [s, members] of sortSystem.classifiers) {
      let touched = false;
      for (const m of members) if (priorsTable.has(m)) { touched = true; break; }
      if (!touched) continue;
      for (const m of members) {
        const w = priorsTable.get(m) || [1n, 1n];
        clauses.set(`prior/${s}/${m}`, {
          hash: Store.put('prior', [Store.put('atom', [s]), Store.put('atom', [m]), putRat(w[0], w[1])]),
          premises: [],
        });
      }
    }
  }

  const _tTypeCheck = _phaseStart();
  // Strictness comes from the CALCULUS (cc.typeCheck: 'strict' — till) or
  // the caller; strict = closed world (undeclared symbols are errors) and
  // load FAILURE on any sort error, not stderr noise.
  const _strictTypes = opts.strictTypes !== undefined
    ? opts.strictTypes : cc.typeCheck === 'strict';
  // CALC_SORT_AUDIT=1: closed-world checking everywhere, NON-fatal — the
  // measuring instrument for auditing an open-world corpus (ILL) before
  // flipping it strict.
  const _sortAudit = typeof process !== 'undefined' && process.env.CALC_SORT_AUDIT === '1';
  const diagnostics = checkAll(definitions, compiledRules, clauses,
    { ...opts, closedWorld: _strictTypes || _sortAudit, strict: false,
      sorts: sortSystem,
      queries: (_strictTypes || _sortAudit) ? splitQueries : undefined });
  if (_sortAudit && !_strictTypes && diagnostics.errors.length > 0) {
    for (const e of new Set(diagnostics.errors)) process.stderr.write(`sort-audit: ${e}\n`);
  }
  _phaseEnd('load/type-check', _tTypeCheck, {
    rules: compiledRules.length,
    definitions: definitions.size,
    clauses: clauses ? clauses.size : 0,
    errors: (diagnostics.errors || []).length,
    warnings: (diagnostics.warnings || []).length,
  });
  if (diagnostics.errors.length > 0) {
    if (_strictTypes || opts.strict) {
      throw new Error(`Sort checking failed (${diagnostics.errors.length} error(s)):\n  ${diagnostics.errors.join('\n  ')}`);
    }
    for (const e of diagnostics.errors) {
      if (typeof process !== 'undefined') process.stderr.write(`type-check: ${e}\n`);
      else console.error(`type-check: ${e}`);
    }
  }

  // Build backward prover index once at load time (2x speedup)
  const _tBackIdx = _phaseStart();
  const backchainIndex = backward.buildIndex(clauses, definitions);
  _phaseEnd('load/backchain-index', _tBackIdx, {
    clauses: clauses ? clauses.size : 0,
    definitions: definitions.size,
    indexedPredicates: backchainIndex && backchainIndex.byPred
      ? (backchainIndex.byPred instanceof Map ? backchainIndex.byPred.size : Object.keys(backchainIndex.byPred).length)
      : 0,
  });

  // Build FFI context from calculus config (injected into compile + runtime)
  const ffiContext = cc.ffi ? {
    meta: cc.ffi.meta,
    parsedModes: cc.ffi.parsedModes,
    get: cc.ffi.get,
    isFFIGround: cc.ffi.isFFIGround,
  } : null;
  const _ffiPM = ffiContext ? ffiContext.parsedModes : null;
  // Validate FFI arity bounds at build time (moved from opt/ffi.js lazy path)
  if (_ffiPM) {

    _validateArity(_ffiPM);
  }

  // Build compiled clause dispatch (Tier 1 base cases + Tier 2 recursive)

  const theoryLookup = buildTheoryLookup(_allTheories);
  const _tDispatch = _phaseStart();
  const dispatch = clauseDispatch(backchainIndex, _ffiPM);
  _phaseEnd('load/clause-dispatch', _tDispatch, {
    ffiEnabled: !!_ffiPM,
    dispatchEntries: dispatch
      ? (dispatch instanceof Map ? dispatch.size : (typeof dispatch === 'object' ? Object.keys(dispatch).length : 0))
      : 0,
  });

  // Backward opts from calculus config (threaded to backchain.js)
  const backwardOpts = cc.backward ? {
    normalize: cc.backward.normalize,
    tryFFI: cc.backward.tryFFI,
    getFFIMeta: cc.backward.getFFIMeta,
    buildClauseTerm: cc.backward.buildClauseTerm,
    buildFFITerm: cc.backward.buildFFITerm,
    buildTypeTerm: cc.backward.buildTypeTerm,
    theories: _allTheories,
  } : null;

  // Domain config from calculus config (EVM-specific)
  const domainConfig = cc.domain || null;

  // Capture calc context for backward proving + engine dispatch
  const calcContext = {
    definitions, clauses, backchainIndex, connectives,
    clauseDispatch: dispatch, theoryLookup, canonicalize,
    ffiContext, backwardOpts, domainConfig,
    theories: _allTheories,
  };

  // Generate compiled persistent steps per rule (after calcContext — specs need dispatch table)
  const _tPersSteps = _phaseStart();
  let _rulesWithSteps = 0;
  let _totalSteps = 0;
  let _compiledSteps = 0;
  for (const rule of compiledRules) {
    const persistentPats = rule.antecedent.persistent || [];
    if (persistentPats.length === 0) continue;
    const steps = persistentPats.map(p => _compilePS(p, rule.metavarSlots, calcContext, ffiContext));
    _totalSteps += steps.length;
    for (const s of steps) { if (s !== null) _compiledSteps++; }
    if (steps.some(s => s !== null)) { rule.persistentSteps = steps; _rulesWithSteps++; }
  }
  _phaseEnd('load/persistent-steps', _tPersSteps, {
    totalRules: compiledRules.length,
    rulesWithSteps: _rulesWithSteps,
    totalSteps: _totalSteps,
    compiledSteps: _compiledSteps,
  });

  // Compile existential chains (direct FFI for ∃-goals, bypasses provePersistent)

  const _tExChain = _phaseStart();
  let _rulesWithChains = 0;
  for (const rule of compiledRules) {
    const chain = compileExChain(rule, ffiContext);
    if (chain) { rule._compiledExChain = chain; _rulesWithChains++; }
  }
  _phaseEnd('load/ex-chains', _tExChain, {
    totalRules: compiledRules.length,
    rulesWithChains: _rulesWithChains,
  });

  // ── Composition root: resolve ALL layer callbacks ──
  // The orchestrator (this module) is the single point that has visibility
  // into all layers. By pre-resolving these callbacks, forward.js/explore.js
  // receive fully-configured opts and never need cross-layer requires —
  // achieving the LCF kernel property that inner layers are parameterized
  // by, not dependent on, outer layers.


  // LNL layer




  // opt layer





  const _rc = _resolveConn(connectives, cc.gradeConfig);

  /** Build per-call matchOpts with all layer callbacks injected.
   *  Layer provenance: each protocol factory documents which layer provides which fields.
   */
  function _buildMatchOpts(execOpts) {
    const useFFI = execOpts.dangerouslyUseFFI || false;
    return _match.buildMatchOpts({
      ..._match.buildGenericProtocol({
        optimizePreserved: execOpts.optimizePreserved !== false,
        evidence: execOpts.evidence || false,
        canonicalize,
        onProveFail: execOpts.onProveFail,
        onProveSuccess: execOpts.onProveSuccess,
        // Route the persistent-proving interface: FFI-accelerated vs naive clause prover.
        // Wiring decision belongs at the composition root, not a single-field factory.
        provePersistent: useFFI ? _proveWithFFI : _proveNaive,
      }),
      ..._match.buildLnlProtocol({
        matchLoli: _matchLoli,
        resolveEx: _resolveEx,
        drainLolis: _drainLolis,
        rc: _rc,
        // Production default: FFI-on for backward-clause arithmetic unless
        // the caller explicitly opts out (`useFFI: false`). The factory
        // default is `false` (platonic empty) — the pragmatic default lives
        // here because only the composition root sees the full execOpts.
        backchainUseFFI: execOpts.useFFI !== false,
      }),
      ..._match.buildOptProtocol({
        execPS: _execPS,
        execExStep: _execExStep,
        tryCCDispatch: _tryCCDispatch,
        useCompiledSteps: useFFI,
      }),
      ..._match.buildFfiProtocol(ffiContext),
    });
  }

  // Create engine with profile-driven function pointers (fingerprint injected)
  const _tEngineInit = _phaseStart();
  const prof = profile(opts.profile);
  const eng = engine(prof, compiledRules, {
    fpDetect: _fpDetect, fpLayer: _fpLayer, attachPred: _attachPred,
  });
  _phaseEnd('load/engine-init', _tEngineInit, {
    rules: compiledRules.length,
    profile: opts.profile || 'default',
  });

  // ── SELL label infrastructure (T7) ──
  const rootLabel = opts.rootLabel || null;
  const labelDeps = opts.labelDeps || new Map();

  // Build label index: label → [ruleName, ...]
  const _tLabelIdx = _phaseStart();
  const labelIndex = new Map();
  for (const r of compiledRules) {
    const label = r.sourceLabel || 'unknown';
    if (!labelIndex.has(label)) labelIndex.set(label, []);
    labelIndex.get(label).push(r.name);
  }
  _phaseEnd('load/label-index', _tLabelIdx, {
    labels: labelIndex.size,
    rules: compiledRules.length,
    unlabeled: (labelIndex.get('unknown') || []).length,
  });

  // resolveLabels(['evm']) → Set{'evm', 'bin', 'bool', ...} (+ transitive deps)
  function resolveLabels(requestedLabels) {
    const resolved = new Set();
    for (const label of requestedLabels) {
      resolved.add(label);
      for (const dep of labelDeps.get(label) || []) resolved.add(dep);
    }
    return resolved;
  }

  // ── Tier 2: Module resolution (T13) ──
  const moduleDecls = opts.moduleDecls || [];
  const modules = new Map(); // name → Set<ruleName>
  for (const decl of moduleDecls) {
    modules.set(decl.name, _resolveModule(decl.expr, labelIndex, modules, resolveLabels));
  }

  // ── Shared rule filtering — Tier 1 (label list) + Tier 2 (module name) + grade-0 exclusion ──
  // The no-filter result is memoized: settle-per-tick callers (TODO_0277)
  // get one STABLE array, so per-list caches (coalesce observers) hit and
  // no O(#rules) filter allocation runs per call.
  let _allRuntimeRules = null;
  function filterRules(execOpts) {
    let rules = compiledRules;

    // Grade-0 exclusion: rules with grade-0 antecedent/consequent patterns are
    // compile-time only (SELL/QTT convention). Grade-0 non-interference guarantees
    // these have no runtime effect (Choudhury et al. POPL 2021, Lemma 6.2).
    // See THY_0015 for stratified cut elimination by grade.
    if (!execOpts.rules) {
      if (!_allRuntimeRules) _allRuntimeRules = rules.filter(r => !r.hasGrade0);
      return _allRuntimeRules;
    }
    rules = rules.filter(r => !r.hasGrade0);

    if (Array.isArray(execOpts.rules)) {
      // Tier 1: list of labels → resolve transitive deps → filter by sourceLabel
      const allowedLabels = resolveLabels(execOpts.rules);
      // Validate labels
      for (const label of execOpts.rules) {
        if (!labelIndex.has(label) && !labelDeps.has(label)) {
          const known = [...labelIndex.keys()].join(', ');
          throw new Error(`Unknown rule label: '${label}'. Known labels: ${known}`);
        }
      }
      if (rootLabel) allowedLabels.add(rootLabel); // D3: root always participates
      return rules.filter(r => allowedLabels.has(r.sourceLabel));
    }

    if (typeof execOpts.rules === 'string') {
      // D7: check modules first, fall back to label
      const moduleNames = modules.get(execOpts.rules);
      if (moduleNames) {
        // Tier 2: module name → resolved set of rule names
        const allowedNames = new Set(moduleNames); // copy — don't mutate canonical set
        // D3: root file rules always participate
        if (rootLabel) {
          for (const n of (labelIndex.get(rootLabel) || [])) allowedNames.add(n);
        }
        return rules.filter(r => allowedNames.has(r.name));
      }
      // Fallback: treat as single label (Tier 1)
      if (!labelIndex.has(execOpts.rules) && !labelDeps.has(execOpts.rules)) {
        const known = [...labelIndex.keys(), ...modules.keys()].join(', ');
        throw new Error(`Unknown rule label or module: '${execOpts.rules}'. Known: ${known}`);
      }
      const allowedLabels = resolveLabels([execOpts.rules]);
      if (rootLabel) allowedLabels.add(rootLabel);
      return rules.filter(r => allowedLabels.has(r.sourceLabel));
    }

    return rules;
  }

  // ── Timed scheduler API (TODO_0265 Phase 4) ──
  // A calculus with a grade algebra (cc.grades: availability order + effect
  // monoid over stamps) gets settle/nextActivation/settleExplore and the
  // read-only views. ILL declares no grades slot → no timed API; the timed
  // matcher OWNS window/count/delay evaluation, so these rules never reach
  // forward.run's untimed intake (its guard stays loud).
  let _timedApi = null;
  if (cc.grades) {
    const _tcfg = timed.buildTimedConfig(cc);
    // D16 productivity lint (Phase 5): conservative load-time WARNING on
    // zero-delay rule cycles (static Zeno check; maxSteps stays the
    // runtime backstop). Findings also ride on the API as `timedLint`.
    const _lint = lintProductivity(compiledRules.filter(r => !r.hasGrade0), _tcfg);
    for (const f of _lint) {
      console.warn(f.kind === 'self-cycle'
        ? `timed lint (D16): rule '${f.rule}' re-produces everything it consumes at zero delay — a Zeno self-cycle unless windows/guards break it`
        : `timed lint (D16): zero-delay rule cycle ${f.via} (rules: ${f.rules.join(', ')}) — Zeno unless resources deplete`);
    }
    // C1 chain-collapse advisory (same load-time channel as D16, advisory
    // tone) — gated on a productivity-clean rule set so Zeno cycles are
    // fixed before vocabulary advice is offered. Rides the API as
    // `timedAdvice`; collapsing stays the author's call.
    const _runtimeRules = compiledRules.filter(r => !r.hasGrade0);
    const _advice = [
      ...(_lint.length ? [] : lintChainCollapse(_runtimeRules, _tcfg)),
      ...lintHypothesisS(_runtimeRules, _tcfg, _rc),
      ...lintWholeBind(_runtimeRules, _tcfg),
    ];
    for (const f of _advice) {
      if (f.kind === 'chain-collapse') {
        console.warn(`timed lint (C1): '${f.pred}' is an unconditional chain intermediate — produced by ${f.producers.join(', ')}, consumed only by '${f.consumer}' with no other premise, window, or observer; consider collapsing the pair into one rule (delays add)`);
      } else if (f.kind === 'persistent-conclusion') {
        console.warn(`timed lint (C2): rule '${f.rule}' concludes persistent '${f.pred}' (${f.via}) — learned knowledge can backdate enablement (Hypothesis S, settle-optimality §1.3); external-choice menus are exempt`);
      } else if (f.kind === 'whole-bind-arrivals') {
        console.warn(`timed lint (C3): rule '${f.rule}' whole-binds '${f.pred}' while ${f.producers.join(', ')} produce(s) it — !_W chases every arrival and can starve under a deterministic chooser (PP2 §3b); prefer a counted take`);
      }
    }
    // Possessed rules (Phase 6c): compile a loli FACT on demand — a rule
    // and a loli are the same formula shape, so this is literally the rule
    // compiler (its content-addressed cache makes repeats free). Fences:
    // ground only (v1), no $-sugar leftovers, no unweighted multi-alt.
    const _compileLoli = (h) => {
      const r = forward.compileRule({
        name: 'loli:' + h, hash: h,
        antecedent: Store.child(h, 0), consequent: Store.child(h, 1),
      }, _compileOpts(cc));
      if (r.metavarCount > 0) {
        throw new Error('timed loli facts must be ground (v1) — variable-binding possessed rules are a 6b extension');
      }
      for (const p of (r.antecedent.linear || [])) {
        if (Store.tag(p) === 'preserved') {
          throw new Error('$-sugar inside a possessed rule: write the resource on both sides explicitly');
        }
      }
      if (r.consequentAlts && r.consequentAlts.length > 1 && !r.weighted) {
        throw new Error('unweighted additive-choice consequents in a possessed rule — use woplus');
      }
      return r;
    };
    const _timedOpts = (T, execOpts) => ({
      ...execOpts,
      horizon: _tcfg.parseStamp(T),
      timedConfig: _tcfg,
      calc: calcContext,
      compileLoli: _compileLoli,
      matchOpts: execOpts.matchOpts || _buildMatchOpts(execOpts),
    });
    _timedApi = {
      settle: (state, T, execOpts = {}) =>
        timed.settle(state, filterRules(execOpts), _timedOpts(T, execOpts)),
      // T2-applicability certifier (TODO_0293 (a), settle-optimality §11):
      // structural conflict-freedom first, else the monotone-relaxation
      // pairwise independence check — never runs settle
      certifyContention: (state, T, execOpts = {}) =>
        certifyContention(
          { prove: (g) => backward.prove(g, clauses, definitions, backwardOpts) },
          filterRules(execOpts), _tcfg, state, _tcfg.parseStamp(T), execOpts),
      // Bounded catch-up slices (TODO_0278 A2): same contract as settle,
      // plus chunk (slice width, parsed like a horizon) and onChunk.
      settleChunked: (state, T, execOpts = {}) =>
        timed.settleChunked(state, filterRules(execOpts), {
          ..._timedOpts(T, execOpts),
          ...(execOpts.chunk !== undefined ? { chunk: _tcfg.parseStamp(execOpts.chunk) } : {}),
        }),
      settleExplore: (state, T, execOpts = {}) =>
        timed.settleExplore(state, filterRules(execOpts), _timedOpts(T, execOpts)),
      nextActivation: (state, execOpts = {}) =>
        timed.nextActivation(state, filterRules(execOpts), {
          timedConfig: _tcfg, calc: calcContext,
          matchOpts: execOpts.matchOpts || _buildMatchOpts(execOpts),
        }),
      observable: (state, T) => views.observable(state, _tcfg.parseStamp(T), _tcfg),
      pending: (state, T) => views.pending(state, _tcfg.parseStamp(T), _tcfg),
      inFlight: (events, T) => views.inFlight(events, _tcfg.parseStamp(T), _tcfg),
      // with-projection: the host collapses an offered menu (external
      // choice); now-marked alternatives are strict — refused unless
      // fireable at the decision time (rules in scope for that check)
      choose: (state, factHash, index, chOpts = {}) =>
        game.withProject(state, factHash, index, {
          ...chOpts, timedConfig: _tcfg, roles: _rc,
          rules: filterRules(chOpts), calc: calcContext,
          compileLoli: _compileLoli,
          matchOpts: chOpts.matchOpts || _buildMatchOpts(chOpts),
        }),
      // per-alternative availability at horizon T (UI greying — pure query)
      menuStatus: (state, factHash, T, execOpts = {}) =>
        game.menuStatus(state, factHash, filterRules(execOpts),
          { ..._timedOpts(T, execOpts), roles: _rc }),
      timedLint: _lint,
      timedAdvice: _advice,
      // the timed-config record (grades/parseStamp/units) — public: the
      // bridge and debug tooling read it (round-15 F7; was _timedConfig)
      timedConfig: _tcfg,
    };
  }

  // ── Bundle fingerprint (TODO_0278 A1) ──────────────────────────────────
  // Orbit certificates key on raw Store hashes, which are only meaningful
  // against the bit-identical arena prefix that the load produced. Capture
  // the prefix bounds NOW (all load-time Store writes are done); the digest
  // is computed lazily on first certificate mint/verify. The certificate
  // carries mark + digest, so a resume validates against ITS OWN arena at
  // the certificate's mark — works in-process, across fresh loads of the
  // same source, and across store-binary restores. engineVersion rides
  // along: replay semantics must match, not just the data.
  const _fpMark = Store.fingerprintMark();
  let _bundleFp;
  const _bundleFingerprint = () => {
    if (_bundleFp === undefined) {
      const m = _fpMark;
      _bundleFp = `ev=${engineVersion()};n=${m.n};c=${m.c};s=${m.s};b=${m.b};a=${m.a};t=${m.t};d=${Store.prefixDigest(m)}`;
    }
    return _bundleFp;
  };
  const _verifyFingerprint = (fp) => {
    if (typeof fp !== 'string') return false;
    const m = /^ev=([0-9a-f]+);n=(\d+);c=(\d+);s=(\d+);b=(\d+);a=(\d+);t=(\d+);d=([0-9a-f]+)$/.exec(fp);
    if (!m || m[1] !== engineVersion()) return false;
    const d = Store.prefixDigest({ n: +m[2], c: +m[3], s: +m[4], b: +m[5], a: +m[6], t: +m[7] });
    return d !== null && d === m[8];
  };
  Object.defineProperty(calcContext, 'bundleFingerprint', { get: _bundleFingerprint });
  calcContext.verifyFingerprint = _verifyFingerprint;

  const api = {
    definitions,
    clauses,
    queries,
    querySettings,
    splitQueries,
    forwardRules: compiledRules.filter(r => !r.hasGrade0),
    _compiledRules: compiledRules,
    argNamesTable,
    sortVarsTable,
    // Refinement-sort system (TODO_0011 rung 1) — null for sortless
    // programs; the till shell reads classifier membership from here.
    sorts: sortSystem,
    // Constructor priors (@w, TODO_0292 D5/M6): member → [n, d] ℚ≥0
    // ratios; empty Map when the program declares none. priorLint carries
    // the T2 subcriticality advisory.
    priors: priorsTable,
    priorLint: priorAdvice,
    engine: eng,
    labelIndex,
    modules,
    ...(_timedApi || {}),

    // Structural roles of the ACTIVE calculus (TODO_0265 Phase 3, B7):
    // the resolveConn record — the ONE role shape (camelCase keys +
    // roles.computation = { tag, bodyIdx, gradeIdx }). bridge.modeSwitch
    // reads roles.computation; without this a graded calculus silently
    // fell back to ILL's unary layout (wrong bodyIdx).
    roles: _rc,

    // Bundle fingerprint (TODO_0278 A1): pins orbit certificates to the
    // exact loaded arena prefix + engine version.
    get bundleFingerprint() { return _bundleFingerprint(); },
    verifyFingerprint: _verifyFingerprint,

    // Backward chaining proof search (merges calculus-level backwardOpts)
    prove: (goal, opts) => backward.prove(goal, clauses, definitions, { ...backwardOpts, ...opts }),

    // All-solutions backward query (resolve-all SLD enumeration, capped;
    // solutions are theta arrays for kernel `apply`). The driver boundary
    // for clause-derived bias (TODO_0298): every DISTINCT derived
    // instance conditions the posterior — committed choice would drop
    // all but the first.
    proveAll: (goals, opts = {}) => resolveAll([].concat(goals), clauses, definitions, {
      maxSolutions: 256, canonicalize,
      backchainOpts: { theories: _allTheories },
      ...(ffiContext ? { ffiContext } : {}),
      ...opts,
    }),

    // Forward chaining execution (auto-injects calc + engine, supports rule filtering) (T15)
    exec: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      const matchOpts = execOpts.matchOpts || _buildMatchOpts(execOpts);
      return forward.run(state, rules, { ...execOpts, calc: calcContext, engine: eng, matchOpts });
    },

    // Exhaustive exploration (same filtering as exec) (T16)
    explore: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      const matchOpts = execOpts.matchOpts || _buildMatchOpts(execOpts);
      return explore.explore(state, rules, {
        ...execOpts, calc: calcContext, engine: eng, matchOpts,
        predictNext: _predictNext,
        structuralMemoFns: _structuralMemoFns,
      });
    },

    // Exposed for direct callers that need pre-built matchOpts
    _calcContext: calcContext,
    _buildMatchOpts,
  };

  // Decimation driver (TODO_0297 P2): collapse of superposed existentials
  // — presence-gated on the timed API (settle) + a sort system; running
  // it is the D4 opt-in (plain settle leaves suspended ∃-facts inert).
  if (api.settle && sortSystem) {
    api.collapse = (state, o = {}) =>
      decimate.collapse(api, state, { stampTag: cc.stampTag || 'at', ...o });
  }
  return api;
}

/**
 * Resolve a module algebra expression to a set of rule names.
 */
function _resolveModule(expr, labelIndex, modules, resolveLabels) {
  switch (expr.type) {
    case 'label': {
      // D7: modules shadow labels — check modules first
      if (modules.has(expr.name)) {
        return new Set(modules.get(expr.name));
      }
      // Otherwise treat as import label → all rule names + transitive deps
      const labels = resolveLabels([expr.name]);
      const names = new Set();
      for (const l of labels)
        for (const n of (labelIndex.get(l) || [])) names.add(n);
      return names;
    }
    case 'names': return new Set(expr.names);
    case 'union': {
      const l = _resolveModule(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModule(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l, ...r]);
    }
    case 'subtract': {
      const l = _resolveModule(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModule(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l].filter(x => !r.has(x)));
    }
    case 'intersect': {
      const l = _resolveModule(expr.left, labelIndex, modules, resolveLabels);
      const r = _resolveModule(expr.right, labelIndex, modules, resolveLabels);
      return new Set([...l].filter(x => r.has(x)));
    }
    default:
      throw new Error(`Unknown module expression type: ${expr.type}`);
  }
}

/**
 * Deserialize compiled rules from JSON storage.
 * Converts array fields (freevars, persistentDeps) back to Sets.
 */
function _deserRules(rules) {
  return rules.map(r => {
    if (!r.linearMeta) return r;
    const lm = {};
    for (const k in r.linearMeta) {
      const m = r.linearMeta[k];
      lm[k] = {
        ...m,
        freevars: Array.isArray(m.freevars) ? new Set(m.freevars) : m.freevars,
        persistentDeps: Array.isArray(m.persistentDeps) ? new Set(m.persistentDeps) : m.persistentDeps,
      };
    }
    return { ...r, linearMeta: lm };
  });
}

/**
 * Write current Store state + metadata to binary cache file.
 * @returns {number} byte size of written file
 */
function _snapToFile(cachePath, definitions, clauses, rawForwardRules, _compiledRules, queries, argNamesTable, sortVarsTable, priorsTable) {
  const metadata = {
    types: Object.fromEntries(definitions),
    clauses: Object.fromEntries(
      Array.from(clauses.entries()).map(([k, v]) => [k, v])
    ),
    forwardRules: rawForwardRules,
    // compiledRules omitted — recomputed on restore (~1.5ms, saves ~85KB)
    queries: Object.fromEntries(queries),
    argNamesTable: argNamesTable ? Object.fromEntries(argNamesTable) : {},
    sortVarsTable: sortVarsTable ? Object.fromEntries(sortVarsTable) : {},
    priors: _serPriors(priorsTable)
  };
  const snap = Store.snapshot(metadata);
  const bin = compact(snap);
  const buf = serialize(bin);
  // No gzip — compacted binary is small enough (~50KB) and gunzip costs 0.3ms
  fs.mkdirSync(path.dirname(cachePath), { recursive: true });
  fs.writeFileSync(cachePath, buf);
  return buf.length;
}

/**
 * Compute transitive closure of SDK paths from top-level imports.
 */
function _sdkPaths(tree, topLevelImports) {
  const sdkPaths = new Set();
  const nodeMap = new Map(tree.map(n => [n.path, n]));
  function add(p) {
    if (sdkPaths.has(p)) return;
    sdkPaths.add(p);
    const node = nodeMap.get(p);
    if (node) node.deps.forEach(add);
  }
  topLevelImports.forEach(add);
  return sdkPaths;
}

// ─── SELL label helpers ─────────────────────────────────────────────────────

/**
 * Build transitive dependency map from import tree: label → Set<label>.
 * Also detects label collisions (T8): two files with same stem → error.
 * @param {Array<{path: string, deps: string[]}>} tree - topo-sorted import tree
 * @returns {Map<string, Set<string>>} label → transitive dep labels
 */
function labelDeps(tree) {
  const deps = new Map();
  const labelToPath = new Map(); // for collision detection
  const nodeMap = new Map();     // path → node for O(1) lookup

  for (const node of tree) {
    const label = path.basename(node.path, path.extname(node.path));
    if (labelToPath.has(label)) {
      throw new Error(
        `Label collision: '${label}' matches both ${labelToPath.get(label)} and ${node.path}. ` +
        `Rename one of the files to disambiguate.`
      );
    }
    labelToPath.set(label, node.path);
    nodeMap.set(node.path, node);
  }

  function transitive(nodePath, visited) {
    const label = path.basename(nodePath, path.extname(nodePath));
    if (visited.has(label)) return visited;
    visited.add(label);
    const node = nodeMap.get(nodePath);
    if (node) {
      for (const dep of node.deps) transitive(dep, visited);
    }
    return visited;
  }

  for (const node of tree) {
    const label = path.basename(node.path, path.extname(node.path));
    const all = transitive(node.path, new Set());
    all.delete(label); // don't include self
    deps.set(label, all);
  }
  return deps;
}

// ─── Cache-aware load helpers ───────────────────────────────────────────────

/**
 * Try loading from a binary cache file. Returns calc context or null.
 * Deletes corrupted cache files gracefully.
 * @param {Object} [sellOpts] - SELL label opts to thread to _buildCalc
 */
function _tryLoadFromCache(cachePath, sellOpts) {
  try {
    if (fs.existsSync(cachePath)) return loadPrecompiled(cachePath, sellOpts);
  } catch (e) {
    try { fs.unlinkSync(cachePath); } catch {}
  }
  return null;
}

/**
 * Restore SDK from binary cache, parse top file on top.
 * Returns intermediate result (raw data for further caching).
 */
function _loadCached(topFilePath, sdkCachePath, sdkPaths, cc = _defaultCalcConfig) {
  Store.clear();
  const data = _readSnapshotFile(sdkCachePath);
  Store.restore(data);

  const meta = data.metadata;
  const definitions = new Map(Object.entries(meta.types));
  const clauses = new Map(Object.entries(meta.clauses));
  const rawForwardRules = [...meta.forwardRules];
  const sdkCompiledRules = meta.compiledRules
    ? _deserRules(meta.compiledRules)
    : rawForwardRules.map(r => forward.compileRule(r, _compileOpts(cc)));
  const queries = new Map(Object.entries(meta.queries));
  const sdkRuleCount = rawForwardRules.length;
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];

  // Restore SDK argNamesTable from cache, then parse top file on top
  // T2: SDK rules already have sourceLabel from cache (survives JSON round-trip
  // via {...r} spread in _serRules). Only tag new rules from top file.
  const argNamesTable = meta.argNamesTable
    ? new Map(Object.entries(meta.argNamesTable)) : new Map();
  const sortVarsTable = meta.sortVarsTable
    ? new Map(Object.entries(meta.sortVarsTable)) : new Map();
  // Priors (@w) live in the TOP file's parse (SDK bundles carry none) —
  // a fresh table per load, filled by the loadFile below.
  const priorsTable = new Map();
  const prevRuleCount = rawForwardRules.length;
  const prevClauseNames = new Set(clauses.keys());
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported: new Set(sdkPaths), argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls,
    priorsTable, loaderConfig: cc.loader
  });
  // T2: Tag top-file rules with root label
  const rootLabel = path.basename(topFilePath, path.extname(topFilePath));
  for (let i = prevRuleCount; i < rawForwardRules.length; i++) {
    rawForwardRules[i].sourceLabel = rootLabel;
  }
  for (const [name, clause] of clauses) {
    if (!prevClauseNames.has(name)) clause.sourceLabel = rootLabel;
  }

  // Compile only new forward rules
  const newRaw = rawForwardRules.slice(sdkRuleCount);
  const newCompiled = newRaw.map(r => forward.compileRule(r, _compileOpts(cc)));
  const allCompiled = [...sdkCompiledRules, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled,
    queries, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls, priorsTable };
}

/**
 * Parse from scratch with SDK caching. Parses SDK imports bottom-up,
 * snapshots imports cache, then parses top file.
 * Returns intermediate result (raw data for further caching).
 */
function _parseFresh(topFilePath, sdkNodes, importsCachePath, cc = _defaultCalcConfig) {
  Store.clear();
  const definitions = new Map(), clauses = new Map(), rawForwardRules = [], queries = new Map();
  const alreadyImported = new Set();
  const argNamesTable = new Map();
  const sortVarsTable = new Map();
  const querySettings = new Map();
  const splitQueries = new Map();
  const moduleDecls = [];
  const priorsTable = new Map();

  // Phase 1: Parse SDK imports bottom-up (topo order)
  for (const node of sdkNodes) {
    const prevRuleCount = rawForwardRules.length;
    const prevClauseNames = new Set(clauses.keys());
    convert.loadFile(node.path, definitions, clauses, rawForwardRules, queries, {
      alreadyImported, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls,
      priorsTable, loaderConfig: cc.loader
    });
    alreadyImported.add(node.path);
    // T1: Tag new forward rules with source label
    const label = path.basename(node.path, path.extname(node.path));
    for (let i = prevRuleCount; i < rawForwardRules.length; i++) {
      rawForwardRules[i].sourceLabel = label;
    }
    // Tag new clauses
    for (const [name, clause] of clauses) {
      if (!prevClauseNames.has(name)) clause.sourceLabel = label;
    }
  }

  // Compile SDK rules and write imports cache
  const sdkCompiled = rawForwardRules.map(r => forward.compileRule(r, _compileOpts(cc)));
  const sdkRuleCount = rawForwardRules.length;
  if (importsCachePath && sdkNodes.length > 0) {
    _snapToFile(importsCachePath, definitions, clauses,
      [...rawForwardRules], sdkCompiled, new Map(queries), new Map(argNamesTable),
      new Map(sortVarsTable));
  }

  // Phase 2: Parse top file (SDK imports skipped via alreadyImported)
  const prevRuleCount = rawForwardRules.length;
  const prevClauseNames = new Set(clauses.keys());
  convert.loadFile(topFilePath, definitions, clauses, rawForwardRules, queries, {
    alreadyImported, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls,
    priorsTable, loaderConfig: cc.loader
  });
  // T1: Tag top-file rules with root label
  const rootLabel = path.basename(topFilePath, path.extname(topFilePath));
  for (let i = prevRuleCount; i < rawForwardRules.length; i++) {
    rawForwardRules[i].sourceLabel = rootLabel;
  }
  for (const [name, clause] of clauses) {
    if (!prevClauseNames.has(name)) clause.sourceLabel = rootLabel;
  }

  // Compile only new forward rules
  const newRaw = rawForwardRules.slice(sdkRuleCount);
  const newCompiled = newRaw.map(r => forward.compileRule(r, _compileOpts(cc)));
  const allCompiled = [...sdkCompiled, ...newCompiled];

  return { definitions, clauses, rawForwardRules, compiledRules: allCompiled,
    queries, argNamesTable, sortVarsTable, querySettings, splitQueries, moduleDecls, priorsTable };
}

/**
 * Load without caching (old behavior).
 */
function _loadFresh(filePath, extraOpts) {
  const onPhase = extraOpts && extraOpts.onPhase;
  const _cc = (extraOpts && extraOpts.calculusConfig) || _defaultCalcConfig;
  const _t0 = onPhase ? performance.now() : 0;
  const { definitions, clauses, forwardRules, queries, argNamesTable,
    sortVarsTable, querySettings, splitQueries, moduleDecls, priorsTable, importTree } =
    convert.load(filePath, { onPhase, loaderConfig: _cc.loader });
  if (onPhase) onPhase('load/parse', performance.now() - _t0, {
    definitions: definitions.size,
    clauses: clauses.size,
    forwardRules: forwardRules.length,
    queries: queries.size,
    files: importTree ? importTree.length : 1,
  });
  const absPath = path.resolve(Array.isArray(filePath) ? filePath[0] : filePath);
  const rootLabel = path.basename(absPath, path.extname(absPath));
  const ld = importTree ? labelDeps(importTree) : new Map();
  return _buildCalc(definitions, clauses, forwardRules, queries, {
    argNamesTable, sortVarsTable, rootLabel, labelDeps: ld, querySettings, splitQueries, moduleDecls, priorsTable,
    ...extraOpts
  });
}

// ─── Public API ─────────────────────────────────────────────────────────────

/**
 * Load MDE file and prepare for execution.
 *
 * Auto-caching (default): computes content hashes of source files, uses
 * two-tier cache (full program + imports-only) in a temp directory.
 *
 * @param {string|string[]} filePath - file path(s) to load
 * @param {Object} [opts]
 * @param {boolean|string} [opts.cache=true] - true (auto-cache), 'imports' (cache SDK only), false (no cache)
 * @param {string} [opts.cacheDir] - cache directory (default: os.tmpdir()/calc-cache/)
 * @returns {Object} calc context
 */
function load(filePath, opts = {}) {
  // ── Env overrides (TODO_0218 Phase 3) ───────────────────────────────────
  // CALC_CACHE=0 fully disables cache r/w; option beats env only if set.
  let cacheMode = opts.cache;
  if (cacheMode === undefined) {
    cacheMode = process.env.CALC_CACHE === '0' ? false : true;
  }

  // Active calculus config (TODO_0265 Phase 3, B5): threaded through every
  // parse/compile/cache path below — a non-ILL load must never silently
  // compile as ILL.
  const cc = opts.calculusConfig || _defaultCalcConfig;

  // ── bytecode API (TODO_0218 H7) ─────────────────────────────────────────
  // `bytecode: '0x...'` expands internally to extraGrade0Facts + scopeGuard.
  // Keeps the scopeGuard identity computable from the hex bytes — no
  // caller-declared ID that can go stale.
  let { extraGrade0Facts, scopeGuard, residualResolver,
        chainFusionPredicates, linearFusionPredicate, sroaConfig,
        composeDiskCache, fusionBarriers, skipSpecialize } = opts;
  let bytecodeHex = null;
  if (opts.bytecode) {
    if (extraGrade0Facts || scopeGuard) {
      throw new Error('mde.load: bytecode is mutually exclusive with extraGrade0Facts/scopeGuard');
    }
    bytecodeHex = opts.bytecode.startsWith('0x') || opts.bytecode.startsWith('0X')
      ? opts.bytecode.slice(2) : opts.bytecode;

    const { loadBytecode, bytecodeArrGetGuard } = _getBytecodeLoader();
    const bc = loadBytecode(bytecodeHex);
    extraGrade0Facts = bc.facts;
    scopeGuard = bytecodeArrGetGuard;
  }
  // Default fuseBasicBlocks on when external grade-0 facts are provided —
  // compose is always beneficial with concrete fact sets (5x execution speedup).
  const fuseBasicBlocks = opts.fuseBasicBlocks !== undefined
    ? opts.fuseBasicBlocks
    : !!extraGrade0Facts;
  const onPhase = opts.onPhase || null;
  const composeOpts = opts.calculusConfig || extraGrade0Facts || scopeGuard || residualResolver || fuseBasicBlocks
      || chainFusionPredicates || linearFusionPredicate || sroaConfig || composeDiskCache || fusionBarriers || onPhase || skipSpecialize
      || opts.strictTypes !== undefined
    ? { calculusConfig: opts.calculusConfig, extraGrade0Facts, scopeGuard, residualResolver, fuseBasicBlocks,
        chainFusionPredicates, linearFusionPredicate, sroaConfig,
        composeDiskCache, fusionBarriers, onPhase, skipSpecialize,
        strictTypes: opts.strictTypes } : undefined;

  // ── Compose disk cache (TODO_0218 Phase 4: explicit opt-in) ────────────
  // Activates when any of the following is true:
  //   - composeDiskCache is truthy (legacy back-compat opt-in)
  //   - cache: 'compose' or cache: 'verify' (new explicit sugar)
  //   - env CALC_COMPOSE_CACHE=1 AND cache is not false
  //
  // The compose cache round-trips post-compose rule pools through
  // Store.snapshot/restore. Not all compose-generated rule shapes (fused,
  // specialized, tabled) reconstruct cleanly via `Store.child(hash, 0/1)`
  // recompilation, so making this default-on across the full test matrix
  // currently produces execution divergences. Opt-in users get the big win
  // on their own iteration loops; making this default-on safely requires
  // Phase 5's tail-processing (re-run tabling/specialize/fuse post-restore)
  // so that only the deterministic Store arena is cached, not the downstream
  // compose artefacts.
  // Activation: any of (a) composeDiskCache truthy, (b) cache:'compose'/'verify',
  // (c) CALC_COMPOSE_CACHE=1 with cache not explicitly false. `composeDiskCache:
  // false` and array-inputs are hard opt-outs.
  const useComposeCache =
    !Array.isArray(filePath) &&
    composeDiskCache !== false && (
      !!composeDiskCache ||
      cacheMode === 'compose' || cacheMode === 'verify' ||
      (process.env.CALC_COMPOSE_CACHE === '1' && cacheMode !== false)
    );
  if (useComposeCache) {
    const absPathForCache = path.resolve(filePath);
    const tree = convert.buildImportTree(absPathForCache);
    const treeHashes = convert.computeTreeHashes(tree);
    const composeCacheDir =
      typeof composeDiskCache === 'string' ? composeDiskCache :
      opts.cacheDir ||
      process.env.CALC_CACHE_DIR ||
      path.join(os.homedir(), '.cache', 'calc', 'snapshots');
    // Phase 6: best-effort format migration — if the version tag doesn't
    // match the current engine version, wipe stale compose-*.bin files.
    ensureVersionTag(composeCacheDir, engineVersion());
    const composeCacheKey = _composeCacheKey(treeHashes, absPathForCache, bytecodeHex, {
      fuseBasicBlocks, cacheVersion: opts.cacheVersion, cacheEpoch: cc.compile.cacheEpoch,
    });
    const composeCachePath = path.join(composeCacheDir, `compose-${composeCacheKey}.bin`);
    const rootLabel = path.basename(absPathForCache, path.extname(absPathForCache));
    const ld = labelDeps(tree);

    // ── Verify mode (TODO_0218 Phase 4): CALC_CACHE_VERIFY=1 or
    //    cache: 'verify'. Runs cold path, caches it, then runs cached path
    //    and diffs the results. Any divergence throws loudly.
    const verifyMode =
      cacheMode === 'verify' ||
      process.env.CALC_CACHE_VERIFY === '1';

    if (!verifyMode) {
      const cached = _loadCSnap(composeCachePath, { rootLabel, labelDeps: ld });
      if (cached) return cached;
    }

    // Cache miss (or verify pass 1) — parse + compose, then save snapshot.
    // Do NOT Store.clear() here: callers may have already placed content
    // (e.g., bytecode-derived extraGrade0Facts hashes) into the Store.
    const loaded = convert.load(filePath, { loaderConfig: cc.loader });
    const calc = _buildCalc(loaded.definitions, loaded.clauses, loaded.forwardRules, loaded.queries, {
      argNamesTable: loaded.argNamesTable, sortVarsTable: loaded.sortVarsTable,
      rootLabel, labelDeps: ld,
      querySettings: loaded.querySettings, splitQueries: loaded.splitQueries,
      moduleDecls: loaded.moduleDecls, ...composeOpts
    });
    _saveCSnap(composeCachePath, calc,
      calc.definitions, calc.clauses, calc.queries,
      loaded.argNamesTable, loaded.querySettings, loaded.splitQueries,
      loaded.moduleDecls, rootLabel, ld, loaded.sortVarsTable);
    // Phase 6: best-effort LRU eviction — keep the cache dir under budget.
    lruEvict(composeCacheDir, opts.cacheMaxBytes || DEFAULT_MAX_BYTES);

    if (verifyMode) {
      // Pass 2: restore from the just-written snapshot and diff rule names.
      // Fresh Store — restore does an onReplace, invalidating dependent caches.
      Store.clear();
      const replay = _loadCSnap(composeCachePath, { rootLabel, labelDeps: ld });
      if (!replay) {
        throw new Error(`CALC_CACHE_VERIFY: failed to read back freshly-written snapshot at ${composeCachePath}`);
      }
      _verifyEq(calc, replay);
      // Return replay (post-restore) so the caller exercises the cached path.
      return replay;
    }
    return calc;
  }

  // No caching or array input — use simple path
  if (cacheMode === false || Array.isArray(filePath)) {
    return _loadFresh(filePath, composeOpts);
  }

  const absPath = path.resolve(filePath);
  const cacheDir = opts.cacheDir || path.join(os.tmpdir(), 'calc-cache');

  // Build import tree and compute content hashes
  // CACHE_VERSION: bump when parser/compiler changes affect binary output
  // (e.g., bang arity 1→2 in SELL graded modality).
  const CACHE_VERSION = 5;
  // Cache keys are epoch-qualified: .bin files parsed/compiled under one
  // calculus config must not be restored under another (TODO_0265 Phase 3).
  const _epochHash = hashString(cc.compile.cacheEpoch || '');
  const tree = convert.buildImportTree(absPath);
  const hashes = convert.computeTreeHashes(tree);
  const topNode = tree[tree.length - 1];
  const fullHash = hashCombine(hashes.get(absPath), CACHE_VERSION, _epochHash);

  // Determine SDK imports (top-level imports + transitive deps)
  const topLevelImports = convert.extractTopLevelImports(topNode.source, absPath);
  const sdkPaths = _sdkPaths(tree, topLevelImports);
  const sdkNodes = tree.filter(n => sdkPaths.has(n.path));

  // Compute imports hash from top-level import file hashes
  let importsHash = null;
  if (topLevelImports.length > 0) {
    const sortedHashes = [...topLevelImports].sort().map(p => hashes.get(p));
    importsHash = hashCombine(...sortedHashes, CACHE_VERSION, _epochHash);
  }

  const fullCachePath = path.join(cacheDir, `${(fullHash >>> 0).toString(16)}.bin`);
  const importsCachePath = importsHash
    ? path.join(cacheDir, `${(importsHash >>> 0).toString(16)}.bin`)
    : null;

  // T6: Compute label infrastructure from tree (shared by all cache-mode branches)
  const rootLabel = path.basename(absPath, path.extname(absPath));
  const ld = labelDeps(tree);

  /** Thread SELL opts from intermediate result to _buildCalc */
  function _sellOpts(result) {
    return {
      compiledRules: result.compiledRules,
      argNamesTable: result.argNamesTable,
      sortVarsTable: result.sortVarsTable,
      rootLabel,
      labelDeps: ld,
      querySettings: result.querySettings,
      splitQueries: result.splitQueries,
      moduleDecls: result.moduleDecls,
      priorsTable: result.priorsTable,
      calculusConfig: opts.calculusConfig,
    };
  }

  // === cache: true (default) — two-tier auto-cache ===
  if (cacheMode === true) {
    // Tier 1: Try full cache hit
    const fullHit = _tryLoadFromCache(fullCachePath,
      { rootLabel, labelDeps: ld, calculusConfig: opts.calculusConfig });
    if (fullHit) return fullHit;

    // Tier 2: Try imports cache + parse top file
    if (importsCachePath) {
      try {
        if (fs.existsSync(importsCachePath)) {
          const result = _loadCached(absPath, importsCachePath, sdkPaths, cc);
          // Write full cache for next time
          _snapToFile(fullCachePath, result.definitions, result.clauses,
            result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable,
            result.sortVarsTable, result.priorsTable);
          return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
            _sellOpts(result));
        }
      } catch (e) {
        try { fs.unlinkSync(importsCachePath); } catch {}
      }
    }

    // Full miss: parse everything, cache both tiers
    const result = _parseFresh(absPath, sdkNodes, importsCachePath, cc);
    _snapToFile(fullCachePath, result.definitions, result.clauses,
      result.rawForwardRules, result.compiledRules, result.queries, result.argNamesTable,
      result.sortVarsTable, result.priorsTable);
    return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
      _sellOpts(result));
  }

  // === cache: 'imports' — cache SDK only, always parse top file fresh ===
  if (cacheMode === 'imports') {
    // No imports → degrade to fresh load
    if (!importsCachePath) return _loadFresh(filePath, composeOpts);

    // Try imports cache hit
    try {
      if (fs.existsSync(importsCachePath)) {
        const result = _loadCached(absPath, importsCachePath, sdkPaths, cc);
        return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
          _sellOpts(result));
      }
    } catch (e) {
      try { fs.unlinkSync(importsCachePath); } catch {}
    }

    // Miss: parse everything, cache imports only
    const result = _parseFresh(absPath, sdkNodes, importsCachePath, cc);
    return _buildCalc(result.definitions, result.clauses, result.rawForwardRules, result.queries,
      _sellOpts(result));
  }

  // Unknown cache mode — fallback to fresh
  return _loadFresh(filePath, composeOpts);
}

/**
 * Precompile MDE files to binary cache.
 * Includes compiled forward rules for fast restore.
 * @param {string|string[]} filePaths - source files to precompile
 * @param {string} cachePath - output binary file path
 * @returns {{ definitions, clauses, forwardRules, queries, byteSize }}
 */
function precompile(filePaths, cachePath, opts = {}) {
  Store.clear();
  const cc = opts.calculusConfig || _defaultCalcConfig;
  const { definitions, clauses, forwardRules, queries, argNamesTable, sortVarsTable, priorsTable } =
    convert.load(filePaths, { loaderConfig: cc.loader });
  const compiledRules = forwardRules.map(r => forward.compileRule(r, _compileOpts(cc)));
  const byteSize = _snapToFile(cachePath, definitions, clauses, forwardRules, compiledRules, queries, argNamesTable, sortVarsTable, priorsTable);
  return { definitions, clauses, forwardRules, queries, argNamesTable, sortVarsTable, priorsTable, byteSize };
}

/**
 * Load from precompiled binary cache.
 * Restores Store state and uses cached compiled rules.
 *
 * NOTE: a .bin has no config association — a cache written by
 * precompile(..., { calculusConfig }) must be loaded with the SAME config
 * in sellOpts.calculusConfig, or this silently builds under the ILL
 * default (audit round 12, F5).
 *
 * @param {string} cachePath - binary cache file path
 * @param {Object} [sellOpts] - SELL label opts (rootLabel, labelDeps,
 *   calculusConfig) to thread
 * @returns {Object} calc context (same shape as load())
 */
function loadPrecompiled(cachePath, sellOpts) {
  const data = _readSnapshotFile(cachePath);
  Store.restore(data);

  const { types: defsObj, clauses: clausesObj, forwardRules, compiledRules, queries: queriesObj } = data.metadata;

  const definitions = new Map(Object.entries(defsObj));
  const clauses = new Map(Object.entries(clausesObj));
  const queries = new Map(Object.entries(queriesObj));
  const argNamesTable = data.metadata.argNamesTable
    ? new Map(Object.entries(data.metadata.argNamesTable)) : new Map();
  const sortVarsTable = data.metadata.sortVarsTable
    ? new Map(Object.entries(data.metadata.sortVarsTable)) : new Map();
  const priorsTable = _desPriors(data.metadata.priors);

  const opts = { argNamesTable, sortVarsTable, priorsTable, ...(sellOpts || {}) };
  // Use cached compiledRules if present, otherwise recompile from forwardRules
  if (compiledRules) opts.compiledRules = _deserRules(compiledRules);
  return _buildCalc(definitions, clauses, forwardRules, queries, opts);
}

// EVM bytecode normalization — delegated to ill/bytecode-normalize.js,
// loaded lazily like the bytecode loader above (audit 2026-08-23: the
// generic entry's static module graph carries ONE ill/ import, the
// default calculus config). Only normalizeQuery is re-exported (decompose
// + codeToArrlit + bytesToSemantic); the passes live in ill/.
let _bcNorm = null;
function normalizeQuery(hash) {
  if (!_bcNorm) _bcNorm = _require('./ill/bytecode-normalize.js').default;
  return _bcNorm.normalizeQuery(hash);
}

const parseExpr = convert.parseExpr;
const hasMonad = convert.hasMonad;
// decomposeQuery is the GENERIC query decomposition (convert.js). The EVM
// bytecode-normalizing variant is exported under its own name,
// normalizeQuery — it was previously aliased AS decomposeQuery, which
// misnamed EVM semantics as generic API (TODO_0265 Phase 2b).
const decomposeQuery = convert.decomposeQuery;
const prove = backward.prove;
const exec = forward.run;
const createState = forward.createState;
const compileRule = forward.compileRule;

export {
  load,
  precompile,
  loadPrecompiled,
  parseExpr,
  hasMonad,
  decomposeQuery,
  normalizeQuery,
  prove,
  exec,
  createState,
  compileRule,
  Store,
  _composeCacheKey,
};
export default {
  load,
  precompile,
  loadPrecompiled,
  parseExpr,
  hasMonad,
  decomposeQuery,
  normalizeQuery,
  prove,
  exec,
  createState,
  compileRule,
  Store,
  _composeCacheKey,
};

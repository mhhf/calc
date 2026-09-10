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
 * Reference instances: calculus/ill/calculus-config.js (ILL) and
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
 * @property {Object}  [family]     structural family layer piece (e.g.
 *   family/lnl/family-config.js): { name, engine: { proveNaive,
 *   matchDynamicRule, drainDynamicRules, resolveEx } } — the engine hooks
 *   the composition root wires into the family protocol (TODO_0086).
 *   Absent: state-lookup-only persistent proving, no dynamic rules.
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
 *   until 0157 — the rule-hash builder needs kernel rTensor/rOne)
 * @property {Object}  [domain]     display/memo policy { memoControlTags,
 *   classifyLeaf, showExclude, ... }
 */

import convert from './convert.js';
import forward from './forward.js';
import explore from './explore.js';
import { buildTimedApi } from '../timed/timed-api.js';
import backward from './backchain.js';
import Store from '../kernel/store.js';
import { hashCombine, hashString } from '../hash.js';
import { profile, engine } from './optimizer.js';
import { engineVersion } from './cache/engine-version.js';
import { cacheFlagFingerprint } from './cache/cache-flags.js';
import { ensureVersionTag, lruEvict, DEFAULT_MAX_BYTES } from './cache/cache-evict.js';
import fs from 'fs';
import path from 'path';
import os from 'os';
// Hoisted by tools/esm-hoist.js:
import { compilePS as _compilePS, execPS as _execPS } from './opt/ffi.js';
import { buildTheoryLookup, buildCanonicalizer, defaultTheories as _defaultTh } from '../kernel/eq-theory.js';
import { compose0 } from './compose.js';
import { fuseBlocksPass as _fuseBlocksPass, fuseChainsPass as _fuseChainsPass } from './opt/compose-fuse.js';
import { sroaPass as _sroaPass } from './opt/compose-sroa.js';
// Compose optimization pass records, appended to compose0's pool
// pipeline in this order (P5 → P5.5 → P6; RES_0143 F3/M4)
const _composeOptPasses = [_fuseBlocksPass, _fuseChainsPass, _sroaPass];
import { checkAll, deriveGradeMeta } from './type-check.js';
import { validateCalculusConfig } from './cc-schema.js';
import { defaultGradeConfig as _defaultGradeConfig } from './grades.js';
import { materializeLoadTimeClauses } from './materialize.js';
import { checkPriors as _checkPriors } from '../measure/priors.js';
import { checkWellModed } from './well-moded.js';
import { buildCollapseApi } from '../measure/collapse-api.js';
import { certifyConfluence } from './certify-confluence.js';
import { toObject as _fsToObject } from './fact-set.js';
import { resolve as resolveAll } from './resolve-all.js';
import { _validateArity } from './opt/ffi.js';
import { clauseDispatch } from './opt/compiled-clauses.js';
import { compileExChain, execExStep as _execExStep } from './opt/existential-compile.js';
import { resolveConn as _resolveConn } from './formula-utils.js';
import _match from './match.js';
import { proveWithFFI as _proveWithFFI, ffiDirect as _ffiDirect } from './opt/ffi.js';
import { tryCCDispatch as _tryCCDispatch } from './opt/compiled-clauses.js';
import { predictNext as _predictNext } from './opt/prediction.js';
import _structuralMemoFns from './opt/structural-memo.js';
import { fpDetect as _fpDetect, fpLayer as _fpLayer, attachPred as _attachPred } from './opt/fingerprint.js';
import { deltaBypass as _deltaBypassFn } from './opt/delta-bypass.js';
import { clearBWCache as _clearBWCache } from './opt/backward-cache.js';

/**
 * The active calculus config, required on every load path (audit
 * 2026-09-02): the engine holds NO default — the former static ILL
 * import made the generic module graph depend on a calculus. ILL
 * callers use calculus/ill/index.js, the pre-bound facade.
 */
function _requireConfig(cc, site) {
  if (!cc) {
    throw new Error(`${site}: opts.calculusConfig is required — pass a calculus config ` +
      `(ILL callers: import the pre-bound facade calculus/ill/index.js)`);
  }
  // The cc PORT contract (RES_0143 F1): fail-fast on unknown/typo'd keys,
  // missing requireds, wrong types. Validated once per config object.
  if (!_validatedCCs.has(cc)) {
    validateCalculusConfig(cc, site);
    _validatedCCs.add(cc);
  }
  return cc;
}
const _validatedCCs = new WeakSet();

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
    // State-canonicity gate (theory-eq sweep): the composed canonicalizer
    // and the theory value-class tags, config-derived (no global-
    // registration ordering hazard) — compile flags consequent patterns
    // whose instantiations can leave canonical form (canonPatterns).
    canonicalize: buildCanonicalizer([..._defaultTh, ...(cc.theories || [])]),
    classTags: _ccClassTags(cc),
    // Mode metadata for the fused-block resolution-body dataflow sort
    // (TODO_0307 P3). Absent ⇒ no body is computed (fused rules keep the
    // plain match-time + resolveEx split).
    getModeMeta: cc.compile.getModeMeta || null,
  };
}

/** Theory value-class tags from a calculus config (tag-name Set). */
function _ccClassTags(cc) {
  const s = new Set();
  for (const t of [..._defaultTh, ...(cc.theories || [])]) {
    for (const tag of t.classTags || []) s.add(tag);
  }
  return s;
}

// ─── Compose disk cache ─────────────────────────────────────────────────────
// (extracted to cache/compose-cache.js, RES_0143 M3 — the snapshot
// builder is injected; _loadCSnap is re-bound to _buildCalc here.)
import { COMPOSE_DISK_VERSION, _readSnapshotFile, _composeCacheKey, _serPriors,
  _desPriors, _saveCSnap, _loadCSnap as _loadCSnapRaw, _verifyEq } from './cache/compose-cache.js';
const _loadCSnap = (cachePath, sellOpts) => _loadCSnapRaw(cachePath, sellOpts, _buildCalc);
// Two-tier file-hash load cache (audit item 7 — extracted, deps injected)
import { loadTwoTier, labelDeps, deserRules, snapToFile } from './cache/load-cache.js';

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

  const cc = _requireConfig(opts.calculusConfig, 'engine _buildCalc');
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
      // (audit round 12, F3). NOTE: compose reads bang/loli/monad tags
      // from rc (parametric), but its rule-hash builder goes through
      // kernel/ast.js rTensor/rOne — hardcoded 'tensor'/'one' — so a
      // calculus without those connectives is NOT yet supported for
      // grade-0 compose (recorded residue; the coupling lives in the
      // kernel helper, not compose.js).
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
      composeOpts.gradeUnit = cc.gradeUnit;
      // Optimization pass records P5/P5.5/P6 injected from opt/ (RES_0143 M4/F3)
      composeOpts.optPasses = _composeOptPasses;
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

  // Sort-check declarations + rules (load-time only, zero runtime cost).
  // Sort system + the three intra-logical materialization riders
  // (subsort closure, datasort masses, constructor priors) extracted
  // verbatim to materialize.js (audit 2026-09-02 readability split).
  const priorsTable = opts.priorsTable || new Map();
  const { sortSystem, priorAdvice, stateMasses } = materializeLoadTimeClauses({
    checkPriors: _checkPriors,
    cc, definitions, clauses, sortVarsTable, priorsTable,
    phaseStart: _phaseStart, phaseEnd: _phaseEnd,
  });

  // Well-modedness check (task #81 / P7, THY_0039 §6) — discharges Theorem 3's
  // hypothesis: certify functional forced modes (§6.1), and (P2/P3) verify no
  // parameter is structurally matched or reaches an uncovered ⊕-guard. Presence-
  // gated on there being something parametric to check (an existential slot or
  // an internal-choice consequent). Warn-first: findings land on
  // calc.wellModedLint; cc.wellModed === 'strict' flips them to a load error
  // once the calculus's corpus is confirmed inside the accepted set.
  // Certification (§6.1) runs whenever there are clauses (it is independent of
  // whether the program has parametric rules; task #84 consumes it too). The
  // parametric checks inside (forcing goals, P2 taint/V1, P3 guard-coverage)
  // self-scope to programs with existentials / internal choice.
  let functionalPreds = new Set();
  let decidablePreds = new Set();
  let wellModedLint = null;
  if ((clauses && clauses.size > 0) || compiledRules.length > 0) {
    const _wm = checkWellModed({ compiledRules, clauses, definitions, cc });
    functionalPreds = _wm.functionalPreds;
    decidablePreds = _wm.decidablePreds;
    if (_wm.warnings.length > 0 || _wm.errors.length > 0) {
      wellModedLint = { warnings: _wm.warnings, errors: _wm.errors };
    }
    // Strictness comes from the CALCULUS (cc.wellModed: 'strict' — ILL, once
    // its corpus is confirmed clean, task #85) but a caller may override per
    // load (opts.wellModed, mirroring opts.strictTypes) — used to OBSERVE the
    // warnings of a deliberately ill-moded program rather than fail its load.
    //
    // Enforcement targets a FRESH, UNSPECIALIZED SOURCE load (THY_0039 Thm 3).
    // Two derived-artifact cases stay WARN-FIRST (findings on wellModedLint, no
    // throw), because the source-level taint analysis reads their rules
    // imprecisely and the source's well-modedness was already enforced at its
    // own fresh load:
    //   • SPECIALIZED (bytecode/grade-0 facts + basic-block fusion): fusion
    //     inlines backward goals into forward antecedents, so an inlined
    //     arr_get matching a GROUND pc's binary structure trips V1. Fusion is
    //     a trusted semantics-preserving transform (compose-equivalence tests).
    //   • A SNAPSHOT RESTORE (skipCompose: the compose/two-tier disk cache
    //     rebuilding from already-composed rules) — rebuilding a validated
    //     artifact, not re-vetting a source program.
    const _wellModed = opts.wellModed !== undefined ? opts.wellModed : cc.wellModed;
    const _derived = !!(opts.extraGrade0Facts || opts.fuseBasicBlocks || opts.skipCompose);
    if (_wellModed === 'strict' && !_derived && _wm.warnings.length > 0) {
      throw new Error(
        `Well-modedness (${_wm.warnings.length}):\n  ${_wm.warnings.join('\n  ')}`);
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
      // Grade-position vocabulary from calculus data (RES_0143 L6)
      gradeMeta: deriveGradeMeta(connectives, cc.gradeConfig || _defaultGradeConfig),
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
    // Certified total decision procedures (§6.1′) — explore intersects the
    // declared order guards with this set so an uncertified guard is never
    // pruned on an unbacked comparator (task #84).
    decidablePreds,
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

  // Family layer: the structural family's engine hooks arrive as DATA on the
  // calculus config (cc.family.engine, e.g. family/lnl/family-config.js) —
  // the generic engine imports no family module (TODO_0086). Absent family:
  // state-lookup-only persistent proving, null dynamic-rule slots.
  const _fam = (cc.family && cc.family.engine) || null;
  const _famProveNaive = _fam ? _fam.proveNaive : null;

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
        // Route the persistent-proving interface: FFI-accelerated vs the
        // family's naive clause prover (falls back to state-lookup-only when
        // no family is configured). Wiring decision belongs at the
        // composition root, not a single-field factory.
        provePersistent: useFFI ? _proveWithFFI : _famProveNaive,
      }),
      ..._match.buildFamilyProtocol({
        matchDynamicRule: _fam && _fam.matchDynamicRule,
        resolveEx: _fam && _fam.resolveEx,
        drainDynamicRules: _fam && _fam.drainDynamicRules,
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
        // Strategy A matcher fast path — profile-gated here (RES_0143 F4:
        // the deltaBypass profile flag used to gate nothing).
        deltaBypass: prof.deltaBypass ? _deltaBypassFn : null,
        useCompiledSteps: useFFI,
      }),
      ..._match.buildFfiProtocol(ffiContext),
    });
  }

  // Create engine with profile-driven function pointers (fingerprint injected)
  const _tEngineInit = _phaseStart();
  const prof = profile(opts.profile || cc.compile.profile);
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
  // Construction extracted verbatim to timed/timed-api.js (audit
  // 2026-09-02 readability split): grades-gated settle/views/game API +
  // the D16/C1-C3 load-time lints. null when cc declares no grades.
  const _timedApi = buildTimedApi({
    cc, compiledRules, compileOpts: _compileOpts(cc), calcContext, rc: _rc,
    filterRules, buildMatchOpts: _buildMatchOpts, clauses, definitions, backwardOpts,
  });

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
    // Well-modedness (task #81 / P7, THY_0039 §6): the certified-functional
    // forced modes ("pred#outPos") and the warn-first violation lint (null when
    // clean or when the check is not applicable). functionalPreds is consumed by
    // the forcing-goal check; decidablePreds (certified total decision
    // procedures, §6.1′) gates the G2 order-tell prune (task #84).
    functionalPreds,
    decidablePreds,
    wellModedLint,
    // Inside masses (fence B slices 2+3): state name (classifier ⊤,
    // datasort, or product key) → exact [n, d] mass — null unless the
    // program declares recursive datasorts (presence-gated; solved at
    // load by the calculus-bound solver, extended lazily for products).
    masses: stateMasses,
    _datasortMass: cc.datasortMasses || null,
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
      // Per-run backward-cache lifecycle (RES_0143 F4): cached FAILURES
      // are only valid against one persistent context — clear at the
      // boundary that owns the cache wiring (provePersistent above).
      _clearBWCache();
      return forward.run(state, rules, { ...execOpts, calc: calcContext, engine: eng, matchOpts });
    },

    // Exhaustive exploration (same filtering as exec) (T16)
    explore: (state, execOpts = {}) => {
      const rules = filterRules(execOpts);
      const matchOpts = execOpts.matchOpts || _buildMatchOpts(execOpts);
      // Domain state-representation conversion at the orchestrator
      // boundary (RES_0143 L8): noFFI converts bytecode arrlits -> tries
      // for clause resolution; FFI mode keeps arrlit for O(1) arr_get.
      // explore.js itself performs no domain conversion.
      //
      // Gated on the ABSENCE of grade-0-fact specialization (TODO_0307
      // Track 2): when bytecode facts are injected as grade-0 (opts.extra-
      // Grade0Facts, incl. the `bytecode: '0x…'` sugar), arr_get(bytecode,…)
      // is resolved AT COMPILE TIME, so no clause navigates the bytecode at
      // runtime — the trie buys nothing. The specialized rules PRESERVE the
      // bytecode as `bytecode(arrlit …)`, so converting the live fact to a
      // trie would make that pattern un-matchable and silently stall the run
      // (the FFI-off hole: fired under FFI, dead under clause resolution).
      const _b2t = cc.domain && cc.domain.bytecodeToTrie;
      if (_b2t && !execOpts.dangerouslyUseFFI && !opts.extraGrade0Facts && state.linear && !state.linear.group) {
        state = _b2t(state);
      }
      _clearBWCache(); // per-run cache lifecycle (RES_0143 F4 — see exec)
      // Structural-memo control predicates from cc.domain.memoControlTags
      // (RES_0143 L5: the key existed but was never consumed — the memo
      // silently ran on hardcoded EVM names for every calculus).
      const _mct = (cc.domain && cc.domain.memoControlTags) || null;
      const controlOpts = execOpts.controlOpts ||
        (_mct && _mct.length ? { pcPred: _mct[0], stackPred: _mct[1] || null } : null);
      return explore.explore(state, rules, {
        ...execOpts, calc: calcContext, engine: eng, matchOpts,
        controlOpts,
        predictNext: _predictNext,
        structuralMemoFns: _structuralMemoFns,
      });
    },

    // Exposed for direct callers that need pre-built matchOpts
    _calcContext: calcContext,
    _buildMatchOpts,
  };

  // ── API attachers (RES_0143 F6) ──────────────────────────────────
  // Post-construction api extensions, each self-gated, returning a
  // partial api or null. The measure layer (decimation driver + CI
  // certifier) is the engine-default attacher; a CALCULUS adds its own
  // methods via cc.apiExtensions — the api surface is config-extensible
  // without touching this file.
  const _attachCtx = { api, cc, calc: calcContext, sortSystem };
  const _attachers = [
    ({ api, cc, sortSystem }) => buildCollapseApi(api, cc, sortSystem),
    // Confluence certifier (TODO_0309 P2, THY_0036): certifies the
    // RUNTIME rule set (post grade-0 filter) + an initial state under a
    // caller-declared destination discipline; the certificate feeds
    // explore's opts.confluence (single-interleaving commit).
    () => ({
      certifyConfluence: (initialState, o = {}) => {
        const plain = initialState && initialState.linear && initialState.linear.group
          ? _fsToObject(initialState) : initialState;
        return certifyConfluence(filterRules({}), plain, { rc: _rc, ...o });
      },
    }),
    ...(cc.apiExtensions || []),
  ];
  for (const attach of _attachers) {
    Object.assign(api, attach(_attachCtx) || {});
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
 * Load without caching (old behavior).
 */
function _loadFresh(filePath, extraOpts) {
  const onPhase = extraOpts && extraOpts.onPhase;
  const _cc = _requireConfig(extraOpts && extraOpts.calculusConfig, 'engine _loadFresh');
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
  // compile as ILL. Required since audit 2026-09-02 (no engine default).
  const cc = _requireConfig(opts.calculusConfig, 'mde.load');

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

    // Bytecode loading is DOMAIN machinery — the calculus config binds it
    // (cc.domain.loadBytecode / bytecodeArrGetGuard; ILL's EVM loader lives
    // in calculus/ill/lib/bytecode-loader.js). A calculus without the
    // binding structurally lacks the bytecode API.
    if (!cc.domain || !cc.domain.loadBytecode) {
      throw new Error('mde.load: opts.bytecode requires a calculus config that binds a bytecode loader (cc.domain.loadBytecode)');
    }
    const bc = cc.domain.loadBytecode(bytecodeHex);
    extraGrade0Facts = bc.facts;
    scopeGuard = cc.domain.bytecodeArrGetGuard;
    // Jump-target fusion barriers (TODO_0307 Bug A): fusing a JUMPDEST away
    // leaves a dynamic jump there with no entry rule. The loader provides the
    // barrier arg-hash set; wire it unless the caller supplied its own.
    if (bc.barrierRefs && !fusionBarriers) fusionBarriers = bc.barrierRefs;
  }
  // Default fuseBasicBlocks on when external grade-0 facts are provided —
  // compose is always beneficial with concrete fact sets (5x execution speedup).
  const fuseBasicBlocks = opts.fuseBasicBlocks !== undefined
    ? opts.fuseBasicBlocks
    : !!extraGrade0Facts;
  const onPhase = opts.onPhase || null;
  const composeOpts = { calculusConfig: cc, extraGrade0Facts, scopeGuard, residualResolver, fuseBasicBlocks,
        chainFusionPredicates, linearFusionPredicate, sroaConfig,
        composeDiskCache, fusionBarriers, onPhase, skipSpecialize,
        strictTypes: opts.strictTypes, wellModed: opts.wellModed };

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
      const cached = _loadCSnap(composeCachePath, { rootLabel, labelDeps: ld, calculusConfig: cc });
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
      const replay = _loadCSnap(composeCachePath, { rootLabel, labelDeps: ld, calculusConfig: cc });
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

  // Two-tier file-hash cache (cache: true / 'imports') — the strategy
  // lives in cache/load-cache.js (audit item 7); the builder, fresh
  // fallback, precompiled loader, and config-bound rule compiler are
  // injected (the compose-cache pattern).
  return loadTwoTier(filePath, cacheMode, opts, {
    cc,
    compileRule: (r) => forward.compileRule(r, _compileOpts(cc)),
    buildCalc: _buildCalc,
    loadFresh: () => _loadFresh(filePath, composeOpts),
    loadPrecompiled,
  });
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
  const cc = _requireConfig(opts.calculusConfig, 'mde.precompile');
  const { definitions, clauses, forwardRules, queries, argNamesTable, sortVarsTable, priorsTable } =
    convert.load(filePaths, { loaderConfig: cc.loader });
  const compiledRules = forwardRules.map(r => forward.compileRule(r, _compileOpts(cc)));
  const byteSize = snapToFile(cachePath, definitions, clauses, forwardRules, compiledRules, queries, argNamesTable, sortVarsTable, priorsTable);
  return { definitions, clauses, forwardRules, queries, argNamesTable, sortVarsTable, priorsTable, byteSize };
}

/**
 * Load from precompiled binary cache.
 * Restores Store state and uses cached compiled rules.
 *
 * NOTE: a .bin has no config association — a cache written by
 * precompile(..., { calculusConfig }) must be loaded with the SAME config
 * in sellOpts.calculusConfig. Loading without one THROWS (audit
 * 2026-09-02; formerly it silently built under the ILL default — audit
 * round 12, F5).
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
  if (compiledRules) opts.compiledRules = deserRules(compiledRules);
  return _buildCalc(definitions, clauses, forwardRules, queries, opts);
}

const parseExpr = convert.parseExpr;
const hasMonad = convert.hasMonad;
// decomposeQuery is the GENERIC query decomposition (convert.js). The EVM
// bytecode-normalizing variant (normalizeQuery) is DOMAIN machinery and
// lives with its calculus: calculus/ill (facade + cc.domain.normalizeQuery).
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
  prove,
  exec,
  createState,
  compileRule,
  Store,
  _composeCacheKey,
};

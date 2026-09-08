/**
 * ILL Calculus Configuration — single assembly point.
 *
 * Bundles all ILL-specific configuration into one object.
 * This is the ONLY file (besides ill/ submodules) that imports from ill/.
 * The generic engine receives this config via opts.calculusConfig.
 *
 * Layered design mirroring the prover lasagne (L0-L6):
 *   L0: Kernel init (atoms + theories)
 *   L1: Structural (connective table + theories)
 *   L2: Compile (rule compilation config)
 *   L3: Backward (backward chaining defaults)
 *   L4: FFI (optimization dispatch)
 *   L5: Compose (grade-0 pipeline)
 *   L6: Domain (EVM-specific)
 */

'use strict';

import { lnlFamily } from '../../family/lnl/family-config.js';
import { buildForwardParser } from './lib/forward-parser.js';
import { connTagsFrom } from '../../lib/engine/formula-utils.js';
import { illConnectives } from './lib/connectives.js';
import { binlitTheory } from './lib/binlit-theory.js';
import backchainIll from './lib/backchain-ill.js';
import { ILL_CHAIN_CONFIGS, ILL_SROA_CONFIG } from './lib/compose-config.js';
import { bytecodeToTrie, codeToArrlit, bytesToSemantic, normalizeQuery } from './lib/bytecode-normalize.js';
import { loadBytecode, bytecodeArrGetGuard } from './lib/bytecode-loader.js';
import { binToInt, isGround as _binIsGround } from './lib/ffi/convert.js';
import { trieNav } from './lib/ffi/array.js';
// EVM debug/inspection policy (RES_0143 L2): the terminal atoms, control
// predicate, and noisy-predicate exclusions ARE calculus data — they live
// here, not as show.js defaults. The generic classifyLeaf/showInteresting
// take these via cc.domain; the facade exports pre-bound versions.
const EVM_LEAF_POLICY = Object.freeze({
  terminals: Object.freeze({ stop: 'STOP', revert: 'REVERT', invalid: 'INVALID' }),
  runningPred: 'pc',
});
const EVM_SHOW_EXCLUDE = Object.freeze(['bytecode', 'calldata']);
import { monadUnit, grade0 } from '../../lib/engine/grades.js';
import Store from '../../lib/kernel/store.js';
import * as _ffiMod from './lib/ffi/index.js';
import { residualResolver as _residualResolverFn } from './lib/residual-resolver.js';

function _getFfi() { return _ffiMod; }
function _getResidualResolver() { return _residualResolverFn; }

const illCalculusConfig = {
  // ── Structural family: LNL (two zones, cartesian ! + linear) ──
  family: lnlFamily,

  // ── L0: Kernel Init ──────────────────────────────────────────
  // Called once at calc build time. Registers ILL-specific atoms
  // and installs equational theories into the global unifier.
  init() { backchainIll.initILL(); },

  // ── L1: Structural ───────────────────────────────────────────
  // Derived from ill.calc @category/@polarity annotations (lazy — see
  // connectives.js; TODO_0268 item B killed the hand-written mirror).
  get connectives() { return illConnectives(); },
  // Closed-world sort checking (Phase 6 post-mortem): the real ILL corpus
  // (prelude, EVM, multisig — audited 2026-08-19) is fully declared; only
  // synthetic engine-test fixtures needed fixing. Loads with undeclared
  // symbols FAIL; strictTypes: false opts out per load (deliberately
  // ill-sorted engine fixtures).
  typeCheck: 'strict',
  theories: [binlitTheory],
  // Unit grade of the (binary, D6-merged) lax monad: `{B}` elides it in
  // the parser/renderer; compile.js skips it during delay extraction.
  gradeUnit: monadUnit,
  // Two slots ILL deliberately OMITS (absence ⇒ trivial; TODO_0265 Phase 3):
  //   gradeConfig: { grade0: () => hash, gradeOmega: () => hash }
  //     — the bang-grade atoms resolveConn threads to every formula walker
  //       (default: engine/grades.js {0, 1, ω}).
  //   grades: { effect: { unit, compose, leq }, availability: { join, cmp },
  //             windows: { after, before } }
  //     — the grade ALGEBRA over content-addressed rational terms; till
  //       supplies the tropical instance (⊕ = max on availability,
  //       ⊗ = + on duration), and its availability.cmp doubles as the
  //       FactSet index policy comparator (D5).
  // ── L2: Loader ───────────────────────────────────────────────
  // convert.js loaderConfig — buildParser is ILL-own machinery
  // (forward-parser.js); connTags DERIVED from ill.calc's connective
  // table like every other calculus (RES_0143 L7 — this used to import
  // the lib-side default record, an inverted dependency).
  loader: {
    buildParser: buildForwardParser,
    get connTags() {
      if (!this._ct) this._ct = connTagsFrom(illConnectives());
      return this._ct;
    },
    grade0,
    timed: false,
  },

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    get getModes() { return _getFfi().getModes; },
    get getModeMeta() { return _getFfi().getModeMeta; },
    // Virtual-discriminator predicates (compile.js Phase B2): persistent
    // !arr_get(array, index, GROUND) patterns act as fingerprint
    // discriminators for EVM bytecode dispatch.
    discriminatorPreds: ['arr_get'],
    // Compile-cache namespace — compiled rules depend on the opts above, so
    // each calculus config gets its own cache epoch.
    cacheEpoch: 'ill',
  },

  // ── L3: Backward ─────────────────────────────────────────────
  backward: {
    normalize: backchainIll.normalize,
    tryFFI: backchainIll.tryFFI,
    getFFIMeta: backchainIll.getFFIMeta,
    buildClauseTerm: backchainIll.buildClauseTerm,
    buildFFITerm: backchainIll.buildFFITerm,
    buildTypeTerm: backchainIll.buildTypeTerm,
  },

  // ── L4: FFI ──────────────────────────────────────────────────
  ffi: {
    get meta() { return _getFfi().defaultMeta; },
    get parsedModes() { return _getFfi().parsedModes; },
    get get() { return _getFfi().get; },
    get isFFIGround() { return _getFfi().convert.isGround; },
    evalNumeric: binToInt,
  },

  // ── L5: Compose ──────────────────────────────────────────────
  compose: {
    chainConfigs: ILL_CHAIN_CONFIGS,
    sroaConfig: ILL_SROA_CONFIG,
    linearFusionPredicate: 'pc',
    get residualResolver() { return _getResidualResolver(); },
  },

  // ── L6: Domain (EVM) ────────────────────────────────────────
  domain: {
    evalNumeric(h) { return _binIsGround(h) ? binToInt(h) : null; },
    // Which persistent predicates carry equality/disequality semantics for
    // the branch-pruning solver (RES_0143 L3): declared in bin.ill with
    // backward clauses; the solver treats them as constraints, everything
    // else is opaque.
    constraintPreds: { eq: 'eq', neq: 'neq' },
    memoControlTags: ['pc', 'stack'],
    // Debug/inspection policy (show.js): EVM terminal atoms + control pred,
    // and the noisy predicates excluded from showInteresting. Defined at the
    // top of this file — a second logic declares its own in its config
    // (TODO_0265 Phase 2b; RES_0143 L2 removed the show.js copies).
    classifyLeafPolicy: EVM_LEAF_POLICY,
    showExclude: EVM_SHOW_EXCLUDE,
    // Bytecode API bindings (mde.load opts.bytecode routes through these;
    // a calculus without them structurally lacks the bytecode API).
    loadBytecode,
    bytecodeArrGetGuard,
    bytecodeToTrie,
    codeToArrlit,
    bytesToSemantic,
    normalizeQuery,
    trieNav,
    lookupArrayValue(keyHash, arrayHash) {
      const idx = binToInt(keyHash);
      if (idx === null) return null;
      const elems = Store.getArrayElements(arrayHash);
      if (elems) {
        if (idx < 0n || idx >= BigInt(elems.length)) return null;
        return elems[Number(idx)];
      }
      return trieNav(arrayHash, idx);
    },
  },
};

export default illCalculusConfig;
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

import { ILL_CONNECTIVES } from './connectives.js';
import { binlitTheory } from './binlit-theory.js';
import backchainIll from './backchain-ill.js';
import { ILL_CHAIN_CONFIGS, ILL_SROA_CONFIG } from './compose-config.js';
import { bytecodeToTrie, codeToArrlit, bytesToSemantic, normalizeQuery } from './bytecode-normalize.js';
import { binToInt, isGround as _binIsGround } from './ffi/convert.js';
import { trieNav } from './ffi/array.js';
import { DEFAULT_LEAF_POLICY, DEFAULT_SHOW_EXCLUDE } from '../show.js';
import Store from '../../kernel/store.js';
import * as _ffiMod from './ffi/index.js';
import { residualResolver as _residualResolverFn } from './residual-resolver.js';

function _getFfi() { return _ffiMod; }
function _getResidualResolver() { return _residualResolverFn; }

const illCalculusConfig = {
  // ── L0: Kernel Init ──────────────────────────────────────────
  // Called once at calc build time. Registers ILL-specific atoms
  // and installs equational theories into the global unifier.
  init() { backchainIll.initILL(); },

  // ── L1: Structural ───────────────────────────────────────────
  connectives: ILL_CONNECTIVES,
  theories: [binlitTheory],

  // ── L2: Compile ──────────────────────────────────────────────
  compile: {
    get getModes() { return _getFfi().getModes; },
    get getModeMeta() { return _getFfi().getModeMeta; },
    // Virtual-discriminator predicates (compile.js Phase B2): persistent
    // !arr_get(array, index, GROUND) patterns act as fingerprint
    // discriminators for EVM bytecode dispatch.
    discriminatorPreds: ['arr_get'],
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
    memoControlTags: ['pc', 'stack'],
    // Debug/inspection policy (show.js): EVM terminal atoms + control pred,
    // and the noisy predicates excluded from showInteresting. These ARE the
    // show.js compat defaults — named here so a second logic overrides them
    // in its own config instead of patching show.js (TODO_0265 Phase 2b).
    classifyLeafPolicy: DEFAULT_LEAF_POLICY,
    showExclude: DEFAULT_SHOW_EXCLUDE,
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
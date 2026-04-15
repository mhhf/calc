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

const { ILL_CONNECTIVES } = require('./connectives');
const { binlitTheory } = require('./binlit-theory');
const backchainIll = require('./backchain-ill');
const { ILL_CHAIN_CONFIGS, ILL_SROA_CONFIG } = require('./compose-config');
const { bytecodeToTrie, codeToArrlit, bytesToSemantic, normalizeQuery } = require('./bytecode-normalize');
const { binToInt, isGround: _binIsGround } = require('./ffi/convert');
const { trieNav } = require('./ffi/array');
const Store = require('../../kernel/store');

// Lazy loading to avoid circular deps
let _ffi = null;
function _getFfi() {
  if (!_ffi) _ffi = require('./ffi');
  return _ffi;
}


let _residualResolver = null;
function _getResidualResolver() {
  if (!_residualResolver) _residualResolver = require('./residual-resolver').residualResolver;
  return _residualResolver;
}

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

module.exports = illCalculusConfig;

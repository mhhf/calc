/**
 * ILL Binlit Equational Theory
 *
 * Layer: ILL (Intuitionistic Linear Logic)
 *
 * Single source of truth for binary number equational theory.
 * Used by: unify.js (via setTheories), backchain.js (theory lookup),
 * backchain-ill.js (normalize = canonicalize), match.js (_normalizeBin).
 *
 * Binary number representational equivalence:
 *   binlit(10n) ↔ o(i(o(i(e))))
 *   binlit(0n)  ↔ atom('e')
 *
 * Both representations are semantically identical. The compact binlit form
 * is preferred for state storage (O(1) equality). The structural form
 * appears in rule patterns and clause heads.
 */

const Store = require('../../kernel/store');

// Tag IDs — built-in tags are stable.
// Predicate tags (i, o) are registered dynamically, resolved lazily.
const _TAG_BINLIT = Store.TAG.binlit;
const _TAG_ATOM = Store.TAG.atom;
const _TAG_STRLIT = Store.TAG.strlit;
const _TAG_CHARLIT = Store.TAG.charlit;
const _TAG_FREEVAR = Store.TAG.freevar;
const _TAG_METAVAR = Store.TAG.metavar;
const _TAG_ARRLIT = Store.TAG.arrlit;

function _tagO() { return Store.TAG.o; }
function _tagI() { return Store.TAG.i; }

// Lazy FFI import for binToInt/intToBin
let _convert = null;
function _getConvert() {
  if (!_convert) _convert = require('./ffi/convert');
  return _convert;
}

const binlitTheory = {
  name: 'binlit',
  sourceTagIds: [_TAG_BINLIT],

  canRewrite(srcTid, dstTid) {
    if (srcTid === _TAG_BINLIT) {
      return dstTid === _TAG_ATOM || dstTid === _tagO() || dstTid === _tagI();
    }
    return false;
  },

  /**
   * Rewrite binlit to structural form matching the destination tag.
   *
   *   binlit(0n)  + dstTid=atom → atom('e')
   *   binlit(10n) + dstTid=o    → o(binlit(5n))
   *   binlit(7n)  + dstTid=i    → i(binlit(3n))
   */
  rewrite(srcTid, srcHash, dstTid, dstArity) {
    if (srcTid !== _TAG_BINLIT) return null;
    const val = Store.child(srcHash, 0);
    if (typeof val !== 'bigint') return null;

    if (val === 0n && dstTid === _TAG_ATOM) return Store.put('atom', ['e']);
    if (dstTid === _tagO() && dstArity === 1 && val > 0n && (val & 1n) === 0n)
      return Store.put('o', [Store.put1('binlit', val >> 1n)]);
    if (dstTid === _tagI() && dstArity === 1 && (val & 1n) === 1n)
      return Store.put('i', [Store.put1('binlit', val >> 1n)]);

    return null;
  },

  /**
   * Canonicalize: normalize structural binary (i/o/e chains) to compact binlit.
   *
   * Prevents hash divergence between forward engine state and clause resolution
   * results. Structural forms like i(o(e)) are converted to binlit(2n).
   *
   * Recurses into compound terms (tensor, loli, etc.) to normalize embedded
   * binary subterms. Leaves non-binary terms unchanged.
   */
  canonicalize(h) {
    if (!Store.isTerm(h)) return h;
    const tid = Store.tagId(h);

    // Binary constructors → compact binlit
    const ti = _tagI(), to = _tagO();
    if (ti !== undefined && (tid === ti || tid === to)) {
      const convert = _getConvert();
      const v = convert.binToInt(h);
      if (v !== null) return convert.intToBin(v);
    }

    // atom('e') → binlit(0n)
    if (tid === _TAG_ATOM) {
      if (Store.child(h, 0) === 'e') {
        const convert = _getConvert();
        const v = convert.binToInt(h);
        if (v !== null) return convert.intToBin(v);
      }
      return h;
    }

    // Leaf types — no recursion needed
    if (tid === _TAG_BINLIT || tid === _TAG_STRLIT ||
        tid === _TAG_CHARLIT || tid === _TAG_FREEVAR || tid === _TAG_METAVAR) return h;

    // arrlit — recurse into elements
    if (tid === _TAG_ARRLIT) {
      const elems = Store.getArrayElements(h);
      if (!elems || elems.length === 0) return h;
      let changed = false;
      const newElems = new Uint32Array(elems.length);
      for (let i = 0; i < elems.length; i++) {
        const ne = binlitTheory.canonicalize(elems[i]);
        newElems[i] = ne;
        if (ne !== elems[i]) changed = true;
      }
      return changed ? Store.putArray(newElems) : h;
    }

    // Compound terms — recurse into children
    const arity = Store.arity(h);
    if (arity === 0) return h;
    let changed = false;
    const nc = [];
    for (let i = 0; i < arity; i++) {
      const c = Store.child(h, i);
      if (typeof c === 'number' && Store.isTerm(c)) {
        const rc = binlitTheory.canonicalize(c);
        nc.push(rc);
        if (rc !== c) changed = true;
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(Store.tag(h), nc) : h;
  }
};

module.exports = { binlitTheory };

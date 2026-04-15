/**
 * EVM bytecode normalization — domain-specific state transformations.
 *
 * Layer: ILL (domain-specific)
 *
 * Converts between bytecode representations:
 *   code PC V (linear facts) → bytecode(arrlit) → bytecode(trie)
 *
 * These functions are EVM-specific: they understand 'code', 'bytecode' tags,
 * PUSH opcodes (0x60-0x7f), and binary numeral encoding (binlit/i/o/e).
 *
 * Moved from engine/index.js to break ILL coupling from the generic engine.
 */

const Store = require('../../kernel/store');

/**
 * Convert `code PC V` linear facts into a single `bytecode` arrlit fact.
 * Operates on plain state objects { linear: {hash:count}, persistent: {hash:true} }.
 * Returns a new state with code facts replaced by a bytecode fact.
 * No-op if no code facts found or bytecode fact already exists.
 */
function codeToArrlit(state) {
  const { binToInt } = require('./ffi/convert');
  const codeTagId = Store.TAG['code'];
  const bcTagId = Store.TAG['bytecode'];
  if (codeTagId === undefined) return state;

  // Check if bytecode already exists
  if (bcTagId !== undefined) {
    for (const h of Object.keys(state.linear)) {
      if (Store.tagId(Number(h)) === bcTagId) return state;
    }
  }

  // Collect code facts: { pc: int, val: hash, factHash: number }
  const codeFacts = [];
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) === codeTagId && state.linear[hStr] > 0) {
      const pcHash = Store.child(h, 0);
      const valHash = Store.child(h, 1);
      const pcInt = binToInt(pcHash);
      if (pcInt !== null) {
        codeFacts.push({ pc: Number(pcInt), val: valHash, hash: h });
      }
    }
  }

  if (codeFacts.length === 0) return state;

  // Build sparse arrlit: fill gaps with 0 (intToBin(0))
  const maxPC = Math.max(...codeFacts.map(f => f.pc));
  const elements = new Uint32Array(maxPC + 1);
  for (const f of codeFacts) {
    elements[f.pc] = f.val;
  }

  const arrHash = Store.putArray(elements);
  const bytecodeHash = Store.put('bytecode', [arrHash]);

  // Build new linear state: remove code facts, add bytecode
  const newLinear = {};
  for (const [hStr, count] of Object.entries(state.linear)) {
    if (Store.tagId(Number(hStr)) !== codeTagId) {
      newLinear[hStr] = count;
    }
  }
  newLinear[bytecodeHash] = 1;

  return { linear: newLinear, persistent: state.persistent };
}

/**
 * Convert byte-by-byte bytecode arrlit → semantic arrlit.
 * Walks the byte array identifying PUSH opcodes (0x60-0x7f) and combining
 * their N data bytes (N = opcode - 0x5f) into single big-endian values.
 *
 * Guard: all elements must be ground binlit with value <= 0xFF.
 * Returns new state with semantic bytecode, or original if already semantic.
 */
function bytesToSemantic(state) {
  const { intToBin } = require('./ffi/convert');
  const bcTagId = Store.TAG['bytecode'];
  if (bcTagId === undefined) return state;

  // Find bytecode fact
  let bcFactHash = null;
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) === bcTagId) { bcFactHash = h; break; }
  }
  if (bcFactHash === null) return state;

  const arrHash = Store.child(bcFactHash, 0);
  const elems = Store.getArrayElements(arrHash);
  if (!elems || elems.length === 0) return state;

  // Guard: check all elements are ground binlit with value <= 0xFF
  let isByteLevel = true;
  for (let i = 0; i < elems.length; i++) {
    const t = Store.tag(elems[i]);
    if (t !== 'binlit') { isByteLevel = false; break; }
    const v = Store.child(elems[i], 0);
    if (typeof v !== 'bigint' || v > 0xFFn) { isByteLevel = false; break; }
  }
  if (!isByteLevel) return state; // already semantic or mixed

  // Pre-scan to find required array length (PUSH data may extend beyond bytecode)
  let requiredLen = elems.length;
  {
    let scanPc = 0;
    while (scanPc < elems.length) {
      const opVal = Number(Store.child(elems[scanPc], 0));
      if (opVal >= 0x60 && opVal <= 0x7f) {
        const n = opVal - 0x5f;
        const nextPc = scanPc + 1 + n;
        const needed = nextPc >= elems.length ? nextPc + 1 : scanPc + 2;
        if (needed > requiredLen) requiredLen = needed;
        scanPc = nextPc;
      } else {
        scanPc++;
      }
    }
  }

  // Walk bytes, group PUSHn data
  const semantic = new Uint32Array(requiredLen);
  const zeroBinlit = intToBin(0n);
  let pc = 0;
  while (pc < elems.length) {
    const opVal = Number(Store.child(elems[pc], 0));
    semantic[pc] = elems[pc]; // opcode itself
    if (opVal >= 0x60 && opVal <= 0x7f) {
      const n = opVal - 0x5f;
      let combined = 0n;
      const available = Math.min(n, elems.length - (pc + 1));
      for (let j = 0; j < available; j++) {
        combined = (combined << 8n) | Store.child(elems[pc + 1 + j], 0);
      }
      combined <<= BigInt((n - available) * 8); // pad missing bytes with 0
      semantic[pc + 1] = intToBin(combined);
      for (let j = 2; j <= n && pc + j < elems.length; j++) {
        semantic[pc + j] = zeroBinlit;
      }
      pc += 1 + n;
    } else {
      pc++;
    }
  }
  // EVM spec: bytes beyond bytecode are 0x00 (STOP opcode)
  for (let i = elems.length; i < requiredLen; i++) {
    if (semantic[i] === 0) semantic[i] = zeroBinlit;
  }

  const newArrHash = Store.putArray(semantic);
  const newBcHash = Store.put('bytecode', [newArrHash]);

  const newLinear = {};
  for (const [hStr, count] of Object.entries(state.linear)) {
    if (Number(hStr) === bcFactHash) {
      newLinear[newBcHash] = count;
    } else {
      newLinear[hStr] = count;
    }
  }

  return { linear: newLinear, persistent: state.persistent };
}

/**
 * Convert bytecode arrlit to trie representation.
 * arrlit is an I/O format; trie (tn) is the logical representation
 * that compiled clause dispatch can resolve without FFI.
 */
function bytecodeToTrie(state) {
  const { arrToTrie } = require('./ffi/array');
  const bcTagId = Store.TAG['bytecode'];
  if (bcTagId === undefined) return state;

  let bcFactHash = null;
  for (const hStr of Object.keys(state.linear)) {
    const h = Number(hStr);
    if (Store.tagId(h) === bcTagId) { bcFactHash = h; break; }
  }
  if (bcFactHash === null) return state;

  const arrHash = Store.child(bcFactHash, 0);
  // Already a trie — no conversion needed
  if (Store.tag(arrHash) === 'tn' || Store.tag(arrHash) === 'atom') return state;

  const elems = Store.getArrayElements(arrHash);
  if (!elems) return state;

  const trieHash = arrToTrie(arrHash);
  if (trieHash === arrHash) return state; // arrToTrie returned unchanged

  const newBcHash = Store.put('bytecode', [trieHash]);
  const newLinear = {};
  for (const [hStr, count] of Object.entries(state.linear)) {
    if (Number(hStr) === bcFactHash) {
      newLinear[newBcHash] = count;
    } else {
      newLinear[hStr] = count;
    }
  }
  // Cache original elements for O(1) prediction (trie is O(log N) per lookup)
  const result = { linear: newLinear, persistent: state.persistent };
  result._bytecodeElems = elems;
  return result;
}

/**
 * Normalize bytecode state: convert old code facts → arrlit, then byte→semantic.
 * Wraps decomposeQuery for backward compatibility.
 *
 * arrlit→trie conversion is deferred: explore() calls bytecodeToTrie in noFFI mode
 * where clause resolution needs trie format. FFI mode keeps arrlit for O(1) access.
 */
function normalizeQuery(hash) {
  const convert = require('../convert');
  let state = convert.decomposeQuery(hash);
  state = codeToArrlit(state);
  state = bytesToSemantic(state);
  return state;
}

module.exports = {
  codeToArrlit,
  bytesToSemantic,
  bytecodeToTrie,
  normalizeQuery,
};

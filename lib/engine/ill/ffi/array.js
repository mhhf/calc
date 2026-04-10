/**
 * Array FFI — O(1) arrlit + O(log N) trie operations
 *
 * All functions follow the standard FFI pattern:
 *   (args: number[]) → { success: boolean, theta?: [var, val][], reason?: string }
 */

const Store = require('../../../kernel/store');
const { binToInt, intToBin, isGround } = require('./convert');

// ── Trie tag cache (lazy-init after calculus load) ──────────────────────────

let _tnTag = 0;
let _tnNilHash = 0;

function tnTag() {
  if (!_tnTag) _tnTag = Store.TAG['tn'];
  return _tnTag;
}

function tnNilHash() {
  if (!_tnNilHash) _tnNilHash = Store.put('atom', ['tn_nil']);
  return _tnNilHash;
}

// Reset cached hashes when Store is cleared (test isolation)
Store.onClear(() => { _tnTag = 0; _tnNilHash = 0; });

// ── Trie navigation (shared by FFI and arrToTrie) ───────────────────────────

/**
 * Navigate a trie term in the Store by integer index.
 * Returns the value hash at the given index, or null if the path doesn't exist.
 * O(log N) where N = index value (number of bits).
 */
function trieNav(node, idx) {
  const tag = tnTag();
  let bits = idx;

  while (true) {
    if (Store.tagId(node) !== tag) return null;
    if (bits === 0n) return Store.rawChild(node, 1); // tn(L, V, R) → V
    const bit = bits & 1n;
    bits >>= 1n;
    node = Store.rawChild(node, bit === 0n ? 0 : 2); // left or right
  }
}

// ── arrToTrie: convert arrlit → trie term ───────────────────────────────────

/**
 * Convert an arrlit hash to a bit-indexed trie term in the Store.
 * Returns the trie root hash, or the input unchanged if not an arrlit.
 */
function arrToTrie(arrHash) {
  const elems = Store.getArrayElements(arrHash);
  if (!elems || elems.length === 0) return arrHash;

  const nil = tnNilHash();
  const zero = intToBin(0n);

  // Build trie by inserting each element
  let root = nil;
  for (let i = 0; i < elems.length; i++) {
    root = _trieInsert(root, BigInt(i), elems[i], nil, zero);
  }
  return root;
}

function _trieInsert(node, index, value, nil, zero) {
  if (index === 0n) {
    // Place/replace value at this node
    if (node === nil) {
      return Store.put('tn', [nil, value, nil]);
    }
    const left = Store.rawChild(node, 0);
    const right = Store.rawChild(node, 2);
    return Store.put('tn', [left, value, right]);
  }

  const bit = index & 1n;
  const rest = index >> 1n;

  let left, val, right;
  if (node === nil) {
    left = nil; val = zero; right = nil;
  } else {
    left = Store.rawChild(node, 0);
    val = Store.rawChild(node, 1);
    right = Store.rawChild(node, 2);
  }

  if (bit === 0n) {
    left = _trieInsert(left, rest, value, nil, zero);
  } else {
    right = _trieInsert(right, rest, value, nil, zero);
  }
  return Store.put('tn', [left, val, right]);
}

// ── arr_get FFI ─────────────────────────────────────────────────────────────

/**
 * FFI for arr_get: arr_get Array Index Value
 * Mode: + + -
 * Handles both arrlit (O(1)) and trie (O(log N)).
 */
function arr_get(args) {
  const [arrHash, idxHash, valHash] = args;

  if (!isGround(arrHash) || !isGround(idxHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  // Fast path: arrlit — O(1)
  const elems = Store.getArrayElements(arrHash);
  if (elems) {
    const idx = binToInt(idxHash);
    if (idx === null) return { success: false, reason: 'index_not_int' };
    if (idx < 0n || idx >= BigInt(elems.length)) return { success: false, reason: 'out_of_bounds' };
    return { success: true, theta: [[valHash, elems[Number(idx)]]] };
  }

  // Trie path — O(log N)
  const idx = binToInt(idxHash);
  if (idx === null) return { success: false, reason: 'index_not_int' };
  const val = trieNav(arrHash, idx);
  if (val === null) return { success: false, reason: 'trie_miss' };
  return { success: true, theta: [[valHash, val]] };
}

// ── trie_get FFI ────────────────────────────────────────────────────────────

/**
 * FFI for trie_get: trie_get Trie Index Value
 * Mode: + + -
 * O(log N) trie navigation in JS.
 */
function trie_get(args) {
  const [trieHash, idxHash, valHash] = args;

  if (!isGround(trieHash) || !isGround(idxHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const idx = binToInt(idxHash);
  if (idx === null) return { success: false, reason: 'index_not_int' };
  const val = trieNav(trieHash, idx);
  if (val === null) return { success: false, reason: 'trie_miss' };
  return { success: true, theta: [[valHash, val]] };
}

// ── arr_set FFI ─────────────────────────────────────────────────────────────

/**
 * FFI for arr_set: arr_set Array Index Value Result
 * Mode: + + + -
 * Handles both arrlit (O(1) copy) and trie (O(log N) path copy).
 */
function arr_set(args) {
  const [arrHash, idxHash, valHash, resultHash] = args;

  if (!isGround(arrHash) || !isGround(idxHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  // Fast path: arrlit — O(1) copy
  const elems = Store.getArrayElements(arrHash);
  if (elems) {
    const idx = binToInt(idxHash);
    if (idx === null) return { success: false, reason: 'index_not_int' };
    if (idx < 0n || idx >= BigInt(elems.length)) return { success: false, reason: 'out_of_bounds' };
    const newData = new Uint32Array(elems.length);
    newData.set(elems);
    newData[Number(idx)] = valHash;
    const newArr = Store.put('arrlit', [newData]);
    return { success: true, theta: [[resultHash, newArr]] };
  }

  // Trie path — O(log N) path copy
  const idx = binToInt(idxHash);
  if (idx === null) return { success: false, reason: 'index_not_int' };
  const newRoot = _trieSet(arrHash, idx, valHash);
  if (newRoot === null) return { success: false, reason: 'trie_set_fail' };
  return { success: true, theta: [[resultHash, newRoot]] };
}

/**
 * Functional trie update: returns new trie root with value at index replaced.
 */
function _trieSet(node, index, value) {
  const tag = tnTag();

  if (index === 0n) {
    if (Store.tagId(node) !== tag) return null;
    const left = Store.rawChild(node, 0);
    const right = Store.rawChild(node, 2);
    return Store.put('tn', [left, value, right]);
  }

  if (Store.tagId(node) !== tag) return null;
  const left = Store.rawChild(node, 0);
  const val = Store.rawChild(node, 1);
  const right = Store.rawChild(node, 2);

  const bit = index & 1n;
  const rest = index >> 1n;

  if (bit === 0n) {
    const newLeft = _trieSet(left, rest, value);
    if (newLeft === null) return null;
    return Store.put('tn', [newLeft, val, right]);
  } else {
    const newRight = _trieSet(right, rest, value);
    if (newRight === null) return null;
    return Store.put('tn', [left, val, newRight]);
  }
}

// ── trie_set FFI ────────────────────────────────────────────────────────────

/**
 * FFI for trie_set: trie_set Trie Index Value Result
 * Mode: + + + -
 * O(log N) functional trie update in JS.
 */
function trie_set(args) {
  const [trieHash, idxHash, valHash, resultHash] = args;

  if (!isGround(trieHash) || !isGround(idxHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const idx = binToInt(idxHash);
  if (idx === null) return { success: false, reason: 'index_not_int' };
  const newRoot = _trieSet(trieHash, idx, valHash);
  if (newRoot === null) return { success: false, reason: 'trie_set_fail' };
  return { success: true, theta: [[resultHash, newRoot]] };
}

// ── alen FFI ────────────────────────────────────────────────────────────────

/**
 * FFI for alen: alen Array Length
 * Mode: + -
 * Returns array length as binlit
 */
function alen(args) {
  const [arrHash, lenHash] = args;

  if (!isGround(arrHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const elems = Store.getArrayElements(arrHash);
  if (!elems) return { success: false, reason: 'not_arrlit' };

  return { success: true, theta: [[lenHash, intToBin(BigInt(elems.length))]] };
}

// ── read_bytes FFI ──────────────────────────────────────────────────────────

/**
 * FFI for read_bytes: read_bytes Array Offset NumBytes Value
 * Mode: + + + -
 * Reads N contiguous bytes from array, combines big-endian into single binlit.
 * Supports both arrlit and trie formats.
 */
function read_bytes(args) {
  const [arrHash, offsetHash, numHash, valHash] = args;

  if (!isGround(arrHash) || !isGround(offsetHash) || !isGround(numHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const offset = binToInt(offsetHash);
  const num = binToInt(numHash);
  if (offset === null || num === null) return { success: false, reason: 'not_int' };
  if (offset < 0n || num <= 0n) return { success: false, reason: 'invalid_range' };

  // Try arrlit fast path
  const elems = Store.getArrayElements(arrHash);
  if (elems) {
    if (offset + num > BigInt(elems.length)) return { success: false, reason: 'out_of_bounds' };
    let result = 0n;
    const off = Number(offset);
    const n = Number(num);
    for (let i = 0; i < n; i++) {
      const byteVal = binToInt(elems[off + i]);
      if (byteVal === null) return { success: false, reason: 'non_ground_byte' };
      result = (result << 8n) | (byteVal & 0xFFn);
    }
    return { success: true, theta: [[valHash, intToBin(result)]] };
  }

  // Trie path
  let result = 0n;
  const n = Number(num);
  for (let i = 0; i < n; i++) {
    const byteHash = trieNav(arrHash, offset + BigInt(i));
    if (byteHash === null) return { success: false, reason: 'trie_miss' };
    const byteVal = binToInt(byteHash);
    if (byteVal === null) return { success: false, reason: 'non_ground_byte' };
    result = (result << 8n) | (byteVal & 0xFFn);
  }
  return { success: true, theta: [[valHash, intToBin(result)]] };
}

// ── notMember FFI ──────────────────────────────────────────────────────────

/**
 * FFI for notMember: notMember Key List
 * Mode: + +
 * Returns success if Key is NOT in List (arrlit or acons/ae chain).
 * Key is a binlit, List elements are binlits.
 */
function notMember(args) {
  const [keyHash, listHash] = args;

  if (!isGround(keyHash) || !isGround(listHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const keyVal = binToInt(keyHash);
  if (keyVal === null) return { success: false, reason: 'key_not_int' };

  // Fast path: arrlit
  const elems = Store.getArrayElements(listHash);
  if (elems) {
    for (let i = 0; i < elems.length; i++) {
      const elemVal = binToInt(elems[i]);
      if (elemVal === keyVal) return { success: false, reason: 'member_found' };
    }
    return { success: true, theta: [] };
  }

  // acons/ae chain
  let current = listHash;
  const aconsTag = Store.TAG['acons'];
  while (true) {
    const tag = Store.tag(current);
    if (tag === 'atom') break; // ae = end of list
    if (Store.tagId(current) === aconsTag) {
      const elemVal = binToInt(Store.child(current, 0));
      if (elemVal === keyVal) return { success: false, reason: 'member_found' };
      current = Store.child(current, 1);
    } else {
      break;
    }
  }
  return { success: true, theta: [] };
}

module.exports = { arr_get, arr_set, alen, read_bytes, trie_get, trie_set, arrToTrie, trieNav, notMember };

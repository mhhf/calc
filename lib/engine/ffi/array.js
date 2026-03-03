/**
 * Array FFI — O(1) operations on arrlit-backed arrays
 *
 * All functions follow the standard FFI pattern:
 *   (args: number[]) → { success: boolean, theta?: [var, val][], reason?: string }
 */

const Store = require('../../kernel/store');
const { binToInt, intToBin, isGround } = require('./convert');

/**
 * FFI for arr_get: arr_get Array Index Value
 * Mode: + + -
 * O(1) array element access via ARRAY_TABLE
 */
function arr_get(args) {
  const [arrHash, idxHash, valHash] = args;

  if (!isGround(arrHash) || !isGround(idxHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const elems = Store.getArrayElements(arrHash);
  if (!elems) return { success: false, reason: 'not_arrlit' };

  const idx = binToInt(idxHash);
  if (idx === null) return { success: false, reason: 'index_not_int' };
  if (idx < 0n || idx >= BigInt(elems.length)) return { success: false, reason: 'out_of_bounds' };

  return { success: true, theta: [[valHash, elems[Number(idx)]]] };
}

/**
 * FFI for arr_set: arr_set Array Index Value Result
 * Mode: + + + -
 * Returns new arrlit with element at Index replaced by Value
 */
function arr_set(args) {
  const [arrHash, idxHash, valHash, resultHash] = args;

  if (!isGround(arrHash) || !isGround(idxHash) || !isGround(valHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const elems = Store.getArrayElements(arrHash);
  if (!elems) return { success: false, reason: 'not_arrlit' };

  const idx = binToInt(idxHash);
  if (idx === null) return { success: false, reason: 'index_not_int' };
  if (idx < 0n || idx >= BigInt(elems.length)) return { success: false, reason: 'out_of_bounds' };

  const newData = new Uint32Array(elems.length);
  newData.set(elems);
  newData[Number(idx)] = valHash;
  const newArr = Store.put('arrlit', [newData]);

  return { success: true, theta: [[resultHash, newArr]] };
}

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

/**
 * FFI for read_bytes: read_bytes Array Offset NumBytes Value
 * Mode: + + + -
 * Reads N contiguous bytes from array, combines big-endian into single binlit
 */
function read_bytes(args) {
  const [arrHash, offsetHash, numHash, valHash] = args;

  if (!isGround(arrHash) || !isGround(offsetHash) || !isGround(numHash)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const elems = Store.getArrayElements(arrHash);
  if (!elems) return { success: false, reason: 'not_arrlit' };

  const offset = binToInt(offsetHash);
  const num = binToInt(numHash);
  if (offset === null || num === null) return { success: false, reason: 'not_int' };
  if (offset < 0n || num <= 0n) return { success: false, reason: 'invalid_range' };
  if (offset + num > BigInt(elems.length)) return { success: false, reason: 'out_of_bounds' };

  // Combine bytes big-endian
  let result = 0n;
  const off = Number(offset);
  const n = Number(num);
  for (let i = 0; i < n; i++) {
    const byteHash = elems[off + i];
    const byteVal = binToInt(byteHash);
    if (byteVal === null) return { success: false, reason: 'non_ground_byte' };
    result = (result << 8n) | (byteVal & 0xFFn);
  }

  return { success: true, theta: [[valHash, intToBin(result)]] };
}

module.exports = { arr_get, arr_set, alen, read_bytes };

/**
 * Memory Operations for FFI
 *
 * Write-log memory model: MSTORE wraps a `write` constructor (O(1)),
 * MLOAD traverses via McCarthy's axioms as ILL forward rules.
 * FFIs here accelerate pure-arithmetic helpers.
 */

const { binToInt, intToBin } = require('./convert');
const Store = require('../../../kernel/store');

const EMPTY_THETA = [];

/** Check if a hash is the empty_mem term (handles both tag and atom encoding) */
function isEmptyMem(h) {
  const t = Store.tag(h);
  if (t === 'empty_mem') return true;
  if (t === 'atom' && Store.child(h, 0) === 'empty_mem') return true;
  return false;
}

/**
 * EVM memory cost formula: cost(words) = 3*words + floor(words²/512)
 */
function memCost(sizeBytes) {
  if (sizeBytes === 0n) return 0n;
  const words = sizeBytes / 32n; // sizeBytes is always word-aligned
  return 3n * words + (words * words) / 512n;
}

/**
 * FFI for mem_expand: high-water mark update + gas cost
 * Mode: + + + - -
 * mem_expand(OldSize, Offset, AccessLen, NewSize, GasCost)
 * NewSize = max(OldSize, ceil((Offset + AccessLen) / 32) * 32)
 * GasCost = memCost(NewSize) - memCost(OldSize)
 * Zero-length access does NOT expand (EVM spec).
 */
function mem_expand(args) {
  const [oldSize, offset, accessLen, outSlot, gasCostSlot] = args;
  const s = binToInt(oldSize);
  const o = binToInt(offset);
  const l = binToInt(accessLen);
  if (s === null || o === null || l === null)
    return { success: false, reason: 'mode_mismatch' };
  if (l === 0n)
    return { success: true, theta: [[outSlot, oldSize], [gasCostSlot, intToBin(0n)]] };
  const needed = ((o + l + 31n) / 32n) * 32n;
  const newSize = needed > s ? needed : s;
  const gasCost = memCost(newSize) - memCost(s);
  return { success: true, theta: [[outSlot, intToBin(newSize)], [gasCostSlot, intToBin(gasCost)]] };
}

/**
 * FFI for no_overlap: disjoint range check
 * Mode: + + + +
 * no_overlap(R, Rs, W, Ws)
 * Succeeds iff [R, R+Rs) ∩ [W, W+Ws) = ∅
 * i.e. R+Rs <= W || W+Ws <= R
 */
function no_overlap(args) {
  const [r, rs, w, ws] = args;
  const rInt = binToInt(r);
  const rsInt = binToInt(rs);
  const wInt = binToInt(w);
  const wsInt = binToInt(ws);
  if (rInt === null || rsInt === null || wInt === null || wsInt === null)
    return { success: false, reason: 'mode_mismatch' };
  const disjoint = (rInt + rsInt <= wInt) || (wInt + wsInt <= rInt);
  return { success: disjoint, theta: EMPTY_THETA };
}

/**
 * FFI for mem_read: read a 32-byte word from write-log memory
 * Mode: + + -
 * mem_read(MemHash, Offset, Value)
 * Walks write-log via Store.tag()/Store.child(), traversing the chain
 * for 32-byte aligned reads (the MLOAD case).
 * Returns the assembled 256-bit value or fails for symbolic offsets/values.
 */
function mem_read(args) {
  const [memHash, offsetHash, valueSlot] = args;
  const offset = binToInt(offsetHash);
  if (offset === null)
    return { success: false, reason: 'symbolic_offset' };

  // Track byte-level coverage for overlapping writes
  const result = new Uint8Array(32);   // zero-filled
  const covered = new Uint8Array(32);  // 0 = uncovered
  let coveredCount = 0;

  let current = memHash;
  while (true) {
    if (isEmptyMem(current)) break;
    const tag = Store.tag(current);
    if (tag === 'write') {
      const wOff = binToInt(Store.child(current, 0));
      if (wOff === null)
        return { success: false, reason: 'symbolic_offset' };
      const wVal = Store.child(current, 1);

      // Compute overlap FIRST to skip non-overlapping writes (even with symbolic values)
      const overlapStart = wOff > offset ? wOff : offset;
      const wEnd = wOff + 32n;
      const rEnd = offset + 32n;
      const overlapEnd = wEnd < rEnd ? wEnd : rEnd;

      if (overlapStart < overlapEnd) {
        // Exact hit: write offset equals read offset and no prior coverage.
        // Return value hash directly (works for symbolic values too).
        if (wOff === offset && coveredCount === 0) {
          return { success: true, theta: [[valueSlot, wVal]] };
        }

        // Overlapping write with concrete value — extract bytes
        const wValInt = binToInt(wVal);
        if (wValInt === null)
          return { success: false, reason: 'symbolic_value' };
        for (let i = overlapStart; i < overlapEnd; i++) {
          const ri = Number(i - offset);
          if (!covered[ri]) {
            const byteIdx = Number(i - wOff);
            result[ri] = Number((wValInt >> BigInt(8 * (31 - byteIdx))) & 0xFFn);
            covered[ri] = 1;
            coveredCount++;
          }
        }
        if (coveredCount === 32) break;
      }
      current = Store.child(current, 2);  // rest
    } else {
      return { success: false, reason: 'unknown_node' };
    }
  }

  // Assemble 32 bytes into a BigInt (big-endian)
  let resultInt = 0n;
  for (let i = 0; i < 32; i++)
    resultInt = (resultInt << 8n) | BigInt(result[i]);
  return { success: true, theta: [[valueSlot, intToBin(resultInt)]] };
}

/**
 * Read a single byte from write-log memory at a given byte address.
 * Returns the byte value (0-255), or 0 for uninitialized memory.
 * Returns null if the memory or address is symbolic.
 */
function readByte(memHash, byteAddr) {
  const wordAddr = (byteAddr / 32n) * 32n;
  const byteOffset = Number(byteAddr % 32n);

  let current = memHash;
  while (true) {
    if (isEmptyMem(current)) return 0; // uninitialized = 0
    const tag = Store.tag(current);
    if (tag !== 'write') return null; // symbolic
    const wOff = binToInt(Store.child(current, 0));
    if (wOff === null) return null;
    if (wOff === wordAddr) {
      const wVal = binToInt(Store.child(current, 1));
      if (wVal === null) return null;
      return Number((wVal >> BigInt(8 * (31 - byteOffset))) & 0xFFn);
    }
    current = Store.child(current, 2);
  }
}

/**
 * FFI for sha3_compute: concrete keccak256 over memory range
 * Mode: + + + -
 * sha3_compute(Mem, Offset, End, Hash)
 * Reads bytes from Offset to End, computes keccak256, returns 256-bit hash.
 * Falls through to clause resolution (symbolic sha3 constructor) when
 * memory or addresses are symbolic.
 */
function sha3_compute(args) {
  const [memHash, offsetHash, endHash, resultSlot] = args;
  const offset = binToInt(offsetHash);
  const end = binToInt(endHash);
  if (offset === null || end === null)
    return { success: false, reason: 'symbolic_address' };

  const size = Number(end - offset);
  if (size < 0) return { success: false, reason: 'negative_size' };

  // Read bytes from memory
  const bytes = Buffer.alloc(size);
  for (let i = 0; i < size; i++) {
    const b = readByte(memHash, offset + BigInt(i));
    if (b === null) return { success: false, reason: 'symbolic_memory' };
    bytes[i] = b;
  }

  // Compute keccak256
  const { keccak256 } = require('js-sha3');
  const hashHex = keccak256(bytes);
  const resultHash = intToBin(BigInt('0x' + hashHex));

  return { success: true, theta: [[resultSlot, resultHash]] };
}

module.exports = {
  mem_expand,
  mem_read,
  no_overlap,
  sha3_compute,
};

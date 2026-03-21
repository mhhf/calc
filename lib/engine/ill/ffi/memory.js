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
 * FFI for mem_expand: high-water mark update
 * Mode: + + + -
 * mem_expand(OldSize, Offset, AccessLen, NewSize)
 * NewSize = max(OldSize, ceil((Offset + AccessLen) / 32) * 32)
 * Zero-length access does NOT expand (EVM spec).
 */
function mem_expand(args) {
  const [oldSize, offset, accessLen, outSlot] = args;
  const s = binToInt(oldSize);
  const o = binToInt(offset);
  const l = binToInt(accessLen);
  if (s === null || o === null || l === null)
    return { success: false, reason: 'mode_mismatch' };
  if (l === 0n)
    return { success: true, theta: [[outSlot, oldSize]] };
  const needed = ((o + l + 31n) / 32n) * 32n;
  const newSize = needed > s ? needed : s;
  return { success: true, theta: [[outSlot, intToBin(newSize)]] };
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

  // Track byte-level coverage for overlap/write8 patches
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
    } else if (tag === 'write8') {
      const wAddr = binToInt(Store.child(current, 0));
      if (wAddr === null)
        return { success: false, reason: 'symbolic_offset' };
      // Check overlap before extracting byte value
      if (wAddr >= offset && wAddr < offset + 32n) {
        const ri = Number(wAddr - offset);
        if (!covered[ri]) {
          const wByteInt = binToInt(Store.child(current, 1));
          if (wByteInt === null)
            return { success: false, reason: 'symbolic_value' };
          result[ri] = Number(wByteInt & 0xFFn);
          covered[ri] = 1;
          coveredCount++;
          if (coveredCount === 32) break;
        }
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

module.exports = {
  mem_expand,
  mem_read,
  no_overlap,
};

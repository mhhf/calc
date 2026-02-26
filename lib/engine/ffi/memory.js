/**
 * Memory Operations for FFI
 *
 * Write-log memory model: MSTORE wraps a `write` constructor (O(1)),
 * MLOAD traverses via McCarthy's axioms as ILL forward rules.
 * FFIs here accelerate pure-arithmetic helpers.
 */

const { binToInt, intToBin } = require('./convert');
const Store = require('../../kernel/store');

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
 * FFI for mem_read_range: read byte range from write-log
 * Mode: + + + -
 * mem_read_range(MemHash, Offset, Size, Bytes)
 * Walks write-log via Store.tag()/Store.child() — no state access.
 * Most-recent-write-wins (outermost first).
 */
function mem_read_range(args) {
  const [memHash, offsetHash, sizeHash, bytesSlot] = args;
  const offset = binToInt(offsetHash);
  const size = binToInt(sizeHash);
  if (offset === null || size === null)
    return { success: false, reason: 'mode_mismatch' };
  if (size === 0n)
    return { success: true, theta: [[bytesSlot, intToBin(0n)]] };

  const sizeNum = Number(size);
  const result = new Uint8Array(sizeNum);   // zero-filled
  const covered = new Uint8Array(sizeNum);  // 0 = uncovered

  let current = memHash;
  while (true) {
    if (isEmptyMem(current)) break;
    const tag = Store.tag(current);
    if (tag === 'write') {
      const wOff = binToInt(Store.child(current, 0));
      if (wOff === null)
        return { success: false, reason: 'symbolic_offset' };
      // Compute overlap before extracting value (skip non-overlapping symbolic writes)
      const overlapStart = wOff > offset ? wOff : offset;
      const wEnd = wOff + 32n;
      const rEnd = offset + size;
      const overlapEnd = wEnd < rEnd ? wEnd : rEnd;
      if (overlapStart < overlapEnd) {
        const wValInt = binToInt(Store.child(current, 1));
        if (wValInt === null)
          return { success: false, reason: 'symbolic_value' };
        for (let i = overlapStart; i < overlapEnd; i++) {
          const ri = Number(i - offset);
          if (!covered[ri]) {
            const byteIdx = Number(i - wOff);
            result[ri] = Number((wValInt >> BigInt(8 * (31 - byteIdx))) & 0xFFn);
            covered[ri] = 1;
          }
        }
      }
      current = Store.child(current, 2);  // rest
    } else if (tag === 'write8') {
      const wAddr = binToInt(Store.child(current, 0));
      if (wAddr === null)
        return { success: false, reason: 'symbolic_offset' };
      // Check overlap before extracting byte value
      if (wAddr >= offset && wAddr < offset + size) {
        const ri = Number(wAddr - offset);
        if (!covered[ri]) {
          const wByteInt = binToInt(Store.child(current, 1));
          if (wByteInt === null)
            return { success: false, reason: 'symbolic_value' };
          result[ri] = Number(wByteInt & 0xFFn);
          covered[ri] = 1;
        }
      }
      current = Store.child(current, 2);  // rest
    } else {
      return { success: false, reason: 'unknown_node' };
    }
  }

  // Assemble result bytes into a BigInt (big-endian)
  let resultInt = 0n;
  for (let i = 0; i < result.length; i++)
    resultInt = (resultInt << 8n) | BigInt(result[i]);
  return { success: true, theta: [[bytesSlot, intToBin(resultInt)]] };
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
 * FFI for overlaps: partial overlap check
 * Mode: + + + +
 * overlaps(R, Rs, W, Ws)
 * Succeeds iff [R, R+Rs) ∩ [W, W+Ws) ≠ ∅
 * Negation of no_overlap.
 */
function overlaps(args) {
  const [r, rs, w, ws] = args;
  const rInt = binToInt(r);
  const rsInt = binToInt(rs);
  const wInt = binToInt(w);
  const wsInt = binToInt(ws);
  if (rInt === null || rsInt === null || wInt === null || wsInt === null)
    return { success: false, reason: 'mode_mismatch' };
  const disjoint = (rInt + rsInt <= wInt) || (wInt + wsInt <= rInt);
  return { success: !disjoint, theta: EMPTY_THETA };
}

/**
 * FFI for splice: byte-level overlay of overlapping writes
 * Mode: + + + + -
 * splice(Base, ReadOff, WriteOff, WriteVal, Result)
 * Overlay WriteVal@WriteOff onto Base@ReadOff for the 32-byte read window.
 * Both Base and WriteVal are 256-bit big-endian words.
 */
function splice(args) {
  const [base, readOff, writeOff, writeVal, resultSlot] = args;
  const baseInt = binToInt(base);
  const rOff = binToInt(readOff);
  const wOff = binToInt(writeOff);
  const wValInt = binToInt(writeVal);
  if (baseInt === null || rOff === null || wOff === null || wValInt === null)
    return { success: false, reason: 'mode_mismatch' };

  // Read window: [rOff, rOff+32), Write window: [wOff, wOff+32)
  // Overlap: [max(rOff, wOff), min(rOff+32, wOff+32))
  const overlapStart = rOff > wOff ? rOff : wOff;
  const rEnd = rOff + 32n;
  const wEnd = wOff + 32n;
  const overlapEnd = rEnd < wEnd ? rEnd : wEnd;

  if (overlapStart >= overlapEnd) {
    // No overlap — return base unchanged
    return { success: true, theta: [[resultSlot, intToBin(baseInt)]] };
  }

  // Start with base as 32-byte big-endian
  const bytes = new Uint8Array(32);
  for (let i = 0; i < 32; i++) {
    bytes[i] = Number((baseInt >> BigInt(8 * (31 - i))) & 0xFFn);
  }

  // Overlay write bytes for the overlapping range
  for (let addr = overlapStart; addr < overlapEnd; addr++) {
    const rIdx = Number(addr - rOff);    // index into read window (0..31)
    const wIdx = Number(addr - wOff);    // index into write value (0..31)
    bytes[rIdx] = Number((wValInt >> BigInt(8 * (31 - wIdx))) & 0xFFn);
  }

  // Reassemble
  let resultInt = 0n;
  for (let i = 0; i < 32; i++) {
    resultInt = (resultInt << 8n) | BigInt(bytes[i]);
  }

  return { success: true, theta: [[resultSlot, intToBin(resultInt)]] };
}

/**
 * FFI for splice_byte: set a single byte in a 32-byte word
 * Mode: + + + + -
 * splice_byte(Base, ReadOff, Addr, Byte, Result)
 * Sets byte at position (Addr - ReadOff) within the 32-byte word Base.
 */
function splice_byte(args) {
  const [base, readOff, addr, byte_, resultSlot] = args;
  const baseInt = binToInt(base);
  const rOff = binToInt(readOff);
  const a = binToInt(addr);
  const b = binToInt(byte_);
  if (baseInt === null || rOff === null || a === null || b === null)
    return { success: false, reason: 'mode_mismatch' };

  const idx = Number(a - rOff);  // byte index within 32-byte word (0..31)
  if (idx < 0 || idx >= 32)
    return { success: true, theta: [[resultSlot, intToBin(baseInt)]] };

  // Clear the target byte and set it (use XOR with all-ones to avoid negative BigInt from ~)
  const shift = BigInt(8 * (31 - idx));
  const allOnes = (1n << 256n) - 1n;
  const mask = allOnes ^ (0xFFn << shift);
  const resultInt = (baseInt & mask) | ((b & 0xFFn) << shift);
  return { success: true, theta: [[resultSlot, intToBin(resultInt)]] };
}

/**
 * FFI for mem_read: read a 32-byte word from write-log memory
 * Mode: + + -
 * mem_read(MemHash, Offset, Value)
 * Walks write-log via Store.tag()/Store.child() — same logic as mem_read_range
 * but specialized for 32-byte aligned reads (the MLOAD case).
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
  mem_read_range,
  no_overlap,
  overlaps,
  splice,
  splice_byte
};

/**
 * Calldata FFI — cd_read for ground binlit calldata
 *
 * Handles byte extraction from ground BigInt calldata values.
 * Sconcat traversal is left to backward clause resolution (DRY).
 *
 * LEADING-ZERO LIMITATION: This FFI only handles raw binlit calldata where the
 * BigInt value has no leading-zero bytes. For calldata like 0x00AABB (3 bytes,
 * first byte = 0x00), the BigInt strips the leading zero to 0xAABB (2 bytes),
 * causing byteLen = 2 instead of 3 — wrong byte offsets result.
 *
 * The canonical calldata representation is sconcat(32, chunk, rest), which
 * encode byte positions correctly in 32-byte aligned chunks. translate.js always
 * produces sconcat chains; this FFI is only an optimization for non-leading-zero
 * binlit cases. For any calldata with leading-zero bytes, use sconcat form.
 */

'use strict';

const { binToInt, intToBin } = require('./convert');

/**
 * FFI for cd_read: read 32 bytes from ground binlit calldata at offset.
 * Mode: + + - (multiModal)
 * cd_read(CD, Offset, Value)
 *
 * Only handles ground binlit CD and ground Offset.
 * Returns 32-byte left-aligned value with zero-padding past end.
 *
 * Precondition: cdVal must not have leading-zero bytes (see module doc above).
 * If cdVal might have leading zeros, use sconcat representation instead.
 */
function cd_read(args) {
  const [cdHash, offsetHash, valueSlot] = args;
  const cdVal = binToInt(cdHash);
  if (cdVal === null) return { success: false, reason: 'symbolic_calldata' };
  const offset = binToInt(offsetHash);
  if (offset === null) return { success: false, reason: 'symbolic_offset' };

  const off = Number(offset);

  // Compute byte length of calldata from minimal BigInt representation.
  // NOTE: This drops leading-zero bytes — correct only when cdVal's most-significant
  // byte is non-zero (i.e., no leading zeros in the byte-level representation).
  // For leading-zero calldata, use sconcat form (see module-level comment).
  let byteLen = 0;
  if (cdVal > 0n) {
    let v = cdVal;
    while (v > 0n) { v >>= 8n; byteLen++; }
  }

  if (off >= byteLen) {
    return { success: true, theta: [[valueSlot, intToBin(0n)]] };
  }

  const avail = Math.min(32, byteLen - off);
  const rightShift = BigInt(Math.max(0, byteLen - off - 32) * 8);
  const mask = (1n << BigInt(avail * 8)) - 1n;
  const extracted = (cdVal >> rightShift) & mask;
  const result = (extracted << BigInt((32 - avail) * 8)) & ((1n << 256n) - 1n);

  return { success: true, theta: [[valueSlot, intToBin(result)]] };
}

module.exports = { cd_read };

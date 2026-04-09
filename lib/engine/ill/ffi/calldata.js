/**
 * Calldata FFI — cd_read for ground binlit calldata
 *
 * Handles byte extraction from ground BigInt calldata values.
 * Sconcat traversal is left to backward clause resolution (DRY).
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
 */
function cd_read(args) {
  const [cdHash, offsetHash, valueSlot] = args;
  const cdVal = binToInt(cdHash);
  if (cdVal === null) return { success: false, reason: 'symbolic_calldata' };
  const offset = binToInt(offsetHash);
  if (offset === null) return { success: false, reason: 'symbolic_offset' };

  const off = Number(offset);

  // Compute byte length of calldata (minimal representation — see leading-zero caveat)
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

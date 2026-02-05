/**
 * Hex-to-Binary Conversion Utilities for MDE
 *
 * Converts N_XX hex notation to binary (LSB-first) representation
 * used in MDE files.
 *
 * Examples:
 *   N_00 → e
 *   N_01 → (i e)
 *   N_02 → (o (i e))
 *   N_ff → (i (i (i (i (i (i (i (i e))))))))
 */

/**
 * Convert a hex string like "00", "ff", "0100" to binary MDE notation
 * Returns LSB-first binary: e.g., 5 = "101" → (i (o (i e)))
 */
function hexToBin(hex) {
  const n = parseInt(hex, 16);
  if (n === 0) return 'e';

  let val = n;
  const bits = [];
  while (val > 0) {
    bits.push(val & 1 ? 'i' : 'o');
    val = val >>> 1;
  }

  // Build LSB-first binary notation
  let result = 'e';
  for (let i = bits.length - 1; i >= 0; i--) {
    result = `(${bits[i]} ${result})`;
  }
  return result;
}

/**
 * Convert a decimal number to binary MDE notation
 */
function decToBin(n) {
  if (n === 0) return 'e';

  let val = n;
  const bits = [];
  while (val > 0) {
    bits.push(val & 1 ? 'i' : 'o');
    val = val >>> 1;
  }

  let result = 'e';
  for (let i = bits.length - 1; i >= 0; i--) {
    result = `(${bits[i]} ${result})`;
  }
  return result;
}

/**
 * Expand N_XX notation in MDE source code to explicit binary
 *
 * Replaces:
 *   N_00 → e
 *   N_01 → (i e)
 *   N_xx → corresponding binary
 *   N_0100 → 256 in binary
 *
 * Also handles Member01, Member02, etc. as hex constants (20-byte addresses)
 */
function expandHexNotation(source) {
  // Replace N_XXXX (multi-byte hex) first, then N_XX (single-byte)
  let expanded = source;

  // N_XXXX format (4+ hex digits)
  expanded = expanded.replace(/\bN_([0-9a-fA-F]{4,})\b/g, (match, hex) => {
    return hexToBin(hex);
  });

  // N_XX format (2 hex digits)
  expanded = expanded.replace(/\bN_([0-9a-fA-F]{2})\b/g, (match, hex) => {
    return hexToBin(hex);
  });

  // A_XX format (address bytes - used in some celf files)
  expanded = expanded.replace(/\bA_([0-9a-fA-F]+)\b/g, (match, hex) => {
    return hexToBin(hex);
  });

  return expanded;
}

/**
 * Generate binary representation for common EVM constants
 */
function generateConstants() {
  const constants = {};
  for (let i = 0; i <= 255; i++) {
    const hex = i.toString(16).padStart(2, '0').toUpperCase();
    constants[`N_${hex}`] = hexToBin(hex);
  }
  // Extended constants
  constants['N_0100'] = hexToBin('0100'); // 256
  constants['N_200'] = hexToBin('200');   // 512
  return constants;
}

/**
 * Parse binary MDE notation back to decimal
 */
function binToDec(binStr) {
  binStr = binStr.trim();
  if (binStr === 'e') return 0;

  // Remove outer parens if present
  if (binStr.startsWith('(') && binStr.endsWith(')')) {
    binStr = binStr.slice(1, -1).trim();
  }

  // Parse recursively
  const match = binStr.match(/^([io])\s+(.+)$/);
  if (match) {
    const [, bit, inner] = match;
    const innerVal = binToDec(inner);
    return bit === 'i' ? 2 * innerVal + 1 : 2 * innerVal;
  }

  // Handle "i X" or "o X" without parens
  if (binStr.startsWith('i ')) return 2 * binToDec(binStr.slice(2)) + 1;
  if (binStr.startsWith('o ')) return 2 * binToDec(binStr.slice(2));

  return NaN;
}

module.exports = {
  hexToBin,
  decToBin,
  binToDec,
  expandHexNotation,
  generateConstants,
};

/**
 * Arithmetic Operations for FFI
 *
 * All functions follow the pattern:
 * - Check mode (ground inputs)
 * - Convert to BigInt
 * - Compute result
 * - Return substitution binding output to result
 */

const { binToInt, intToBin, strToHash, hashToStr, isGround } = require('./convert');

/**
 * FFI for plus: A + B = C
 * Mode: + + -
 */
function plus(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt + bInt;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for inc: succ(A) = B
 * Mode: + -
 */
function inc(args) {
  const [a, b] = args;

  if (!isGround(a)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  if (aInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const bInt = aInt + 1n;
  const bHash = intToBin(bInt);

  return {
    success: true,
    theta: [[b, bHash]]
  };
}

/**
 * FFI for mul: A * B = C
 * Mode: + + -
 */
function mul(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt * bInt;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for sub: A - B = C (saturating at 0)
 * Mode: + + -
 */
function sub(args) {
  const [a, b, c] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const cInt = aInt >= bInt ? aInt - bInt : 0n;
  const cHash = intToBin(cInt);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for div: A / B = Q (integer division)
 * Mode: + + -
 */
function div(args) {
  const [a, b, q] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const qInt = aInt / bInt;
  const qHash = intToBin(qInt);

  return {
    success: true,
    theta: [[q, qHash]]
  };
}

/**
 * FFI for mod: A % B = R
 * Mode: + + -
 */
function mod(args) {
  const [a, b, r] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const rInt = aInt % bInt;
  const rHash = intToBin(rInt);

  return {
    success: true,
    theta: [[r, rHash]]
  };
}

/**
 * FFI for lt: A < B
 * Mode: + +
 * Returns success if true, failure if false
 */
function lt(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return {
    success: aInt < bInt,
    theta: []
  };
}

/**
 * FFI for le: A <= B
 * Mode: + +
 */
function le(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return {
    success: aInt <= bInt,
    theta: []
  };
}

/**
 * FFI for eq: A == B
 * Mode: + +
 */
function eq(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return {
    success: aInt === bInt,
    theta: []
  };
}

/**
 * FFI for fixed_mul: Fixed-point multiplication
 * C = (A * B) / 10^D
 * Mode: + + + -
 */
function fixed_mul(args) {
  const [d, a, b, c] = args;

  if (!isGround(d) || !isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const decimals = binToInt(d);
  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (decimals === null || aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  const scale = 10n ** decimals;
  const result = (aInt * bInt) / scale;
  const cHash = intToBin(result);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for fixed_div: Fixed-point division
 * C = (A * 10^D) / B
 * Mode: + + + -
 */
function fixed_div(args) {
  const [d, a, b, c] = args;

  if (!isGround(d) || !isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const decimals = binToInt(d);
  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (decimals === null || aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  if (bInt === 0n) {
    return { success: false, reason: 'division_by_zero' };
  }

  const scale = 10n ** decimals;
  const result = (aInt * scale) / bInt;
  const cHash = intToBin(result);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for string_concat: String concatenation
 * C = A ++ B
 * Mode: + + -
 */
function string_concat(args) {
  const [a, b, c] = args;

  const aStr = hashToStr(a);
  const bStr = hashToStr(b);

  if (aStr === null || bStr === null) {
    return { success: false, reason: 'not_string' };
  }

  const cHash = strToHash(aStr + bStr);

  return {
    success: true,
    theta: [[c, cHash]]
  };
}

/**
 * FFI for string_length: String length
 * Len = length(S)
 * Mode: + -
 */
function string_length(args) {
  const [s, len] = args;

  const str = hashToStr(s);

  if (str === null) {
    return { success: false, reason: 'not_string' };
  }

  const lenHash = intToBin(BigInt(str.length));

  return {
    success: true,
    theta: [[len, lenHash]]
  };
}

/**
 * FFI for neq: A != B
 * Mode: + +
 * Returns success if values are not equal, failure if equal
 */
function neq(args) {
  const [a, b] = args;

  if (!isGround(a) || !isGround(b)) {
    return { success: false, reason: 'mode_mismatch' };
  }

  const aInt = binToInt(a);
  const bInt = binToInt(b);

  if (aInt === null || bInt === null) {
    return { success: false, reason: 'conversion_failed' };
  }

  return {
    success: aInt !== bInt,
    theta: []
  };
}

module.exports = {
  plus, inc, mul, sub, div, mod, lt, le, eq, neq,
  fixed_mul, fixed_div,
  string_concat, string_length
};

/**
 * Arithmetic Operations for FFI
 *
 * All functions follow the pattern:
 * - Check mode (ground inputs)
 * - Convert to BigInt
 * - Compute result
 * - Return substitution binding output to result
 */

const { binToInt, intToBin, isGround } = require('./convert');

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

module.exports = { plus, inc, mul, sub, div, mod, lt, le, eq };

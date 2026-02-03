/**
 * Linear Logic Context (Multiset)
 *
 * Content-addressed multiset for efficient linear resource tracking.
 * Used internally by the focused prover - not part of generic kernel.
 *
 * Format: { [hash]: { formula, count } }
 *
 * Provides O(1) lookup and proper multiset semantics (duplicates with count).
 */

const { hashAST } = require('../../kernel/sequent');

/**
 * Create empty multiset context
 */
const empty = () => ({});

/**
 * Create multiset from array of formulas
 */
const fromArray = (formulas) => {
  const ms = {};
  for (const formula of formulas) {
    const h = String(hashAST(formula));
    if (h in ms) {
      ms[h].count++;
    } else {
      ms[h] = { formula, count: 1, hash: h };
    }
  }
  return ms;
};

/**
 * Convert multiset to array (respecting counts)
 */
const toArray = (ms) => {
  const arr = [];
  for (const entry of Object.values(ms)) {
    for (let i = 0; i < entry.count; i++) {
      arr.push(entry.formula);
    }
  }
  return arr;
};

/**
 * Get total count of formulas
 */
const size = (ms) => {
  let n = 0;
  for (const entry of Object.values(ms)) n += entry.count;
  return n;
};

/**
 * Check if empty
 */
const isEmpty = (ms) => Object.keys(ms).length === 0;

/**
 * Add formula to multiset (returns new multiset)
 */
const add = (ms, formula, count = 1) => {
  const h = String(hashAST(formula));
  const newMs = { ...ms };

  if (h in newMs) {
    newMs[h] = { ...newMs[h], count: newMs[h].count + count };
  } else {
    newMs[h] = { formula, count, hash: h };
  }

  return newMs;
};

/**
 * Remove formula from multiset by hash (returns new multiset or null if not enough)
 */
const remove = (ms, hash, count = 1) => {
  const h = String(hash);
  if (!(h in ms)) return null;

  const entry = ms[h];
  if (entry.count < count) return null;

  const newMs = { ...ms };
  if (entry.count === count) {
    delete newMs[h];
  } else {
    newMs[h] = { ...entry, count: entry.count - count };
  }

  return newMs;
};

/**
 * Remove formula (auto-compute hash)
 */
const removeFormula = (ms, formula, count = 1) => {
  return remove(ms, hashAST(formula), count);
};

/**
 * Check if formula exists in multiset
 */
const has = (ms, formula) => {
  const h = String(hashAST(formula));
  return h in ms;
};

/**
 * Get entry by hash
 */
const get = (ms, hash) => ms[String(hash)] || null;

/**
 * Get all entries as array of { formula, count, hash }
 */
const entries = (ms) => Object.values(ms);

/**
 * Copy multiset (shallow - formulas are immutable)
 */
const copy = (ms) => {
  const newMs = {};
  for (const [h, entry] of Object.entries(ms)) {
    newMs[h] = { ...entry };
  }
  return newMs;
};

/**
 * Merge two multisets (add counts)
 */
const merge = (ms1, ms2) => {
  const result = copy(ms1);
  for (const [h, entry] of Object.entries(ms2)) {
    if (h in result) {
      result[h] = { ...result[h], count: result[h].count + entry.count };
    } else {
      result[h] = { ...entry };
    }
  }
  return result;
};

/**
 * Subtract ms2 from ms1 (returns null if ms2 has more of any formula)
 */
const subtract = (ms1, ms2) => {
  let result = copy(ms1);
  for (const [h, entry] of Object.entries(ms2)) {
    result = remove(result, h, entry.count);
    if (result === null) return null;
  }
  return result;
};

/**
 * Check if ms1 contains all of ms2 (ms2 ⊆ ms1)
 */
const contains = (ms1, ms2) => {
  for (const [h, entry] of Object.entries(ms2)) {
    const e1 = ms1[h];
    if (!e1 || e1.count < entry.count) return false;
  }
  return true;
};

/**
 * Check equality (same formulas with same counts)
 */
const eq = (ms1, ms2) => {
  const keys1 = Object.keys(ms1);
  const keys2 = Object.keys(ms2);
  if (keys1.length !== keys2.length) return false;

  for (const h of keys1) {
    if (!(h in ms2) || ms1[h].count !== ms2[h].count) return false;
  }
  return true;
};

/**
 * Apply substitution to all formulas in multiset
 */
const substitute = (ms, theta) => {
  const { apply } = require('../../kernel/substitute');
  const result = {};

  for (const entry of Object.values(ms)) {
    const newFormula = apply(entry.formula, theta);
    const newHash = String(hashAST(newFormula));

    if (newHash in result) {
      result[newHash].count += entry.count;
    } else {
      result[newHash] = { formula: newFormula, count: entry.count, hash: newHash };
    }
  }

  return result;
};

/**
 * Find formula matching predicate (returns { formula, count, hash } or null)
 */
const find = (ms, predicate) => {
  for (const entry of Object.values(ms)) {
    if (predicate(entry.formula)) return entry;
  }
  return null;
};

/**
 * Filter formulas matching predicate (returns new multiset)
 */
const filter = (ms, predicate) => {
  const result = {};
  for (const [h, entry] of Object.entries(ms)) {
    if (predicate(entry.formula)) {
      result[h] = { ...entry };
    }
  }
  return result;
};

module.exports = {
  empty,
  fromArray,
  toArray,
  size,
  isEmpty,
  add,
  remove,
  removeFormula,
  has,
  get,
  entries,
  copy,
  merge,
  subtract,
  contains,
  eq,
  substitute,
  find,
  filter
};

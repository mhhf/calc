/**
 * Linear Logic Context (Multiset) for content-addressed terms
 *
 * With content-addressed architecture, formulas ARE their hashes.
 * Context is simply: { [hash]: count }
 *
 * This is O(1) for all operations:
 * - add: increment count
 * - remove: decrement count
 * - lookup: check if hash exists
 * - equality: compare hash (already O(1))
 */

const Store = require('../../kernel/store');
const { apply: subApply } = require('../../kernel/substitute');

/**
 * Create empty multiset context
 * @returns {{ [hash: number]: number }}
 */
const empty = () => ({});

/**
 * Create multiset from array of formula hashes
 * @param {number[]} formulas - Array of formula hashes
 * @returns {{ [hash: number]: number }}
 */
const fromArray = (formulas) => {
  const ms = {};
  for (const h of formulas) {
    ms[h] = (ms[h] || 0) + 1;
  }
  return ms;
};

/**
 * Convert multiset to array (respecting counts)
 * @param {{ [hash: number]: number }} ms
 * @returns {number[]} Array of formula hashes
 */
const toArray = (ms) => {
  const arr = [];
  for (const [h, count] of Object.entries(ms)) {
    const hash = Number(h);
    for (let i = 0; i < count; i++) {
      arr.push(hash);
    }
  }
  return arr;
};

/**
 * Get total count of formulas
 */
const size = (ms) => {
  let n = 0;
  for (const count of Object.values(ms)) n += count;
  return n;
};

/**
 * Check if empty
 */
const isEmpty = (ms) => Object.keys(ms).length === 0;

/**
 * Add formula hash to multiset (returns new multiset)
 * @param {{ [hash: number]: number }} ms
 * @param {number} h - Formula hash
 * @param {number} count - How many to add (default 1)
 */
const add = (ms, h, count = 1) => {
  const newMs = { ...ms };
  newMs[h] = (newMs[h] || 0) + count;
  return newMs;
};

/**
 * Remove formula by hash (returns new multiset or null if not enough)
 * @param {{ [hash: number]: number }} ms
 * @param {number} h - Formula hash
 * @param {number} count - How many to remove (default 1)
 */
const remove = (ms, h, count = 1) => {
  const current = ms[h] || 0;
  if (current < count) return null;

  const newMs = { ...ms };
  if (current === count) {
    delete newMs[h];
  } else {
    newMs[h] = current - count;
  }
  return newMs;
};

/**
 * Check if formula exists in multiset
 * @param {number} h - Formula hash
 */
const has = (ms, h) => (ms[h] || 0) > 0;

/**
 * Get count of formula
 * @param {number} h - Formula hash
 */
const getCount = (ms, h) => ms[h] || 0;

/**
 * Copy multiset (shallow - just counts)
 */
const copy = (ms) => ({ ...ms });

/**
 * Merge two multisets (add counts)
 */
const merge = (ms1, ms2) => {
  const result = { ...ms1 };
  for (const [h, count] of Object.entries(ms2)) {
    result[h] = (result[h] || 0) + count;
  }
  return result;
};

/**
 * Subtract ms2 from ms1 (returns null if ms2 has more of any formula)
 */
const subtract = (ms1, ms2) => {
  let result = { ...ms1 };
  for (const [h, count] of Object.entries(ms2)) {
    const hash = Number(h);
    result = remove(result, hash, count);
    if (result === null) return null;
  }
  return result;
};

/**
 * Check if ms1 contains all of ms2 (ms2 ⊆ ms1)
 */
const contains = (ms1, ms2) => {
  for (const [h, count] of Object.entries(ms2)) {
    if ((ms1[h] || 0) < count) return false;
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
    if (ms1[h] !== ms2[h]) return false;
  }
  return true;
};

/**
 * Apply substitution to all formulas in multiset
 * @param {{ [hash: number]: number }} ms
 * @param {Array<[number, number]>} theta - Substitution
 */
const substitute = (ms, theta) => {
  const result = {};
  for (const [h, count] of Object.entries(ms)) {
    const hash = Number(h);
    const newHash = subApply(hash, theta);
    result[newHash] = (result[newHash] || 0) + count;
  }
  return result;
};

/**
 * Find formula matching predicate
 * @param {Function} predicate - (hash) => boolean
 * @returns {number|null} Formula hash or null
 */
const find = (ms, predicate) => {
  for (const h of Object.keys(ms)) {
    const hash = Number(h);
    if (predicate(hash)) return hash;
  }
  return null;
};

/**
 * Filter formulas matching predicate
 * @param {Function} predicate - (hash) => boolean
 */
const filter = (ms, predicate) => {
  const result = {};
  for (const [h, count] of Object.entries(ms)) {
    const hash = Number(h);
    if (predicate(hash)) {
      result[hash] = count;
    }
  }
  return result;
};

/**
 * Get all hashes as array (each hash once, ignoring counts)
 */
const keys = (ms) => Object.keys(ms).map(Number);

/**
 * Iterate over [hash, count] pairs
 */
const entries = (ms) => Object.entries(ms).map(([h, c]) => [Number(h), c]);

module.exports = {
  empty,
  fromArray,
  toArray,
  size,
  isEmpty,
  add,
  remove,
  has,
  getCount,
  copy,
  merge,
  subtract,
  contains,
  eq,
  substitute,
  find,
  filter,
  keys,
  entries
};

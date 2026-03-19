/**
 * Linear Logic Context (Multiset) for content-addressed terms
 *
 * With content-addressed architecture, formulas ARE their hashes (u32).
 * Representation: sorted Uint32Array with duplicates for counts > 1.
 *
 *   { 5: 2, 12: 1, 42: 3 }  →  Uint32Array [5, 5, 12, 42, 42, 42]
 *
 * Production code uses: empty, fromArray, toArray, isEmpty, remove.
 * Remaining functions form the complete multiset API, tested in sequent-ext.test.js.
 */

const { apply: subApply } = require('../kernel/substitute');

const _EMPTY = new Uint32Array(0);

// Binary search: returns any index of h, or -1
function _bsearch(ms, h) {
  let lo = 0, hi = ms.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >>> 1;
    const v = ms[mid];
    if (v === h) return mid;
    if (v < h) lo = mid + 1;
    else hi = mid - 1;
  }
  return -1;
}

// Returns leftmost insertion point for h (bisect_left)
function _bisectLeft(ms, h) {
  let lo = 0, hi = ms.length;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (ms[mid] < h) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

// Count occurrences of h starting from a known index
function _countAt(ms, h, knownIdx) {
  let lo = knownIdx, hi = knownIdx;
  while (lo > 0 && ms[lo - 1] === h) lo--;
  while (hi < ms.length - 1 && ms[hi + 1] === h) hi++;
  return { lo, count: hi - lo + 1 };
}

/**
 * Create empty multiset context
 * @returns {Uint32Array}
 */
const empty = () => _EMPTY;

/**
 * Create multiset from array of formula hashes
 * @param {number[]} formulas
 * @returns {Uint32Array}
 */
const fromArray = (formulas) => {
  if (formulas.length === 0) return _EMPTY;
  const a = new Uint32Array(formulas);
  a.sort();
  return a;
};

/**
 * Convert multiset to array (respecting counts)
 * @param {Uint32Array} ms
 * @returns {number[]}
 */
const toArray = (ms) => Array.from(ms);

/**
 * Get total count of formulas
 */
const size = (ms) => ms.length;

/**
 * Check if empty
 */
const isEmpty = (ms) => ms.length === 0;

/**
 * Add formula hash to multiset (returns new multiset)
 * @param {Uint32Array} ms
 * @param {number} h - Formula hash
 * @param {number} count - How many to add (default 1)
 */
const add = (ms, h, count = 1) => {
  const pos = _bisectLeft(ms, h);
  const out = new Uint32Array(ms.length + count);
  out.set(ms.subarray(0, pos));
  out.fill(h, pos, pos + count);
  out.set(ms.subarray(pos), pos + count);
  return out;
};

/**
 * Remove formula by hash (returns new multiset or null if not enough)
 * @param {Uint32Array} ms
 * @param {number} h - Formula hash
 * @param {number} count - How many to remove (default 1)
 */
const remove = (ms, h, count = 1) => {
  const idx = _bsearch(ms, h);
  if (idx < 0) return null;
  const { lo, count: have } = _countAt(ms, h, idx);
  if (have < count) return null;
  if (ms.length === count) return _EMPTY;
  const out = new Uint32Array(ms.length - count);
  out.set(ms.subarray(0, lo));
  out.set(ms.subarray(lo + count), lo);
  return out;
};

/**
 * Check if formula exists in multiset
 * @param {number} h - Formula hash
 */
const has = (ms, h) => _bsearch(ms, h) >= 0;

/**
 * Merge two multisets (sorted merge, O(n+m))
 */
const merge = (ms1, ms2) => {
  if (ms1.length === 0) return ms2;
  if (ms2.length === 0) return ms1;
  const out = new Uint32Array(ms1.length + ms2.length);
  let i = 0, j = 0, k = 0;
  while (i < ms1.length && j < ms2.length) {
    if (ms1[i] <= ms2[j]) out[k++] = ms1[i++];
    else out[k++] = ms2[j++];
  }
  while (i < ms1.length) out[k++] = ms1[i++];
  while (j < ms2.length) out[k++] = ms2[j++];
  return out;
};

/**
 * Subtract ms2 from ms1 (returns null if ms2 has more of any formula)
 */
const subtract = (ms1, ms2) => {
  let result = ms1;
  let i = 0;
  while (i < ms2.length) {
    const h = ms2[i];
    let cnt = 1;
    while (i + cnt < ms2.length && ms2[i + cnt] === h) cnt++;
    result = remove(result, h, cnt);
    if (result === null) return null;
    i += cnt;
  }
  return result;
};

/**
 * Check if ms1 contains all of ms2 (ms2 ⊆ ms1)
 */
const contains = (ms1, ms2) => {
  let i = 0;
  while (i < ms2.length) {
    const h = ms2[i];
    let cnt2 = 1;
    while (i + cnt2 < ms2.length && ms2[i + cnt2] === h) cnt2++;
    const idx = _bsearch(ms1, h);
    if (idx < 0) return false;
    if (_countAt(ms1, h, idx).count < cnt2) return false;
    i += cnt2;
  }
  return true;
};

/**
 * Check equality (same formulas with same counts)
 */
const eq = (ms1, ms2) => {
  if (ms1.length !== ms2.length) return false;
  for (let i = 0; i < ms1.length; i++) {
    if (ms1[i] !== ms2[i]) return false;
  }
  return true;
};

/**
 * Apply substitution to all formulas in multiset
 * @param {Uint32Array} ms
 * @param {Array<[number, number]>} theta - Substitution
 */
const substitute = (ms, theta) => {
  if (ms.length === 0) return _EMPTY;
  const out = new Uint32Array(ms.length);
  for (let i = 0; i < ms.length; i++) {
    out[i] = subApply(ms[i], theta);
  }
  out.sort();
  return out;
};

/**
 * Find formula matching predicate
 * @param {Function} predicate - (hash) => boolean
 * @returns {number|null} Formula hash or null
 */
const find = (ms, predicate) => {
  for (let i = 0; i < ms.length; i++) {
    if (predicate(ms[i])) return ms[i];
  }
  return null;
};

/**
 * Filter formulas matching predicate
 * @param {Function} predicate - (hash) => boolean
 */
const filter = (ms, predicate) => {
  let count = 0;
  for (let i = 0; i < ms.length; i++) {
    if (predicate(ms[i])) count++;
  }
  if (count === 0) return _EMPTY;
  if (count === ms.length) return ms;
  const out = new Uint32Array(count);
  let k = 0;
  for (let i = 0; i < ms.length; i++) {
    if (predicate(ms[i])) out[k++] = ms[i];
  }
  return out;
};

/**
 * Iterate over [hash, count] pairs
 */
const entries = (ms) => {
  const result = [];
  let i = 0;
  while (i < ms.length) {
    const h = ms[i];
    let cnt = 1;
    while (i + cnt < ms.length && ms[i + cnt] === h) cnt++;
    result.push([h, cnt]);
    i += cnt;
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
  has,
  merge,
  subtract,
  contains,
  eq,
  substitute,
  find,
  filter,
  entries
};

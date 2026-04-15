/**
 * FFI Registry and Dispatch
 *
 * Central registry for all FFI functions.
 * Functions are registered by path (e.g., "arithmetic.plus")
 */

const arithmetic = require('./arithmetic');
const memory = require('./memory');
const calldata = require('./calldata');
const array = require('./array');
const mode = require('./mode');
const convert = require('./convert');

// ============================================================================
// REGISTRY
// ============================================================================

const registry = new Map();

/**
 * Register an FFI function
 * @param {string} path - Function path (e.g., "arithmetic.plus")
 * @param {Function} fn - Implementation
 */
function register(path, fn) {
  registry.set(path, fn);
}

/**
 * Get an FFI function
 * @param {string} path
 * @returns {Function|undefined}
 */
function get(path) {
  return registry.get(path);
}

/**
 * Check if FFI is available for a path
 * @param {string} path
 * @returns {boolean}
 */
function has(path) {
  return registry.has(path);
}

// ============================================================================
// BUILT-IN REGISTRATIONS
// ============================================================================

// Register all arithmetic functions
register('arithmetic.plus', arithmetic.plus);
register('arithmetic.inc', arithmetic.inc);
register('arithmetic.mul', arithmetic.mul);
register('arithmetic.sub', arithmetic.sub);
register('arithmetic.div', arithmetic.div);
register('arithmetic.mod', arithmetic.mod);
register('arithmetic.lt', arithmetic.lt);
register('arithmetic.le', arithmetic.le);
register('arithmetic.eq', arithmetic.eq);
register('arithmetic.eq_bool', arithmetic.eq_bool);
register('arithmetic.neq', arithmetic.neq);
register('arithmetic.gt', arithmetic.gt);
register('arithmetic.bitwiseAnd', arithmetic.bitwiseAnd);
register('arithmetic.bitwiseOr', arithmetic.bitwiseOr);
register('arithmetic.bitwiseNot', arithmetic.bitwiseNot);
register('arithmetic.bitwiseXor', arithmetic.bitwiseXor);
register('arithmetic.to256', arithmetic.to256);
register('arithmetic.shr', arithmetic.shr);
register('arithmetic.shl', arithmetic.shl);
register('arithmetic.slt', arithmetic.slt);
register('arithmetic.sub256', arithmetic.sub256);
register('arithmetic.div256', arithmetic.div256);
register('arithmetic.mod256', arithmetic.mod256);
register('arithmetic.exp256', arithmetic.exp256);
register('arithmetic.trim', arithmetic.trim);
register('arithmetic.sdiv256', arithmetic.sdiv256);
register('arithmetic.smod256', arithmetic.smod256);
register('arithmetic.addmod256', arithmetic.addmod256);
register('arithmetic.mulmod256', arithmetic.mulmod256);
register('arithmetic.signextend256', arithmetic.signextend256);
register('arithmetic.byte256', arithmetic.byte256);
register('arithmetic.sar256', arithmetic.sar256);
register('arithmetic.checked_sub', arithmetic.checked_sub);
register('arithmetic.byte_size256', arithmetic.byte_size256);
register('arithmetic.sstore_gas', arithmetic.sstore_gas);
register('arithmetic.fixed_mul', arithmetic.fixed_mul);
register('arithmetic.fixed_div', arithmetic.fixed_div);
register('arithmetic.string_concat', arithmetic.string_concat);
register('arithmetic.string_length', arithmetic.string_length);
register('arithmetic.is_push', arithmetic.is_push);
register('arithmetic.is_dup', arithmetic.is_dup);
register('arithmetic.is_swap', arithmetic.is_swap);
register('arithmetic.byte_replace', arithmetic.byte_replace);

// Register all memory functions
register('memory.mem_expand', memory.mem_expand);
register('memory.mem_read', memory.mem_read);
register('memory.no_overlap', memory.no_overlap);
register('memory.sha3_compute', memory.sha3_compute);

// Register calldata functions
register('calldata.cd_read', calldata.cd_read);

// Register all array functions
register('array.arr_get', array.arr_get);
register('array.arr_set', array.arr_set);
register('array.alen', array.alen);
register('array.read_bytes', array.read_bytes);
register('array.notMember', array.notMember);

// ============================================================================
// DEFAULT FFI METADATA
// ============================================================================

/**
 * Default FFI metadata for known predicates
 * This is used when @ffi annotations are not present in source files
 */
const defaultMeta = {
  plus: { ffi: 'arithmetic.plus', mode: '+ + +', multiModal: true },
  inc: { ffi: 'arithmetic.inc', mode: '+ -' },
  mul: { ffi: 'arithmetic.mul', mode: '+ + -' },
  sub: { ffi: 'arithmetic.sub', mode: '+ + -' },
  div: { ffi: 'arithmetic.div', mode: '+ + -' },
  mod: { ffi: 'arithmetic.mod', mode: '+ + -' },
  lt: { ffi: 'arithmetic.lt', mode: '+ +' },
  le: { ffi: 'arithmetic.le', mode: '+ +' },
  eq: { ffi: 'arithmetic.eq', mode: '+ +' },
  eq_bool: { ffi: 'arithmetic.eq_bool', mode: '+ + -' },
  neq: { ffi: 'arithmetic.neq', mode: '+ +' },
  gt: { ffi: 'arithmetic.gt', mode: '+ + + -' },
  and: { ffi: 'arithmetic.bitwiseAnd', mode: '+ + -' },
  or: { ffi: 'arithmetic.bitwiseOr', mode: '+ + -' },
  not: { ffi: 'arithmetic.bitwiseNot', mode: '+ -' },
  xor: { ffi: 'arithmetic.bitwiseXor', mode: '+ + -' },
  not256: { ffi: 'arithmetic.bitwiseNot', mode: '+ -' },
  to256: { ffi: 'arithmetic.to256', mode: '+ -' },
  shr: { ffi: 'arithmetic.shr', mode: '+ + -' },
  shl: { ffi: 'arithmetic.shl', mode: '+ + -' },
  slt: { ffi: 'arithmetic.slt', mode: '+ + -' },
  sub256: { ffi: 'arithmetic.sub256', mode: '+ + -' },
  div256: { ffi: 'arithmetic.div256', mode: '+ + -' },
  mod256: { ffi: 'arithmetic.mod256', mode: '+ + -' },
  exp256: { ffi: 'arithmetic.exp256', mode: '+ + -' },
  trim: { ffi: 'arithmetic.trim', mode: '+ -' },
  sdiv256: { ffi: 'arithmetic.sdiv256', mode: '+ + -' },
  smod256: { ffi: 'arithmetic.smod256', mode: '+ + -' },
  addmod256: { ffi: 'arithmetic.addmod256', mode: '+ + + -' },
  mulmod256: { ffi: 'arithmetic.mulmod256', mode: '+ + + -' },
  signextend256: { ffi: 'arithmetic.signextend256', mode: '+ + -' },
  byte256: { ffi: 'arithmetic.byte256', mode: '+ + -' },
  sar256: { ffi: 'arithmetic.sar256', mode: '+ + -' },
  checked_sub: { ffi: 'arithmetic.checked_sub', mode: '+ + -' },
  byte_size256: { ffi: 'arithmetic.byte_size256', mode: '+ -' },
  sstore_gas: { ffi: 'arithmetic.sstore_gas', mode: '+ + -', multiModal: true },
  mem_expand: { ffi: 'memory.mem_expand', mode: '+ + + - -' },
  mem_read: { ffi: 'memory.mem_read', mode: '+ + -', multiModal: true },
  no_overlap: { ffi: 'memory.no_overlap', mode: '+ + + +' },
  sha3_compute: { ffi: 'memory.sha3_compute', mode: '+ + + -' },
  arr_get: { ffi: 'array.arr_get', mode: '+ + -' },
  arr_set: { ffi: 'array.arr_set', mode: '+ + + -', multiModal: true },
  alen: { ffi: 'array.alen', mode: '+ -' },
  read_bytes: { ffi: 'array.read_bytes', mode: '+ + + -' },
  trie_get: { mode: '+ + -' },   // compiled clause dispatch (Tier 2) — FFI removed
  trie_set: { mode: '+ + + -' }, // compiled clause dispatch (Tier 2) — FFI removed
  notMember: { ffi: 'array.notMember', mode: '+ +' },
  cd_read: { ffi: 'calldata.cd_read', mode: '+ + -', multiModal: true },
  fixed_mul: { ffi: 'arithmetic.fixed_mul', mode: '+ + + -' },
  fixed_div: { ffi: 'arithmetic.fixed_div', mode: '+ + + -' },
  string_concat: { ffi: 'arithmetic.string_concat', mode: '+ + -' },
  string_length: { ffi: 'arithmetic.string_length', mode: '+ -' },
  is_push: { ffi: 'arithmetic.is_push', mode: '+ -' },
  is_dup: { ffi: 'arithmetic.is_dup', mode: '+ -' },
  is_swap: { ffi: 'arithmetic.is_swap', mode: '+ -' },
  byte_replace: { ffi: 'arithmetic.byte_replace', mode: '+ + + -' },
};

// Pre-parsed mode strings (computed once, shared by match.js and compile.js)
const parsedModes = {};
for (const key in defaultMeta) {
  parsedModes[key] = mode.parseMode(defaultMeta[key].mode);
}

/**
 * Get parsed modes for a predicate.
 * @param {string} pred - predicate name
 * @returns {string[]|null}
 */
function getModes(pred) {
  return parsedModes[pred] || null;
}

/**
 * Get mode metadata for a predicate (modes + multiModal flag).
 * Used by compose.js for topological sorting of persistent goals.
 * @param {string} pred - predicate name
 * @returns {{ modes: string[], multiModal: boolean }|null}
 */
function getModeMeta(pred) {
  const meta = defaultMeta[pred];
  if (!meta) return null;
  return { modes: parsedModes[pred], multiModal: !!meta.multiModal };
}

module.exports = {
  register,
  get,
  has,
  registry,
  mode,
  arithmetic,
  memory,
  calldata,
  array,
  convert,
  defaultMeta,
  parsedModes,
  getModes,
  getModeMeta,
};

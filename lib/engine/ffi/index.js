/**
 * FFI Registry and Dispatch
 *
 * Central registry for all FFI functions.
 * Functions are registered by path (e.g., "arithmetic.plus")
 */

const arithmetic = require('./arithmetic');
const memory = require('./memory');
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
register('arithmetic.neq', arithmetic.neq);
register('arithmetic.gt', arithmetic.gt);
register('arithmetic.bitwiseAnd', arithmetic.bitwiseAnd);
register('arithmetic.to256', arithmetic.to256);
register('arithmetic.shr', arithmetic.shr);
register('arithmetic.shl', arithmetic.shl);

// Register all memory functions
register('memory.mem_expand', memory.mem_expand);
register('memory.mem_read', memory.mem_read);
register('memory.no_overlap', memory.no_overlap);

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
  neq: { ffi: 'arithmetic.neq', mode: '+ +' },
  gt: { ffi: 'arithmetic.gt', mode: '+ + + -' },
  and: { ffi: 'arithmetic.bitwiseAnd', mode: '+ + -' },
  to256: { ffi: 'arithmetic.to256', mode: '+ -' },
  shr: { ffi: 'arithmetic.shr', mode: '+ + -' },
  shl: { ffi: 'arithmetic.shl', mode: '+ + -' },
  mem_expand: { ffi: 'memory.mem_expand', mode: '+ + + -' },
  mem_read: { ffi: 'memory.mem_read', mode: '+ + -', multiModal: true },
  no_overlap: { ffi: 'memory.no_overlap', mode: '+ + + +' },
};

module.exports = {
  register,
  get,
  has,
  registry,
  mode,
  arithmetic,
  memory,
  convert,
  defaultMeta
};

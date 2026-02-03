/**
 * Hash Algorithm Alternatives for Benchmarking
 *
 * Provides unified API for comparing different hashing approaches:
 * 1. BigInt FNV-1a (current) - 64-bit, collision-safe, SLOW
 * 2. Number FNV-1a - 32-bit, fast, collision risk at 77k items
 * 3. xxHash128 - 128-bit, very fast via WASM, collision-proof
 *
 * Each implementation provides:
 * - hashString(str) -> hash
 * - hashCombine(...hashes) -> hash
 * - hashAST(ast) -> hash
 * - hashEquals(h1, h2) -> boolean
 * - hashToString(hash) -> string (for use as Map key)
 */

// ============================================================
// OPTION 1: BigInt FNV-1a (Current Implementation)
// ============================================================

const bigint = (() => {
  const FNV_PRIME = 0x100000001b3n;
  const FNV_OFFSET = 0xcbf29ce484222325n;
  const MASK_64 = (1n << 64n) - 1n;

  function hashString(str) {
    let hash = FNV_OFFSET;
    for (let i = 0; i < str.length; i++) {
      hash ^= BigInt(str.charCodeAt(i));
      hash = (hash * FNV_PRIME) & MASK_64;
    }
    return hash;
  }

  function hashCombine(...hashes) {
    let hash = FNV_OFFSET;
    for (const h of hashes) {
      hash ^= h;
      hash = (hash * FNV_PRIME) & MASK_64;
    }
    return hash;
  }

  function hashAST(ast) {
    if (!ast?.tag) return hashString(String(ast ?? ''));
    let h = hashString(ast.tag);
    for (const c of ast.children) h = hashCombine(h, hashAST(c));
    return h;
  }

  function hashEquals(h1, h2) {
    return h1 === h2;
  }

  function hashToString(hash) {
    return hash.toString(16);
  }

  return {
    name: 'BigInt FNV-1a (64-bit)',
    hashString,
    hashCombine,
    hashAST,
    hashEquals,
    hashToString,
    isAsync: false
  };
})();


// ============================================================
// OPTION 2: Number FNV-1a (32-bit, fast but collision risk)
// ============================================================

const number32 = (() => {
  const FNV_PRIME = 0x01000193;
  const FNV_OFFSET = 0x811c9dc5;

  function hashString(str) {
    let hash = FNV_OFFSET;
    for (let i = 0; i < str.length; i++) {
      hash ^= str.charCodeAt(i);
      hash = Math.imul(hash, FNV_PRIME) >>> 0;
    }
    return hash;
  }

  function hashCombine(...hashes) {
    let hash = FNV_OFFSET;
    for (const h of hashes) {
      hash ^= h;
      hash = Math.imul(hash, FNV_PRIME) >>> 0;
    }
    return hash;
  }

  function hashAST(ast) {
    if (!ast?.tag) return hashString(String(ast ?? ''));
    let h = hashString(ast.tag);
    for (const c of ast.children) h = hashCombine(h, hashAST(c));
    return h;
  }

  function hashEquals(h1, h2) {
    return h1 === h2;
  }

  function hashToString(hash) {
    return hash.toString(16).padStart(8, '0');
  }

  return {
    name: 'Number FNV-1a (32-bit)',
    hashString,
    hashCombine,
    hashAST,
    hashEquals,
    hashToString,
    isAsync: false
  };
})();


// ============================================================
// OPTION 3: xxHash128 via hash-wasm (128-bit, fast, collision-proof)
// ============================================================

const xxhash128 = (() => {
  let xxhash128Fn = null;
  let createXXHash128 = null;
  let initialized = false;

  // Lazy init to avoid blocking require
  async function init() {
    if (initialized) return;
    try {
      const hashWasm = require('hash-wasm');
      xxhash128Fn = hashWasm.xxhash128;
      createXXHash128 = hashWasm.createXXHash128;
      initialized = true;
    } catch (e) {
      console.error('hash-wasm not available:', e.message);
      throw e;
    }
  }

  // Synchronous hash using pre-created hasher (for hot path)
  let hasherPool = [];

  async function getHasher() {
    if (hasherPool.length > 0) return hasherPool.pop();
    await init();
    return createXXHash128();
  }

  function returnHasher(h) {
    h.init();
    hasherPool.push(h);
  }

  // For string hashing - returns hex string (128-bit)
  async function hashString(str) {
    await init();
    return xxhash128Fn(str);
  }

  // Combine hashes by concatenating and re-hashing
  async function hashCombine(...hashes) {
    await init();
    const combined = hashes.join(':');
    return xxhash128Fn(combined);
  }

  // Hash AST recursively
  async function hashAST(ast) {
    if (!ast?.tag) {
      return hashString(String(ast ?? ''));
    }

    const childHashes = [];
    for (const c of ast.children) {
      childHashes.push(await hashAST(c));
    }

    // Combine tag with child hashes
    const input = ast.tag + '\0' + childHashes.join('\0');
    return xxhash128Fn(input);
  }

  // Sync version using memoization (for benchmarking hot path)
  function hashASTSync(ast, cache = new Map()) {
    if (!ast?.tag) {
      const key = String(ast ?? '');
      if (cache.has(key)) return cache.get(key);
      // For sync, we need pre-computed hashes
      throw new Error('hashASTSync requires pre-initialized cache');
    }

    // Check cache
    if (ast._xxh128) return ast._xxh128;

    const childHashes = ast.children.map(c =>
      typeof c === 'string' ? c : hashASTSync(c, cache)
    );

    const input = ast.tag + '\0' + childHashes.join('\0');
    // This would need sync xxhash - use fallback for now
    throw new Error('Sync xxHash128 not available');
  }

  function hashEquals(h1, h2) {
    return h1 === h2;
  }

  function hashToString(hash) {
    return hash; // Already a hex string
  }

  return {
    name: 'xxHash128 (128-bit WASM)',
    init,
    hashString,
    hashCombine,
    hashAST,
    hashEquals,
    hashToString,
    isAsync: true
  };
})();


// ============================================================
// OPTION 4: Interned with 32-bit runtime index
// (Best of both worlds: 128-bit CID + fast integer ops)
// ============================================================

const interned = (() => {
  const store = {
    byCID: new Map(),  // CID string -> term
    byIdx: [],         // idx -> term
    nextIdx: 0,
    stringHashes: new Map()  // string -> CID
  };

  let xxhash128Fn = null;
  let initialized = false;

  async function init() {
    if (initialized) return;
    try {
      const hashWasm = require('hash-wasm');
      xxhash128Fn = hashWasm.xxhash128;
      initialized = true;
    } catch (e) {
      // Fallback to 32-bit for testing
      console.warn('hash-wasm not available, using 32-bit fallback');
      xxhash128Fn = (str) => number32.hashString(str).toString(16).padStart(8, '0');
      initialized = true;
    }
  }

  // Compute CID for a string
  async function hashString(str) {
    await init();
    if (store.stringHashes.has(str)) {
      return store.stringHashes.get(str);
    }
    const cid = await xxhash128Fn(str);
    store.stringHashes.set(str, cid);
    return cid;
  }

  // Intern an AST, returns object with _cid and _idx
  async function intern(ast) {
    await init();

    // Handle primitives
    if (!ast?.tag) {
      const str = String(ast ?? '');
      const cid = await hashString(str);
      if (store.byCID.has(cid)) return store.byCID.get(cid);

      const term = { value: str, _cid: cid, _idx: store.nextIdx++ };
      store.byCID.set(cid, term);
      store.byIdx.push(term);
      return term;
    }

    // Intern children first
    const children = [];
    for (const c of ast.children) {
      children.push(typeof c === 'string' ? await intern(c) : await intern(c));
    }

    // Compute CID from tag + child CIDs
    const childCIDs = children.map(c => c._cid);
    const input = ast.tag + '\0' + childCIDs.join('\0');
    const cid = await xxhash128Fn(input);

    // Return existing if found
    if (store.byCID.has(cid)) {
      return store.byCID.get(cid);
    }

    // Create new interned term
    const term = {
      tag: ast.tag,
      children,
      _cid: cid,
      _idx: store.nextIdx++
    };
    store.byCID.set(cid, term);
    store.byIdx.push(term);
    return term;
  }

  // Hash AST (returns CID string)
  async function hashAST(ast) {
    const interned = await intern(ast);
    return interned._cid;
  }

  // For runtime: compare by index (O(1))
  function hashEquals(t1, t2) {
    // If both have _idx, compare integers
    if (t1._idx !== undefined && t2._idx !== undefined) {
      return t1._idx === t2._idx;
    }
    // Fall back to CID comparison
    return t1._cid === t2._cid;
  }

  function hashToString(term) {
    return term._cid;
  }

  function getIdx(term) {
    return term._idx;
  }

  function reset() {
    store.byCID.clear();
    store.byIdx.length = 0;
    store.nextIdx = 0;
    store.stringHashes.clear();
  }

  function stats() {
    return {
      terms: store.byIdx.length,
      strings: store.stringHashes.size
    };
  }

  return {
    name: 'Interned xxHash128 + idx',
    init,
    intern,
    hashString,
    hashAST,
    hashEquals,
    hashToString,
    getIdx,
    reset,
    stats,
    isAsync: true,
    isInterned: true
  };
})();


module.exports = {
  bigint,
  number32,
  xxhash128,
  interned,

  // Default export for drop-in replacement testing
  algorithms: {
    'bigint': bigint,
    'number32': number32,
    'xxhash128': xxhash128,
    'interned': interned
  }
};

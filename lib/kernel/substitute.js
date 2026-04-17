/**
 * Substitution for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Equality is O(1) hash comparison.
 * Substitution returns a new hash (interned).
 */

const Store = require('./store');

const _TAG_ARRLIT = Store.TAG.arrlit;

// TODO_0216 Phase 1 (idea D): apply() short-circuits on ground terms.
// A term with no metavar anywhere is a substitution-fixpoint, so we can
// return it unchanged without walking its children or scanning θ.
// Gated by a feature flag so the optimization can be disabled at runtime
// without touching the side-table maintenance (which always runs).
const _GROUND_BIT_ENABLED = (typeof process !== 'undefined') &&
  (process.env.CALC_0216_GROUND_BIT === '1');
const _isGround = Store.isGround;

// TODO_0216 Phase 2 (idea A): Map-indexed θ.
// Linear θ-scan at every AST node is O(|θ|) per step. On fusion pipelines θ
// grows past the size where a hash-map lookup wins vs. linear scan. Above a
// tunable threshold we build a Map once per `apply()` call and replace the
// inner scan with `map.get(hash)`.
//
// Semantics: first-match (see H1 fuzz tests/kernel-apply-fuzz.test.js:203).
// H11 (tools/0216-dup-key-probe.js) confirmed 0 duplicate-key θ in production
// — the fuzz test is the only place where first!=last matters — but we still
// preserve first-match so the Map path is a drop-in replacement for any θ.
//
// Threshold of 8 picked from idea-A writeup. Override with CALC_0216_MAP_THETA_N.
const _MAP_THETA_ENABLED = (typeof process !== 'undefined') &&
  (process.env.CALC_0216_MAP_THETA === '1');
const _MAP_THETA_THRESHOLD = (() => {
  if (typeof process === 'undefined') return 8;
  const raw = parseInt(process.env.CALC_0216_MAP_THETA_N, 10);
  return Number.isFinite(raw) && raw > 0 ? raw : 8;
})();

// Build a first-match Map<hash,hash> from the theta array.
// First occurrence of each key wins — mirrors the linear scan at line ~113.
function _buildThetaMap(theta) {
  const m = new Map();
  for (let i = 0; i < theta.length; i++) {
    const k = theta[i][0];
    if (!m.has(k)) m.set(k, theta[i][1]);
  }
  return m;
}

// Arrlit helper: substitute each element, return new arrlit if changed.
function _subArrlit(hash, goFn) {
  const elems = Store.getArrayElements(hash);
  if (!elems || elems.length === 0) return hash;
  let changed = false;
  let newElems;
  for (let i = 0; i < elems.length; i++) {
    const ne = goFn(elems[i]);
    if (ne !== elems[i]) {
      if (!changed) {
        changed = true;
        newElems = new Uint32Array(elems.length);
        for (let j = 0; j < i; j++) newElems[j] = elems[j];
      }
      newElems[i] = ne;
    } else if (changed) {
      newElems[i] = elems[i];
    }
  }
  return changed ? Store.putArray(newElems) : hash;
}

/**
 * Equality: O(1) hash comparison
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @returns {boolean}
 */
const eq = (a, b) => a === b;

/**
 * Copy is identity for content-addressed terms (immutable)
 * @param {number} h - Term hash
 * @returns {number} Same hash
 */
const copy = h => h;

/**
 * Substitute v with val in term h
 * @param {number} h - Term hash
 * @param {number} v - Variable hash to replace
 * @param {number} val - Replacement term hash
 * @returns {number} New term hash (or same if unchanged)
 */
const sub = (h, v, val) => {
  if (h === v) return val;

  const t = Store.tag(h);
  if (!t) return h;

  // Arrlit: descend into element array
  if (Store.tagId(h) === _TAG_ARRLIT) return _subArrlit(h, e => sub(e, v, val));

  const a = Store.arity(h);
  let changed = false;
  const newChildren = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const newC = sub(c, v, val);
      if (newC !== c) changed = true;
      newChildren.push(newC);
    } else {
      newChildren.push(c);
    }
  }

  if (!changed) return h;
  return Store.put(t, newChildren);
};

/**
 * Apply a substitution (list of [var, val] pairs) - single traversal
 * Complexity: O(N + M) where N = |theta|, M = term size
 * REQUIRES: theta is idempotent (variables don't reference other bound vars)
 * @param {number} h - Term hash
 * @param {Array<[number, number]>} theta - Substitution
 * @returns {number} New term hash
 */
const apply = (h, theta) => {
  // Phase 3 (idea N): accept Substitution wrapper in addition to the legacy
  // array form. Unwrap once at entry — hot path remains array-typed.
  if (theta && typeof theta.toArray === 'function' && !Array.isArray(theta)) {
    theta = theta.toArray();
  }
  if (theta.length === 0) return h;
  // Outer short-circuit: a ground term can never be changed by any θ.
  if (_GROUND_BIT_ENABLED && _isGround(h)) return h;

  // Phase 2: build Map once per call when θ is large enough to amortize.
  // Single closure shape per-call either way — `lookup` is the only branch
  // so V8 keeps the IC monomorphic inside `go()` (see H4 ic-probe).
  const useMap = _MAP_THETA_ENABLED && theta.length > _MAP_THETA_THRESHOLD;
  const thetaMap = useMap ? _buildThetaMap(theta) : null;

  function go(hash) {
    // Inner short-circuit: skip the θ-scan and recursive walk on ground
    // subtrees. This is the dominant win on deep ASTs that carry a handful
    // of metavars at known positions (typical of fused EVM rules).
    if (_GROUND_BIT_ENABLED && _isGround(hash)) return hash;

    if (thetaMap !== null) {
      const hit = thetaMap.get(hash);
      if (hit !== undefined) return hit;
    } else {
      for (let i = 0; i < theta.length; i++) {
        if (theta[i][0] === hash) return theta[i][1];
      }
    }

    const t = Store.tag(hash);
    if (!t) return hash;

    // Atoms, freevars, and metavars (not in varMap) are leaves
    if (t === 'atom' || t === 'freevar' || t === 'metavar') return hash;

    // Arrlit: descend into element array
    if (Store.tagId(hash) === _TAG_ARRLIT) return _subArrlit(hash, go);

    const a = Store.arity(hash);
    let changed = false;
    const newChildren = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) {
        const nc = go(c);
        if (nc !== c) changed = true;
        newChildren.push(nc);
      } else {
        newChildren.push(c);
      }
    }

    return changed ? Store.put(t, newChildren) : hash;
  }

  return go(h);
};

/**
 * Check if variable v occurs in term h
 * @param {number} v - Variable hash
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const occurs = (v, h) => {
  if (v === h) return true;

  // Arrlit: check element array
  if (Store.tagId(h) === _TAG_ARRLIT) {
    const elems = Store.getArrayElements(h);
    if (elems) {
      for (let i = 0; i < elems.length; i++) {
        if (occurs(v, elems[i])) return true;
      }
    }
    return false;
  }

  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && occurs(v, c)) return true;
  }
  return false;
};

/**
 * De Bruijn substitution: replace bound(index) with replacement in body.
 * Increments depth under nested exists/forall binders.
 * @param {number} bodyHash - Term hash containing bound variables
 * @param {bigint} index - De Bruijn index to replace (0n = innermost binder)
 * @param {number} replacement - Term hash to substitute in
 * @returns {number} New term hash
 */
const debruijnSubst = (bodyHash, index, replacement) => {
  const TAG_BOUND = Store.TAG.bound;
  const TAG_EXISTS = Store.TAG.exists;
  const TAG_FORALL = Store.TAG.forall;
  function go(h, depth) {
    const tid = Store.tagId(h);
    if (!tid) return h;
    if (tid === TAG_BOUND) {
      const k = Store.child(h, 0); // BigInt
      return k === BigInt(depth) ? replacement : h;
    }
    if (tid === TAG_EXISTS || tid === TAG_FORALL) {
      const body = Store.child(h, 0);
      const newBody = go(body, depth + 1);
      return newBody !== body ? Store.put(Store.TAG_NAMES[tid], [newBody]) : h;
    }
    // Arrlit: descend into element array
    if (tid === _TAG_ARRLIT) return _subArrlit(h, e => go(e, depth));
    const a = Store.arity(h);
    if (a === 0) return h;
    let changed = false;
    const nc = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (Store.isTermChild(c)) {
        const r = go(c, depth);
        if (r !== c) changed = true;
        nc.push(r);
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(Store.TAG_NAMES[tid], nc) : h;
  }
  return go(bodyHash, Number(index));
};

/**
 * Apply an indexed substitution (Stage 6 de Bruijn theta).
 *
 * theta[slot] = value, slots[hash] = slotIndex.
 * O(1) metavar lookup instead of O(n) linear scan.
 *
 * See RES_0011 (de Bruijn indexed pattern matching).
 *
 * @param {number} h - Term hash
 * @param {Array} theta - Indexed theta (theta[slot] = value)
 * @param {Object} slots - { [metavarHash]: slotIndex }
 * @returns {number} New term hash
 */
const applyIndexed = (h, theta, slots) => {
  function go(hash) {
    // O(1) slot lookup (undefined if hash not a metavar in this rule)
    const slot = slots[hash];
    if (slot !== undefined) {
      let val = theta[slot];
      if (val !== undefined) {
        // Follow metavar chain: fused rules may bind A→B→concrete via
        // intermediate variables (e.g., arr_get binds ?m1=?m2, later and binds ?m2=val).
        let chain;
        while ((chain = slots[val]) !== undefined && theta[chain] !== undefined) {
          val = theta[chain];
        }
        return val;
      }
    }

    const t = Store.tag(hash);
    if (!t || t === 'atom' || t === 'freevar' || t === 'metavar') return hash;

    // Arrlit: descend into element array
    if (Store.tagId(hash) === _TAG_ARRLIT) return _subArrlit(hash, go);

    const a = Store.arity(hash);

    // Arity-specialized paths (avoid children array allocation)
    if (a === 1) {
      const c0 = Store.child(hash, 0);
      const n0 = Store.isTermChild(c0) ? go(c0) : c0;
      return n0 !== c0 ? Store.put1(t, n0) : hash;
    }
    if (a === 2) {
      const c0 = Store.child(hash, 0), c1 = Store.child(hash, 1);
      const n0 = Store.isTermChild(c0) ? go(c0) : c0;
      const n1 = Store.isTermChild(c1) ? go(c1) : c1;
      return (n0 !== c0 || n1 !== c1) ? Store.put2(t, n0, n1) : hash;
    }
    if (a === 3) {
      const c0 = Store.child(hash, 0), c1 = Store.child(hash, 1), c2 = Store.child(hash, 2);
      const n0 = Store.isTermChild(c0) ? go(c0) : c0;
      const n1 = Store.isTermChild(c1) ? go(c1) : c1;
      const n2 = Store.isTermChild(c2) ? go(c2) : c2;
      return (n0 !== c0 || n1 !== c1 || n2 !== c2) ? Store.put3(t, n0, n1, n2) : hash;
    }
    if (a === 0) return hash;

    let changed = false;
    const nc = [];
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) {
        const r = go(c);
        if (r !== c) changed = true;
        nc.push(r);
      } else {
        nc.push(c);
      }
    }
    return changed ? Store.put(t, nc) : hash;
  }

  return go(h);
};

/**
 * Compiled substitution — direct Store.put from precomputed recipe.
 * Bypasses recursive applyIndexed traversal for flat patterns.
 *
 * recipe: { tag, sources: [{type:'slot',slot}|{type:'literal',value}], compiled, isSlot }
 *
 * @param {Object} recipe - Compiled substitution recipe
 * @param {Array} theta - Indexed theta (theta[slot] = value)
 * @returns {number} New term hash
 */
const subCompiled = (recipe, theta) => {
  if (recipe.isSlot) return theta[recipe.slot];
  const sources = recipe.sources;
  const n = sources.length;
  if (n === 1) {
    const s = sources[0];
    return Store.put(recipe.tag, [s.type === 'slot' ? theta[s.slot] : s.value]);
  }
  if (n === 2) {
    const s0 = sources[0], s1 = sources[1];
    return Store.put(recipe.tag, [
      s0.type === 'slot' ? theta[s0.slot] : s0.value,
      s1.type === 'slot' ? theta[s1.slot] : s1.value
    ]);
  }
  const children = [];
  for (let i = 0; i < n; i++) {
    const s = sources[i];
    children.push(s.type === 'slot' ? theta[s.slot] : s.value);
  }
  return Store.put(recipe.tag, children);
};

module.exports = {
  sub,
  apply,
  applyIndexed,
  subCompiled,
  debruijnSubst,
  eq,
  copy,
  occurs
};

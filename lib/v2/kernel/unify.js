/**
 * Unification for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Uses Store to dereference when inspecting structure.
 *
 * Supports ephemeral expansion for compact primitive literals:
 * - binlit(n) can be pattern-matched against (i X), (o X), e
 * - strlit(s) can be pattern-matched against cons(H, T), nil
 */

const Store = require('./store');
const { sub, eq, occurs } = require('./substitute');

// ============================================================================
// EPHEMERAL EXPANSION FOR PRIMITIVES
// ============================================================================

/**
 * Try to unify a pattern against a binlit term via ephemeral expansion
 *
 * binlit(10n) vs (o X) → X = binlit(5n)
 * binlit(0n) vs e → success
 * binlit(7n) vs (i X) → X = binlit(3n)
 *
 * @param {number} pattern - Pattern term hash
 * @param {number} term - binlit term hash
 * @param {Array} G - Goal list to push new constraints to
 * @returns {boolean} Whether ephemeral expansion succeeded
 */
function unifyBinlit(pattern, term, G) {
  const termNode = Store.get(term);
  if (!termNode || termNode.tag !== 'binlit') return false;
  const value = termNode.children[0];

  const patternNode = Store.get(pattern);
  if (!patternNode) return false;

  // Pattern: e (zero)
  if (patternNode.tag === 'atom' && patternNode.children[0] === 'e') {
    return value === 0n;
  }

  // Pattern: binlit (direct comparison)
  if (patternNode.tag === 'binlit') {
    return patternNode.children[0] === value;
  }

  // Pattern: app(o, X) or app(i, X)
  if (patternNode.tag === 'app') {
    const head = Store.get(patternNode.children[0]);
    if (!head || head.tag !== 'atom') return false;

    const bit = head.children[0];
    const tailPattern = patternNode.children[1];

    if (bit === 'o') {
      // o X matches even non-zero numbers
      if (value === 0n || value % 2n !== 0n) return false;
      const tailValue = Store.intern('binlit', [value / 2n]);
      G.push([tailPattern, tailValue]);
      return true;
    }

    if (bit === 'i') {
      // i X matches odd numbers
      if (value % 2n !== 1n) return false;
      const tailValue = Store.intern('binlit', [value / 2n]);
      G.push([tailPattern, tailValue]);
      return true;
    }
  }

  return false;
}

/**
 * Try to unify a pattern against a strlit term via ephemeral expansion
 *
 * strlit("hello") vs cons(H, T) → H = charlit('h'), T = strlit("ello")
 * strlit("") vs nil → success
 *
 * @param {number} pattern - Pattern term hash
 * @param {number} term - strlit term hash
 * @param {Array} G - Goal list to push new constraints to
 * @returns {boolean} Whether ephemeral expansion succeeded
 */
function unifyStrlit(pattern, term, G) {
  const termNode = Store.get(term);
  if (!termNode || termNode.tag !== 'strlit') return false;
  const str = termNode.children[0];

  const patternNode = Store.get(pattern);
  if (!patternNode) return false;

  // Pattern: nil (empty string)
  if (patternNode.tag === 'atom' && patternNode.children[0] === 'nil') {
    return str === '';
  }

  // Pattern: strlit (direct comparison)
  if (patternNode.tag === 'strlit') {
    return patternNode.children[0] === str;
  }

  // Pattern: cons(H, T) - represented as app(app(cons, H), T)
  if (patternNode.tag === 'app') {
    const head = Store.get(patternNode.children[0]);
    if (head && head.tag === 'app') {
      const consAtom = Store.get(head.children[0]);
      if (consAtom && consAtom.tag === 'atom' && consAtom.children[0] === 'cons') {
        if (str === '') return false;  // Can't destructure empty string

        const headPattern = head.children[1];  // H
        const tailPattern = patternNode.children[1];  // T

        // First char as charlit, rest as strlit
        const firstChar = Store.intern('charlit', [str.charCodeAt(0)]);
        const restStr = Store.intern('strlit', [str.slice(1)]);

        G.push([headPattern, firstChar]);
        G.push([tailPattern, restStr]);
        return true;
      }
    }
  }

  return false;
}

/**
 * Check if term is a metavar (unification variable)
 * Metavars are freevars whose name starts with underscore
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const isMetavar = h => {
  const node = Store.get(h);
  if (!node || node.tag !== 'freevar') return false;
  const name = node.children[0];
  return typeof name === 'string' && name.startsWith('_');
};

/**
 * Check if term is a regular freevar (not a metavar)
 * @param {number} h - Term hash
 * @returns {boolean}
 */
const isFreevar = h => {
  const node = Store.get(h);
  if (!node || node.tag !== 'freevar') return false;
  const name = node.children[0];
  return typeof name === 'string' && !name.startsWith('_');
};

/**
 * Alias for isMetavar (backwards compat)
 */
const isVar = isMetavar;

/**
 * Get the variable name from a freevar term
 * @param {number} h - Freevar hash
 * @returns {string|undefined}
 */
const getVarName = h => {
  const node = Store.get(h);
  if (!node || node.tag !== 'freevar') return undefined;
  return node.children[0];
};

/**
 * Unify two terms using idempotent MGU (legacy/quadratic)
 * Complexity: O(K² × M) where K = bindings, M = term size
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @returns {Array<[number, number]>|null} Substitution or null if unification fails
 */
const unifyIdempotent = (a, b) => {
  const G = [[a, b]];
  let theta = [];

  while (G.length) {
    const [t0, t1] = G.pop();

    // Equal terms - nothing to do
    if (t0 === t1) continue;

    // Metavar on left - bind it
    if (isMetavar(t0)) {
      if (occurs(t0, t1)) return null;  // Occurs check
      // Apply substitution to existing bindings and add new binding
      theta = [...theta.map(([v, x]) => [v, sub(x, t0, t1)]), [t0, t1]];
      // Apply to remaining goals
      G.forEach((g, i) => { G[i] = [sub(g[0], t0, t1), sub(g[1], t0, t1)]; });
      continue;
    }

    // Metavar on right - swap and retry
    if (isMetavar(t1)) {
      G.push([t1, t0]);
      continue;
    }

    // Both are freevars (not metavars) - must have same name
    if (isFreevar(t0) && isFreevar(t1)) {
      if (getVarName(t0) !== getVarName(t1)) return null;
      continue;
    }

    // Get nodes for structural comparison
    const n0 = Store.get(t0);
    const n1 = Store.get(t1);

    // Both must be valid nodes
    if (!n0 || !n1) return null;

    // Same tag and arity - decompose
    if (n0.tag === n1.tag && n0.children.length === n1.children.length) {
      // Add child pairs to goal list
      for (let i = 0; i < n0.children.length; i++) {
        const c0 = n0.children[i];
        const c1 = n1.children[i];
        // Only unify term children (not string primitives)
        if (Store.isTermChild(c0) && Store.isTermChild(c1)) {
          G.push([c0, c1]);
        } else if (c0 !== c1) {
          // Primitive children must be equal
          return null;
        }
      }
      continue;
    }

    // Different structure - fail
    return null;
  }

  return theta;
};

// ============================================================================
// UNION-FIND UNIFICATION
// ============================================================================

/**
 * Union-Find data structure for unification
 * Supports path compression for O(α(n)) operations
 */
class UnionFind {
  constructor() {
    this.parent = new Map();  // var → (var | ground term)
  }

  /**
   * Find the canonical representative of a term
   * @param {number} v - Term hash
   * @returns {number} Canonical representative
   */
  find(v) {
    if (!this.parent.has(v)) return v;

    const p = this.parent.get(v);

    // If parent is not a metavar, it's the ground binding
    const pNode = Store.get(p);
    if (!pNode || pNode.tag !== 'freevar' || !pNode.children[0]?.startsWith('_')) {
      return p;
    }

    // Path compression: make v point directly to root
    const root = this.find(p);
    if (root !== p) {
      this.parent.set(v, root);
    }
    return root;
  }

  /**
   * Union two terms (bind var to term)
   * @param {number} v - Variable hash
   * @param {number} term - Term to bind to
   */
  union(v, term) {
    const rv = this.find(v);
    this.parent.set(rv, term);
  }

  /**
   * Convert to theta list for compatibility
   * @returns {Array<[number, number]>}
   */
  toTheta() {
    const theta = [];
    const processed = new Set();

    for (const [v] of this.parent) {
      if (processed.has(v)) continue;

      const root = this.find(v);
      if (root !== v) {
        theta.push([v, root]);
      }
      processed.add(v);
    }

    return theta;
  }
}

/**
 * Occurs check within union-find context
 * @param {number} v - Variable to check for
 * @param {number} h - Term to check in
 * @param {UnionFind} uf - Union-find structure
 * @returns {boolean}
 */
function occursInUF(v, h, uf) {
  const resolved = uf.find(h);
  if (v === resolved) return true;

  const node = Store.get(resolved);
  if (!node) return false;

  return node.children.some(c =>
    Store.isTermChild(c) ? occursInUF(v, c, uf) : false
  );
}

/**
 * Unify two terms using union-find
 * Complexity: O(K × α(K) × M) ≈ O(K × M) where K = bindings, M = term size
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @param {Object} opts - Options { deferOccursCheck: boolean }
 * @returns {Array<[number, number]>|null} Substitution or null if unification fails
 */
const unifyUF = (a, b, opts = {}) => {
  const deferOccursCheck = opts.deferOccursCheck || false;
  const uf = new UnionFind();
  const G = [[a, b]];
  const deferredChecks = [];  // For deferred occurs check

  while (G.length) {
    const [t0raw, t1raw] = G.pop();

    // Resolve through union-find
    const t0 = uf.find(t0raw);
    const t1 = uf.find(t1raw);

    // Equal after resolution - nothing to do
    if (t0 === t1) continue;

    // Metavar on left - bind it
    if (isMetavar(t0)) {
      if (deferOccursCheck) {
        // Defer occurs check to end
        deferredChecks.push([t0, t1]);
      } else {
        // Eager occurs check
        if (occursInUF(t0, t1, uf)) return null;
      }
      uf.union(t0, t1);
      continue;
    }

    // Metavar on right - swap and retry
    if (isMetavar(t1)) {
      G.push([t1, t0]);
      continue;
    }

    // Both are freevars (not metavars) - must have same name
    if (isFreevar(t0) && isFreevar(t1)) {
      if (getVarName(t0) !== getVarName(t1)) return null;
      continue;
    }

    // Get nodes for structural comparison
    const n0 = Store.get(t0);
    const n1 = Store.get(t1);

    // Both must be valid nodes
    if (!n0 || !n1) return null;

    // Ephemeral expansion for binlit
    if (n0.tag === 'binlit' || n1.tag === 'binlit') {
      // binlit vs binlit: direct value comparison
      if (n0.tag === 'binlit' && n1.tag === 'binlit') {
        if (n0.children[0] !== n1.children[0]) return null;
        continue;
      }
      // Pattern vs binlit: ephemeral expansion
      const [pat, lit] = n0.tag === 'binlit' ? [t1, t0] : [t0, t1];
      if (!unifyBinlit(pat, lit, G)) return null;
      continue;
    }

    // Ephemeral expansion for strlit
    if (n0.tag === 'strlit' || n1.tag === 'strlit') {
      // strlit vs strlit: direct value comparison
      if (n0.tag === 'strlit' && n1.tag === 'strlit') {
        if (n0.children[0] !== n1.children[0]) return null;
        continue;
      }
      // Pattern vs strlit: ephemeral expansion
      const [pat, lit] = n0.tag === 'strlit' ? [t1, t0] : [t0, t1];
      if (!unifyStrlit(pat, lit, G)) return null;
      continue;
    }

    // Charlit: direct value comparison only
    if (n0.tag === 'charlit' || n1.tag === 'charlit') {
      if (n0.tag !== 'charlit' || n1.tag !== 'charlit') return null;
      if (n0.children[0] !== n1.children[0]) return null;
      continue;
    }

    // Same tag and arity - decompose
    if (n0.tag === n1.tag && n0.children.length === n1.children.length) {
      for (let i = 0; i < n0.children.length; i++) {
        const c0 = n0.children[i];
        const c1 = n1.children[i];
        if (Store.isTermChild(c0) && Store.isTermChild(c1)) {
          G.push([c0, c1]);
        } else if (c0 !== c1) {
          return null;
        }
      }
      continue;
    }

    // Different structure - fail
    return null;
  }

  // Deferred occurs check at end (if enabled)
  if (deferOccursCheck) {
    for (const [v, term] of deferredChecks) {
      if (occursInUF(v, term, uf)) return null;
    }
  }

  return uf.toTheta();
};

/**
 * Unify two terms, returning MGU substitution or null
 * Uses union-find for better performance
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @returns {Array<[number, number]>|null} Substitution or null if unification fails
 */
const unify = (a, b) => unifyUF(a, b, { deferOccursCheck: false });

/**
 * One-way matching: pattern matches term
 * @param {number} pattern - Pattern hash (may contain metavars)
 * @param {number} term - Term hash (ground)
 * @param {Array<[number, number]>} initialTheta - Initial substitution to extend
 * @returns {Array<[number, number]>|null} Substitution or null
 */
const match = (pattern, term, initialTheta = []) => {
  const G = [[pattern, term]];
  let theta = [...initialTheta];

  while (G.length) {
    const [p, t] = G.pop();

    // Equal - nothing to do
    if (p === t) continue;

    // Pattern is a metavar - bind it
    if (isVar(p)) {
      // Check for consistent binding
      const existing = theta.find(([v]) => v === p);
      if (existing && existing[1] !== t) return null;
      if (!existing) theta.push([p, t]);
      continue;
    }

    // Get nodes for structural comparison
    const np = Store.get(p);
    const nt = Store.get(t);

    if (!np || !nt) return null;

    // Same tag and arity - decompose
    if (np.tag === nt.tag && np.children.length === nt.children.length) {
      for (let i = 0; i < np.children.length; i++) {
        const cp = np.children[i];
        const ct = nt.children[i];
        if (Store.isTermChild(cp) && Store.isTermChild(ct)) {
          G.push([cp, ct]);
        } else if (cp !== ct) {
          return null;
        }
      }
      continue;
    }

    // Different structure - fail
    return null;
  }

  return theta;
};

module.exports = {
  unify,
  unifyUF,
  unifyIdempotent,
  match,
  isVar,
  isMetavar,
  isFreevar,
  getVarName,
  UnionFind,
  // Ephemeral expansion helpers (for testing)
  unifyBinlit,
  unifyStrlit
};

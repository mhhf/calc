/**
 * Unification for content-addressed terms
 *
 * All terms are represented as hashes (numbers).
 * Uses Store to dereference when inspecting structure.
 */

const Store = require('./store');
const { sub, eq, occurs } = require('./substitute');

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
 * Unify two terms, returning MGU substitution or null
 * @param {number} a - Term hash
 * @param {number} b - Term hash
 * @returns {Array<[number, number]>|null} Substitution or null if unification fails
 */
const unify = (a, b) => {
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

/**
 * One-way matching: pattern matches term
 * @param {number} pattern - Pattern hash (may contain metavars)
 * @param {number} term - Term hash (ground)
 * @returns {Array<[number, number]>|null} Substitution or null
 */
const match = (pattern, term) => {
  const G = [[pattern, term]];
  let theta = [];

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

module.exports = { unify, match, isVar, isMetavar, isFreevar, getVarName };

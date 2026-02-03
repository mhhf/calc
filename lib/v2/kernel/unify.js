/**
 * Unification: unify(a, b) → theta | null
 * MGU algorithm.
 */

const { sub, eq, occurs } = require('./substitute');

// Metavars (unification variables) start with underscore
const isMetavar = ast => ast?.tag === 'freevar' && ast.children[0]?.startsWith('_');
// Regular freevars are "ground" - only unify with themselves
const isFreevar = ast => ast?.tag === 'freevar' && !ast.children[0]?.startsWith('_');
// For backwards compat
const isVar = ast => isMetavar(ast);

const unify = (a, b) => {
  const G = [[a, b]];
  let theta = [];

  while (G.length) {
    const [t0, t1] = G.pop();
    if (eq(t0, t1)) continue;

    // Metavars (_X, _Y, etc.) are true unification variables
    if (isMetavar(t0)) {
      if (occurs(t0, t1)) return null;
      theta = [...theta.map(([v, x]) => [v, sub(x, t0, t1)]), [t0, t1]];
      G.forEach((g, i) => { G[i] = [sub(g[0], t0, t1), sub(g[1], t0, t1)]; });
    } else if (isMetavar(t1)) {
      G.push([t1, t0]);
    } else if (isFreevar(t0) && isFreevar(t1)) {
      // Two freevars with different names don't unify
      if (t0.children[0] !== t1.children[0]) return null;
    } else if (!t0?.tag || !t1?.tag) {
      return null;  // strings/primitives that aren't equal
    } else if (t0.tag === t1.tag && t0.children.length === t1.children.length) {
      t0.children.forEach((c, i) => G.push([c, t1.children[i]]));
    } else {
      return null;
    }
  }
  return theta;
};

const match = (pattern, term) => {
  const G = [[pattern, term]];
  let theta = [];

  while (G.length) {
    const [p, t] = G.pop();
    if (eq(p, t)) continue;

    if (isVar(p)) {
      const existing = theta.find(([v]) => eq(v, p));
      if (existing && !eq(existing[1], t)) return null;
      if (!existing) theta.push([p, t]);
    } else if (p?.tag === t?.tag && p.children?.length === t.children?.length) {
      p.children.forEach((c, i) => G.push([c, t.children[i]]));
    } else {
      return null;
    }
  }
  return theta;
};

module.exports = { unify, match, isVar, isMetavar, isFreevar };

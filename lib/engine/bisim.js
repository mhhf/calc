/**
 * Structural bisimulation of execution trees (TODO_0009 §7, Inc-7).
 *
 * Two finite-state forward programs are bisimilar when their exhaustive
 * execution trees (explore() output) have the same branching structure and
 * related leaf states. `bisimTrees` decides this for the bounded case; the
 * INFINITE-state case is the coinductive `bisim` relation proven by co-LP
 * (Inc-5b) — declare the bisimulation relation coinductive and a guarded loop is
 * a coinductive success (see tests/engine/backchain-coinductive.test.js, the
 * infinite-graph-path shape).
 *
 * Soundness: `bisimilar: true` means a strong bisimulation relates the two
 * trees — every branch of one is matched by an equally-labelled branch of the
 * other with bisimilar continuations, and terminal states are related by the
 * caller's `stateEq`. The checker verifies the STRUCTURE given the relation; the
 * state-equivalence relation itself is the caller's obligation (as in any
 * simulation check). `bisimilar: false` returns a counterexample path; it can be
 * conservative when several edges share a rule label (it matches them pairwise
 * after sorting rather than searching all pairings) — a false negative, never a
 * false positive.
 *
 * Pure: no engine imports. The caller supplies the two trees (from its own
 * explore()) and the state-equivalence predicate.
 */

const TERMINAL = new Set(['leaf', 'cycle', 'bound', 'memo']);

/**
 * @param {Object} t1 - execution tree (explore() node: { type, state?, children? })
 * @param {Object} t2 - execution tree to compare against
 * @param {Object} opts
 *   stateEq: (s1, s2) => boolean — equivalence on terminal states (default ===)
 *   ruleMap: { [rule]: canonicalRule } — rename rules before matching (default identity)
 * @returns {{ bisimilar: true } | { bisimilar: false, counterexample: { path, reason } }}
 */
function bisimTrees(t1, t2, opts = {}) {
  const stateEq = opts.stateEq || ((a, b) => a === b);
  const rmap = opts.ruleMap || null;
  const ruleOf = (r) => (rmap && rmap[r] !== undefined ? rmap[r] : r);

  const liveEdges = (node) =>
    (node.children || []).filter(e => e.child && e.child.type !== 'dead');

  function go(a, b, path) {
    if (!a || !b) return a === b ? null : { path, reason: 'one side missing' };
    if (a.type !== b.type) return { path, reason: `node type ${a.type} ≠ ${b.type}` };
    if (a.type === 'dead') return null;                       // both pruned
    if (TERMINAL.has(a.type)) {
      return stateEq(a.state, b.state) ? null : { path, reason: `${a.type} states not equivalent` };
    }
    if (a.type === 'branch') {
      const e1 = liveEdges(a).slice().sort((x, y) => String(ruleOf(x.rule)).localeCompare(String(ruleOf(y.rule))));
      const e2 = liveEdges(b).slice().sort((x, y) => String(ruleOf(x.rule)).localeCompare(String(ruleOf(y.rule))));
      if (e1.length !== e2.length) return { path, reason: `branching degree ${e1.length} ≠ ${e2.length}` };
      for (let i = 0; i < e1.length; i++) {
        const r1 = ruleOf(e1[i].rule), r2 = ruleOf(e2[i].rule);
        if (r1 !== r2) return { path, reason: `rule label ${r1} ≠ ${r2}` };
        const sub = go(e1[i].child, e2[i].child, [...path, r1]);
        if (sub) return sub;
      }
      return null;
    }
    return { path, reason: `unhandled node type ${a.type}` };
  }

  const cx = go(t1, t2, []);
  return cx ? { bisimilar: false, counterexample: cx } : { bisimilar: true };
}

export { bisimTrees };
export default { bisimTrees };

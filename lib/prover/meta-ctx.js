/**
 * Metacontext — first-class metavar state for proof search.
 *
 * Standard approach from Lean 4 (MetavarContext), Agda (MetaState), Twelf (Σ).
 * Replaces the previous post-hoc applyThetaToTree walk with an incremental
 * approach: bindings are absorbed as they're discovered by unify(), and
 * proof tree nodes are resolved lazily via resolveSeq/resolveTree.
 *
 * WAM-style trail for backtracking: save() returns a trail mark, restore(mark)
 * undoes all bindings after that mark. This is O(K) where K = bindings undone,
 * vs the previous O(N·S) full-tree walk (N = tree nodes, S = theta size).
 *
 * Key invariant: unify() stays pure (returns theta list). The MetaCtx is a
 * prover concern (focused.js), not a kernel concern. The caller absorbs
 * unify's theta via absorbTheta(). This keeps generic.js unaware of MetaCtx.
 *
 * Future: register() for unsolved metavars (needed for dependent types,
 * TODO_0011). Currently all entries are solved (bind-only, no null values).
 */

const { apply: subApply } = require('../kernel/substitute');
const Seq = require('../kernel/sequent');

class MetaCtx {
  constructor() {
    this.bindings = new Map(); // metavar_hash → ground_hash | null
    this.trail = [];           // undo log: [metavar_hash, ...]
  }

  /** Record a binding discovered by unify */
  bind(metavar, term) {
    this.trail.push(metavar);
    this.bindings.set(metavar, term);
  }

  /** Record all bindings from a theta list (from unify()) */
  absorbTheta(theta) {
    for (const [v, t] of theta) this.bind(v, t);
  }

  /**
   * Resolve a single hash. Returns input unchanged for ground terms.
   * For direct metavar hits, returns the bound value (O(1) Map lookup).
   * For compound terms containing metavars, delegates to _resolveCompound
   * which calls substitute.apply — O(term_size) but only when needed.
   */
  resolve(hash) {
    const bound = this.bindings.get(hash);
    // null check: defensive for future register() support (TODO_0011 dependent types)
    if (bound !== undefined) return bound === null ? hash : bound;
    if (this.bindings.size === 0) return hash;
    return this._resolveCompound(hash);
  }

  /** Resolve all hashes in a sequent */
  resolveSeq(seq) {
    return Seq.substitute(seq, this._asTheta());
  }

  /** Save trail position for backtracking */
  save() { return this.trail.length; }

  /** Restore to saved trail position, undoing bindings */
  restore(mark) {
    while (this.trail.length > mark)
      this.bindings.delete(this.trail.pop());
  }

  /** Are there any solved bindings? Assumes all entries are solved (no register()). */
  hasBindings() { return this.bindings.size > 0; }

  /**
   * Resolve all sequents in a proof tree (catches sibling gaps).
   *
   * Sibling gap: when search branches (e.g., tensor_r), the left subtree
   * may be constructed before the right subtree binds a shared metavar.
   * The left subtree's conclusion has unresolved hashes. resolveTree
   * fixes these post-hoc — called once at the end of prove() when
   * hasBindings() is true.
   */
  resolveTree(tree) {
    const { ProofTree } = require('./pt');
    const theta = this._asTheta();
    if (theta.length === 0) return tree;
    const walk = (node) => new ProofTree({
      conclusion: Seq.substitute(node.conclusion, theta),
      premises: node.premises.map(walk),
      rule: node.rule,
      proven: node.proven,
      state: node.state
    });
    return walk(tree);
  }

  /** @private Resolve compound term via substitute.apply */
  _resolveCompound(hash) {
    const theta = this._asTheta();
    if (theta.length === 0) return hash;
    return subApply(hash, theta);
  }

  /** @private Extract solved bindings as theta list */
  _asTheta() {
    const theta = [];
    for (const [v, t] of this.bindings)
      if (t !== null) theta.push([v, t]);
    return theta;
  }
}

module.exports = { MetaCtx };

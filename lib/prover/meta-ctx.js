/**
 * Metacontext — first-class metavar state for proof search.
 *
 * Threads metavar bindings through backward search with WAM-style
 * trail for backtracking. Replaces post-hoc applyThetaToTree walk.
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

  /** Resolve a single hash. Returns input unchanged for ground terms. */
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

  /** Resolve all sequents in a proof tree (catches sibling gaps) */
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

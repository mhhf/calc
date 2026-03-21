/**
 * Constraint Solver for Branch Pruning
 *
 * EqNeqSolver: union-find with forbid list for eq/neq constraints.
 * Supports checkpoint/restore for DFS backtracking.
 *
 * Used by explore to prune infeasible branches at oplus expansion time:
 * - !eq X Y → union(X, Y)
 * - !neq X Y → forbid(X, Y)
 * - checkSAT() → false if any forbid pair shares a representative
 *
 * Ground short-circuit: if both args are ground, evaluate directly.
 */

const Store = require('../kernel/store');
const { getPredicateHead } = require('../kernel/ast');
const { binToInt } = require('./ill/ffi/convert');
const { isGround } = require('./ill/ffi/convert');

// ─── Union-Find with Undo ────────────────────────────────────────────

class EqNeqSolver {
  constructor() {
    // Union-find arrays (indexed by variable ID)
    this.parent = [];
    this.rank = [];

    // Forbid pairs: [[varA, varB], ...]
    this.forbids = [];

    // Hash → variable ID mapping
    this._hashToVar = new Map();
    this._nextVar = 0;

    // Undo log: entries are { type, ...data }
    // type: 'union' | 'forbid' | 'newvar'
    this._undoLog = [];
  }

  /**
   * Get or create a variable ID for a content-addressed hash.
   */
  _varFor(h) {
    let v = this._hashToVar.get(h);
    if (v !== undefined) return v;
    v = this._nextVar++;
    this._hashToVar.set(h, v);
    this.parent[v] = v;
    this.rank[v] = 0;
    this._undoLog.push({ type: 'newvar', hash: h, id: v });
    return v;
  }

  /**
   * Find representative (with path compression recorded in undo log).
   */
  _find(x) {
    while (this.parent[x] !== x) {
      // Path halving (no compression to keep undo simple)
      x = this.parent[x];
    }
    return x;
  }

  /**
   * Union two variables by rank. Records undo info.
   * Returns true if they were in different sets (actual union happened).
   */
  _union(a, b) {
    const ra = this._find(a);
    const rb = this._find(b);
    if (ra === rb) return false;

    // Union by rank
    if (this.rank[ra] < this.rank[rb]) {
      this._undoLog.push({ type: 'union', child: ra, oldParent: ra, oldRank: this.rank[ra] });
      this.parent[ra] = rb;
    } else if (this.rank[ra] > this.rank[rb]) {
      this._undoLog.push({ type: 'union', child: rb, oldParent: rb, oldRank: this.rank[rb] });
      this.parent[rb] = ra;
    } else {
      this._undoLog.push({ type: 'union', child: rb, oldParent: rb, oldRank: this.rank[ra], rankBump: ra });
      this.parent[rb] = ra;
      this.rank[ra]++;
    }
    return true;
  }

  /**
   * Add a constraint from a persistent fact hash.
   * Returns true if the constraint was recognized and added.
   */
  addConstraint(h) {
    const pred = getPredicateHead(h);
    if (pred !== 'eq' && pred !== 'neq') return false;
    if (Store.arity(h) < 2) return false;

    const arg0 = Store.child(h, 0);
    const arg1 = Store.child(h, 1);

    // Ground short-circuit: evaluate directly without touching union-find
    const a0 = isGround(arg0) ? binToInt(arg0) : null;
    const a1 = isGround(arg1) ? binToInt(arg1) : null;
    if (a0 !== null && a1 !== null) {
      if (pred === 'eq') {
        if (a0 !== a1) {
          // Ground eq contradiction — mark UNSAT by adding a self-forbid
          const v = this._varFor(arg0);
          this._undoLog.push({ type: 'forbid', idx: this.forbids.length });
          this.forbids.push([v, v]);
        }
        // If equal, no constraint needed (trivially true)
      } else {
        if (a0 === a1) {
          // Ground neq contradiction
          const v = this._varFor(arg0);
          this._undoLog.push({ type: 'forbid', idx: this.forbids.length });
          this.forbids.push([v, v]);
        }
        // If not equal, no constraint needed (trivially true)
      }
      return true;
    }

    // Symbolic: use union-find
    const v0 = this._varFor(arg0);
    const v1 = this._varFor(arg1);

    if (pred === 'eq') {
      this._union(v0, v1);
    } else {
      this._undoLog.push({ type: 'forbid', idx: this.forbids.length });
      this.forbids.push([v0, v1]);
    }
    return true;
  }

  /**
   * Check satisfiability.
   * Returns false if any forbid pair shares a representative.
   */
  checkSAT() {
    for (let i = 0; i < this.forbids.length; i++) {
      const [a, b] = this.forbids[i];
      if (this._find(a) === this._find(b)) return false;
    }
    return true;
  }

  /**
   * Create a checkpoint for backtracking.
   * Returns an opaque token (undo log length).
   */
  checkpoint() {
    return this._undoLog.length;
  }

  /**
   * Restore to a previous checkpoint, undoing all operations since.
   */
  restore(token) {
    while (this._undoLog.length > token) {
      const entry = this._undoLog.pop();
      switch (entry.type) {
        case 'union':
          this.parent[entry.child] = entry.oldParent;
          if (entry.rankBump !== undefined) {
            this.rank[entry.rankBump]--;
          }
          break;
        case 'forbid':
          this.forbids.pop();
          break;
        case 'newvar':
          this._hashToVar.delete(entry.hash);
          this._nextVar--;
          break;
      }
    }
  }
}

module.exports = { EqNeqSolver };

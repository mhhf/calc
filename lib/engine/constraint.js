/**
 * Constraint Solver for Branch Pruning
 *
 * EqNeqSolver: union-find with forbid list for eq/neq constraints.
 * Supports checkpoint/restore for DFS backtracking.
 *
 * Used by explore to prune infeasible branches at oplus expansion time:
 * - !<eq> X Y → union(X, Y)
 * - !<neq> X Y → forbid(X, Y)
 * - checkSAT() → false if any forbid pair shares a representative
 *
 * WHICH predicates carry equality/disequality semantics is calculus
 * data: `opts.predNames` ({ eq, neq }, from cc.domain.constraintPreds).
 * Without it the solver recognizes nothing and every branch survives —
 * a program's unrelated `eq` predicate never gets constraint semantics
 * imposed on it (RES_0143 L3; the names were hardcoded before).
 *
 * Ground short-circuit: if both args are ground, evaluate directly.
 *
 * Order guards (task #84, THY_0039 §4 G2 residual (i)): `opts.order` maps a
 * predicate name to a comparator op ('<' | '<=' | '>' | '>='). A GROUND tell of
 * such an atom (e.g. `!lt 7 5`) is decided by direct value evaluation — the
 * same evalNumeric short-circuit eq/neq use — and a false one is marked UNSAT,
 * pruning the branch whose denotation it drove to ∅. Unlike eq/neq there is no
 * symbolic (union-find) reading of an order relation, so a non-ground order
 * atom is opaque (the branch survives — completeness-only, never soundness).
 * The map explore passes is already the intersection of the declared order
 * guards with the certified total decision procedures (calc.decidablePreds,
 * §6.1′) — an uncertified guard never reaches here.
 */

import Store from '../kernel/store.js';
import { predHead } from '../kernel/ast.js';
import { applyIndexed as subApplyIdx } from '../kernel/substitute.js';
import { INSERT_OP } from './fact-set.js';

// Ground comparator evaluation for order guards. `a`/`b` are the decoded values
// evalNumeric returns (BigInt for bin/rat — exact at 256 bits, no precision
// loss); the relational operators are polymorphic over BigInt and number.
function _cmpHolds(op, a, b) {
  switch (op) {
    case '<': return a < b;
    case '<=': return a <= b;
    case '>': return a > b;
    case '>=': return a >= b;
    default: return true; // unknown op: never refute (opaque)
  }
}

// ─── Union-Find with Undo ────────────────────────────────────────────

class EqNeqSolver {
  constructor(opts = {}) {
    this._evalNumeric = opts.evalNumeric || null;
    this._predNames = opts.predNames || null;
    // predName → comparator op ('<'|'<='|'>'|'>='); already certified-total
    // and declared (explore intersects order guards with calc.decidablePreds).
    this._order = opts.order || null;
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
    const pn = this._predNames;
    if (!pn) return false;
    const pred = predHead(h);
    const isEq = pred === pn.eq;
    const isNeq = pred === pn.neq;
    const op = (!isEq && !isNeq && this._order) ? this._order[pred] : undefined;
    if (!isEq && !isNeq && op === undefined) return false;
    if (Store.arity(h) < 2) return false;

    const arg0 = Store.child(h, 0);
    const arg1 = Store.child(h, 1);

    // Ground short-circuit: evaluate directly without touching union-find
    const a0 = this._evalNumeric ? this._evalNumeric(arg0) : null;
    const a1 = this._evalNumeric ? this._evalNumeric(arg1) : null;

    // Order guard (task #84): decidable ONLY by direct value evaluation. A
    // symbolic order atom has no union-find reading — opaque (survive).
    if (op !== undefined) {
      if (a0 === null || a1 === null) return false;
      if (!_cmpHolds(op, a0, a1)) {
        // False ground order tell — its leaf denotes ∅. Mark UNSAT.
        const v = this._varFor(arg0);
        this._undoLog.push({ type: 'forbid', idx: this.forbids.length });
        this.forbids.push([v, v]);
      }
      return true;
    }

    if (a0 !== null && a1 !== null) {
      if (isEq) {
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

    if (isEq) {
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

// ─── Explore Integration ─────────────────────────────────────────────
// Solver lifecycle inside explore: feeding persistent facts from the
// arena, SAT-filtering oplus alternatives.

/**
 * Feed newly-added persistent facts from perArena into the solver.
 * Reads arena records from checkpoint to current cursor, looking for INSERT ops.
 *
 * @param {EqNeqSolver} solver - Constraint solver
 * @param {Arena} perArena - Persistent FactSet arena
 * @param {number} checkpoint - Arena checkpoint before mutation
 */
function feedPers(solver, perArena, checkpoint) {
  const buf = perArena.buf;
  let added = 0;
  for (let i = checkpoint; i < perArena.cursor; i += 4) {
    if (buf[i] === INSERT_OP) {
      if (solver.addConstraint(buf[i + 2])) added++; // hash is at offset +2
    }
  }
  return added; // # recognized constraints (eq/neq) — 0 ⇒ skip checkSAT (G2)
}

/**
 * SAT-filter oplus alternatives via constraint solver.
 * Returns array of surviving alternative indices.
 *
 * @param {EqNeqSolver} solver - Constraint solver
 * @param {Object[]} alts - Consequent alternatives
 * @param {Array} theta - Substitution bindings
 * @param {Object} slots - Metavar slot mapping
 * @returns {number[]} Indices of SAT alternatives
 */
function satFilter(solver, alts, theta, slots) {
  const satAlts = [];
  for (let i = 0; i < alts.length; i++) {
    const scp = solver.checkpoint();
    for (const pattern of alts[i].persistent) {
      const h = subApplyIdx(pattern, theta, slots);
      solver.addConstraint(h);
    }
    if (solver.checkSAT()) satAlts.push(i);
    solver.restore(scp);
  }
  return satAlts;
}

export { EqNeqSolver, feedPers, satFilter };
export default { EqNeqSolver, feedPers, satFilter };

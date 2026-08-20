/**
 * Refinement sorts (TODO_0011 rung 1) — subsorts, classifiers, bounded
 * sort variables. Lovas–Pfenning-style EXTRINSIC refinements over the
 * closed-world checker: a term may inhabit many sorts, membership is a
 * judgment, checking is erased at runtime (proof irrelevance).
 *
 * Membership is semantics, tables are optimization (the FFI principle one
 * level up): subsort declarations `A <: B.` are ordinary persistent facts
 * (sedge clauses, synthesized by the loader) over the machinery predicates
 * declared in the sorts prelude logic file (leq/refl + leq/step give the
 * reflexive-transitive closure). This module compiles those clauses into
 * an ancestor-set index; `leqViaProver` is the deductive face, and the
 * fuzz suite keeps the two in agreement.
 *
 * This module carries ZERO domain knowledge: no sort name, membership, or
 * subsort edge appears here — they live in logic files (`bin <: q.` in the
 * till prelude) and in the calculus config (literal classification).
 * The only names below are the MACHINERY contract, mirrored by the sorts
 * prelude:
 *   sedge A B — a declared subsort edge      leq A B — the closure
 *   sort      — the classifier of sort names ('resource: sort.')
 *
 * Three judgments, kept distinct:
 *   s ≤ t        subsort order (leq) — reflexive-transitive edge closure,
 *                plus classifier ≤ 'type' (members of a classifier are
 *                propositions; term sorts do NOT refine 'type').
 *   n : sort     sort-hood of a NAME (isSort) — definitional, from usage.
 *   t : s        term membership — least sort (syntax-directed) + ≤,
 *                resolved by the checker (type-check.js).
 */

import Store from '../kernel/store.js';
import { _parseSignature } from './type-check.js';
import { backchain } from './backchain.js';

const SORT_PREDS = {
  EDGE: 'sedge',   // declared subsort edge (unit clauses)
  LEQ: 'leq',      // reflexive-transitive subsort order (prover face)
  SORT: 'sort',    // the meta-sort: classifier of sort names
  TYPE: 'type',    // the proposition sort ('formula' in .calc files)
};

/** Harvest ground subsort edges from sedge unit clauses. */
function _harvestEdges(clauses, errors) {
  const edges = [];
  const tid = Store.TAG[SORT_PREDS.EDGE];
  if (tid === undefined) return edges;
  for (const [name, c] of clauses) {
    if (Store.tagId(c.hash) !== tid) continue;
    if ((c.premises || []).length > 0) continue;
    const a = Store.child(c.hash, 0), b = Store.child(c.hash, 1);
    if (Store.tag(a) !== 'atom' || Store.tag(b) !== 'atom') {
      errors.push(`subsort edge '${name}': edges must be ground sort names`);
      continue;
    }
    edges.push([Store.child(a, 0), Store.child(b, 0)]);
  }
  return edges;
}

/**
 * Build the sort system from loader outputs. Returns null when the program
 * declares no sort content (presence-gated: absent, not disabled).
 *
 * @param {Object} o
 * @param {Map} o.definitions       name → signature hash (convert.load)
 * @param {Map} o.clauses           name → { hash, premises }
 * @param {Map} [o.sortVarsTable]   name → [{name, rel, sort}] bounded sort vars
 * @param {Object} [o.calc]         calculus-level sorts from the .calc spec:
 *                                  { edges: [[sub,sup]], members: {name: sort} }
 * @param {Object} [o.lit]          literal classification (calculus config):
 *                                  { literals: {tag: sort}, fences: {sort: h=>bool} }
 * @param {Object} [o.connArgSorts] connective tag → argSorts (.calc signatures)
 * @param {string} [o.formulaSort]  the .calc proposition sort name ('formula')
 * @returns {Object|null} sort system, or null when no sort content exists
 * @throws {Error} on hygiene violations (cycles, unknown sorts, bad members)
 */
function buildSortSystem({ definitions, clauses, sortVarsTable, calc, lit, connArgSorts, formulaSort }) {
  const errors = [];
  const progEdges = _harvestEdges(clauses, errors);

  // Signatures of every declared name (arrow chains and nullary members)
  const sigs = new Map();
  for (const [name, hash] of definitions) {
    const sig = _parseSignature(hash);
    if (sig) sigs.set(name, sig);
  }

  // Classifiers: `resource: sort.` — and their members `wood: resource.`
  const classifiers = new Map(); // name → Set(members)
  for (const [name, sig] of sigs) {
    if (sig.argSorts.length === 0 && sig.returnSort === SORT_PREDS.SORT) {
      classifiers.set(name, new Set());
    }
  }
  for (const [name, sig] of sigs) {
    if (!classifiers.has(sig.returnSort)) continue;
    if (sig.argSorts.length > 0) {
      errors.push(`declaration '${name}': classifier members must be atomic propositions (rung 1) — '${sig.returnSort}' member with arguments`);
      continue;
    }
    classifiers.get(sig.returnSort).add(name);
  }

  const present = progEdges.length > 0 || classifiers.size > 0 ||
    (sortVarsTable && sortVarsTable.size > 0);
  if (!present) {
    if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);
    return null;
  }

  // The machinery must come from the prelude logic file, not thin air
  if (progEdges.length > 0 && !definitions.has(SORT_PREDS.EDGE)) {
    throw new Error(`subsort declarations need the sorts prelude (declares '${SORT_PREDS.EDGE}'/'${SORT_PREDS.LEQ}') — import it (calculus/till/prelude/sorts.till)`);
  }
  if (classifiers.size > 0 && !definitions.has(SORT_PREDS.SORT)) {
    throw new Error(`classifier declarations need the sorts prelude (declares '${SORT_PREDS.SORT}') — import it (calculus/till/prelude/sorts.till)`);
  }

  // ── Universe ──
  const sorts = new Set();
  for (const c of classifiers.keys()) sorts.add(c);
  for (const [name, sig] of sigs) {
    for (const a of sig.argSorts) sorts.add(a);
    if (sig.returnSort !== SORT_PREDS.TYPE && sig.returnSort !== SORT_PREDS.SORT) {
      sorts.add(sig.returnSort);
    }
  }
  const calcEdges = (calc && calc.edges) || [];
  const calcMembers = (calc && calc.members) || {};
  for (const [a, b] of progEdges) { sorts.add(a); sorts.add(b); }
  for (const [a, b] of calcEdges) { sorts.add(a); sorts.add(b); }
  for (const s of Object.values(calcMembers)) sorts.add(s);
  if (lit && lit.literals) for (const s of Object.values(lit.literals)) sorts.add(s);

  // Program edge operands must be declared sorts (closed world). Calc
  // edges are the calculus's own spec — trusted.
  const declaredAsSort = (n) => {
    const sig = sigs.get(n);
    if (sig && sig.argSorts.length === 0 &&
        (sig.returnSort === SORT_PREDS.TYPE || sig.returnSort === SORT_PREDS.SORT)) return true;
    for (const [a, b] of calcEdges) if (n === a || n === b) return true;
    return false;
  };
  for (const [a, b] of progEdges) {
    for (const op of [a, b]) {
      if (!declaredAsSort(op)) errors.push(`subsort declaration '${a} <: ${b}': unknown sort '${op}' — declare it ('${op}: type.') first`);
    }
  }
  if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);

  // ── Closure (the compiled index over the sedge/leq clauses) ──
  const adj = new Map(); // sort → Set(direct supersorts)
  const addEdge = (a, b) => {
    if (a === b) { errors.push(`subsort cycle: '${a} <: ${a}'`); return; }
    if (!adj.has(a)) adj.set(a, new Set());
    adj.get(a).add(b);
  };
  for (const [a, b] of progEdges) addEdge(a, b);
  for (const [a, b] of calcEdges) addEdge(a, b);
  for (const c of classifiers.keys()) addEdge(c, SORT_PREDS.TYPE);

  const ancestors = new Map(); // sort → Set(sort), reflexive
  const state = new Map();     // 0 in-progress, 1 done
  function up(s) {
    if (ancestors.has(s)) return ancestors.get(s);
    if (state.get(s) === 0) {
      throw new Error(`Sort system: subsort cycle through '${s}'`);
    }
    state.set(s, 0);
    const set = new Set([s]);
    for (const t of adj.get(s) || []) {
      for (const u of up(t)) set.add(u);
    }
    state.set(s, 1);
    ancestors.set(s, set);
    return set;
  }
  for (const s of sorts) up(s);
  up(SORT_PREDS.TYPE);
  if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);

  const leq = (a, b) => a === b || (ancestors.get(a) ? ancestors.get(a).has(b) : false);

  // Least upper bound over the closed universe: unique minimal common
  // ancestor, or a structured failure for the checker's error message.
  function lub(names) {
    const list = names.filter(n => n && n !== '_');
    if (list.length === 0) return { sort: null };
    let common = null;
    for (const n of list) {
      const ups = ancestors.get(n);
      if (!ups) return { error: `'${n}' is not a sort`, candidates: [] };
      common = common === null ? new Set(ups)
        : new Set([...common].filter(x => ups.has(x)));
    }
    if (common.size === 0) return { error: 'no common supersort', candidates: list };
    const minimals = [...common].filter(c =>
      ![...common].some(d => d !== c && leq(d, c)));
    if (minimals.length === 1) return { sort: minimals[0] };
    return { error: 'ambiguous least upper bound', candidates: minimals };
  }

  /** ∃ sort t with t ≤ c for every constraint c — returns a witness or null. */
  function satisfiable(constraints) {
    const cs = [...constraints].filter(c => c !== '_');
    if (cs.length === 0) return SORT_PREDS.TYPE;
    outer: for (const t of [...sorts, SORT_PREDS.TYPE]) {
      for (const c of cs) if (!leq(t, c)) continue outer;
      return t;
    }
    return null;
  }

  // Bounded sort variables: entries are { vars, instSorts } — vars the
  // binders, instSorts the DECLARED instance signatures' sorts (loader
  // promotion, TODO_0011 §instances). One variable per signature (rung 1).
  const sortVars = sortVarsTable || new Map();
  for (const [name, entry] of sortVars) {
    if (!entry.vars || entry.vars.length !== 1) {
      errors.push(`declaration '${name}': exactly one sort variable per signature (rung 1)`);
      continue;
    }
    const v = entry.vars[0];
    if (!sorts.has(v.sort) && v.sort !== SORT_PREDS.TYPE) {
      errors.push(`declaration '${name}': sort variable bound '${v.sort}' is not a known sort`);
      continue;
    }
    for (const s of entry.instSorts || []) {
      if (!leq(s, v.sort)) {
        errors.push(`declaration '${name}': declared instance sort '${s}' is outside the bound '${v.sort}'`);
      }
    }
  }
  if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);

  const literals = (lit && lit.literals) || {};
  const fences = (lit && lit.fences) || {};

  return {
    sorts, classifiers, ancestors, edges: [...progEdges, ...calcEdges],
    leq, lub, satisfiable,
    isSort: (n) => sorts.has(n),
    membersOf: (c) => classifiers.get(c) || new Set(),
    isClassifier: (c) => classifiers.has(c),
    leastSortOfName: (n) => {
      if (Object.prototype.hasOwnProperty.call(calcMembers, n)) return calcMembers[n];
      const sig = sigs.get(n);
      return sig ? sig.returnSort : null;
    },
    sortVarsOf: (n) => (sortVars.get(n) || {}).vars || null,
    /** Sorts of DECLARED instance signatures (loader promotion). */
    instSigSortsOf: (n) => (sortVars.get(n) || {}).instSorts || [],
    sortVarPreds: () => [...sortVars.keys()],
    /** Literal classification (calculus config): store tag → least sort. */
    litSort: (tag) => Object.prototype.hasOwnProperty.call(literals, tag) ? literals[tag] : null,
    /** Value fence for literal downcasts (e.g. nonneg rationals at 'delay'). */
    fence: (sortName, h) => (typeof fences[sortName] === 'function' ? !!fences[sortName](h) : false),
    connArgSorts: connArgSorts || null,
    formulaSort: formulaSort || null,
  };
}

/**
 * Deductive face of ≤ — certificate-checked membership over the loaded
 * clause set (sorts prelude + synthesized sedge facts).
 *
 * CALC's backchainer is COMMITTED-CHOICE per subgoal (first solution only
 * — the mode discipline the numeric clause corpus is written for), so the
 * naive transitive query `leq a b` is complete only for the paths the
 * first-candidate commitment happens to walk. Instead of tabling, the
 * split follows the FFI principle: the compiled index DECIDES (it finds
 * the subsort path), the prover CERTIFIES — the reflexive base and every
 * hop of the path are proved against the leq/sedge clauses. A `true` here
 * is therefore backed end-to-end by proof search over the logic files;
 * the negative side is the index's completeness, cross-checked by
 * independent reachability enumeration in the fuzz suite.
 */
function certifyLeq(system, a, b, clauses, definitions, opts = {}) {
  const atom = (n) => Store.put('atom', [n]);
  const proveGoal = (pred, x, y) => {
    const res = backchain(Store.put(pred, [atom(x), atom(y)]), clauses, definitions,
      { maxDepth: opts.maxDepth || 64 });
    return !!(res && res.success);
  };
  if (a === b) return proveGoal(SORT_PREDS.LEQ, a, a); // leq/refl
  // BFS over the declared edges for the certificate path a → … → b
  const adj = new Map();
  for (const [x, y] of system.edges) {
    if (!adj.has(x)) adj.set(x, []);
    adj.get(x).push(y);
  }
  const prev = new Map([[a, null]]);
  const queue = [a];
  while (queue.length > 0 && !prev.has(b)) {
    const x = queue.shift();
    for (const y of adj.get(x) || []) {
      if (!prev.has(y)) { prev.set(y, x); queue.push(y); }
    }
  }
  if (!prev.has(b)) return false;
  const path = [];
  for (let n = b; prev.get(n) !== null; n = prev.get(n)) path.unshift([prev.get(n), n]);
  return path.every(([x, y]) => proveGoal(SORT_PREDS.EDGE, x, y));
}

export { buildSortSystem, certifyLeq, SORT_PREDS };
export default { buildSortSystem, certifyLeq, SORT_PREDS };

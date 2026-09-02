/**
 * Refinement sorts (TODO_0011 rung 1 + fence B) — subsorts, classifiers,
 * bounded sort variables, and DATASORTS (regular-tree subset events with
 * their automaton index, stateInfo). Lovas–Pfenning-style EXTRINSIC
 * refinements over the closed-world checker: a term may inhabit many
 * sorts, membership is a judgment, checking is erased at runtime (proof
 * irrelevance).
 *
 * Membership is semantics, tables are optimization (the FFI principle one
 * level up): subsort declarations `A <: B.` are ordinary persistent facts
 * (sedge clauses, synthesized by the loader) over the machinery predicates
 * declared in the sorts prelude logic file. The reflexive-transitive
 * closure is MATERIALIZED at load: this module compiles the ancestor-set
 * index, `closurePairs()` enumerates it, and the loader injects each pair
 * as a ground `subsort A B` fact — so in-logic subsort queries are total
 * fact lookups (no recursive closure clause, no committed-choice caveat).
 * The fuzz suite keeps table, facts, and independent reachability in
 * agreement.
 *
 * This module carries ZERO domain knowledge: no sort name, membership, or
 * subsort edge appears here — they live in logic files (`bin <: q.` in the
 * till prelude) and in the calculus config (literal classification).
 * The only names below are the MACHINERY contract, mirrored by the sorts
 * prelude:
 *   sedge A B   — a declared subsort edge     subsort A B — the closure
 *   sort        — the classifier of sort names ('resource: sort.')
 *
 * Three judgments, kept distinct:
 *   s ≤ t        subsort order — reflexive-transitive edge closure,
 *                plus classifier ≤ 'type' (members of a classifier are
 *                propositions; term sorts do NOT refine 'type').
 *   n : sort     sort-hood of a NAME (isSort) — definitional, from usage.
 *   t : s        term membership — least sort (syntax-directed) + ≤,
 *                resolved by the checker (type-check.js).
 */

import Store from '../kernel/store.js';
import { _parseSignature } from './type-check.js';

const SORT_PREDS = {
  EDGE: 'sedge',    // declared subsort edge (unit clauses)
  SUB: 'subsort',   // reflexive-transitive subsort order (materialized facts)
  SORT: 'sort',     // the meta-sort: classifier of sort names
  TYPE: 'type',     // the proposition sort ('formula' in .calc files)
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
    // Rung 2 (TODO_0297 P3): members may be term CONSTRUCTORS
    // (`cons: (a: lst) -> lst.`) — the bin-tower shape (i/o/e) at the
    // program level. Structured members make the sort RECURSIVE for the
    // wave machinery (lazy head-constructor collapse, Chi–Geman lint);
    // rule-schema expansion over such a sort is a load error (the member
    // set is an infinite term language — convert.js guards the site).
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
    throw new Error(`subsort declarations need the sorts prelude (declares '${SORT_PREDS.EDGE}'/'${SORT_PREDS.SUB}') — import your calculus's sorts prelude (e.g. prelude/sorts.till)`);
  }
  if (classifiers.size > 0 && !definitions.has(SORT_PREDS.SORT)) {
    throw new Error(`classifier declarations need the sorts prelude (declares '${SORT_PREDS.SORT}') — import your calculus's sorts prelude (e.g. prelude/sorts.till)`);
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
  // ── Datasorts (fence B slice 1, TODO_0011 round-2 spec) ──
  // An undeclared-LHS subsort declaration `warm <: tile_t.` INTRODUCES a
  // datasort: a subset of the base classifier, defined by ordinary
  // membership clauses (`warm/s: warm sea.`). The name gets a loader-
  // synthesized dual role — sort-name atom here, unary membership
  // predicate in the definitions map (index.js synthesizes the signature;
  // sound post-f7ec930a). Slice 1 fence: bases are finite atomic
  // classifiers (subset events, no fixpoint).
  const datasorts = new Map(); // name → { base, members: Set }
  for (const [a, b] of progEdges) {
    if (!declaredAsSort(a) && declaredAsSort(b)) {
      if (sigs.has(a)) {
        errors.push(`datasort declaration '${a} <: ${b}': '${a}' is already declared — a datasort introduces a NEW name`);
        continue;
      }
      if (datasorts.has(a)) {
        errors.push(`datasort '${a}' declared twice`);
        continue;
      }
      if (!classifiers.has(b)) {
        errors.push(`datasort '${a} <: ${b}': base '${b}' is not a classifier — datasorts refine classifier sorts (recursive/refinement bases are fence B2+)`);
        continue;
      }
      datasorts.set(a, { base: b, members: new Set(), trans: new Map() });
      continue;
    }
    for (const op of [a, b]) {
      if (!declaredAsSort(op)) errors.push(`subsort declaration '${a} <: ${b}': unknown sort '${op}' — declare it ('${op}: type.') first`);
    }
  }
  if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);

  // (Membership-clause harvesting runs after the closure is built —
  // premise base-compatibility needs the subsort order.)

  // ── Closure: dual representation (the compiled index over the sedge facts) ──
  // WHY TWO FORMS? The checker needs an O(1) `ancestors` map for fast
  // `subsort(a,b)` queries at type-check time. In-logic backward chaining
  // needs ground `subsort A B` FACTS (no recursive closure clause — avoids
  // committed-choice caveat). Both are derived from the same edge set and
  // kept in agreement by the fuzz suite (`closurePairs()` enumerates pairs
  // for the loader to inject as facts; `ancestors` is the compiled index).
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

  const subsort = (a, b) => a === b || (ancestors.get(a) ? ancestors.get(a).has(b) : false);

  // ── Datasort membership clauses (fences f1–f3; slice 2: constructor
  // heads with datasort premises on immediate subterm variables) ──
  // Nullary head (`warm sea.`): joins ds.members. Constructor head
  // (`even (cons H T) <- odd T.`): f1 = the head is ONE constructor
  // pattern of the base at declared arity, every argument a distinct
  // variable; f2 = premises are unary DATASORT goals on head argument
  // variables, each variable constrained at most once, the premise
  // datasort's base compatible with the argument's declared sort;
  // f3 = at most one clause per (datasort, head). The result is a
  // top-down deterministic tree automaton: ds.trans maps a constructor
  // to its child-state vector (a datasort name where a premise binds
  // the argument, the declared argument sort — ⊤ — otherwise).
  if (datasorts.size > 0) {
    const isVar = (h) => { const t = Store.tag(h); return t === 'metavar' || t === 'freevar'; };
    const checkHead = (cname, ds, dname, hash, premises) => {
      if (Store.arity(hash) !== 1) {
        errors.push(`'${cname}': datasort membership clause must be unary ('${dname} <head>')`);
        return;
      }
      const arg = Store.child(hash, 0);
      if (Store.tag(arg) === 'atom') {
        const m = Store.child(arg, 0);
        if (!classifiers.get(ds.base).has(m)) {
          errors.push(`'${cname}': '${m}' is not a member of classifier '${ds.base}'`);
          return;
        }
        if (premises.length > 0) {
          errors.push(`'${cname}': premises on a nullary-member clause (f2 — premises may only classify constructor subterm variables)`);
          return;
        }
        if (ds.members.has(m) || ds.trans.has(m)) {
          errors.push(`'${cname}': duplicate clause for ('${dname}', '${m}') — determinism fence f3 (one clause per head)`);
          return;
        }
        ds.members.add(m);
        return;
      }
      if (isVar(arg)) {
        errors.push(`'${cname}': datasort head must name a constructor or member of '${ds.base}' (f1) — a bare variable matches everything`);
        return;
      }
      // constructor pattern head
      const m = Store.tag(arg);
      if (!classifiers.get(ds.base).has(m)) {
        errors.push(`'${cname}': '${m}' is not a member of classifier '${ds.base}'`);
        return;
      }
      const sig = sigs.get(m);
      const arity = sig ? sig.argSorts.length : 0;
      if (arity === 0 || Store.arity(arg) !== arity) {
        errors.push(`'${cname}': head is not '${m}' at its declared arity ${arity} (f1)`);
        return;
      }
      const argVars = [];
      for (let i = 0; i < arity; i++) {
        const ch = Store.child(arg, i);
        if (!isVar(ch) || argVars.includes(ch)) {
          errors.push(`'${cname}': head arguments must be distinct variables (f1 — depth-one patterns only)`);
          return;
        }
        argVars.push(ch);
      }
      if (ds.members.has(m) || ds.trans.has(m)) {
        errors.push(`'${cname}': duplicate clause for ('${dname}', '${m}') — determinism fence f3 (one clause per head)`);
        return;
      }
      const childStates = sig.argSorts.slice();
      const constrained = new Set();
      for (const p of premises) {
        const ph = typeof p === 'number' ? p : p.hash !== undefined ? p.hash : p;
        const ptid = Store.tagId(ph);
        const pname = ptid >= Store.PRED_BOUNDARY ? Store.TAG_NAMES[ptid] : null;
        const pds = pname !== null ? datasorts.get(pname) : null;
        if (!pds || Store.arity(ph) !== 1) {
          errors.push(`'${cname}': premise must be a unary datasort goal on a head argument variable (f2)`);
          return;
        }
        const pv = Store.child(ph, 0);
        const vi = argVars.indexOf(pv);
        if (vi < 0) {
          errors.push(`'${cname}': premise '${pname}' constrains a variable that is not a head argument (f2)`);
          return;
        }
        if (constrained.has(vi)) {
          errors.push(`'${cname}': head argument constrained twice (f2 — one datasort per subterm)`);
          return;
        }
        if (pds.base !== sig.argSorts[vi] && !subsort(sig.argSorts[vi], pds.base)) {
          errors.push(`'${cname}': premise '${pname}' refines '${pds.base}' but the argument's sort is '${sig.argSorts[vi]}'`);
          return;
        }
        constrained.add(vi);
        childStates[vi] = pname;
      }
      ds.trans.set(m, childStates);
    };
    const dsOf = (hash) => {
      const tid = Store.tagId(hash);
      if (tid < Store.PRED_BOUNDARY) return null;
      const dname = Store.TAG_NAMES[tid];
      const ds = datasorts.get(dname);
      return ds ? { ds, dname } : null;
    };
    // Premise-free membership facts live in the DEFINITIONS map (like any
    // premise-free axiom); conditional clauses live in the clauses map.
    for (const [cname, hash] of definitions) {
      if (typeof hash !== 'number') continue;
      const hit = dsOf(hash);
      if (hit) checkHead(cname, hit.ds, hit.dname, hash, []);
    }
    for (const [cname, c] of clauses) {
      const hit = dsOf(c.hash);
      if (hit) checkHead(cname, hit.ds, hit.dname, c.hash, c.premises || []);
    }
    for (const [name, ds] of datasorts) {
      if (ds.members.size === 0 && ds.trans.size === 0) {
        errors.push(`datasort '${name}' has no membership clauses — an empty event is a load error (define members: '${name}/x: ${name} <head>.')`);
      }
    }
    if (errors.length === 0) {
      // Emptiness (least fixpoint): a datasort is inhabited iff some head
      // is a nullary member, or a constructor all of whose datasort child
      // states are inhabited (⊤ child states are inhabited — classifiers
      // have members). A declared-but-empty language is a load error.
      const inhabited = new Set();
      let grew = true;
      while (grew) {
        grew = false;
        for (const [name, ds] of datasorts) {
          if (inhabited.has(name)) continue;
          let ok = ds.members.size > 0;
          if (!ok) {
            for (const states of ds.trans.values()) {
              if (states.every((s) => !datasorts.has(s) || inhabited.has(s))) { ok = true; break; }
            }
          }
          if (ok) { inhabited.add(name); grew = true; }
        }
      }
      for (const name of datasorts.keys()) {
        if (!inhabited.has(name)) {
          errors.push(`datasort '${name}' denotes the empty language — every constructor clause recurses without a base case`);
        }
      }
    }
  }
  if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);

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
      ![...common].some(d => d !== c && subsort(d, c)));
    if (minimals.length === 1) return { sort: minimals[0] };
    return { error: 'ambiguous least upper bound', candidates: minimals };
  }

  /** ∃ sort t with t ≤ c for every constraint c — returns a witness or null. */
  function satisfiable(constraints) {
    const cs = [...constraints].filter(c => c !== '_');
    if (cs.length === 0) return SORT_PREDS.TYPE;
    outer: for (const t of [...sorts, SORT_PREDS.TYPE]) {
      for (const c of cs) if (!subsort(t, c)) continue outer;
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
      if (!subsort(s, v.sort)) {
        errors.push(`declaration '${name}': declared instance sort '${s}' is outside the bound '${v.sort}'`);
      }
    }
  }
  if (errors.length > 0) throw new Error(`Sort system: ${errors.join('; ')}`);

  const literals = (lit && lit.literals) || {};
  const fences = (lit && lit.fences) || {};

  return {
    sorts, classifiers, ancestors, edges: [...progEdges, ...calcEdges],
    subsort, lub, satisfiable,
    /**
     * The materialized closure: every strict pair a < b over declared +
     * calc edges. The loader injects each as a ground `subsort a b` fact;
     * with `subsort/refl` that makes in-logic subsort queries total.
     * Classifier ≤ 'type' pairs are EXCLUDED — 'type' is not an atom;
     * that judgment stays definitional (as today).
     */
    closurePairs: () => {
      const pairs = [];
      for (const [a, ups] of ancestors) {
        if (a === SORT_PREDS.TYPE) continue;
        for (const b of ups) {
          if (b === a || b === SORT_PREDS.TYPE) continue;
          pairs.push([a, b]);
        }
      }
      return pairs;
    },
    isSort: (n) => sorts.has(n),
    membersOf: (c) => classifiers.get(c) || new Set(),
    isClassifier: (c) => classifiers.has(c),
    datasorts,
    isDatasort: (n) => datasorts.has(n),
    datasortInfo: (n) => datasorts.get(n) || null,
    /**
     * Uniform state resolver (slice 3): a state is a declared datasort
     * name or a canonical PRODUCT key `d1&d2&…` (sorted, '&'-joined —
     * identifiers cannot contain '&'). Products are the ANONYMOUS
     * intersections of Q2: heads admitted by every component, child
     * states the componentwise intersection (⊤ components drop out;
     * singletons collapse to plain names). Intersection MEMBERSHIP
     * needs no resolver — proving both goals is the intersection; this
     * is only the mass/draw index. Returns null for classifiers and
     * unknown names. Cached; deterministic from the declared datasorts,
     * so a checker can rebuild the same products independently.
     */
    stateInfo: (() => {
      const cache = new Map();
      const canon = (names) => [...new Set(names)].sort().join('&');
      const resolve = (key) => {
        if (datasorts.has(key)) return datasorts.get(key);
        if (!key.includes('&')) return null;
        const hit = cache.get(key);
        if (hit !== undefined) return hit;
        const names = key.split('&');
        const infos = names.map((n) => datasorts.get(n));
        if (infos.some((i) => !i)) { cache.set(key, null); return null; }
        const base = infos[0].base;
        if (infos.some((i) => i.base !== base)) { cache.set(key, null); return null; }
        const members = new Set(
          [...infos[0].members].filter((m) => infos.every((i) => i.members.has(m))));
        const trans = new Map();
        for (const c of infos[0].trans.keys()) {
          if (!infos.every((i) => i.trans.has(c))) continue;
          const vecs = infos.map((i) => i.trans.get(c));
          const cs = [];
          for (let j = 0; j < vecs[0].length; j++) {
            const parts = new Set();
            let top = null;
            for (const v of vecs) {
              const s = v[j];
              if (s.includes('&')) for (const p of s.split('&')) parts.add(p);
              else if (datasorts.has(s)) parts.add(s);
              else top = s;
            }
            cs.push(parts.size === 0 ? top : canon([...parts]));
          }
          trans.set(c, cs);
        }
        const info = { base, members, trans, product: true };
        cache.set(key, info);
        return info;
      };
      resolve.canon = canon;
      return resolve;
    })(),
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

export { buildSortSystem, SORT_PREDS };
export default { buildSortSystem, SORT_PREDS };

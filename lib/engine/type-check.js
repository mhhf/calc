/**
 * Sort Checking for CALC — load-time verification of arity/sort consistency.
 *
 * Builds a sort table from LF-style type declarations (arrow signatures),
 * then checks forward rules and backward clauses against it.
 * Zero runtime cost — all work happens at _buildCalc() time.
 *
 * Two modes, one code path (TODO_0011 rung 1):
 *   SORTLESS (cx.sorts == null) — string-equality sorts, the closed-world
 *     checker ILL runs. Bit-identical to the pre-rung-1 behavior.
 *   SORTED (cx.sorts = a sort system from lib/engine/sorts.js) — sort
 *     equality relaxes to subsumption ≤ (subsorts, classifiers ≤ 'type'),
 *     metavars collect constraint SETS (satisfiability: ∃ sort below all
 *     upper bounds), literals classify via the calculus config with value
 *     fences for downcasts, connective children check against the .calc
 *     signature sorts, and bounded-sort-variable signatures solve
 *     s := lub(argument least sorts) and require an instance at s.
 *
 * Design: SortEntry = { argSorts: string[], returnSort: string }
 * Extension path: rung 2 (GADT indexed families) refines argSorts from
 * strings to constructor-term indices.
 */

import Store from '../kernel/store.js';
import { SORT_PREDS } from './sorts.js';

// ─── Sort Table Construction ─────────────────────────────────────────────────

/**
 * Extract sort name from a hash.
 * tag='type' → 'type', tag='atom' → atom name, else null.
 */
function _extractSortName(h) {
  const t = Store.tag(h);
  if (t === 'type') return 'type';
  if (t === 'atom') return Store.child(h, 0);
  return null;
}

/**
 * Parse an arrow-chain hash into a sort signature.
 * arrow(atom('bin'), arrow(atom('bin'), type())) → { argSorts: ['bin','bin'], returnSort: 'type' }
 * Returns null for non-signature hashes (axioms, predicate applications).
 */
function _parseSignature(h) {
  const argSorts = [];
  let current = h;
  while (Store.tag(current) === 'arrow') {
    const left = Store.child(current, 0);
    const sortName = _extractSortName(left);
    if (sortName === null) return null;
    argSorts.push(sortName);
    current = Store.child(current, 1);
  }
  const returnSort = _extractSortName(current);
  if (returnSort === null) return null;
  return { argSorts, returnSort };
}

/**
 * Build sort table from definitions Map.
 * Iterates definitions, parses arrow signatures, skips axioms.
 * @param {Map<string, number>} definitions - name → hash from convert.load()
 * @param {Map<string, string[]>} [argNamesTable] - name → arg names (optional)
 * @returns {Map<string, {argSorts: string[], returnSort: string, argNames?: (string|null)[]}>}
 */
function sortTable(definitions, argNamesTable) {
  const table = new Map();
  for (const [name, hash] of definitions) {
    const sig = _parseSignature(hash);
    if (sig) {
      if (argNamesTable && argNamesTable.has(name)) {
        sig.argNames = argNamesTable.get(name);
      }
      table.set(name, sig);
    }
  }
  return table;
}

// ─── Checking Context ────────────────────────────────────────────────────────

// Default context: sortless, open world — the behavior of the bare exported
// helpers (_checkTerm etc.) when called without a context.
const _LEGACY_CX = Object.freeze({ closedWorld: false, sorts: null, instances: null });

/** Signature rendering for error messages. */
function _sigString(entry) {
  return entry.argNames
    ? entry.argSorts.map((s, i) => entry.argNames[i] ? `${entry.argNames[i]}: ${s}` : s).join(', ')
    : entry.argSorts.join(', ');
}

/**
 * actual ≤ expected — string equality in sortless mode, subsumption under
 * a sort system. '_' is unconstrained on either side.
 */
function _sortOk(actual, expected, cx) {
  if (expected === '_' || actual === '_') return true;
  if (actual === expected) return true;
  return cx.sorts ? cx.sorts.leq(actual, expected) : false;
}

/** Record a metavar constraint (sorted: a Set of upper bounds). */
function _recordMetavar(h, expectedSort, metavarSorts, errors, path, cx) {
  if (cx.sorts) {
    let set = metavarSorts.get(h);
    if (!(set instanceof Set)) { set = new Set(); metavarSorts.set(h, set); }
    if (expectedSort !== '_') set.add(expectedSort);
    return;
  }
  if (expectedSort === '_') return;
  const existing = metavarSorts.get(h);
  if (existing === undefined) {
    metavarSorts.set(h, expectedSort);
  } else if (existing !== '_' && existing !== expectedSort) {
    const name = Store.child(h, 0);
    errors.push(`${path}: metavar ${name} used as '${existing}' and '${expectedSort}'`);
  }
}

/** Sorted mode: verify every metavar's constraint set is inhabitable. */
function _checkMetavarSatisfiability(metavarSorts, errors, path, cx) {
  if (!cx.sorts) return;
  for (const [h, set] of metavarSorts) {
    if (!(set instanceof Set) || set.size < 2) continue;
    if (cx.sorts.satisfiable(set) === null) {
      const name = Store.child(h, 0);
      errors.push(`${path}: metavar ${name} used at incompatible sorts {${[...set].join(', ')}} — no sort lies below all of them`);
    }
  }
}

/**
 * Least sort of a determinable term (sorted mode) — null when the term's
 * sort cannot be read off syntactically (metavars, unknown symbols,
 * nested bounded-variable applications).
 */
function _leastSort(h, sortTable, cx) {
  const t = Store.tag(h);
  if (!t) return null;
  if (t === 'freevar' || t === 'metavar') return null;
  const byLit = cx.sorts.litSort(t);
  if (byLit !== null) return byLit;
  let name = null;
  if (t === 'atom') name = Store.child(h, 0);
  else {
    const tid = Store.tagId(h);
    if (tid >= Store.PRED_BOUNDARY) name = Store.TAG_NAMES[tid];
  }
  if (name === null) return null;
  const entry = sortTable.get(name);
  if (!entry) return null;
  if (cx.sorts.sortVarsOf(name)) return null; // bounded-var result: not syntax-determinable
  return entry.returnSort;
}

// ─── Term Checking ───────────────────────────────────────────────────────────

/**
 * Check a term against an expected sort. Recurses into children.
 * Collects errors into `errors` array; does not throw.
 *
 * @param {number} h - term hash
 * @param {string} expectedSort - expected sort ('_' = unconstrained)
 * @param {Map} sortTable
 * @param {Map} metavarSorts - freevar hash → recorded sort/constraints (mutated)
 * @param {Array} errors - collected error strings (mutated)
 * @param {string} path - context for error messages (e.g. "rule 'evm/add'")
 * @param {Object} [cx] - checking context { closedWorld, sorts, instances }
 */
function _checkTerm(h, expectedSort, sortTable, metavarSorts, errors, path, cx = _LEGACY_CX) {
  const t = Store.tag(h);
  if (!t) return;

  const tid = Store.tagId(h);

  // Freevar/metavar: record or check sort consistency
  if (t === 'freevar' || t === 'metavar') {
    _recordMetavar(h, expectedSort, metavarSorts, errors, path, cx);
    return;
  }

  // Literals. Sorted mode: classify via the calculus config; a literal at
  // a refinement sort its least sort does not reach passes iff the config's
  // VALUE FENCE for that sort admits it (nonneg rationals at 'delay',
  // integers at 'count', [0,1] at 'weight') — the decidable shadow of
  // value-dependent membership (rung-2 territory).
  if (t === 'binlit' || t === 'ratlit' || t === 'strlit') {
    const legacySort = t === 'strlit' ? 'string' : 'bin';
    if (cx.sorts) {
      const ls = cx.sorts.litSort(t) ?? legacySort;
      if (_sortOk(ls, expectedSort, cx)) return;
      if (cx.sorts.fence(expectedSort, h)) return;
      errors.push(`${path}: expected sort '${expectedSort}', got '${ls}' (${t === 'strlit' ? 'string' : t === 'ratlit' ? 'rational' : 'binary'} literal)`);
      return;
    }
    if (expectedSort !== '_' && expectedSort !== legacySort) {
      errors.push(`${path}: expected sort '${expectedSort}', got '${legacySort}' (${t === 'strlit' ? 'string' : t === 'ratlit' ? 'rational' : 'binary'} literal)`);
    }
    return;
  }

  // Atom (nullary constructor)
  if (t === 'atom') {
    const name = Store.child(h, 0);
    const entry = sortTable.get(name);
    if (!entry) {
      // Calculus-level sort names (grade sorts from the .calc) have no .ill
      // declaration but ARE terms of the meta-sort — sedge facts mention them.
      if (cx.sorts && cx.sorts.isSort(name)) {
        if (expectedSort !== '_' && expectedSort !== SORT_PREDS.SORT) {
          errors.push(`${path}: expected sort '${expectedSort}', got the sort name '${name}'`);
        }
        return;
      }
      if (cx.closedWorld) {
        errors.push(`${path}: unknown atom '${name}' — undeclared (closed world): declare it ('${name}: type.' for a token) or fix the typo`);
      }
      return; // open world: not in sort table, skip
    }
    if (entry.argSorts.length !== 0) {
      errors.push(`${path}: '${name}' expects ${entry.argSorts.length} args (${_sigString(entry)}), got 0`);
      return;
    }
    if (expectedSort !== '_') {
      const ok = _sortOk(entry.returnSort, expectedSort, cx) ||
        (cx.sorts && expectedSort === SORT_PREDS.SORT && cx.sorts.isSort(name));
      if (!ok) {
        errors.push(`${path}: expected sort '${expectedSort}', got '${entry.returnSort}' for '${name}'`);
      }
    }
    return;
  }

  // Connective / structural tag (< PRED_BOUNDARY, not atom/freevar/binlit)
  if (tid < Store.PRED_BOUNDARY) {
    const a = Store.arity(h);
    // Sorted mode: the .calc connective signature supplies per-child sorts
    // (grade holes get their declared sort — 'delay' on the monad, 'count'
    // on the bang); the calculus's proposition sort maps to 'type'.
    const connSorts = cx.sorts && cx.sorts.connArgSorts ? cx.sorts.connArgSorts[t] : null;
    if (connSorts && connSorts.length === a) {
      for (let i = 0; i < a; i++) {
        const ch = Store.child(h, i);
        if (typeof ch === 'number' && Store.isTerm(ch)) {
          const s = connSorts[i] === cx.sorts.formulaSort ? 'type' : connSorts[i];
          _checkTerm(ch, s, sortTable, metavarSorts, errors, path, cx);
        }
      }
      return;
    }
    // Grade positions (bang/monad child 0) live in the GRADE algebra
    // (D2/D4), not the term sorts — but they have their own closed
    // grammar: counts (binlit), delays (ratlit), rule variables, and the
    // internal g0/gw markers. Anything else is a malformed grade.
    const start = (t === 'bang' || t === 'monad') ? 1 : 0;
    if (start === 1) {
      const g = Store.child(h, 0);
      const gt = Store.tag(g);
      const gradeOk = gt === 'binlit' || gt === 'ratlit' ||
        gt === 'metavar' || gt === 'freevar' ||
        (gt === 'atom' && (Store.child(g, 0) === 'g0' || Store.child(g, 0) === 'gw'));
      if (!gradeOk && cx.closedWorld) {
        errors.push(`${path}: invalid grade '${gt === 'atom' ? Store.child(g, 0) : gt}' on ${t} — grades are counts (integers), delays (rationals), rule variables, or the g0/gw markers (D2/D4)`);
      }
    }
    for (let i = start; i < a; i++) {
      const ch = Store.child(h, i);
      if (typeof ch === 'number' && Store.isTerm(ch)) {
        _checkTerm(ch, '_', sortTable, metavarSorts, errors, path, cx);
      }
    }
    return;
  }

  // Predicate tag (>= PRED_BOUNDARY)
  const predName = Store.TAG_NAMES[tid];
  const entry = sortTable.get(predName);
  if (!entry) {
    if (cx.closedWorld) {
      errors.push(`${path}: unknown predicate '${predName}' — undeclared (closed world)`);
      // still check the children against '_' so their atoms are validated
      const ar = Store.arity(h);
      for (let i = 0; i < ar; i++) {
        const ch = Store.child(h, i);
        if (typeof ch === 'number' && Store.isTerm(ch)) {
          _checkTerm(ch, '_', sortTable, metavarSorts, errors, path, cx);
        }
      }
    }
    return; // open world: not in sort table, skip
  }

  const a = Store.arity(h);
  if (a !== entry.argSorts.length) {
    errors.push(`${path}: '${predName}' expects ${entry.argSorts.length} args (${_sigString(entry)}), got ${a}`);
    return;
  }

  if (expectedSort !== '_' && !_sortOk(entry.returnSort, expectedSort, cx)) {
    errors.push(`${path}: expected sort '${expectedSort}', got '${entry.returnSort}' for '${predName}'`);
  }

  // Bounded sort variable signature (sorted mode): solve the variable as
  // the lub of the determinable argument sorts, require an instance at the
  // solution, and check every variable position against the solution —
  // result metavars refine downstream (sub a b D ⇒ D ≤ bin).
  const sortVars = cx.sorts ? cx.sorts.sortVarsOf(predName) : null;
  if (sortVars) {
    _checkBoundedApplication(h, predName, entry, sortVars[0], sortTable, metavarSorts, errors, path, cx);
    return;
  }

  for (let i = 0; i < a; i++) {
    const ch = Store.child(h, i);
    if (typeof ch === 'number' && Store.isTerm(ch)) {
      _checkTerm(ch, entry.argSorts[i], sortTable, metavarSorts, errors, path, cx);
    }
  }
}

/** Application of a bounded-sort-variable predicate (see _checkTerm). */
function _checkBoundedApplication(h, predName, entry, svar, sortTable, metavarSorts, errors, path, cx) {
  const a = Store.arity(h);
  const varPositions = [];
  const determined = [];
  for (let i = 0; i < a; i++) {
    if (entry.argSorts[i] !== svar.name) continue;
    varPositions.push(i);
    const ch = Store.child(h, i);
    if (typeof ch === 'number' && Store.isTerm(ch)) {
      const ls = _leastSort(ch, sortTable, cx);
      if (ls !== null) determined.push(ls);
    }
  }

  let solved;
  if (determined.length === 0) {
    solved = svar.sort; // nothing determinable: any instance may apply at runtime
  } else {
    const r = cx.sorts.lub(determined);
    if (r.error) {
      errors.push(`${path}: '${predName}' arguments have ${r.error} (${determined.join(', ')}) under bound '${svar.sort}'`);
      return;
    }
    solved = r.sort;
  }
  if (!cx.sorts.leq(solved, svar.sort)) {
    errors.push(`${path}: '${predName}' solves its sort variable to '${solved}', outside the bound '${svar.sort}'`);
    return;
  }

  const instances = (cx.instances && cx.instances.get(predName)) || new Set();
  let hasInstance = false;
  for (const inst of instances) {
    if (cx.sorts.leq(solved, inst)) { hasInstance = true; break; }
  }
  if (!hasInstance) {
    errors.push(`${path}: '${predName}' has no instance at '${solved}' (instances: {${[...instances].join(', ') || 'none'}}) — coerce the mixed argument explicitly, or declare an instance at '${solved}'`);
    return;
  }

  for (let i = 0; i < a; i++) {
    const ch = Store.child(h, i);
    if (typeof ch === 'number' && Store.isTerm(ch)) {
      const s = entry.argSorts[i] === svar.name ? solved : entry.argSorts[i];
      _checkTerm(ch, s, sortTable, metavarSorts, errors, path, cx);
    }
  }
}

/**
 * Infer the instance sorts of bounded-sort-variable predicates from their
 * clause heads: a head patterning on constructors classifies at the lub of
 * the pattern sorts; a head of bare variables is an instance at the bound.
 * @returns {Map<string, Set<string>>} predicate → instance sorts
 */
function _buildInstances(clauses, sorts, cx) {
  const instances = new Map();
  if (!cx.sorts || !clauses) return instances;
  for (const [cname, clause] of clauses) {
    const tid = Store.tagId(clause.hash);
    if (tid < Store.PRED_BOUNDARY) continue;
    const predName = Store.TAG_NAMES[tid];
    const svars = cx.sorts.sortVarsOf(predName);
    if (!svars) continue;
    const entry = sorts.get(predName);
    if (!entry || entry.argSorts.length !== Store.arity(clause.hash)) continue;
    const svar = svars[0];
    const determined = [];
    for (let i = 0; i < entry.argSorts.length; i++) {
      if (entry.argSorts[i] !== svar.name) continue;
      const ch = Store.child(clause.hash, i);
      if (typeof ch === 'number' && Store.isTerm(ch)) {
        const ls = _leastSort(ch, sorts, cx);
        if (ls !== null) determined.push(ls);
      }
    }
    let inst;
    if (determined.length === 0) {
      inst = svar.sort;
    } else {
      const r = cx.sorts.lub(determined);
      if (r.error) continue; // head itself ill-sorted — clause checking reports it
      inst = r.sort;
    }
    if (!instances.has(predName)) instances.set(predName, new Set());
    instances.get(predName).add(inst);
  }
  return instances;
}

// ─── Rule & Clause Checking ─────────────────────────────────────────────────

/**
 * Check a compiled forward rule against the sort table.
 * @param {Object} rule - compiled rule from compile.js
 * @param {Map} sortTable
 * @param {Object} [cx] - checking context
 * @returns {string[]} error messages (empty = OK)
 */
function checkForwardRule(rule, sortTable, cx = _LEGACY_CX) {
  const errors = [];
  const metavarSorts = new Map();
  const path = `rule '${rule.name}'`;

  for (const h of (rule.antecedent.linear || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path, cx);
  for (const h of (rule.antecedent.persistent || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path, cx);
  for (const h of (rule.consequent.linear || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path, cx);
  for (const h of (rule.consequent.persistent || []))
    _checkTerm(h, 'type', sortTable, metavarSorts, errors, path, cx);

  // Also check alternative consequents (oplus branches)
  if (rule.consequentAlts) {
    for (const alt of rule.consequentAlts.slice(1)) {
      for (const h of (alt.linear || []))
        _checkTerm(h, 'type', sortTable, metavarSorts, errors, path, cx);
      for (const h of (alt.persistent || []))
        _checkTerm(h, 'type', sortTable, metavarSorts, errors, path, cx);
    }
  }

  _checkMetavarSatisfiability(metavarSorts, errors, path, cx);
  return errors;
}

/**
 * Check a backward clause against the sort table.
 * @param {string} name - clause name
 * @param {Object} clause - { hash, premises }
 * @param {Map} sortTable
 * @param {Object} [cx] - checking context
 * @returns {string[]} error messages (empty = OK)
 */
function checkClause(name, clause, sortTable, cx = _LEGACY_CX) {
  const errors = [];
  const metavarSorts = new Map();
  const path = `clause '${name}'`;

  _checkTerm(clause.hash, 'type', sortTable, metavarSorts, errors, path, cx);
  for (const p of clause.premises)
    _checkTerm(p, 'type', sortTable, metavarSorts, errors, path, cx);

  _checkMetavarSatisfiability(metavarSorts, errors, path, cx);
  return errors;
}

// ─── Top-Level Orchestrator ──────────────────────────────────────────────────

/**
 * Check all declarations, forward rules, and clauses.
 * @param {Map} definitions - name → hash
 * @param {Object[]} compiledRules - compiled forward rules
 * @param {Map} clauses - name → { hash, premises }
 * @param {Object} [opts]
 * @param {boolean} [opts.strict] - throw on errors
 * @param {boolean} [opts.closedWorld] - undeclared symbols are errors
 * @param {Object} [opts.sorts] - sort system (lib/engine/sorts.js) or null
 * @returns {{ errors: string[], warnings: string[] }}
 */
function checkAll(definitions, compiledRules, clauses, opts = {}) {
  const sorts = sortTable(definitions, opts.argNamesTable);
  const errors = [];
  const warnings = [];
  const cx = {
    closedWorld: !!opts.closedWorld,
    sorts: opts.sorts || null,
    instances: null,
  };
  if (cx.sorts) cx.instances = _buildInstances(clauses, sorts, cx);

  if (cx.closedWorld) {
    // Signature hygiene: every argument sort must itself exist, and 'type'
    // is BANNED as an argument sort — that would be quantification over
    // propositions, which the theory does not support (LF forbids it; the
    // honest form is a CLASSIFIER — a declared finite class, rung 1).
    const BUILTIN = new Set(['bin', 'string']);
    for (const [name, sig] of sorts) {
      const svarNames = cx.sorts && cx.sorts.sortVarsOf(name)
        ? new Set(cx.sorts.sortVarsOf(name).map(v => v.name)) : null;
      for (const a of sig.argSorts) {
        if (a === 'type') {
          errors.push(`declaration '${name}': argument sort 'type' — quantification over propositions is not supported (declare a classifier: 'c: ${SORT_PREDS.SORT}.' and quantify over that)`);
        } else if (svarNames && svarNames.has(a)) {
          // bounded sort variable — bound validated by the sort system
        } else if (cx.sorts ? !cx.sorts.isSort(a) && !BUILTIN.has(a)
                            : !BUILTIN.has(a) && !sorts.has(a)) {
          errors.push(`declaration '${name}': unknown sort '${a}'`);
        }
      }
    }
  }

  for (const rule of compiledRules) {
    errors.push(...checkForwardRule(rule, sorts, cx));
  }

  for (const [name, clause] of clauses) {
    errors.push(...checkClause(name, clause, sorts, cx));
  }

  // Directives (#expect gates): their formulas are states/patterns — the
  // same closed world applies, or a typo'd token in a GATE self-introduces
  // and the gate silently tests the wrong thing.
  if (opts.queries) {
    for (const [name, q] of opts.queries) {
      const metavarSorts = new Map();
      for (const h of [q.lhsHash, q.rhsHash]) {
        if (typeof h === 'number') {
          _checkTerm(h, 'type', sorts, metavarSorts, errors, `directive '${name}'`, cx);
        }
      }
      _checkMetavarSatisfiability(metavarSorts, errors, `directive '${name}'`, cx);
    }
  }

  if (opts.strict && errors.length > 0) {
    throw new Error(`Sort checking failed (${errors.length} error(s)):\n  ${errors.join('\n  ')}`);
  }

  return { errors, warnings };
}

// ─── Legacy helper (kept for API compatibility) ─────────────────────────────

/**
 * Infer the sort of a term hash.
 * @param {number} h - term hash
 * @param {Map} sortTable
 * @param {Map} metavarSorts - freevar hash → sort
 * @returns {string} sort name or '_' (unknown)
 */
function inferSort(h, sortTable, metavarSorts) {
  const t = Store.tag(h);
  if (!t) return '_';

  if (t === 'freevar' || t === 'metavar') {
    const s = metavarSorts.get(h);
    return (typeof s === 'string' && s) || '_';
  }
  if (t === 'binlit') return 'bin';
  if (t === 'atom') {
    const name = Store.child(h, 0);
    const entry = sortTable.get(name);
    return entry ? entry.returnSort : '_';
  }

  const tid = Store.tagId(h);
  if (tid >= Store.PRED_BOUNDARY) {
    const predName = Store.TAG_NAMES[tid];
    const entry = sortTable.get(predName);
    return entry ? entry.returnSort : '_';
  }

  return '_'; // connective or unknown
}

export { _parseSignature, sortTable, inferSort, _checkTerm, checkForwardRule, checkClause, checkAll };
export default { _parseSignature, sortTable, inferSort, _checkTerm, checkForwardRule, checkClause, checkAll };

/**
 * Load-time clause materialization — extracted verbatim from _buildCalc
 * (index.js; audit 2026-09-02 readability split, zero semantic change).
 *
 * Builds the refinement-sort system and applies the three intra-logical
 * "facts are semantics" riders, each presence-gated on the PROGRAM
 * declaring the predicate:
 *   - subsort closure  → ground `subsort a b` facts   (TODO_0011 §4)
 *   - datasort masses  → ground `mass s m` facts      (fence B slice 3)
 *   - constructor priors → ground `prior s c ρ` facts (TODO_0298 item 1b)
 */

'use strict';

import Store from '../kernel/store.js';
import { buildSortSystem, SORT_PREDS } from './sorts.js';
import { checkPriors } from './priors.js';
import { putRat } from '../kernel/rat-term.js';

/**
 * @returns {{ sortSystem, priorAdvice, stateMasses }}
 */
function materializeLoadTimeClauses({ cc, definitions, clauses, sortVarsTable,
  priorsTable, phaseStart, phaseEnd }) {
  // Refinement-sort system (TODO_0011 rung 1) — presence-gated twice:
  // the CALCULUS opts in via cc.sorts (till), and the PROGRAM opts in by
  // declaring sort content (subsorts/classifiers/sort variables). Absent
  // on either side ⇒ the sortless string checker, bit-identical to before.
  const _tSorts = phaseStart();
  let sortSystem = null;
  if (cc.sorts) {
    sortSystem = buildSortSystem({
      definitions, clauses, sortVarsTable,
      calc: cc.sorts.calc, lit: cc.sorts.lit,
      connArgSorts: cc.sorts.connArgSorts, formulaSort: cc.sorts.formulaSort,
    });
  } else if (Store.TAG[SORT_PREDS.EDGE] !== undefined) {
    for (const [cname, c] of clauses) {
      if (Store.tagId(c.hash) === Store.TAG[SORT_PREDS.EDGE]) {
        throw new Error(`'${cname}': subsort declarations need a calculus with a sorts config (cc.sorts) — this calculus is sortless`);
      }
    }
  }
  // Datasorts (fence B slice 1): synthesize the membership-predicate
  // signature for each datasort name — `warm: (x: tile_t) -> type` — so
  // the membership clauses type-check (closed world) and backward goals
  // `!warm T` resolve like any predicate. The name's OTHER role (sort
  // atom in subsort/within facts) is covered by the checker's sort-name
  // reading; the dual role is loader-synthesized, never user-written.
  if (sortSystem && sortSystem.datasorts && sortSystem.datasorts.size > 0) {
    for (const [dname, info] of sortSystem.datasorts) {
      if (!definitions.has(dname)) {
        definitions.set(dname, Store.put('arrow',
          [Store.put('atom', [info.base]), Store.put('type', [])]));
      }
    }
  }
  // Materialized closure (TODO_0011 §4): inject every strict subsort pair
  // as a ground `subsort a b` fact. With `subsort/refl` in the prelude,
  // in-logic queries (`!subsort X resource` premises) are answered totally
  // by fact lookup — the committed-choice completeness caveat of a
  // recursive closure clause is gone, not worked around. Runs BEFORE
  // checkAll (facts get sort-checked like sedge facts) and before
  // buildIndex (queries see them); idempotent on cache-restore re-entry
  // (same names, same content-addressed hashes).
  if (sortSystem && definitions.has(SORT_PREDS.SUB)) {
    for (const [a, b] of sortSystem.closurePairs()) {
      // Separator is `/` (not `_`): sort names can't contain `/`, so the key
      // is collision-free even for underscore-named sorts — `(foo, bar_x)` and
      // `(foo_bar, x)` would both key to `subsort/foo_bar_x` under `_`, silently
      // dropping one materialized closure fact.
      clauses.set(`${SORT_PREDS.SUB}/${a}/${b}`, {
        hash: Store.put(SORT_PREDS.SUB,
          [Store.put('atom', [a]), Store.put('atom', [b])]),
        premises: [],
      });
    }
  }
  phaseEnd('load/sort-system', _tSorts, {
    present: !!sortSystem,
    sorts: sortSystem ? sortSystem.sorts.size : 0,
    edges: sortSystem ? sortSystem.edges.length : 0,
    classifiers: sortSystem ? sortSystem.classifiers.size : 0,
  });

  // Constructor priors `name: sort @w Q.` (TODO_0292 D5/M6, will P1):
  // validated against the sort system; Chi–Geman subcriticality (T2) is
  // a load-time ADVISORY (M7 — the decimation driver, not the loader,
  // hard-errors on supercritical priors without a depth bound).
  let priorAdvice = [];
  if (priorsTable.size > 0) {
    const pr = checkPriors(priorsTable, sortSystem, definitions);
    if (pr.errors.length > 0) {
      throw new Error(`Priors: ${pr.errors.join('; ')}`);
    }
    priorAdvice = pr.advice;
    for (const a of priorAdvice) {
      console.warn(`priors lint (T2): sort '${a.sort}' is supercritical (m = ${a.m.toFixed(3)} > 1) — lazy collapse over it diverges with positive probability (Chi–Geman); rebalance @w or pass the driver an explicit depth bound`);
    }
  }
  // Inside masses (fence B slices 2+3): recursive datasorts need exact
  // state masses for the conditioned sampler — solved at load (f4
  // linearity + divergence are load errors), null when no structured
  // datasort exists. The solver is CALCULUS-BOUND oracle machinery
  // (cc.datasortMasses — will's config binds calculus/will/lib/datasort-mass.js);
  // the core knows only this interface.
  let stateMasses = null;
  if (sortSystem && sortSystem.datasorts && sortSystem.datasorts.size > 0) {
    const structured = [...sortSystem.datasorts.values()].some((d) => d.trans.size > 0);
    if (structured && !cc.datasortMasses) {
      throw new Error(`recursive datasorts need an inside-mass solver — this calculus binds none (cc.datasortMasses)`);
    }
    const mr = cc.datasortMasses
      ? cc.datasortMasses.solveMasses(sortSystem, priorsTable, definitions)
      : { masses: null, errors: [] };
    if (mr.errors.length > 0) throw new Error(`Datasort masses: ${mr.errors.join('; ')}`);
    stateMasses = mr.masses;
    // Materialized masses (the intra-logical rider, slice 3): mirror the
    // subsort/prior discipline — when the PROGRAM declares the `mass`
    // predicate, every load-time state mass becomes a ground `mass s m`
    // fact, so in-logic `!mass S M` premises are total lookups and the
    // clause-only verification path can re-check the equation system by
    // derivation. (Lazily-solved product states are not materialized.)
    if (stateMasses && definitions.has(SORT_PREDS.MASS)) {
      for (const [s, m] of stateMasses) {
        clauses.set(`${SORT_PREDS.MASS}/${s}`, {
          hash: Store.put(SORT_PREDS.MASS, [Store.put('atom', [s]), putRat(m[0], m[1])]),
          premises: [],
        });
      }
    }
  }
  // Materialized priors (TODO_0298 item 1b): mirror the subsort closure —
  // for every classifier TOUCHED by @w (checkPriors's discipline), every
  // member's ratio (default 1: totality over the touched sort, matching
  // the decimation consumer) becomes a ground `prior s c ρ` fact, so
  // in-logic `!prior S C W` premises and the clause-only draw
  // verification path are total fact lookups. Presence-gated twice: the
  // PROGRAM declares the predicate (the bias discipline — machinery
  // predicates are program-declared with the program's own sorts) AND
  // annotates at least one member of the sort (`m: s @w 1.` opts an
  // otherwise-unannotated sort in). Runs before checkAll — facts get
  // sort-checked like sedge facts.
  if (sortSystem && definitions.has(SORT_PREDS.PRIOR) && priorsTable.size > 0) {
    for (const [s, members] of sortSystem.classifiers) {
      let touched = false;
      for (const m of members) if (priorsTable.has(m)) { touched = true; break; }
      if (!touched) continue;
      for (const m of members) {
        const w = priorsTable.get(m) || [1n, 1n];
        clauses.set(`${SORT_PREDS.PRIOR}/${s}/${m}`, {
          hash: Store.put(SORT_PREDS.PRIOR, [Store.put('atom', [s]), Store.put('atom', [m]), putRat(w[0], w[1])]),
          premises: [],
        });
      }
    }
  }

  return { sortSystem, priorAdvice, stateMasses };
}

export { materializeLoadTimeClauses };
export default { materializeLoadTimeClauses };

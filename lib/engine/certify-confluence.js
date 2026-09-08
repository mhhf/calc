// @ts-check
/**
 * calc.certifyConfluence — the destination-discipline confluence
 * certifier (TODO_0309 P2, THY_0036; the certifyContention mold).
 *
 * CLAIM CERTIFIED: for the given rule set and initial state, ALL
 * interleavings of committed forward steps converge to the same final
 * state (strong diamond ⇒ Church–Rosser, no termination needed).
 *
 * SOUNDNESS-ONLY: `confluent: true` is a certificate backed by the
 * discipline below; a refusal carries a witness naming the first
 * violated condition and NEVER asserts non-confluence. The discipline
 * is the destination-passing / write-once fragment (SAX FSCD 2020
 * Thm. 10, generalized): every linear fact is owned by a destination,
 * rules touch one destination, cells are written once.
 *
 * THE DISCIPLINE (all names arrive via opts — nothing here knows any
 * calculus's vocabulary):
 *   D1 keyed consumption — every linear pattern's predicate has a
 *      declared destination argument (opts.dest), and all of a rule's
 *      linear patterns share ONE destination term.
 *   D2 dispatch exclusion — each rule has exactly one pattern on the
 *      dispatch predicate; for any two rules, same-destination
 *      coexistence is impossible: their dispatch patterns fail to
 *      unify, OR the unifier forces two single-writer cells
 *      (opts.persistentUnique) to hold distinct ground values at the
 *      same key.
 *   D3 determined instances — a rule's variables are fixed by its
 *      linear patterns plus single-writer goals whose keys are already
 *      determined (closure); no witness-choice nondeterminism.
 *   D4 slot reuse — produced linear facts of CONSUMED predicates reuse
 *      a consumed (predicate, destination) slot; produce-only
 *      predicates (never in any antecedent — pure output sinks) are
 *      exempt: their accumulation is commutative multiset addition and
 *      no exclusion argument leans on them. Single-writer persistent
 *      facts are produced only by consuming their declared linear
 *      guard at the same key; guards are never produced.
 *   D5 no engine-level branching — no internal choice (⊕ alternatives),
 *      no existential consequents (fresh-name nondeterminism), no
 *      dynamic-rule production or state (implication facts), no timed
 *      features (requiresScheduler).
 *   D6 initial-state invariants — per (predicate, destination) at most
 *      one linear fact; per single-writer key at most one value; no
 *      cell coexisting with its guard.
 *
 * DIAMOND ARGUMENT (why D1–D6 suffice): take two distinct enabled
 * steps. Different destinations ⇒ their consumed facts are disjoint
 * (D1: every consumed fact carries the destination). Same destination
 * ⇒ both dispatch patterns must match THE unique dispatch fact there
 * (D6 uniqueness, preserved by D4), which D2 rules out — except for
 * the same rule, where D3 forces the identical instance. Disjoint
 * steps commute: linear arithmetic on disjoint multisets, persistent
 * growth is monotone (positive goals stay provable; theories/FFI are
 * pure), and D3+write-once make every witness interleaving-independent.
 * Both orders reach the same state; no fresh names exist (D5), so
 * equality is literal. Invariants D6 are inductive under D4.
 *
 * Explore integration: a valid certificate lets explore() commit to
 * ONE interleaving (opts.confluence) — the certificate is pinned to
 * the exact rule set + initial state via digests; any mismatch throws.
 */

import Store from '../kernel/store.js';
import { predHead } from '../kernel/ast.js';
import { unify } from '../kernel/unify.js';
import { apply } from '../kernel/substitute.js';
import { freshMetavar } from '../kernel/fresh.js';
import { collectMetavars, isGround } from './pattern-utils.js';
import { hashString } from '../hash.js';

/** Digest of a rule set (order-independent): pins a certificate to the
 *  exact rules it certified. */
function ruleSetDigest(rules) {
  const parts = rules.map((r) => `${r.name}:${r.hash}`).sort();
  return hashString(parts.join(';')) >>> 0;
}

/** Digest of a plain initial state (order-independent). */
function initialStateDigest(plain) {
  const lin = Object.entries(plain.linear || {})
    .filter(([, c]) => c > 0)
    .map(([h, c]) => `${h}:${c}`).sort();
  const pers = Object.keys(plain.persistent || {}).sort();
  return hashString(lin.join(',') + '|' + pers.join(',')) >>> 0;
}

/** Rename a rule's metavars apart (fresh names) — returns a θ usable
 *  with apply() on any of the rule's pattern/goal hashes. */
function _renameTheta(hashes) {
  const vars = new Set();
  for (const h of hashes) collectMetavars(h, vars);
  /** @type {[number, number][]} */
  const theta = [];
  for (const v of vars) theta.push([v, freshMetavar()]);
  return theta;
}

const _refuse = (reason, detail) =>
  ({ confluent: false, witness: { reason, ...detail } });

/**
 * Certify confluence of (rules, initialState) under the destination
 * discipline.
 *
 * @param {Object[]} rules - COMPILED runtime rules (post grade-0 filter)
 * @param {Object} initialState - plain { linear: {hash:count}, persistent: {hash:true} }
 * @param {Object} [opts]
 * @param {Object} [opts.rc] - resolved connectives (implication/existential tags)
 * @param {Record<string, number>} [opts.dest] - linear pred → destination arg index
 * @param {string} [opts.dispatch] - the dispatch predicate (per-destination unique focus)
 * @param {Record<string, {keys: number[], values: number[]}>} [opts.persistentUnique]
 *        single-writer persistent predicates (write-once cells)
 * @param {Record<string, string>} [opts.guards]
 *        single-writer pred → the linear guard pred consumed by its writers
 * @returns {Object} { confluent: true, rulesDigest, stateDigest, discipline }
 *                 | { confluent: false, witness }
 */
function certifyConfluence(rules, initialState, opts = {}) {
  const rc = opts.rc || {};
  const dest = opts.dest || {};
  const dispatch = opts.dispatch;
  const pUnique = opts.persistentUnique || {};
  const guards = opts.guards || {};
  if (!dispatch) return _refuse('no-dispatch-declared', {});
  const guardPreds = new Set(Object.values(guards));

  // Predicates ever consumed by a rule: only these need keying, slot
  // reuse, and per-destination uniqueness — produce-only predicates are
  // inert outputs (see D4 note).
  const consumedPreds = new Set();
  for (const r of rules) {
    for (const p of (r.antecedent.linear || [])) {
      const pred = predHead(p);
      if (pred !== null) consumedPreds.add(pred);
    }
  }

  // ── D5 + D1 + D3 + D4: per-rule static checks ──────────────────────
  const perRule = new Map(); // rule → { destTerm, dispatchPat, theta-free info }
  for (const r of rules) {
    if (r.requiresScheduler) {
      return _refuse('timed-feature', { rule: r.name, feature: r.requiresScheduler });
    }
    const alts = r.consequentAlts || [];
    if (alts.length !== 1) {
      return _refuse('internal-choice', { rule: r.name, alternatives: alts.length });
    }
    const alt = alts[0];

    for (const q of (alt.linear || [])) {
      const t = Store.tag(q);
      if (rc.implication && t === rc.implication) {
        return _refuse('dynamic-rule-production', { rule: r.name });
      }
      if (rc.existential && t === rc.existential) {
        return _refuse('existential-consequent', { rule: r.name });
      }
    }

    // D1: keyed consumption, one destination per rule
    const lin = r.antecedent.linear || [];
    let destTerm;
    let dispatchPat = null;
    for (const p of lin) {
      const pred = predHead(p);
      const di = pred !== null ? dest[pred] : undefined;
      if (di === undefined) {
        return _refuse('unkeyed-pattern', { rule: r.name, pred: pred || Store.tag(p) });
      }
      if (Store.arity(p) <= di) {
        return _refuse('unkeyed-pattern', { rule: r.name, pred, detail: 'destination index out of arity' });
      }
      const d = Store.child(p, di);
      if (destTerm === undefined) destTerm = d;
      else if (d !== destTerm) {
        return _refuse('multi-destination', { rule: r.name, pred });
      }
      if (pred === dispatch) {
        if (dispatchPat !== null) {
          return _refuse('dispatch-arity', { rule: r.name, detail: 'two dispatch patterns' });
        }
        dispatchPat = p;
      }
    }
    if (dispatchPat === null) {
      return _refuse('dispatch-arity', { rule: r.name, detail: 'no dispatch pattern' });
    }

    // D4: slot reuse for produced linear; guarded write-once for
    // produced single-writer persistents; guards never produced.
    const consumedSlots = new Map(); // pred → Map(destHash → count)
    for (const p of lin) {
      const pred = predHead(p);
      const d = Store.child(p, dest[pred]);
      if (!consumedSlots.has(pred)) consumedSlots.set(pred, new Map());
      const m = consumedSlots.get(pred);
      m.set(d, (m.get(d) || 0) + 1);
    }
    for (const q of (alt.linear || [])) {
      const pred = predHead(q);
      if (pred !== null && guardPreds.has(pred)) {
        return _refuse('guard-production', { rule: r.name, pred });
      }
      if (pred !== null && !consumedPreds.has(pred)) continue; // produce-only sink
      const di = pred !== null ? dest[pred] : undefined;
      if (di === undefined) {
        return _refuse('unkeyed-production', { rule: r.name, pred: pred || Store.tag(q) });
      }
      const d = Store.child(q, di);
      const m = consumedSlots.get(pred);
      const avail = m ? (m.get(d) || 0) : 0;
      if (avail <= 0) {
        return _refuse('non-slot-reuse-production', { rule: r.name, pred });
      }
      m.set(d, avail - 1);
    }
    for (const g of (alt.persistent || [])) {
      const pred = predHead(g);
      if (pred !== null && pUnique[pred]) {
        const guard = guards[pred];
        if (!guard) {
          return _refuse('unguarded-cell-production', { rule: r.name, pred });
        }
        const key = Store.child(g, pUnique[pred].keys[0]);
        const guarded = lin.some((p) =>
          predHead(p) === guard && Store.child(p, dest[guard]) === key);
        if (!guarded) {
          return _refuse('unguarded-cell-production', { rule: r.name, pred, detail: 'produced key does not consume its guard' });
        }
      }
    }

    // D3: determinacy closure — linear-pattern vars, then single-writer
    // goals whose keys are determined bind their value vars.
    const determined = new Set();
    for (const p of lin) collectMetavars(p, determined);
    const goals = r.antecedent.persistent || [];
    let grew = true;
    while (grew) {
      grew = false;
      for (const g of goals) {
        const pred = predHead(g);
        const pu = pred !== null ? pUnique[pred] : undefined;
        if (!pu) continue;
        const keyVars = new Set();
        for (const k of pu.keys) collectMetavars(Store.child(g, k), keyVars);
        let keysDet = true;
        for (const v of keyVars) if (!determined.has(v)) { keysDet = false; break; }
        if (!keysDet) continue;
        for (const vi of pu.values) {
          const before = determined.size;
          collectMetavars(Store.child(g, vi), determined);
          if (determined.size > before) grew = true;
        }
      }
    }
    const allVars = new Set();
    for (const g of goals) collectMetavars(g, allVars);
    for (const q of (alt.linear || [])) collectMetavars(q, allVars);
    for (const g of (alt.persistent || [])) collectMetavars(g, allVars);
    for (const v of allVars) {
      if (!determined.has(v)) {
        return _refuse('underdetermined-instance', { rule: r.name, variable: Store.child(v, 0) });
      }
    }

    perRule.set(r, { dispatchPat, goals });
  }

  // ── D2: pairwise same-destination exclusion ────────────────────────
  const ruleArr = [...perRule.keys()];
  for (let i = 0; i < ruleArr.length; i++) {
    for (let j = i + 1; j < ruleArr.length; j++) {
      const R = ruleArr[i], S = ruleArr[j];
      const ri = perRule.get(R), si = perRule.get(S);
      const thR = _renameTheta([ri.dispatchPat, ...ri.goals]);
      const thS = _renameTheta([si.dispatchPat, ...si.goals]);
      const dR = apply(ri.dispatchPat, thR);
      const dS = apply(si.dispatchPat, thS);
      const u = /** @type {[number, number][] | null} */ (unify(dR, dS));
      if (u === null) continue; // dispatch patterns exclude each other
      // Single-writer contradiction: some cell pred is demanded at the
      // SAME key with DISTINCT ground values by the two rules.
      let excluded = false;
      outer:
      for (const gR of ri.goals) {
        const pred = predHead(gR);
        const pu = pred !== null ? pUnique[pred] : undefined;
        if (!pu) continue;
        for (const gS of si.goals) {
          if (predHead(gS) !== pred) continue;
          const aR = apply(apply(gR, thR), u);
          const aS = apply(apply(gS, thS), u);
          let sameKeys = true;
          for (const k of pu.keys) {
            if (Store.child(aR, k) !== Store.child(aS, k)) { sameKeys = false; break; }
          }
          if (!sameKeys) continue;
          for (const vi of pu.values) {
            const vR = Store.child(aR, vi), vS = Store.child(aS, vi);
            if (vR !== vS && isGround(vR) && isGround(vS)) {
              excluded = true;
              break outer;
            }
          }
        }
      }
      if (!excluded) {
        return _refuse('overlapping-dispatch', { ruleA: R.name, ruleB: S.name });
      }
    }
  }

  // ── D6: initial-state invariants ───────────────────────────────────
  const linCounts = new Map(); // `${pred}@${destHash}` → count
  const linByPredDest = new Map();
  for (const hStr of Object.keys(initialState.linear || {})) {
    const count = initialState.linear[hStr];
    if (count <= 0) continue;
    const h = Number(hStr);
    const t = Store.tag(h);
    if (rc.implication && t === rc.implication) {
      return _refuse('dynamic-rule-in-state', { fact: h });
    }
    const pred = predHead(h);
    if (pred !== null && !consumedPreds.has(pred)) continue; // inert output fact
    const di = pred !== null ? dest[pred] : undefined;
    if (di === undefined) {
      return _refuse('unkeyed-state-fact', { pred: pred || t });
    }
    const d = Store.child(h, di);
    const key = pred + '@' + d;
    const n = (linCounts.get(key) || 0) + count;
    linCounts.set(key, n);
    if (n > 1) {
      return _refuse('duplicate-destination', { pred, dest: d });
    }
    if (!linByPredDest.has(pred)) linByPredDest.set(pred, new Set());
    linByPredDest.get(pred).add(d);
  }
  const cellKeys = new Map(); // `${pred}@${keyHash}` → valueHash
  for (const hStr of Object.keys(initialState.persistent || {})) {
    const h = Number(hStr);
    const pred = predHead(h);
    const pu = pred !== null ? pUnique[pred] : undefined;
    if (!pu) continue;
    const k = Store.child(h, pu.keys[0]);
    const v = pu.values.length ? Store.child(h, pu.values[0]) : 0;
    const key = pred + '@' + k;
    if (cellKeys.has(key) && cellKeys.get(key) !== v) {
      return _refuse('duplicate-persistent-value', { pred, key: k });
    }
    cellKeys.set(key, v);
    const guard = guards[pred];
    if (guard && linByPredDest.has(guard) && linByPredDest.get(guard).has(k)) {
      return _refuse('guard-cell-coexistence', { pred, key: k });
    }
  }

  return {
    confluent: true,
    rulesDigest: ruleSetDigest(rules),
    stateDigest: initialStateDigest(initialState),
    rules: rules.length,
    discipline: { dest, dispatch, persistentUnique: pUnique, guards },
  };
}

export { certifyConfluence, ruleSetDigest, initialStateDigest };
export default { certifyConfluence, ruleSetDigest, initialStateDigest };

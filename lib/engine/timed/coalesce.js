/**
 * Stamp coalescing — arrived-cohort normalization (TODO_0277, approach 1).
 *
 * Max-plus timed semantics is translation-invariant on DEAD stamps: once a
 * fact has arrived (stamp ≤ the settled bound) and no rule can ever observe
 * its absolute stamp, the stamp is dead information — `iron_ore@0.3 *
 * iron_ore@0.6 * …` is indistinguishable from `!_N iron_ore@0`. Coalescing
 * rewrites such facts to the unit stamp, where the run-length FactSet merges
 * them into one entry. Live-state size becomes O(distinct live facts),
 * independent of elapsed time.
 *
 * Soundness (per the 0277 analysis):
 *  - at a settled bound B (quiescence or the horizon), every pending match
 *    has activation > B; a max over components ≤ B is set by a component
 *    > B (or an after-bound), so lowering ≤ B stamps to 0 changes no
 *    pending activation. Mid-run the same argument holds STRICTLY below
 *    the current event frontier aMin.
 *  - a stamp is LOAD-BEARING (excluded) when some rule can observe it:
 *      1. a stamp-binding antecedent pattern A@T / !_k A@T (bodyIsAt) —
 *         binds or pins the cohort stamp (spoilage, cohort-locked takes);
 *      2. any pattern of a rule carrying a `before` window — the window
 *         compares against the activation max, which coalescing lowers;
 *      3. a wildcard-head pattern in a before-window rule (unknown reach)
 *         → global bail.
 *    The exclusion set is DERIVED from the compiled rules — never
 *    hard-coded. Possessed rules (loli facts) contribute the same way,
 *    recomputed at each coalesce point (they enter and leave the state).
 *  - menu/loli/with facts themselves are never rewritten (their stamp is
 *    a rule-birth base; cheap to keep, and possessed before-windows stay
 *    honest).
 *
 * What coalescing deliberately changes: cohort IDENTITY of merged tokens
 * and therefore the state Zobrist hash — the stateless PRF conflict
 * chooser may resolve future ties differently (any resolution is a valid
 * world, settleExplore's contract). Hence OPT-IN: settle(state, T,
 * { coalesce: true }). Exact-stamp gate suites run without it.
 */

import Store from '../../kernel/store.js';
import { factKeyOf } from '../formula-utils.js';

// Per-rule contribution cache: rules are stable compiled objects; the rule
// LISTS passed to settle are fresh arrays per call, so cache per rule.
const _ruleContrib = new WeakMap();

/** Contribution of one compiled rule to the exclusion set. */
function contribOf(rule, tcfg) {
  let c = _ruleContrib.get(rule);
  if (c) return c;
  const preds = new Set();
  let all = false;
  const hasBefore = !!(rule.windows && rule.windows.before && rule.windows.before.length > 0);
  for (const p of (rule.antecedent.linear || [])) {
    const meta = rule.linearMeta[p];
    const pred = meta ? meta.pred : factKeyOf(p, tcfg.expTag);
    const body = meta ? meta.body : p;
    const stampBinding = Store.tag(body) === tcfg.stampTag;
    if (stampBinding || hasBefore) {
      if (pred) preds.add(pred);
      else all = true;               // wildcard reach — cannot bound it
    }
  }
  c = { preds, all };
  _ruleContrib.set(rule, c);
  return c;
}

/** Union the exclusion sets of a rule list into `into` ({ preds, all }). */
function collectObservers(ruleList, tcfg, into) {
  for (const r of ruleList) {
    const c = contribOf(r, tcfg);
    if (c.all) into.all = true;
    for (const p of c.preds) into.preds.add(p);
  }
  return into;
}

/** Static exclusion record for a settle run's rule list. */
function stampObservers(ruleList, tcfg) {
  return collectObservers(ruleList, tcfg, { preds: new Set(), all: false });
}

/**
 * Coalesce arrived cohorts of a live timed State in place.
 *
 * @param {State} state - FactSet state (normalized: linear facts at-wrapped)
 * @param {number} bound - stamp hash; facts with stamp ≤ bound (strict:
 *   stamp < bound) and non-load-bearing predicate are re-stamped to unit
 * @param {Object} tcfg - timed config (buildTimedConfig)
 * @param {Object} observers - stampObservers(rules, tcfg) for the static
 *   rule list; state lolis are folded in here per call
 * @param {Object} [opts] - { strict, stateLolis, compileLoli }
 *   stateLolis: [{ inner }] possessed rules currently in the state;
 *   compileLoli: compiles one (for their exclusion contributions)
 * @returns {number} facts rewritten
 */
function coalesce(state, bound, tcfg, observers, opts = {}) {
  if (observers.all) return 0;
  const cmp = tcfg.availability.cmp;
  const unit = tcfg.effect.unit();
  const strict = !!opts.strict;

  // Possessed rules can observe stamps too — fold their contributions in.
  let excl = observers.preds;
  if (opts.stateLolis && opts.stateLolis.length > 0 && opts.compileLoli) {
    const dyn = { preds: new Set(observers.preds), all: false };
    collectObservers(opts.stateLolis.map(e => opts.compileLoli(e.inner)), tcfg, dyn);
    if (dyn.all) return 0;
    excl = dyn.preds;
  }

  const linear = state.linear;
  const jobs = [];                     // [hash, count, inner]
  for (let t = 0; t < linear.maxTagId; t++) {
    const len = linear.lens[t];
    if (!len) continue;
    const buf = linear.groups[t];
    const cnt = linear._rl ? linear.counts[t] : null;
    for (let i = 0; i < len; i++) {
      const h = buf[i];
      if (Store.tag(h) !== tcfg.stampTag) continue;
      const s = Store.child(h, 1);
      if (s === unit) continue;
      const c = cmp(s, bound);
      if (strict ? c >= 0 : c > 0) continue;          // not arrived w.r.t. bound
      const inner = Store.child(h, 0);
      const it = Store.tag(inner);
      if (it === 'with' || (tcfg.implTag && it === tcfg.implTag)) continue;
      const pred = factKeyOf(inner, tcfg.expTag);
      if (!pred || excl.has(pred)) continue;
      jobs.push(h, cnt ? cnt[i] : 1, inner);
    }
  }
  for (let j = 0; j < jobs.length; j += 3) {
    const h = jobs[j], c = jobs[j + 1], inner = jobs[j + 2];
    linear.remove(Store.tagId(h), h, null, c);
    const nh = Store.put(tcfg.stampTag, [inner, unit]);
    linear.insert(Store.tagId(nh), nh, null, c);
  }
  return jobs.length / 3;
}

export { stampObservers, coalesce, collectObservers };
export default { stampObservers, coalesce, collectObservers };

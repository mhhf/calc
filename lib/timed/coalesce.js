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

import Store from '../kernel/store.js';
import { factKeyOf } from '../engine/formula-utils.js';
import { packRef } from '../engine/fact-set.js';

// Per-rule contribution cache: rules are stable compiled objects; the rule
// LISTS passed to settle are fresh arrays per call, so cache per rule.
const _ruleContrib = new WeakMap();

/**
 * Formula-level observers: a stored FORMULA (a menu alternative, a rule
 * embedded in a consequent, a possessed loli not yet compiled) can carry
 * stamp-binding antecedent patterns and before-windows just like a static
 * rule — and it can materialize as a fireable rule LATER (projection,
 * production), after coalescing already merged the cohorts it observes.
 * Exclusion is durable, so these observers must be folded in the moment
 * the formula is reachable. Generic recursive walk, cached per hash;
 * depth overflow bails to `all` (conservative — disables coalescing).
 */
const _fObsCache = new Map();          // tcfg-tag-qualified key -> { preds, all, hasWindow, hasBefore }
Store.onClear(() => _fObsCache.clear());

function formulaObservers(h, tcfg, into) {
  // The analysis depends on the tcfg tags, not just the formula — qualify
  // the key so a second timed calculus in the same process cannot poison it.
  const key = tcfg.implTag + '|' + tcfg.expTag + '|' + tcfg.stampTag + '|' + h;
  let c = _fObsCache.get(key);
  if (c === undefined) {
    c = { preds: new Set(), all: false, hasWindow: false, hasBefore: false };
    _walkFormula(h, tcfg, c, 0);
    _fObsCache.set(key, c);
  }
  if (c.all) into.all = true;
  if (c.hasWindow) into.hasWindow = true;
  if (c.hasBefore) into.hasBefore = true;
  for (const p of c.preds) into.preds.add(p);
}

function _walkFormula(h, tcfg, out, depth) {
  if (typeof h !== 'number' || !Store.isTerm(h)) return;
  if (depth > 64) { out.all = true; out.hasWindow = true; out.hasBefore = true; return; }
  const t = Store.tag(h);
  if (!t || t === 'atom') return;
  // Formula-level windows are opaque to the shift-degree analysis
  // (covariance.js works on compiled rules) — record their presence so
  // rebase/acceleration can refuse conservatively.
  if (t === 'before') { out.hasWindow = true; out.hasBefore = true; }
  if (t === 'after') out.hasWindow = true;
  if (tcfg.implTag && t === tcfg.implTag) {
    _anteObservers(Store.child(h, 0), tcfg, out);
  }
  const n = Store.arity(h);
  for (let i = 0; i < n; i++) _walkFormula(Store.child(h, i), tcfg, out, depth + 1);
}

/** Antecedent-side observation analysis of an uncompiled loli formula:
 *  mirrors contribOf on the syntactic shape (stamp-binding patterns; a
 *  before-window pins every pattern of the antecedent). */
function _anteObservers(ante, tcfg, out) {
  const pats = [];
  let hasBefore = false;
  const flat = (x) => {
    const t = Store.tag(x);
    if (t === 'tensor') { flat(Store.child(x, 0)); flat(Store.child(x, 1)); return; }
    if (t === 'one') return;
    if (t === 'before') { hasBefore = true; return; }
    if (t === 'after') return;                       // ground bounds observe nothing;
    if (t === 'preserved' || t === 'readPreserved') { // stamped bounds bind via A@Q
      flat(Store.child(x, 0)); return;
    }
    pats.push(x);
  };
  flat(ante);
  for (const p of pats) {
    let body = p;
    if (tcfg.expTag && Store.tag(body) === tcfg.expTag) body = Store.child(body, 1);
    const stampBinding = Store.tag(body) === tcfg.stampTag;
    if (stampBinding || hasBefore) {
      const pred = factKeyOf(p, tcfg.expTag);
      if (pred) out.preds.add(pred);
      else out.all = true;
    }
  }
}

/** Contribution of one compiled rule to the exclusion set. */
function contribOf(rule, tcfg) {
  let c = _ruleContrib.get(rule);
  if (c) return c;
  const preds = new Set();
  const acc = { preds, all: false, hasWindow: false, hasBefore: false };
  const hasBefore = !!(rule.windows && rule.windows.before && rule.windows.before.length > 0);
  for (const p of (rule.antecedent.linear || [])) {
    const meta = rule.linearMeta[p];
    const pred = meta ? meta.pred : factKeyOf(p, tcfg.expTag);
    const body = meta ? meta.body : p;
    const stampBinding = Store.tag(body) === tcfg.stampTag;
    if (stampBinding || hasBefore) {
      if (pred) preds.add(pred);
      else acc.all = true;           // wildcard reach — cannot bound it
    }
  }
  // Consequent-embedded rules and menus (durable-exclusion audit): what a
  // rule can PRODUCE may observe stamps once it materializes — including
  // PERSISTENT menus/clauses (audit finding: alt.persistent was skipped).
  const alts = rule.weighted && rule.consequentAlts ? rule.consequentAlts : [rule.consequent];
  for (const alt of alts) {
    for (const p of (alt.linear || [])) formulaObservers(p, tcfg, acc);
    for (const p of (alt.persistent || [])) formulaObservers(p, tcfg, acc);
  }
  c = { preds, all: acc.all, hasWindow: acc.hasWindow, hasBefore: acc.hasBefore };
  _ruleContrib.set(rule, c);
  return c;
}

/** Union the exclusion sets of a rule list into `into` ({ preds, all,
 *  hasWindow, hasBefore } — the flags mark FORMULA-level windows reachable
 *  through consequents, opaque to the shift-degree analysis). */
function collectObservers(ruleList, tcfg, into) {
  for (const r of ruleList) {
    const c = contribOf(r, tcfg);
    if (c.all) into.all = true;
    if (c.hasWindow) into.hasWindow = true;
    if (c.hasBefore) into.hasBefore = true;
    for (const p of c.preds) into.preds.add(p);
  }
  return into;
}

/** Static exclusion record for a settle run's rule list. */
function stampObservers(ruleList, tcfg) {
  return collectObservers(ruleList, tcfg, { preds: new Set(), all: false, hasWindow: false, hasBefore: false });
}

// Per-list union cache: index.js hands settle a STABLE default rule array
// (memoized when no rule filter is active), so the union is computed once
// per calculus instead of once per tick.
const _obsCache = new WeakMap();
function stampObserversCached(ruleList, tcfg) {
  let o = _obsCache.get(ruleList);
  if (!o) { o = stampObservers(ruleList, tcfg); _obsCache.set(ruleList, o); }
  return o;
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
/**
 * Effective exclusion at a point in time: the static observers plus the
 * contributions of the possessed rules AND menus currently in the state
 * (a menu alternative is a rule the player can materialize — its
 * observers are durable from the moment the menu exists). Returns
 * { preds, all } (a fresh record when the state contributes).
 */
function effectiveExclusion(observers, stateLolis, compileLoli, tcfg, stateMenus) {
  if (observers.all) return observers;
  const hasLolis = stateLolis && stateLolis.length > 0 && compileLoli;
  const hasMenus = stateMenus && stateMenus.length > 0;
  if (!hasLolis && !hasMenus) return observers;
  const dyn = {
    preds: new Set(observers.preds), all: false,
    hasWindow: !!observers.hasWindow, hasBefore: !!observers.hasBefore,
  };
  if (hasLolis) collectObservers(stateLolis.map(e => compileLoli(e.inner)), tcfg, dyn);
  if (hasMenus) for (const m of stateMenus) formulaObservers(m, tcfg, dyn);
  return dyn;
}

function coalesce(state, bound, tcfg, observers, opts = {}) {
  if (observers.all) return 0;
  const strict = !!opts.strict;

  // Possessed rules and menus can observe stamps too — fold them in.
  const eff = opts.effective ||
    effectiveExclusion(observers, opts.stateLolis, opts.compileLoli, tcfg, opts.stateMenus);
  if (eff.all) return 0;
  const excl = eff.preds;

  // Labelled state (THY_0024): dead cohorts collapse by rewriting the
  // STAMP COLUMN to the unit id — no term is minted, the run-length rows
  // merge on re-insert. `bound` is a stamp id in the state's table.
  const linear = state.linear;
  const st = linear.stamps;
  const jobs = [];                     // [group, inner, sid, count]
  for (let t = 0; t < linear.maxTagId; t++) {
    const len = linear.lens[t];
    if (!len) continue;
    const ib = linear.groups[t], sb = linear.sids[t], cnt = linear.counts[t];
    for (let i = 0; i < len; i++) {
      const sid = sb[i];
      if (sid === 0) continue;                 // already at the unit
      const c = st.cmp(sid, bound);
      // rows are stamp-sorted: the arrived slice is a PREFIX — the first
      // beyond-bound stamp ends the group's work
      if (strict ? c >= 0 : c > 0) break;
      const inner = ib[i];
      const it = Store.tag(inner);
      if (it === 'with' || (tcfg.implTag && it === tcfg.implTag)) continue;
      const pred = factKeyOf(inner, tcfg.expTag);
      if (!pred || excl.has(pred)) continue;
      jobs.push(t, inner, sid, cnt[i]);
    }
  }
  for (let j = 0; j < jobs.length; j += 4) {
    const t = jobs[j], inner = jobs[j + 1], sid = jobs[j + 2], c = jobs[j + 3];
    linear.remove(t, packRef(inner, sid), null, c);
    linear.insert(t, packRef(inner, 0), null, c);
  }
  return jobs.length / 4;
}

export { stampObservers, stampObserversCached, coalesce, collectObservers, effectiveExclusion };

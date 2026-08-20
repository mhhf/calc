/**
 * Game layer — external choice over timed states (till Phase 6/6c).
 *
 * The ENVIRONMENT's moves: withProject collapses a `&`-menu to one
 * alternative (the player's click), menuStatus answers the UI's greying
 * question. Both are pure queries/steps OVER the scheduler — split out of
 * timed.js (round-15 F7 factoring): the scheduler decides what FIRES, this
 * file decides what the environment may CHOOSE.
 */

import Store from '../../kernel/store.js';
import { EMPTY_MATCH_OPTS } from '../match.js';
import { factKeyOf, flattenAnte } from '../formula-utils.js';
import { normalizeTimedState, tryTimedMatch, loliCandidates } from './timed.js';

/**
 * Shared enablement relation (menuStatus + strict projection): does the
 * projection (the diff of `projected` over `base`) let some rule fire at
 * activation ≤ horizon consuming part of it? Consumption is matched by
 * FACT KEY, not exact cohort — a queued identical act whose older cohort
 * the FIFO match prefers does not mask availability.
 */
function _projectionEnabled(base, projected, horizon, ruleList, calc, matchOpts, tcfg, compileLoli) {
  const projKeys = new Set();
  const baseLinear = base.linear || {};
  for (const hStr in projected.linear) {
    if ((projected.linear[hStr] || 0) > (baseLinear[hStr] || 0)) {
      const k = factKeyOf(Number(hStr), tcfg.expTag);
      if (k) projKeys.add(k);
    }
  }
  if (projKeys.size === 0) return true;      // nothing linear (e.g. a sub-menu)
  const cmp = tcfg.availability.cmp;
  const state2 = normalizeTimedState(projected, tcfg);
  const cands = [];
  for (const r of ruleList) {
    const m = tryTimedMatch(r, state2, calc, matchOpts || EMPTY_MATCH_OPTS, tcfg);
    if (m) cands.push(m);
  }
  // Possessed rules count — including the PROJECTED one itself: a costed
  // loli's enablement is exactly "could the cut be formed at the decision
  // time" (its own firing consumes it, and 'loli' is in projKeys).
  if (compileLoli) {
    loliCandidates(state2, tcfg, compileLoli, calc, matchOpts || EMPTY_MATCH_OPTS, cands);
  }
  for (const m of cands) {
    if (cmp(m.activation, horizon) > 0) continue;
    for (const hStr in m.consumed) {
      if (projKeys.has(factKeyOf(Number(hStr), tcfg.expTag))) return true;
    }
  }
  return false;
}

/**
 * Collapse one copy of a menu fact `A₁ & … & Aₙ` to its index-th
 * alternative (0-based, left-to-right over the &-spine). This is the
 * ENVIRONMENT's move — the player/host resolves external choice; the
 * engine never collapses menus itself (settle treats them as inert facts,
 * which is exactly what makes a menu a renderable decision surface, and
 * the host can only choose among alternatives the game actually offered).
 *
 * The projection is timeless; its STAMP is an input like the horizon: the
 * chosen component enters at max(menu stamp, opts.at) — a decision cannot
 * precede the menu's availability, and a later opts.at is the real moment
 * the decision was made. The chosen alternative decomposes like a fired
 * consequent: tensors flatten, !ω goes persistent, !_k yields k copies.
 *
 * Two menu forms:
 *   LINEAR `A & B`      — a consumable one-shot decision: projection
 *                         consumes one copy (a rationed choice).
 *   PERSISTENT `!(A&B)` — a STANDING menu (Seely: !(A & B) ≅ !A ⊗ !B, an
 *                         unlimited supply of its alternatives): projection
 *                         does NOT consume — any alternative, repeatedly,
 *                         at any decision time. Menu stamp is the unit.
 * Alternatives are the leaves of the &-spine (nested & flattens — grouping
 * is presentation); a bang-WRAPPED alternative `!(sub & menu)` is one leaf
 * that projects into the persistent zone: a sub-menu opens (click-through
 * navigation), and rules producing menu facts are menu UNLOCKING.
 *
 * factHash may be the stamped hash as it appears in state.linear, the bare
 * menu formula (stamp defaults to the unit), or a persistent-zone menu.
 * Returns a NEW plain state object; the input is not mutated.
 */
function withProject(inputState, factHash, index, opts = {}) {
  const tcfg = opts.timedConfig, rc = opts.roles;
  if (!tcfg || !rc) throw new Error('choose requires opts.timedConfig and opts.roles');
  if (!rc.externalChoice) throw new Error('choose: calculus has no external-choice connective');
  const linear = { ...(inputState.linear || {}) };
  const persistent = { ...(inputState.persistent || {}) };
  const unit = tcfg.effect.unit();

  let key = Number(factHash);
  let fromPersistent = false;
  let menu, menuStamp = unit;
  if (!linear[key] && Store.tag(key) !== 'at') {
    const wrapped = Store.put('at', [key, unit]);
    if (linear[wrapped]) key = wrapped;
    else if (persistent[key]) fromPersistent = true;
  }
  if (fromPersistent) {
    menu = key;                               // standing menu: timeless, kept
  } else {
    if (!linear[key]) throw new Error('choose: fact not present in state');
    const stamped = Store.tag(key) === 'at';
    menu = stamped ? Store.child(key, 0) : key;
    menuStamp = stamped ? Store.child(key, 1) : unit;
  }
  if (Store.tag(menu) !== rc.externalChoice) {
    throw new Error(`choose: fact is not an external choice (got '${Store.tag(menu)}')`);
  }

  const leaves = [];
  (function spine(h) {
    if (Store.tag(h) === rc.externalChoice) {
      spine(Store.child(h, 0));
      spine(Store.child(h, 1));
    } else leaves.push(h);
  })(menu);
  if (!(index >= 0 && index < leaves.length)) {
    throw new Error(`choose: index ${index} out of range (menu has ${leaves.length} alternatives)`);
  }

  let s = menuStamp;
  // atStamp: an already-parsed stamp hash (internal callers, e.g.
  // menuStatus); at: user-facing string/number through parseStamp.
  if (opts.at !== undefined || opts.atStamp !== undefined) {
    const at = opts.atStamp !== undefined ? opts.atStamp : tcfg.parseStamp(opts.at);
    if (at === undefined || !tcfg.isStamp(at)) throw new Error('choose: opts.at is not a valid stamp');
    if (tcfg.availability.cmp(at, s) > 0) s = at;
  }

  if (!fromPersistent) {                      // standing menus are never spent
    if (linear[key] === 1) delete linear[key];
    else linear[key] = linear[key] - 1;
  }

  const flat = flattenAnte(leaves[index], rc);
  if ((flat.grade0 || []).length > 0) {
    throw new Error('choose: grade-0 components cannot enter a state');
  }
  for (const h of flat.linear) {
    let inner = h, count = 1;
    if (tcfg.expTag && Store.tag(inner) === tcfg.expTag) {
      const g = Store.child(inner, 0);
      if (Store.tag(g) !== 'binlit') throw new Error('choose: count grade must be a ground integer');
      count = Number(Store.child(g, 0));
      inner = Store.child(inner, 1);
    }
    if (count === 0) continue;
    const out = Store.put('at', [inner, s]);
    linear[out] = (linear[out] || 0) + count;
  }
  for (const h of flat.persistent) persistent[h] = true;
  const result = { linear, persistent };

  // Cut vs plan (Phase 6c): a LOLI alternative is a costed button — its
  // default click is a CUT: the possessed rule must be fireable at the
  // decision stamp (cost consumable now), else the click is REFUSED and
  // nothing enters the state. opts.plan = true RESIDUATES instead: the
  // possessed rule enters the context and waits (a queued order). Both
  // are proof steps — the environment picks which inference to perform.
  // Non-loli alternatives project unconditionally, as before.
  if (tcfg.implTag && Store.tag(leaves[index]) === tcfg.implTag &&
      !opts.plan && !opts.noStrict) {
    if (!opts.rules) {
      throw new Error('choose: cut-mode loli alternatives need rules in scope (or pass { plan: true })');
    }
    if (!_projectionEnabled(inputState, result, s, opts.rules,
        opts.calc || null, opts.matchOpts, tcfg, opts.compileLoli)) {
      throw new Error(`choose: alternative ${index} cannot fire at the decision time (pass { plan: true } to queue it)`);
    }
  }
  return result;
}

/**
 * Per-alternative availability of a menu at horizon T — the UI's greying
 * question ("available but inactive"): enabled(i) ⇔ projecting alternative
 * i at T would let some rule fire at activation ≤ T consuming (part of)
 * the projection. A pure, non-committing query on state copies — it does
 * NOT decide what clicking an unsatisfiable choice means; that policy
 * lives in the .till program (an act with an expiry window is strict, an
 * act without one is a standing plan/promise).
 *
 * Consumption is matched by FACT KEY, not exact cohort: if an identical
 * act is already queued, the rule's FIFO match may take the older cohort —
 * the alternative is still actionable.
 *
 * Returns [{ formula, enabled, strict }] in leaf order (formula renderable
 * via show; strict = the alternative is now-marked, so a disabled click
 * would be REFUSED by choose rather than queued).
 */
function menuStatus(inputState, factHash, ruleList, opts) {
  const tcfg = opts.timedConfig, rc = opts.roles;
  const horizon = opts.horizon;
  if (!tcfg || !rc) throw new Error('menuStatus requires opts.timedConfig and opts.roles');
  if (horizon === undefined || !tcfg.isStamp(horizon)) {
    throw new Error('menuStatus: invalid horizon');
  }

  // leaves of the &-spine (same enumeration as withProject)
  let menu = Number(factHash);
  let menuStamp = tcfg.effect.unit();
  if (Store.tag(menu) === 'at') {
    menuStamp = Store.child(menu, 1);
    menu = Store.child(menu, 0);
  }
  if (Store.tag(menu) !== rc.externalChoice) {
    throw new Error(`menuStatus: fact is not an external choice (got '${Store.tag(menu)}')`);
  }
  const leaves = [];
  (function spine(h) {
    if (Store.tag(h) === rc.externalChoice) {
      spine(Store.child(h, 0));
      spine(Store.child(h, 1));
    } else leaves.push(h);
  })(menu);

  return leaves.map((leaf, i) => {
    // strict = a costed loli (cut-by-default click): a disabled click would
    // be REFUSED by choose rather than queued.
    const strict = !!(tcfg.implTag && Store.tag(leaf) === tcfg.implTag);
    let projected;
    try {
      projected = withProject(inputState, factHash, i,
        { timedConfig: tcfg, roles: rc, atStamp: horizon, noStrict: true });
    } catch {
      return { formula: leaf, enabled: false, strict };  // e.g. grade-0 component
    }
    // choose's cut-check fires at s = max(menuStamp, at) — greying must ask
    // the SAME question. For a future-stamped menu the strict cutoff is the
    // projection stamp, not the display horizon: the costed button is
    // enabled iff the click would be ACCEPTED (round-15 F2).
    const effHorizon = strict && tcfg.availability.cmp(menuStamp, horizon) > 0
      ? menuStamp : horizon;
    const enabled = _projectionEnabled(inputState, projected, effHorizon,
      ruleList, opts.calc || null, opts.matchOpts, tcfg, opts.compileLoli);
    return { formula: leaf, enabled, strict };
  });
}

export { withProject, menuStatus };
export default { withProject, menuStatus };

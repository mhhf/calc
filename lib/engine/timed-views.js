/**
 * Views — read-only projections of a timed state / event log (till).
 *
 * Nothing here mutates or fires: observable/pending slice the state at a
 * horizon, inFlight slices the event log, timedSubset/timedExact are the
 * test-harness containment checks (#expect / #expect_exact). Split out of
 * timed.js (round-15 F7 factoring).
 */

import { toObject } from './fact-set.js';
import { isAt, innerOf, stampOf } from './timed.js';

/** The stamp ≤ T slice: player-visible inventory { innerHash: count }. */
function observable(inputState, T, tcfg) {
  const plain = inputState.linear && inputState.linear.group ? toObject(inputState) : inputState;
  const unit = tcfg.effect.unit();
  const out = {};
  for (const hStr in (plain.linear || {})) {
    const h = Number(hStr);
    if (tcfg.availability.cmp(stampOf(h, unit), T) <= 0) {
      const i = innerOf(h);
      out[i] = (out[i] || 0) + plain.linear[hStr];
    }
  }
  return out;
}

/** In-flight facts: stamp > T, sorted by stamp — [{ fact, stamp, count,
 *  remaining? }] (remaining = stamp − T when the effect algebra has sub). */
function pending(inputState, T, tcfg) {
  const plain = inputState.linear && inputState.linear.group ? toObject(inputState) : inputState;
  const unit = tcfg.effect.unit();
  const out = [];
  for (const hStr in (plain.linear || {})) {
    const h = Number(hStr);
    const s = stampOf(h, unit);
    if (tcfg.availability.cmp(s, T) > 0) {
      const e = { fact: innerOf(h), stamp: s, count: plain.linear[hStr] };
      if (tcfg.effect.sub) e.remaining = tcfg.effect.sub(s, T);
      out.push(e);
    }
  }
  out.sort((a, b) => tcfg.availability.cmp(a.stamp, b.stamp));
  return out;
}

/** The scheduler's completion queue at horizon T (E7.3): events with
 *  activation ≤ T < done. Rule name = process kind; θ = which tokens. */
function inFlight(events, T, tcfg) {
  const cmp = tcfg.availability.cmp;
  return events
    .filter(e => cmp(e.activation, T) <= 0 && cmp(T, e.done) < 0)
    .map(e => {
      const r = { rule: e.rule, activation: e.activation, done: e.done, theta: e.theta };
      if (tcfg.effect.sub) r.remaining = tcfg.effect.sub(e.done, T);
      return r;
    });
}

/**
 * Timed subset check (test harnesses): unstamped pattern facts are stamp
 * WILDCARDS (counts sum over all cohorts of the same inner fact); stamped
 * facts match their exact cohort. Persistent facts match exactly.
 */
function timedSubset(pattern, stateObj) {
  for (const hStr in (pattern.linear || {})) {
    const h = Number(hStr);
    const need = pattern.linear[hStr];
    let have = 0;
    if (isAt(h)) {
      have = stateObj.linear[h] || 0;
    } else {
      for (const kStr in stateObj.linear) {
        if (innerOf(Number(kStr)) === h) have += stateObj.linear[kStr];
      }
    }
    if (have < need) return false;
  }
  for (const hStr in (pattern.persistent || {})) {
    if (!stateObj.persistent[hStr]) return false;
  }
  return true;
}

/**
 * Exact-cover variant of timedSubset (#expect_exact, Phase 5.5): the
 * pattern must account for EVERY linear fact. Per inner-head group,
 * stamped pattern facts match their exact cohort, unstamped pattern
 * facts are stamp wildcards, and pattern/state group totals must be
 * EQUAL — a fact the pattern does not mention fails the check (subset
 * semantics cannot catch extra facts). Persistent facts keep subset
 * semantics (derived persistent knowledge is monotone).
 */
function timedExact(pattern, stateObj) {
  const groups = new Map();   // inner hash -> { need, have, exact: Map(fact -> count) }
  const G = (i) => {
    let g = groups.get(i);
    if (!g) { g = { need: 0, have: 0, exact: new Map() }; groups.set(i, g); }
    return g;
  };
  for (const hStr in (pattern.linear || {})) {
    const h = Number(hStr), c = pattern.linear[hStr];
    const g = G(innerOf(h));
    g.need += c;
    if (isAt(h)) g.exact.set(h, (g.exact.get(h) || 0) + c);
  }
  for (const kStr in (stateObj.linear || {})) {
    G(innerOf(Number(kStr))).have += stateObj.linear[kStr];
  }
  for (const g of groups.values()) {
    // totals equal + exact demands satisfiable ⇒ wildcards fill the rest
    if (g.need !== g.have) return false;
    for (const [h, c] of g.exact) {
      if ((stateObj.linear[h] || 0) < c) return false;
    }
  }
  for (const hStr in (pattern.persistent || {})) {
    if (!stateObj.persistent[hStr]) return false;
  }
  return true;
}

export { observable, pending, inFlight, timedSubset, timedExact };
export default { observable, pending, inFlight, timedSubset, timedExact };

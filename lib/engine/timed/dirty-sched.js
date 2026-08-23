/**
 * Dirty scheduler — per-rule activation cache over a lazy-invalidation
 * binary min-heap (P3, TODO_0277; extracted from timed.js, audit
 * 2026-08-23 — a self-contained data structure with a three-method
 * contract: candidates / activations / markFired).
 *
 * The ONLY planned cache (round 9): per-rule activations, recomputed
 * lazily when the rule is dirty. Bindings are NEVER stored across state
 * changes — matches are recomputed for the activation-minimal rules on
 * every step, so no staleness class exists. Acceptance (D13):
 * trace-identical to rescan.
 *
 * Scaling: activations live in a lazy-invalidation binary min-heap — a
 * step costs O(#dirty · match + log #rules) instead of an O(#rules)
 * min-scan. Stale heap entries (superseded versions) discard on pop.
 * The scheduler is reusable across settle calls: settle caches it on the
 * raw State keyed by the FactSet mutation counters (see _schedCache in
 * timed.js).
 *
 * `tryMatch` is injected (timed.js's tryTimedMatch) so this module
 * depends only on the generic layers (formula-utils, labels).
 */

import { factKeyOf } from '../formula-utils.js';
import { refInner } from '../labels.js';

function makeDirtySched(ruleList, tcfg, stamps, tryMatch) {
  // Wake-up keys and fire()'s producedPreds MUST come from the same
  // function (factKeyOf, the lax fact-key space) — deriving one side from
  // strict triggerPreds made literal-fact consumers invisible to dirty
  // tracking (round-14 fuzz find). Rules with unknowable heads
  // (metavar/freevar patterns) stay permanently dirty.
  const predToRules = new Map();
  const alwaysDirty = new Set();
  for (const r of ruleList) {
    const preds = new Set();
    for (const p of (r.antecedent.linear || [])) {
      const pred = factKeyOf(p, tcfg.expTag);
      if (pred) preds.add(pred);
      else alwaysDirty.add(r);
    }
    for (const p of (r.antecedent.persistent || [])) {
      const pred = factKeyOf(p, tcfg.expTag);
      if (pred) preds.add(pred);
    }
    for (const pred of preds) {
      if (!predToRules.has(pred)) predToRules.set(pred, []);
      predToRules.get(pred).push(r);
    }
  }
  const act = new Map(ruleList.map(r => [r, null]));
  const ver = new Map(ruleList.map(r => [r, 0]));
  const dirty = new Set(ruleList);
  const cmp = (a, b) => stamps.cmp(a, b);      // activations are stamp ids

  // Binary min-heap of [activation, rule, version]; lazy deletion.
  const heap = [];
  const hLess = (i, j) => cmp(heap[i][0], heap[j][0]) < 0;
  const hSwap = (i, j) => { const t = heap[i]; heap[i] = heap[j]; heap[j] = t; };
  const hPush = (e) => {
    heap.push(e);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!hLess(i, p)) break;
      hSwap(i, p); i = p;
    }
  };
  const hPop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length) {
      heap[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1, r = l + 1;
        let s = i;
        if (l < heap.length && hLess(l, s)) s = l;
        if (r < heap.length && hLess(r, s)) s = r;
        if (s === i) break;
        hSwap(i, s); i = s;
      }
    }
    return top;
  };
  const hStale = () => heap.length > 0 &&
    (heap[0][2] !== ver.get(heap[0][1]) || act.get(heap[0][1]) === null);

  return {
    candidates(state, calc, matchOpts, tcfg) {
      for (const r of alwaysDirty) dirty.add(r);
      for (const r of dirty) {
        const m = tryMatch(r, state, calc, matchOpts, tcfg);
        act.set(r, m ? m.activation : null);
        const v = ver.get(r) + 1;
        ver.set(r, v);
        if (m) hPush([m.activation, r, v]);
      }
      dirty.clear();
      for (;;) {
        while (hStale()) hPop();
        if (heap.length === 0) return [];
        const aMin = heap[0][0];
        // Collect ALL live rules tied at aMin (pop, then push back), and
        // recompute their matches — θ is never cached (round 9).
        const popped = [];
        while (heap.length && !hStale() && cmp(heap[0][0], aMin) === 0) {
          popped.push(hPop());
          while (hStale()) hPop();
        }
        for (const e of popped) hPush(e);
        const out = [];
        for (const e of popped) {
          const m = tryMatch(e[1], state, calc, matchOpts, tcfg);
          if (m) out.push(m);
          else {
            // Cached activation no longer matches (should not happen —
            // dirty tracking covers every state change): drop and retry.
            act.set(e[1], null);
            ver.set(e[1], ver.get(e[1]) + 1);
          }
        }
        if (out.length > 0) return out;
      }
    },
    /** Live activation cache (rule -> stamp | null) — fresh right after
     *  candidates(); the acceleration signature reads it (TODO_0277). */
    activations() { return act; },
    markFired(m, fired) {
      // Additions and removals dirty uniformly: any rule whose pattern
      // mentions a touched predicate. New persistent facts can enable
      // arbitrary derived goals — dirty everything (rare, conservative).
      if (fired.producedPersistent) {
        for (const r of act.keys()) dirty.add(r);
        return;
      }
      const touched = new Set(fired.producedPreds);
      for (const hStr in m.consumed) {
        const pred = factKeyOf(refInner(Number(hStr)), tcfg.expTag);
        if (pred) touched.add(pred);
      }
      for (const pred of touched) {
        for (const r of (predToRules.get(pred) || [])) dirty.add(r);
      }
    },
  };
}

export { makeDirtySched };
export default { makeDirtySched };

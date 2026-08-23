/**
 * D16 productivity lint (Phase 5) — static Zeno guard for timed rule sets.
 *
 * Load-time analysis only: reads compiled rules + the timed config, never
 * touches a state. Split out of timed.js (round-15 F7 factoring) — the
 * scheduler fires rules; this file only warns about rule SETS.
 */

import Store from '../../kernel/store.js';
import { factKeyOf } from '../formula-utils.js';
import { INT_TAG } from './timed.js';
import { stampObserversCached } from './coalesce.js';

/**
 * Conservative load-time check for zero-delay rule cycles — the static
 * side of the D16 Zeno guard (TAPN circuit-condition analogue). Two tiers:
 *
 *   self-cycle: one zero-delay rule whose produced multiset covers its
 *     consumed multiset (it can re-enable itself forever at one instant);
 *   cycle: a cycle in the consumed→produced pred graph over zero-delay
 *     (rule, alternative) pseudo-rules, AFTER Farkas-style elimination —
 *     a pseudo-rule strictly decreasing a pred that no pseudo-rule
 *     net-produces can never appear in a repetitive firing vector, so it
 *     is removed to fixpoint (exact, Phase 6: clears winner-return duels
 *     whose cross-alternative edges otherwise fake a red→blue→red cycle).
 *
 * Sound as a WARNING, not complete: windows/read arcs/resource depletion
 * can break a flagged cycle (the duel's fight rule consumes two tokens and
 * produces one — token-decreasing, always eliminated), and anything the
 * lint cannot ground (variable delays, !_W counts, metavar heads) stays
 * QUIET rather than guessing. POSSESSED RULES (loli facts, Phase 6c) are
 * invisible to this static pass by nature — a state-born zero-delay cycle
 * is caught only by the runtime maxSteps Zeno guard.
 *
 * Returns [{ rule|rules, kind, via }] — the caller decides how to report.
 */
function lintProductivity(ruleList, tcfg) {
  const cmp = tcfg.availability.cmp, unit = tcfg.effect.unit();
  const findings = [];
  const edges = new Map();      // pred -> Set(pred), surviving zero-delay pseudo-rules
  const edgeRules = new Map();  // 'a→b' -> rule name
  const pseudo = [];            // (rule, alt) pseudo-rules: { rule, consumed, produced }

  for (const r of ruleList) {
    // ground-zero delay only; variable/positive delays are productive or unknowable
    if (r.delay) {
      if (r.delay.ground === undefined) continue;
      let d = r.delay.ground;
      if (tcfg.canonStamp) d = tcfg.canonStamp(d);
      if (!tcfg.isStamp(d) || cmp(d, unit) !== 0) continue;
    }
    const consumed = new Map();   // pred -> count
    let unknown = false;
    const reads = new Set(r.readOnly || []);
    for (const p of (r.antecedent.linear || [])) {
      if (reads.has(p)) continue;                       // reads reserve, never consume
      let body = p, count = 1;
      if (tcfg.expTag && Store.tag(body) === tcfg.expTag) {
        const g = Store.child(body, 0);
        if (Store.tag(g) === INT_TAG) count = Number(Store.child(g, 0));
        else { unknown = true; break; }                 // !_W — cohort-sized, quiet
        body = Store.child(body, 1);
      }
      const pred = factKeyOf(body);
      if (!pred) { unknown = true; break; }
      consumed.set(pred, (consumed.get(pred) || 0) + count);
    }
    if (unknown || consumed.size === 0) continue;

    const alts = r.weighted && r.consequentAlts ? r.consequentAlts : [r.consequent];
    let covers = false;
    const altMaps = [];
    for (const alt of alts) {
      const produced = new Map();
      let altUnknown = false;
      for (let pat of (alt.linear || [])) {
        let count = 1;
        if (tcfg.expTag && Store.tag(pat) === tcfg.expTag) {
          const g = Store.child(pat, 0);
          if (Store.tag(g) === INT_TAG) count = Number(Store.child(g, 0));
          else { altUnknown = true; break; }
          pat = Store.child(pat, 1);
        }
        const pred = factKeyOf(pat);
        if (!pred) { altUnknown = true; break; }
        produced.set(pred, (produced.get(pred) || 0) + count);
      }
      if (altUnknown) continue;                          // quiet on unknowable alts
      altMaps.push(produced);
      let coversAlt = true;
      for (const [pred, need] of consumed) {
        if ((produced.get(pred) || 0) < need) { coversAlt = false; break; }
      }
      if (coversAlt) covers = true;
    }
    if (covers) {
      findings.push({ kind: 'self-cycle', rule: r.name });
      continue;
    }
    for (const alt of altMaps) {
      pseudo.push({ rule: r.name, consumed, produced: alt });
    }
  }

  // Farkas-style elimination (Phase 6, exact): a same-instant infinite run
  // needs a repetitive firing vector x ≥ 0, x ≠ 0 over (rule, alt)
  // pseudo-rules with pointwise production ≥ consumption. If t strictly
  // decreases pred p and NO pseudo-rule net-produces p, every admissible x
  // has x_t = 0 (p's balance would go negative) — remove t and repeat.
  // This clears the combat duel (each alternative strictly depletes the
  // opposing side; alternating alts still drains the red+blue pool), which
  // the pred-graph alone mis-flagged via cross-alternative edges, while
  // keeping genuine cycles: their members are mutually net-replenished.
  // Conservative direction is unaffected: survivors may still be
  // non-repetitive — the cycle check below stays a WARNING.
  let pruned = true;
  while (pruned) {
    pruned = false;
    for (let i = pseudo.length - 1; i >= 0; i--) {
      const t = pseudo[i];
      for (const [p, need] of t.consumed) {
        if ((t.produced.get(p) || 0) >= need) continue;   // t does not decrease p
        const hasProducer = pseudo.some(s =>
          (s.produced.get(p) || 0) > (s.consumed.get(p) || 0));
        if (!hasProducer) { pseudo.splice(i, 1); pruned = true; break; }
      }
    }
  }
  for (const t of pseudo) {
    for (const a of t.consumed.keys()) {
      for (const b of t.produced.keys()) {
        if (!edges.has(a)) edges.set(a, new Set());
        edges.get(a).add(b);
        edgeRules.set(`${a}→${b}`, t.rule);
      }
    }
  }

  // cycle detection on the residual zero-delay graph (iterative DFS)
  const color = new Map();      // 0 unvisited implicit, 1 in-stack, 2 done
  for (const start of edges.keys()) {
    if (color.get(start)) continue;
    const stack = [[start, edges.get(start).values()]];
    color.set(start, 1);
    const path = [start];
    while (stack.length) {
      const top = stack[stack.length - 1];
      const nx = top[1].next();
      if (nx.done) { color.set(top[0], 2); stack.pop(); path.pop(); continue; }
      const b = nx.value;
      if (color.get(b) === 1) {
        const cyc = path.slice(path.indexOf(b)).concat(b);
        const rules = [...new Set(cyc.slice(0, -1).map((p, i) => edgeRules.get(`${p}→${cyc[i + 1]}`)))];
        findings.push({ kind: 'cycle', rules, via: cyc.join(' → ') });
        for (const k of edges.keys()) if (!color.get(k)) color.set(k, 2);   // one report is enough
        return findings;
      }
      if (!color.get(b) && edges.has(b)) {
        color.set(b, 1); path.push(b);
        stack.push([b, edges.get(b).values()]);
      }
    }
  }
  return findings;
}

/**
 * C1 chain-collapse advisory (TODO_0278) — the authoring-time dual of the
 * demoted graded chain fusion: where fusing `a -o {b}@d1` with
 * `b -o {c}@d2` would be SOUND, tell the author to collapse the
 * intermediate vocabulary by hand instead of the engine fusing it.
 *
 * Sound-fragment criterion (C1): b collapses iff its sole consumer is
 * UNCONDITIONAL — b its only linear premise (ground count), no windows,
 * no reads — and nothing else observes b: no second consumer, no read
 * arc, no stamp binding anywhere (the coalesce observer oracle), no
 * whole-pool bind (!_W observes the total), no mention inside a
 * consequent-embedded formula (a minted loli/menu could consume it), no
 * draw-conditional production (weighted alts). Same conservatism as the
 * productivity lint: anything unknowable stays QUIET, and possessed
 * rules/menus already in the state are invisible to a static pass.
 *
 * Advisory only — rides the API as `timedAdvice`, never a warning:
 * destruction/regime semantics may WANT the intermediate to exist
 * (C1's building-guard argument), so collapsing is the author's call.
 *
 * Returns [{ kind: 'chain-collapse', pred, producers, consumer }].
 */
function lintChainCollapse(ruleList, tcfg) {
  const observers = stampObserversCached(ruleList, tcfg);
  if (observers.all) return [];
  const producers = new Map();   // pred -> Set(rule name), plain-fact outputs
  const consumers = new Map();   // pred -> [{ rule, sole }]
  const vetoed = new Set();      // read / !_W / preserved / weighted production
  const opaque = new Set();      // mentioned inside consequent-embedded formulas
  let unknowable = false;

  const mentions = (h, depth = 0) => {
    if (typeof h !== 'number' || !Store.isTerm(h)) return;
    if (depth > 64) { unknowable = true; return; }
    const k = factKeyOf(h, tcfg.expTag, tcfg.stampTag);
    if (k) opaque.add(k);
    const n = Store.arity(h);
    for (let i = 0; i < n; i++) mentions(Store.child(h, i), depth + 1);
  };

  // plain fact = atom or user predicate once grades/stamps are unwrapped;
  // anything else (loli, menu, bang, monad) is a formula that may mint rules
  const isFact = (h) => {
    let body = h;
    if (tcfg.expTag && Store.tag(body) === tcfg.expTag) body = Store.child(body, 1);
    if (tcfg.stampTag && Store.tag(body) === tcfg.stampTag) body = Store.child(body, 0);
    if (typeof body !== 'number' || !Store.isTerm(body)) return false;
    return Store.tag(body) === 'atom' || Store.tagId(body) >= Store.PRED_BOUNDARY;
  };

  for (const r of ruleList) {
    const reads = new Set(r.readOnly || []);
    const linear = r.antecedent.linear || [];
    const hasWindow = !!(r.windows &&
      ((r.windows.before && r.windows.before.length) ||
       (r.windows.after && r.windows.after.length)));
    const taken = new Set();
    for (const p of linear) {
      const meta = r.linearMeta && r.linearMeta[p];
      const pred = meta ? meta.pred : factKeyOf(p, tcfg.expTag, tcfg.stampTag);
      if (!pred) { unknowable = true; continue; }
      if (reads.has(p)) { vetoed.add(pred); continue; }   // read arc = observation
      if (tcfg.expTag && Store.tag(p) === tcfg.expTag) {
        const g = Store.child(p, 0);
        if (Store.tag(g) !== INT_TAG) vetoed.add(pred);    // !_W binds the total
      }
      taken.add(pred);
    }
    const sole = taken.size === 1 && linear.length === 1 &&
                 reads.size === 0 && !hasWindow;
    for (const pred of taken) {
      if (!consumers.has(pred)) consumers.set(pred, []);
      consumers.get(pred).push({ rule: r.name, sole });
    }
    const alts = r.weighted && r.consequentAlts ? r.consequentAlts : [r.consequent];
    for (const alt of alts) {
      for (const p of (alt.linear || [])) {
        if (!isFact(p)) { mentions(p); continue; }
        const pred = factKeyOf(p, tcfg.expTag, tcfg.stampTag);
        if (!pred) { unknowable = true; continue; }
        if (!producers.has(pred)) producers.set(pred, new Set());
        producers.get(pred).add(r.name);
        if (r.weighted) vetoed.add(pred);                  // draw-conditional
        if (taken.has(pred)) vetoed.add(pred);             // preserved/self-feeding
      }
      for (const p of (alt.persistent || [])) if (!isFact(p)) mentions(p);
    }
  }
  if (unknowable) return [];

  const advice = [];
  for (const [pred, cs] of consumers) {
    if (cs.length !== 1 || !cs[0].sole) continue;
    const ps = producers.get(pred);
    if (!ps || ps.size === 0) continue;
    if (vetoed.has(pred) || opaque.has(pred) || observers.preds.has(pred)) continue;
    advice.push({ kind: 'chain-collapse', pred, producers: [...ps].sort(), consumer: cs[0].rule });
  }
  return advice;
}

export { lintProductivity, lintChainCollapse };

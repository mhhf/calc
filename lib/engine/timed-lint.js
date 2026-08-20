/**
 * D16 productivity lint (Phase 5) — static Zeno guard for timed rule sets.
 *
 * Load-time analysis only: reads compiled rules + the timed config, never
 * touches a state. Split out of timed.js (round-15 F7 factoring) — the
 * scheduler fires rules; this file only warns about rule SETS.
 */

import Store from '../kernel/store.js';
import { factKeyOf } from './formula-utils.js';

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
        if (Store.tag(g) === 'binlit') count = Number(Store.child(g, 0));
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
          if (Store.tag(g) === 'binlit') count = Number(Store.child(g, 0));
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

export { lintProductivity };
export default { lintProductivity };

/**
 * Shift-degree (translation-covariance) analysis — TODO_0277 soundness audit.
 *
 * Rebase and orbit acceleration translate the time origin: every live stamp
 * shifts by B. A rule is sound under that translation iff each of its
 * syntactic positions has the right SHIFT DEGREE — how its value moves when
 * every matched stamp moves by B:
 *
 *   window bounds (after E / before E)   degree 1  (absolute time points)
 *   delay, woplus weights, counts        degree 0  (durations / scalars)
 *   pattern inner terms, other goals     degree 0  (stored values never shift)
 *
 * Degrees of rule variables derive from their binding sites — a var bound at
 * the stamp position of a linear pattern has degree 1, every other binding
 * has degree 0 — and combine additively through the q-op goals that window
 * lowering synthesizes (`!plus Q c R` gives deg R = deg Q + deg c). Anything
 * else is opaque: degree unknown, analysis refuses.
 *
 * This is the mechanized analog of the timed-automata result that zone
 * extrapolation is unsound for diagonal constraints (Bouyer-Dufourd-Fleury-
 * Petit, FORMATS 2005): `before (Q1+Q2)` has degree 2 and is REFUSED, never
 * silently mis-shifted. Ground bounds (`after 3`) have degree 0 in a
 * degree-1 position — the program is anchored to absolute time and is not
 * translation-invariant (confirmed divergence repros in
 * tests/engine/till-covariance.test.js).
 *
 * Two consumers, two strengths:
 *  - rebaseSafe(rule): FULL covariance — all window bounds degree 1, delay/
 *    weights degree 0, and no degree-1 var leaking into a non-shifting
 *    position (inner terms, opaque persistent goals, consequents).
 *  - beforeBounds(rule): per-`before`-window classification for the
 *    acceleration cap — 'covariant' (degree 1: the deadline moves with the
 *    cycle), { ground } (absolute: cap the jump below it), or 'unknown'
 *    (refuse certification). `after` bounds need nothing here: they JOIN the
 *    activation max, so an after-pinned match is visible in the checkpoint's
 *    frontier-relative activation signature and can never alias two
 *    sightings (time-inhomogeneity shows up; `before` is a silent filter —
 *    that asymmetry was the audit's confirmed acceleration bug).
 *
 * The q-op degree table comes from the calculus (cc.shiftOps: tag →
 * 'add' | 'sub' | 'scale'); absent, only directly stamp-bound window vars
 * are covariant — conservative, never unsound.
 */

import Store from '../../kernel/store.js';

const _cache = new WeakMap();   // rule -> analysis (tcfg is fixed per calculus)

function _isVar(h) {
  const t = Store.tag(h);
  return t === 'metavar' || t === 'freevar';
}

function _hasVar(h, depth = 0) {
  if (typeof h !== 'number' || !Store.isTerm(h) || depth > 64) return depth > 64;
  if (_isVar(h)) return true;
  const n = Store.arity(h);
  for (let i = 0; i < n; i++) if (_hasVar(Store.child(h, i), depth + 1)) return true;
  return false;
}

/** Analyze one compiled rule (or compiled loli). Cached. */
function analyze(rule, tcfg) {
  let a = _cache.get(rule);
  if (a) return a;
  const slots = rule.metavarSlots || {};

  // Degree-1 binding sites: vars at the stamp position of linear patterns.
  const stampIdx = new Set();
  for (const p of (rule.antecedent.linear || [])) {
    const meta = rule.linearMeta && rule.linearMeta[p];
    const body = meta ? meta.body : p;
    if (Store.tag(body) === tcfg.stampTag) {
      const sv = Store.child(body, 1);
      if (_isVar(sv) && slots[sv] !== undefined) stampIdx.add(slots[sv]);
    }
  }

  // q-op provenance: output slot -> { a, b, kind } (window-lowering goals).
  const ops = tcfg.shiftOps || null;
  const defs = new Map();
  for (let g of (rule.antecedent.persistent || [])) {
    if (tcfg.expTag && Store.tag(g) === tcfg.expTag) g = Store.child(g, 1);
    const kind = ops ? ops[Store.tag(g)] : undefined;
    if (!kind || Store.arity(g) !== 3) continue;
    const v = Store.child(g, 2);
    if (_isVar(v) && slots[v] !== undefined) {
      defs.set(slots[v], { a: Store.child(g, 0), b: Store.child(g, 1), kind });
    }
  }

  const memo = new Map();
  const degTerm = (h, fuel) => {
    if (_isVar(h)) return slots[h] !== undefined ? degSlot(slots[h], fuel) : NaN;
    return _hasVar(h) ? NaN : 0;          // ground literal/term
  };
  const degSlot = (i, fuel) => {
    if (fuel <= 0) return NaN;
    if (memo.has(i)) return memo.get(i);
    memo.set(i, NaN);                      // cycle guard
    let d;
    if (stampIdx.has(i)) {
      d = defs.has(i) ? NaN : 1;           // doubly-constrained — refuse
    } else if (defs.has(i)) {
      const { a, b, kind } = defs.get(i);
      const da = degTerm(a, fuel - 1), db = degTerm(b, fuel - 1);
      if (Number.isNaN(da) || Number.isNaN(db)) d = NaN;
      else if (kind === 'add') d = da + db;
      else if (kind === 'sub') d = da - db;
      else d = (da === 0 && db === 0) ? 0 : NaN;   // 'scale': nonlinear
    } else d = 0;                          // bound from a non-shifting source
    memo.set(i, d);
    return d;
  };
  const degWindow = (w) => (w.ground !== undefined ? 0 : degSlot(w.slot, 64));

  // ── rebaseSafe: full covariance ──────────────────────────────────
  let reason = null;
  const fail = (r) => { if (!reason) reason = r; };
  if (rule.windows) {
    for (const w of rule.windows.after) {
      if (degWindow(w) !== 1) fail('window bound is not shift-degree 1 (absolute or diagonal time reference)');
    }
    for (const w of rule.windows.before) {
      if (degWindow(w) !== 1) fail('window bound is not shift-degree 1 (absolute or diagonal time reference)');
    }
  }
  if (rule.delay && rule.delay.slot !== undefined && degSlot(rule.delay.slot, 64) !== 0) {
    fail('delay derives from a stamp (degree != 0)');
  }
  for (const alt of (rule.consequentAlts || [rule.consequent])) {
    if (alt && alt.weight && alt.weight.syms) {
      for (const s of alt.weight.syms) {
        if (degSlot(s.slot, 64) !== 0) fail('woplus weight derives from a stamp');
      }
    }
  }
  // Degree-1 leakage: a stamp-bound var used where values do not shift.
  if (!reason) {
    const deg1 = new Set([...stampIdx].filter(i => degSlot(i, 64) === 1));
    for (const [i] of defs) if (degSlot(i, 64) === 1) deg1.add(i);
    if (deg1.size > 0) {
      const leaks = (h, depth = 0) => {
        if (typeof h !== 'number' || !Store.isTerm(h) || depth > 64) return depth > 64;
        if (_isVar(h)) return slots[h] !== undefined && deg1.has(slots[h]);
        const n = Store.arity(h);
        for (let i = 0; i < n; i++) if (leaks(Store.child(h, i), depth + 1)) return true;
        return false;
      };
      for (const p of (rule.antecedent.linear || [])) {
        const meta = rule.linearMeta && rule.linearMeta[p];
        const body = meta ? meta.body : p;
        const inner = Store.tag(body) === tcfg.stampTag ? Store.child(body, 0) : body;
        if (leaks(inner)) fail('stamp-bound var occurs in a pattern inner term');
        if (Store.tag(body) === tcfg.stampTag) {
          const sv = Store.child(body, 1);
          if (!_isVar(sv) && _hasVar(sv)) fail('structured stamp pattern');
        }
      }
      for (let g of (rule.antecedent.persistent || [])) {
        let b = g;
        if (tcfg.expTag && Store.tag(b) === tcfg.expTag) b = Store.child(b, 1);
        if (ops && ops[Store.tag(b)] && Store.arity(b) === 3) continue;   // q-op defs shift-covariantly
        if (leaks(b)) fail('stamp-bound var occurs in an opaque persistent goal');
      }
      for (const alt of (rule.consequentAlts || [rule.consequent])) {
        if (!alt) continue;
        for (const p of (alt.linear || [])) if (leaks(p)) fail('stamp-bound var occurs in a produced term');
        for (const p of (alt.persistent || [])) if (leaks(p)) fail('stamp-bound var occurs in a produced persistent fact');
      }
      if ((rule.existentialSlots || []).length > 0) {
        fail('existential outputs have opaque stamp provenance');
      }
    }
  }

  // ── beforeBounds: per-before-window classification for the accel cap ──
  const beforeBounds = [];
  if (rule.windows) {
    for (const w of rule.windows.before) {
      if (w.ground !== undefined) beforeBounds.push({ ground: w.ground });
      else if (degSlot(w.slot, 64) === 1) beforeBounds.push({ covariant: true });
      else beforeBounds.push({ unknown: true });
    }
  }

  a = { rebaseSafe: reason === null, reason, beforeBounds };
  _cache.set(rule, a);
  return a;
}

/** First non-covariant rule of a list (or null). Cached per rule. */
function firstNonCovariant(ruleList, tcfg) {
  for (const r of ruleList) {
    const a = analyze(r, tcfg);
    if (!a.rebaseSafe) return { rule: r, reason: a.reason };
  }
  return null;
}

export { analyze, firstNonCovariant };

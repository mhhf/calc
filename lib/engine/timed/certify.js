/**
 * T2-applicability certifier (TODO_0293 (a), settle-optimality §11) —
 * per-program/per-state contention-freedom checks, so the engine can
 * CERTIFY that the optimality theorem applies rather than assume it.
 *
 * Two tiers, per the paper's hierarchy (§3):
 *
 *   structural conflict-freedom (static, state-independent): each linear
 *     predicate consumed by at most one rule, matched at most once per
 *     firing, plain single takes, no whole-bind, no weighted rules, no
 *     zero-delay rules (the extra guard keeps clause 3 vacuous). The
 *     one-shot-edge discipline (§8.1) — depot.gill's hop rules certify
 *     here.
 *
 *   relaxation check (state-dependent): compute the monotone relaxation's
 *     firing set — the same rule set with consumption disabled, a least
 *     fixed point independent of scheduling — then test PAIRWISE
 *     independence of the firings (clauses 1–3 of §3 against relaxation
 *     supplies). This is what the run-state quantification cannot see
 *     (E2: a deferred producer's demand is visible only here).
 *
 * CONSERVATIVE by construction — a certificate is sound, a refusal is
 * not a refutation: unprovable-now goals retry each round (monotone),
 * unsupported shapes (whole-bind, counted takes, weighted alternatives,
 * existential consequents) refuse with a reason instead of guessing, and
 * clause 3 flags any zero-delay feed without checking instant equality.
 * Never runs settle; the relaxation is its own tiny fixpoint over the
 * declared rule data.
 */

'use strict';

import Store from '../../kernel/store.js';
import { matchIndexed, undoSave, undoRestore } from '../../kernel/unify.js';
import { apply } from '../../kernel/substitute.js';
import { isGround } from '../pattern-utils.js';

/** Static tier: the one-shot-edge discipline. */
function structuralConflictFree(ruleList, tcfg) {
  const consumedBy = new Map();
  const unit = tcfg.effect.unit();
  for (const r of ruleList) {
    if (r.weighted) return { ok: false, reason: `rule '${r.name}' is weighted (internal choice)` };
    if (r.existentialSlots && r.existentialSlots.length) {
      return { ok: false, reason: `rule '${r.name}' has existential consequents` };
    }
    // zero-delay guard (keeps clause 3 vacuous): the delay must be GROUND
    // and strictly positive — a delayless rule fires AT its activation
    // (implicit zero), and a slot-bound delay may be zero at runtime.
    let d = r.delay ? r.delay.ground : undefined;
    if (d === undefined) {
      return { ok: false, reason: `rule '${r.name}' has no ground delay (implicit or variable zero-delay possible)` };
    }
    if (tcfg.canonStamp) d = tcfg.canonStamp(d);
    if (!tcfg.isStamp(d) || tcfg.availability.cmp(d, unit) <= 0) {
      return { ok: false, reason: `rule '${r.name}' has zero delay (instant feeding possible)` };
    }
    const reads = new Set(r.readOnly || []);
    const seen = new Set();
    for (const p of r.antecedent.linear || []) {
      if (reads.has(p)) continue;
      const meta = r.linearMeta && r.linearMeta[p];
      const pred = meta && meta.pred;
      if (!pred) return { ok: false, reason: `unclassifiable premise in '${r.name}'` };
      if (meta.countVar) return { ok: false, reason: `whole-bind on '${pred}' in '${r.name}'` };
      if (meta.countTake > 1) return { ok: false, reason: `counted take on '${pred}' in '${r.name}'` };
      // per-PREDICATE discipline models at most one firing per rule — a
      // non-ground consumed premise can instantiate to several co-enabled
      // firings of the SAME rule sharing another premise's token, which
      // this tier cannot see (audit witness: p X * g, facts p 1 / p 2,
      // one g). State-dependent → relaxation tier.
      if (!isGround(meta.body !== undefined ? meta.body : p)) {
        return { ok: false, reason: `non-ground consumed premise '${pred}' in '${r.name}' (same-rule multi-instance contention possible)` };
      }
      if (seen.has(pred)) return { ok: false, reason: `'${pred}' matched twice in '${r.name}'` };
      seen.add(pred);
      const prev = consumedBy.get(pred);
      if (prev && prev !== r.name) {
        return { ok: false, reason: `'${pred}' consumed by both '${prev}' and '${r.name}'` };
      }
      consumedBy.set(pred, r.name);
    }
  }
  // read-vs-consume cross-check (independence clause 2): a consumed
  // predicate that some rule READS can starve the reader — this tier has
  // no supply information, so hand the program to the relaxation.
  for (const r of ruleList) {
    const reads = new Set(r.readOnly || []);
    for (const p of r.antecedent.linear || []) {
      if (!reads.has(p)) continue;
      const meta = r.linearMeta && r.linearMeta[p];
      const pred = meta && meta.pred;
      if (!pred) return { ok: false, reason: `unclassifiable read premise in '${r.name}'` };
      if (consumedBy.has(pred)) {
        return { ok: false, reason: `'${pred}' consumed by '${consumedBy.get(pred)}' and read by '${r.name}' (read starvation possible)` };
      }
    }
  }
  return { ok: true };
}

const fk = (inner, stamp) => `${inner}|${stamp}`;

/**
 * The monotone relaxation's firing set + pairwise independence.
 * Facts are (inner, stampTerm) with supplies; nothing is ever removed.
 */
function relaxationCertify(engineCalc, ruleList, tcfg, state, horizon, opts = {}) {
  const maxFirings = opts.maxFirings || 2000;
  const cmp = tcfg.availability.cmp;
  const unit = tcfg.effect.unit();
  const ST = tcfg.stampTag;

  // unsupported shapes refuse loudly (conservative, never guess)
  for (const r of ruleList) {
    if (r.weighted) return { certified: false, method: 'relaxation', reason: `rule '${r.name}' is weighted` };
    if (r.existentialSlots && r.existentialSlots.length) {
      return { certified: false, method: 'relaxation', reason: `rule '${r.name}' has existential consequents` };
    }
    for (const p of r.antecedent.linear || []) {
      const meta = r.linearMeta && r.linearMeta[p];
      if (meta && meta.countVar) {
        return { certified: false, method: 'relaxation', reason: `whole-bind in '${r.name}'` };
      }
      if (meta && meta.countTake > 1) {
        return { certified: false, method: 'relaxation', reason: `counted take in '${r.name}'` };
      }
    }
  }

  // fact table: key → { inner, stamp, supply }
  const facts = new Map();
  const addFact = (inner, stamp, n = 1) => {
    const key = fk(inner, stamp);
    const e = facts.get(key);
    if (e) e.supply += n;
    else facts.set(key, { inner, stamp, supply: n });
  };
  for (const k in state.linear || {}) {
    const h = Number(k);
    if (Store.tag(h) === ST) {
      let s = Store.child(h, 1);
      if (tcfg.canonStamp) s = tcfg.canonStamp(s);
      addFact(Store.child(h, 0), s, state.linear[k]);
    } else addFact(h, unit, state.linear[k]);
  }
  const persistent = new Set(Object.keys(state.persistent || {}).map(Number));

  const winTerm = (w, theta) => (w.ground !== undefined ? w.ground : theta[w.slot]);
  const pairsOf = (slots, theta) => {
    const out = [];
    for (const mv of Object.keys(slots)) {
      const v = theta[slots[mv]];
      if (v !== undefined) out.push([Number(mv), v]);
    }
    return out;
  };

  const firings = [];
  const seenFire = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const r of ruleList) {
      const reads = new Set(r.readOnly || []);
      const linear = r.antecedent.linear || [];
      const theta = new Array(r.metavarCount || 0).fill(undefined);
      const slots = r.metavarSlots || {};
      const factList = [...facts.values()];

      // recursive assignment enumeration over the fact table
      const chosen = [];
      const enumerate = (i) => {
        if (firings.length >= maxFirings) return;
        if (i === linear.length) { attempt(); return; }
        const p = linear[i];
        const meta = r.linearMeta && r.linearMeta[p];
        const body = meta ? meta.body : p;
        const bodyIsAt = Store.tag(body) === ST;
        for (const f of factList) {
          const save = undoSave();
          const ok = bodyIsAt
            ? (matchIndexed(Store.child(body, 0), f.inner, theta, slots) &&
               matchIndexed(Store.child(body, 1), f.stamp, theta, slots))
            : matchIndexed(body, f.inner, theta, slots);
          if (ok) {
            chosen.push({ fact: f, read: reads.has(p) });
            enumerate(i + 1);
            chosen.pop();
          }
          undoRestore(theta, save);
        }
      };

      const attempt = () => {
        // activation = join of premise stamps and after-bounds
        let a = unit;
        for (const c of chosen) if (cmp(c.fact.stamp, a) > 0) a = c.fact.stamp;
        for (const w of r.windows?.after || []) {
          const t = winTerm(w, theta);
          if (t === undefined) return;
          const tc = tcfg.canonStamp ? tcfg.canonStamp(t) : t;
          if (!tcfg.isStamp(tc)) return;
          if (cmp(tc, a) > 0) a = tc;
        }
        if (cmp(a, horizon) > 0) return;
        for (const w of r.windows?.before || []) {
          const t = winTerm(w, theta);
          if (t === undefined) return;
          const tc = tcfg.canonStamp ? tcfg.canonStamp(t) : t;
          if (!tcfg.isStamp(tc) || cmp(a, tc) >= 0) return;
        }
        // persistent goals: state facts or the program's clause derivation
        const bindPairs = pairsOf(slots, theta);
        for (const g of r.antecedent.persistent || []) {
          let gg = apply(g, bindPairs);
          for (let i = 0; i < 8; i++) { const n = apply(gg, bindPairs); if (n === gg) break; gg = n; }
          if (persistent.has(gg)) continue;
          try {
            const res = engineCalc.prove(gg);
            if (res && res.success) continue;
          } catch { /* fallthrough */ }
          return;
        }
        // delay + done
        let done = a;
        if (r.delay) {
          let d = r.delay.ground !== undefined ? r.delay.ground : theta[r.delay.slot];
          if (d === undefined) return;
          if (tcfg.canonStamp) d = tcfg.canonStamp(d);
          if (!tcfg.isStamp(d)) return;
          done = tcfg.effect.compose(a, d);
        }
        const consumedKeys = [], readKeys = [];
        for (const c of chosen) {
          (c.read ? readKeys : consumedKeys).push(fk(c.fact.inner, c.fact.stamp));
        }
        const id = `${r.name}|${theta.join(',')}|${[...consumedKeys].sort().join(';')}`;
        if (seenFire.has(id)) return;
        seenFire.add(id);
        // fire (monotone): add produced, never remove
        const producedKeys = [];
        for (const q of r.consequent.linear || []) {
          let gq = apply(q, bindPairs);
          for (let i = 0; i < 8; i++) { const n = apply(gq, bindPairs); if (n === gq) break; gq = n; }
          if (Store.tag(gq) === ST) {
            let s = Store.child(gq, 1);
            if (tcfg.canonStamp) s = tcfg.canonStamp(s);
            addFact(Store.child(gq, 0), s);
            producedKeys.push(fk(Store.child(gq, 0), s));
          } else {
            addFact(gq, done);
            producedKeys.push(fk(gq, done));
          }
        }
        for (const q of r.consequent.persistent || []) {
          let gq = apply(q, bindPairs);
          for (let i = 0; i < 8; i++) { const n = apply(gq, bindPairs); if (n === gq) break; gq = n; }
          persistent.add(gq);
        }
        firings.push({
          rule: r.name, activation: a,
          zeroDelay: cmp(done, a) === 0,
          consumedKeys, readKeys, producedKeys,
        });
        changed = true;
      };

      enumerate(0);
      if (firings.length >= maxFirings) {
        return { certified: false, method: 'relaxation', reason: `relaxation exceeded ${maxFirings} firings` };
      }
    }
  }

  // pairwise independence over the relaxation's firing set
  const contended = [];
  const flag = (i, j, why) => {
    if (contended.length < 16) {
      contended.push({ a: firings[i].rule, b: firings[j].rule, why });
    }
  };
  for (let i = 0; i < firings.length; i++) {
    for (let j = i + 1; j < firings.length; j++) {
      const A = firings[i], B = firings[j];
      // clause 1: combined take within supply, per shared fact
      for (const key of A.consumedKeys) {
        if (!B.consumedKeys.includes(key)) continue;
        const tA = A.consumedKeys.filter(k => k === key).length;
        const tB = B.consumedKeys.filter(k => k === key).length;
        if (tA + tB > facts.get(key).supply) flag(i, j, `demand overlap on ${key}`);
      }
      // clause 2: consumption below the other's read demand
      const readStarve = (X, Y) => {
        for (const key of X.consumedKeys) {
          if (!Y.readKeys.includes(key)) continue;
          const t = X.consumedKeys.filter(k => k === key).length;
          const n = Y.readKeys.filter(k => k === key).length;
          if (t + n > facts.get(key).supply) flag(i, j, `read starvation on ${key}`);
        }
      };
      readStarve(A, B); readStarve(B, A);
      // clause 3: zero-delay production feeding the other (conservative:
      // instant equality not checked)
      const feeds = (X, Y) => {
        if (!X.zeroDelay) return;
        for (const key of X.producedKeys) {
          if (Y.consumedKeys.includes(key) || Y.readKeys.includes(key)) {
            flag(i, j, `instant feed via ${key}`);
          }
        }
      };
      feeds(A, B); feeds(B, A);
    }
  }

  return {
    certified: contended.length === 0,
    method: 'relaxation',
    firings: firings.length,
    ...(contended.length ? { contended } : {}),
  };
}

/**
 * The certifier: structural tier first (state-independent), relaxation
 * tier second. `certified: true` means T2 applies — settle's stamps are
 * the semiring least fixed point σ* below the horizon.
 */
function certifyContention(engineCalc, ruleList, tcfg, state, horizon, opts = {}) {
  const st = structuralConflictFree(ruleList, tcfg);
  if (st.ok) return { certified: true, method: 'structural' };
  const rx = relaxationCertify(engineCalc, ruleList, tcfg, state, horizon, opts);
  return { ...rx, structural: st.reason };
}

export { structuralConflictFree, relaxationCertify, certifyContention };
export default { structuralConflictFree, relaxationCertify, certifyContention };

/**
 * Periodic-orbit acceleration — O(1) deep-time settling (TODO_0277,
 * approach 4 / [[0190]] abstract acceleration, exact-orbit instance).
 *
 * A settling system whose live state RECURS (exactly, modulo a global time
 * translation and modulo pure accumulators) is periodic: the continuation
 * from the recurrence is the continuation from the first sighting shifted
 * by the period. settle can then jump n whole periods in O(state) instead
 * of firing n·E events.
 *
 * Soundness conditions (all checked, bail otherwise):
 *  - EXACT recurrence: the canonical signature (every linear fact with its
 *    frontier-relative stamp, every persistent fact) matches string-equal —
 *    no hashing shortcut, no false positives.
 *  - SINKS only may drift: predicates that appear in NO rule antecedent
 *    (nor any state-loli antecedent, nor any wildcard-pattern rule in
 *    scope) are unmatchable accumulators; their unit-stamp counts are
 *    excluded from the signature and extrapolated linearly. Any wildcard
 *    pattern in the rule set ⇒ no sinks ⇒ recurrence requires full
 *    equality (acceleration usually inert — correct by construction).
 *  - DETERMINISM over the cycle: no multi-candidate tie (PRF chooser) and
 *    no weighted (woplus) firing since the first sighting — those draws
 *    read the state hash, which drifts with sink counts, so replays could
 *    diverge. Matching itself is sink-blind, hence the guard suffices.
 *  - the translation only touches LIVE stamps: unit-stamped facts of
 *    coalescible predicates are dead (coalesce.js invariant) and stay at
 *    the unit; excluded predicates (windows observe their stamps) shift.
 *
 * Contract change under acceleration: events inside jumped periods are
 * NOT emitted — the result carries `accelerated: [{ frontier, period,
 * cycles, skippedEvents }]` instead. States, schedules and all later
 * observations are exactly those of the unaccelerated run.
 *
 * Orbit certificates (TODO_0278 A1): a proof that covers a settle's exit
 * can be minted ({ fingerprint, sigKey, period, sinkDelta, cycleEvents }),
 * saved next to the state, and resumed as one validated jump — see
 * probeOrbit/tryResume/mint and doc/documentation/timed-performance.md.
 * Raw Store hashes in the certificate are pinned by the arena-prefix
 * fingerprint; the state itself must travel by a mechanism that preserves
 * hash identity (same process, same-source reload, store-binary restore).
 */

import Store from '../../kernel/store.js';
import { factKeyOf } from '../formula-utils.js';
import { collectObservers } from './coalesce.js';
import { analyze as covariance } from './covariance.js';
import { putRat } from '../../kernel/rat-term.js';
import { ratParts } from '../theories/ratlit-theory.js';
import { add as rAdd, sub as rSub, mul as rMul, cmp as rCmp } from '../../rat.js';

const I32_FENCE = 0x40000000;    // run-length counts are Int32 — loud fence

/**
 * Sink predicates: heads no ALIVE rule (or state loli) can ever match.
 *
 * Aliveness is a reachability fixpoint over the current state: a rule is
 * alive iff every linear antecedent predicate is present in the state or
 * producible by some alive rule (persistent goals conservatively assumed
 * provable; wildcard patterns conservatively satisfiable). A rule dead
 * under this closure can never fire again within the call — availability
 * only ever shrinks below the closure, and settle admits no external
 * input — so predicates consumed only by dead rules are true accumulators.
 */
function sinkPreds(ruleList, stateLolis, compileLoli, tcfg, state, frontierHash) {
  const rules = stateLolis && compileLoli
    ? [...ruleList, ...stateLolis.map(e => compileLoli(e.inner))]
    : ruleList;
  // Expired-deadline deadness: a ground `before N` bound with N ≤ frontier
  // can never pass again (pending activations only grow) — the rule is
  // call-dead AND stays dead across calls (time is monotone), so it may
  // not block sinkhood or freeze its predicates.
  const cmp = tcfg.availability.cmp;
  const canon = tcfg.canonStamp || ((h) => h);
  const expired = (r) => frontierHash !== undefined && !!r.windows &&
    r.windows.before.some(w => w.ground !== undefined && cmp(canon(w.ground), frontierHash) <= 0);
  const specs = rules.map((r) => {
    if (expired(r)) return { preds: [], wild: false, out: new Set(), dead: true };
    const preds = [];
    let wild = false;
    for (const p of (r.antecedent.linear || [])) {
      const meta = r.linearMeta && r.linearMeta[p];
      const pred = meta ? meta.pred : factKeyOf(p, tcfg.expTag);
      if (pred) preds.push(pred);
      else wild = true;
    }
    const out = new Set();
    const alts = r.weighted && r.consequentAlts ? r.consequentAlts : [r.consequent];
    for (const alt of alts) {
      for (const pat of (alt.linear || [])) {
        const pred = factKeyOf(pat, tcfg.expTag);
        if (pred) out.add(pred);
      }
    }
    return { preds, wild, out };
  });
  const avail = new Set();
  const present = (p) => state.groupForPred(p).length > 0;
  const alive = new Array(specs.length).fill(false);
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < specs.length; i++) {
      if (alive[i]) continue;
      const s = specs[i];
      if (s.dead) continue;
      let ok = true;
      for (const p of s.preds) {
        if (!avail.has(p) && !present(p)) { ok = false; break; }
      }
      if (!ok) continue;
      alive[i] = true;
      changed = true;
      for (const p of s.out) if (!avail.has(p)) avail.add(p);
    }
  }
  const inAnte = new Set();
  let wildcard = false;
  for (let i = 0; i < specs.length; i++) {
    if (!alive[i]) continue;
    for (const p of specs[i].preds) inAnte.add(p);
    if (specs[i].wild) wildcard = true;
  }
  // Capped-stock candidates (surplus abstraction): matchable preds whose
  // every ALIVE matcher takes a BOUNDED count — no countVar (!_W binds the
  // actual total, count-observing) — with cap = the largest single-rule
  // need. Above the cap, matching is count-blind, so the surplus behaves
  // like a sink PROVIDED the pool never dips below the cap over the cycle
  // (validated by the caller's interval minima).
  const caps = new Map();
  if (!wildcard) {
    const bad = new Set();
    for (let i = 0; i < specs.length; i++) {
      if (!alive[i]) continue;
      const r = rules[i];
      const need = new Map();
      for (const p of (r.antecedent.linear || [])) {
        const meta = r.linearMeta && r.linearMeta[p];
        const pred = meta ? meta.pred : factKeyOf(p, tcfg.expTag);
        if (!pred) continue;
        if (meta && meta.countVar) { bad.add(pred); continue; }
        const take = (meta && meta.countTake) || 1;
        need.set(pred, (need.get(pred) || 0) + take);
      }
      for (const [p, n] of need) {
        if (n > (caps.get(p) || 0)) caps.set(p, n);
      }
    }
    for (const p of bad) caps.delete(p);
  }
  const aliveRules = rules.filter((_, i) => alive[i]);
  return { inAnte, wildcard, caps, aliveRules };
}

/**
 * Exact canonical signature of a live timed State at `frontier`.
 * Returns { key, sinks: Map(innerHash -> count) }. Sink facts must sit at
 * the unit stamp (coalesced) to be abstracted; a stamped sink fact stays
 * in the key (still exact, merely less abstraction).
 */
/**
 * cls: pred classification for the orbit —
 *   dead(p)   coalescible: unit-stamp facts are translation-INVARIANT
 *             fixtures ('@A' entries; sink/cap abstraction applies here)
 *   frozen(p) excluded by some rule but observed by NO alive rule: inert
 *             this call, stamps recorded ABSOLUTE (fixtures — a recurring
 *             sig forces them constant, and jumps leave them in place)
 *   live      everything else: frontier-relative, shifted by jumps
 */
function signature(state, frontier, tcfg, cls, isSink, isCapped) {
  const unit = tcfg.effect.unit();
  const fParts = ratParts(frontier);
  const parts = [];
  const sinks = new Map();       // innerHash -> abstracted surplus count
  const capped = new Set();      // preds whose surplus was abstracted
  const linear = state.linear;
  for (let t = 0; t < linear.maxTagId; t++) {
    const len = linear.lens[t];
    if (!len) continue;
    const buf = linear.groups[t];
    const cnt = linear._rl ? linear.counts[t] : null;
    for (let i = 0; i < len; i++) {
      const h = buf[i];
      const c = cnt ? cnt[i] : 1;
      const isAt = Store.tag(h) === tcfg.stampTag;
      const inner = isAt ? Store.child(h, 0) : h;
      const s = isAt ? Store.child(h, 1) : unit;
      const pred = factKeyOf(inner, tcfg.expTag);
      if (s === unit && cls.dead(pred)) {
        if (isSink(pred)) {
          sinks.set(inner, (sinks.get(inner) || 0) + c);
          continue;
        }
        const cap = isCapped ? isCapped(pred) : 0;
        if (cap > 0 && c > cap) {
          // count-blind above the cap: record cap, surplus extrapolates
          sinks.set(inner, (sinks.get(inner) || 0) + (c - cap));
          capped.add(pred);
          parts.push(`${inner}@Ax${cap}`);
          continue;
        }
        parts.push(`${inner}@Ax${c}`);            // arrived fixture
        continue;
      }
      if (cls.frozen(pred)) {
        const [n, d] = ratParts(s);
        parts.push(`${inner}@=${n}/${d}x${c}`);   // absolute fixture
        continue;
      }
      const rel = rSub(ratParts(s), fParts);
      parts.push(`${inner}@${rel[0]}/${rel[1]}x${c}`);
    }
  }
  const pers = [];
  state.persistent.forEach((h) => pers.push(h));
  parts.sort();
  pers.sort((a, b) => a - b);
  return { key: parts.join(',') + '|' + pers.join(','), sinks, capped };
}

/**
 * Jump n whole periods of length `period` ([num, den] rational parts):
 * shift every live stamp by n·period, bump sinks by n·(per-period delta).
 * Mutates `state` in place. Throws on Int32 count overflow (loud fence).
 */
function applyJump(state, nCycles, period, sinkDelta, tcfg, cls) {
  const unit = tcfg.effect.unit();
  const shift = rMul(period, [BigInt(nCycles), 1n]);
  const linear = state.linear;
  const jobs = [];
  for (let t = 0; t < linear.maxTagId; t++) {
    const len = linear.lens[t];
    if (!len) continue;
    const buf = linear.groups[t];
    const cnt = linear._rl ? linear.counts[t] : null;
    for (let i = 0; i < len; i++) {
      const h = buf[i];
      if (Store.tag(h) !== tcfg.stampTag) continue;
      const s = Store.child(h, 1);
      const inner = Store.child(h, 0);
      const pred = factKeyOf(inner, tcfg.expTag);
      // fixtures stay put: arrived dead stamps and frozen (unobserved-
      // this-call) absolutes — the signature already forced them constant
      if (s === unit && cls.dead(pred)) continue;
      if (cls.frozen(pred)) continue;
      jobs.push(h, cnt ? cnt[i] : 1, inner, s);
    }
  }
  for (let j = 0; j < jobs.length; j += 4) {
    const h = jobs[j], c = jobs[j + 1], inner = jobs[j + 2], s = jobs[j + 3];
    const ns = putRat(...rAdd(ratParts(s), shift));
    linear.remove(Store.tagId(h), h, null, c);
    const nh = Store.put(tcfg.stampTag, [inner, ns]);
    linear.insert(Store.tagId(nh), nh, null, c);
  }
  for (const [inner, d] of sinkDelta) {
    const add = d * nCycles;
    if (add === 0) continue;
    const h = Store.put(tcfg.stampTag, [inner, unit]);
    const have = linear.count(Store.tagId(h), h);
    if (have + add >= I32_FENCE) {
      throw new Error(`accelerate: sink count ${have + add} exceeds the Int32 run-length fence — split the accumulator or lower the horizon`);
    }
    linear.insert(Store.tagId(h), h, null, add);
  }
}

/**
 * Orbit probe — the state-dependent half of a checkpoint, shared by the
 * in-run detector, certificate resume, and certificate mint (TODO_0278 A1):
 * sink/cap/aliveness classification, deadline collection, opacity guards,
 * and the exact canonical signature (caps + activation extraKey folded into
 * the key). Returns null when the state is opaque to acceleration.
 */
function probeOrbit(ruleList, tcfg, compileLoli, state, frontierHash, stateLolis, eff, extraKey) {
  const { inAnte, wildcard, caps, aliveRules } = sinkPreds(ruleList, stateLolis, compileLoli, tcfg, state, frontierHash);
  // Alive-restricted exclusion: what the rules that can still fire this
  // call observe. Statically-excluded preds outside it are FROZEN.
  const aliveEff = collectObservers(aliveRules, tcfg, { preds: new Set(), all: false });
  if (aliveEff.all) return null;
  // Deadline guard (audit: confirmed jump THROUGH a ground before-bound).
  // `after` bounds JOIN the activation max, so an after-pinned match is
  // frontier-relatively visible in the activation extraKey and can never
  // alias two sightings. A `before` bound is a silent filter: the cycle
  // recurs exactly while the absolute deadline approaches. Covariant
  // bounds (shift degree 1) move with the cycle — fine; ground bounds
  // cap the jump strictly below the deadline; opaque bounds refuse.
  const deadlines = [];
  for (const r of aliveRules) {
    for (const b of covariance(r, tcfg).beforeBounds) {
      if (b.covariant) continue;
      if (b.ground === undefined) return null;           // unknown provenance
      deadlines.push(b.ground);
    }
  }
  if (eff.hasBefore || aliveEff.hasBefore) return null;  // formula-level bounds are opaque
  const cls = {
    dead: (p) => !!p && !eff.preds.has(p),
    frozen: (p) => !!p && eff.preds.has(p) && !aliveEff.preds.has(p),
  };
  const isSink = (pred) => !wildcard && cls.dead(pred) && !inAnte.has(pred);
  const isCapped = (pred) => (pred && cls.dead(pred) && caps.has(pred)) ? caps.get(pred) : 0;
  const sig = signature(state, frontierHash, tcfg, cls, isSink, isCapped);
  // caps join the key: a changed alive-set means a changed abstraction
  sig.key += '||' + [...caps.entries()].sort().map(([p, c]) => `${p}:${c}`).join(';');
  if (extraKey) sig.key += '||' + extraKey;
  return { sig, caps, deadlines, cls };
}

/** floor(span / period) cycles from `fParts` to the horizon, capped strictly
 *  below every ground before-deadline: jump to just before it, let normal
 *  firing carry the crossing, re-certify after (the expired rule then reads
 *  as dead — a new orbit regime). */
function cappedCycles(fParts, horizonHash, period, deadlines, tcfg) {
  const span = rSub(ratParts(horizonHash), fParts);
  const num = span[0] * period[1], den = span[1] * period[0];
  let cycles = num >= den ? Number(num / den) : 0;
  const canon = tcfg.canonStamp || ((h) => h);
  for (const g of deadlines) {
    const d = rSub(ratParts(canon(g)), fParts);
    const dn = d[0] * period[1], dd = d[1] * period[0];
    const maxC = dn >= dd ? Number(dn / dd) - 1 : 0;
    if (maxC < cycles) cycles = maxC;
  }
  return cycles;
}

/** Earliest ground before-deadline (canonical stamp hash), or null. A
 *  minted certificate is only sound while no deadline has been crossed
 *  since the orbit was proven — the caller compares this against the
 *  horizon at mint time. */
function minDeadline(deadlines, tcfg) {
  const canon = tcfg.canonStamp || ((h) => h);
  const cmp = tcfg.availability.cmp;
  let min = null;
  for (const g of deadlines) {
    const d = canon(g);
    if (min === null || cmp(d, min) < 0) min = d;
  }
  return min;
}

/**
 * Per-settle acceleration bookkeeping. Feed checkpoints; it answers with a
 * jump instruction when an exact periodic orbit is proven.
 */
function makeAccel(ruleList, tcfg, opts) {
  const sightings = new Map();   // sig key -> { frontier: [n,d], step, sinks, interval }
  // Interval minima for the capped-stock validation: per checkpoint
  // interval, the lowest post-consumption unit-pool count of each pred.
  const intervals = [];          // Array<Map pred -> min count>
  let curMin = new Map();
  const unit = tcfg.effect.unit();
  // Adaptive cadence: dense checkpoints find short periods fast (phase
  // alignment needs two same-residue sightings); the interval doubles as
  // the sighting table grows so long-period/transient systems stay cheap.
  let every = 16;
  return {
    /** Current checkpoint interval (events between signature probes). */
    interval() {
      if (sightings.size > 64 * (1024 / every) && every < 1024) every *= 2;
      return every;
    },
    /** Called after every firing with the consumed map — tracks unit-pool
     *  troughs so a capped surplus can prove it never ran short. */
    noteFire(consumed, state) {
      for (const hStr in consumed) {
        const h = Number(hStr);
        if (Store.tag(h) !== tcfg.stampTag) continue;
        if (Store.child(h, 1) !== unit) continue;
        const inner = Store.child(h, 0);
        const pred = factKeyOf(inner, tcfg.expTag);
        if (!pred) continue;
        const left = state.linear.count(Store.tagId(h), h);
        const cur = curMin.get(pred);
        if (cur === undefined || left < cur) curMin.set(pred, left);
      }
    },
    /**
     * @param {State} state - live state (post-coalesce)
     * @param {number} frontierHash - last fired activation (stamp hash)
     * @param {number} step - fired-event count so far
     * @param {number} lastNondet - step index of the last tie/woplus draw
     * @param {number} horizonHash - settle horizon (stamp hash)
     * @param {Array} stateLolis - possessed rules currently in the state
     * @param {Function} isDead - pred => its unit stamp is dead (from the
     *   coalesce observers: NOT excluded, NOT wildcard-blocked)
     * @returns {null | { cycles, period, sinkDelta, skipped }}
     */
    checkpoint(state, frontierHash, step, lastNondet, horizonHash, stateLolis, eff, extraKey) {
      intervals.push(curMin);
      curMin = new Map();
      const p = probeOrbit(ruleList, tcfg, opts.compileLoli, state, frontierHash, stateLolis, eff, extraKey);
      if (p === null) return null;
      const { sig, caps, deadlines, cls } = p;
      const fParts = ratParts(frontierHash);
      const record = () => {
        sightings.set(sig.key, { frontier: fParts, step, sinks: sig.sinks, interval: intervals.length });
      };
      if (process.env.CALC_ACCEL_DEBUG) {
        console.error(`[accel] step=${step} nondet=${lastNondet} key=${sig.key}`);
      }
      const prev = sightings.get(sig.key);
      if (prev === undefined || prev.step < lastNondet) { record(); return null; }
      const period = rSub(fParts, prev.frontier);
      if (period[0] <= 0n) return null;                    // same instant — no orbit
      // Capped-stock validation: over the whole window the unit pool of
      // every capped pred must have stayed at or above its cap — else a
      // shortage shaped the observed cycle and bigger pools would diverge.
      for (const pred of sig.capped) {
        const cap = caps.get(pred);
        for (let i = prev.interval; i < intervals.length; i++) {
          const m = intervals[i].get(pred);
          if (m !== undefined && m < cap) { record(); return null; }
        }
      }
      // exact-signature recurrence + deterministic window ⇒ periodic orbit
      const cycles = cappedCycles(fParts, horizonHash, period, deadlines, tcfg);
      if (cycles < 1) { record(); return null; }
      const sinkDelta = new Map();
      const keys = new Set([...sig.sinks.keys(), ...prev.sinks.keys()]);
      for (const k of keys) {
        const d = (sig.sinks.get(k) || 0) - (prev.sinks.get(k) || 0);
        if (d < 0) { record(); return null; }              // surplus shrank — not periodic
        if (d > 0) sinkDelta.set(k, d);
      }
      sightings.clear();                                   // scale changes after jump
      intervals.length = 0;
      return {
        cycles, period, sinkDelta, cls, skipped: (step - prev.step) * cycles,
        // certificate provenance (TODO_0278 A1): the proving sighting's
        // step (mint requires lastNondet to never pass it), the per-period
        // event count, and the earliest un-crossed ground deadline.
        sightingStep: prev.step, cycleEvents: step - prev.step,
        nextDeadline: minDeadline(deadlines, tcfg),
      };
    },
    /**
     * Certificate resume (TODO_0278 A1). Validates a saved orbit proof at
     * the CURRENT frontier — same probe as an in-run checkpoint (sink/cap/
     * aliveness classification, deadline collection, opacity guards) plus
     * exact signature equality against the certificate. Trust mode returns
     * a jump instruction (cycles may be 0: revalidated but nothing to
     * skip); 'verify' mode instead seeds the sightings table with the
     * certificate as a prior sighting, so the natural checkpoint machinery
     * re-proves ONE period honestly (full live validation, interval minima
     * included) before jumping.
     */
    tryResume(state, frontierHash, horizonHash, stateLolis, eff, extraKey, cert, mode) {
      const p = probeOrbit(ruleList, tcfg, opts.compileLoli, state, frontierHash, stateLolis, eff, extraKey);
      if (p === null) return null;
      if (p.sig.key !== cert.sigKey) {
        if (process.env.CALC_ACCEL_DEBUG) {
          console.error(`[accel] certificate signature mismatch — falling back to re-detection`);
        }
        return null;
      }
      const fParts = ratParts(frontierHash);
      if (mode === 'verify') {
        sightings.set(p.sig.key, { frontier: fParts, step: -1, sinks: p.sig.sinks, interval: 0 });
        return { seeded: true };
      }
      const cycles = cappedCycles(fParts, horizonHash, cert.period, p.deadlines, tcfg);
      return {
        cycles, period: cert.period, sinkDelta: cert.sinkDelta, cls: p.cls,
        skipped: cert.cycleEvents * cycles,
        nextDeadline: minDeadline(p.deadlines, tcfg),
      };
    },
    /**
     * Mint an exit certificate (TODO_0278 A1). The caller guarantees a
     * proven orbit covers the exit (phase-independence: determinism from
     * the proven window forces state(t+p) = shift_p(state(t)) for every
     * t ≥ the first sighting, so the exit phase inherits the period, the
     * per-period sink growth, and the per-period event count). This
     * function contributes the exit-phase signature — the same probe a
     * resume will run — or refuses when the exit state is opaque.
     */
    mint(state, frontierHash, stateLolis, eff, extraKey, proven, fingerprint) {
      const p = probeOrbit(ruleList, tcfg, opts.compileLoli, state, frontierHash, stateLolis, eff, extraKey);
      if (p === null) return null;
      return {
        v: 1,
        fingerprint,
        sigKey: p.sig.key,
        period: [String(proven.period[0]), String(proven.period[1])],
        sinkDelta: [...proven.sinkDelta.entries()],
        cycleEvents: proven.cycleEvents,
      };
    },
  };
}

export { makeAccel, applyJump, signature, sinkPreds, probeOrbit };

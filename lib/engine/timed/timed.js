/**
 * Timed scheduler — min-activation forward chaining over stamped states
 * (till, TODO_0265 Phase 4; semantics: the Matching spec + P1/P2/P3/P5).
 *
 * The untimed engine (forward.js) is committed-choice: fire the first match
 * found. Timed semantics FIXES the order (D12): always fire an enabled match
 * with globally minimal activation a(m) = max(selected stamps, after-bounds);
 * within an activation instant a pluggable conflict chooser decides (P5's
 * content-derived PRF by default — stateless, horizon-split invariant).
 * `settle(state, T)` fires while min a(m) ≤ T (E5) — the horizon is an
 * ARGUMENT, never a state fact; outputs may be stamped beyond it.
 *
 * Generic over the stamp algebra (D13): everything rational lives in the
 * calculus-supplied timed config (buildTimedConfig(cc) reads cc.grades):
 *   availability.cmp(a, b)      — total order on stamp hashes (⊕ = max)
 *   effect.unit() / compose(s, d) — stamp monoid (⊗ = +; unit = stamp 0)
 *   isStamp(h) / parseStamp(x)  — ground-stamp recognition / horizon parsing
 *   canonStamp(h)               — fold clause-derived stamp forms (optional)
 * Stamped tokens are at(A, s) kernel nodes held in the ordinary linear
 * FactSet under the calculus index policy (D5); unstamped facts in an input
 * state default to the unit stamp (D11). Reads (rule.readOnly, E7.2) reserve
 * without consuming; their stamps join the activation max. Count grades
 * (linearMeta.countTake/countVar, D4/P4) split k off a cohort or bind the
 * whole cohort's size at firing time — nothing is ever cached, so `W`
 * reflects the cohort AS OF FIRING (round-8 requirement, automatic here).
 *
 * The index is optimization, the multiset is semantics (D13 corollary):
 * candidate enumeration walks the policy-ordered group (oldest cohort
 * first = the FIFO sampler; `lifo` walks it backward) but validity is
 * decided by matching alone — acceptance: samplers/schedulers may not
 * change WHICH matches exist.
 */

import Store from '../../kernel/store.js';
import { matchIndexed as matchIdx, undoSave, undoRestore, undoDiscard } from '../../kernel/unify.js';
import { applyIndexed as subApplyIdx } from '../../kernel/substitute.js';
import { compiledSub, producePers } from '../state-ops.js';
import { fromObject, toObject } from '../fact-set.js';
import { clearBWCache } from '../backward-cache.js';
import { EMPTY_MATCH_OPTS } from '../match.js';
import { resolveConn, factKeyOf, flattenAnte } from '../formula-utils.js';
import { ratParts } from '../theories/ratlit-theory.js';
import { mul as _wMul, cmp as _wCmp, add as _wAdd, sub as _wSub } from '../../rat.js';
import { stampObserversCached, coalesce, effectiveExclusion } from './coalesce.js';
import { firstNonCovariant } from './covariance.js';
import { makeAccel, applyJump } from './accel.js';
import { putRat } from '../../kernel/rat-term.js';
import { StampTable, packRef, refInner, refStamp } from '../labels.js';
// ─── Timed config ───────────────────────────────────────────────────

/**
 * Resolve a calculus config into the frozen record the scheduler reads.
 * Requires cc.grades ({ availability: { cmp }, effect: { unit, compose,
 * residual? }, isStamp, parseStamp, canonStamp? }); residual is the PARTIAL
 * monoid residual ⊖ (null when out of fence — TODO_0273); policy/scheduler
 * slots are
 * optional (cc.factSetPolicy, cc.scheduler = { chooser, seed, cohort }).
 */
function buildTimedConfig(cc) {
  const g = cc.grades;
  if (!g || !g.availability || !g.effect) {
    throw new Error('buildTimedConfig: calculus config has no grade algebra (cc.grades) — settle is only available on timed calculi');
  }
  // Labelled state (THY_0024): the scheduler runs over label COLUMNS, so
  // the calculus must supply the term-free value algebra beside the
  // term-level one. A calculus-declared index policy carries `labels`
  // itself; absent a policy, synthesize a minimal label policy (no
  // groupKey — facts group by the caller-passed inner tag, the classic
  // ungrouped behavior).
  if (!g.values) {
    throw new Error('buildTimedConfig: cc.grades.values (label value algebra) is required — see THY_0024 / lib/engine/labels.js');
  }
  const stampTag = cc.stampTag || 'at';
  const policy = cc.factSetPolicy
    ? (cc.factSetPolicy.labels ? cc.factSetPolicy
       : Object.freeze({ ...cc.factSetPolicy, labels: g.values }))
    : Object.freeze({ labels: g.values, stampTag });
  const rc = resolveConn(cc.connectives, cc.gradeConfig);
  const sched = cc.scheduler || {};
  return Object.freeze({
    availability: g.availability,
    effect: g.effect,
    values: g.values,                   // label value algebra (THY_0024)
    isStamp: g.isStamp,
    parseStamp: g.parseStamp,
    canonStamp: g.canonStamp || null,
    policy,
    shiftOps: cc.shiftOps || null,      // q-op shift-degree table (covariance.js)
    stampTag,                           // stamp wrapper tag (at(A, t)) — boundary only
    expTag: rc.exponential || null,     // counted-parcel wrapper (bang)
    implTag: rc.implication || null,    // loli guard (v1: no timed lolis)
    chooser: sched.chooser || 'random',
    seed: sched.seed || 0,
    cohort: sched.cohort || 'fifo',
  });
}

// ─── Stamp helpers ──────────────────────────────────────────────────

const isAt = (h) => Store.tag(h) === 'at';
const innerOf = (h) => (isAt(h) ? Store.child(h, 0) : h);
const stampOf = (h, unit) => (isAt(h) ? Store.child(h, 1) : unit);

/** Best-effort stamp-id rendering for error messages — generic over the
 *  label algebra; falls back to the raw id. */
const _stampDbg = (stamps, id) => {
  try { const v = stamps.value(id); return `t=${v[0]}${v[1] === 1n ? '' : '/' + v[1]}`; }
  catch { return `t#${id}`; }
};

/**
 * Normalize an input state for timed execution: rebuild as a LABELLED
 * state (THY_0024) under the index policy — at(A, t) boundary facts
 * decode into (inner, stampId) rows, bare facts take the unit label
 * (D11). Accepts plain { linear, persistent } objects or State objects.
 *
 * A State already indexed under THIS policy passes through untouched
 * (TODO_0277 incremental settle): states returned by settle({ raw: true })
 * are normalized by construction, so re-normalizing per tick would be a
 * pure O(state) tax. Passthrough hands the SAME object back — the caller
 * owns it and settle mutates it in place (raw pipelines are ownership
 * transfer; plain-object input keeps copy semantics).
 */
function normalizeTimedState(input, tcfg) {
  if (input.linear && input.linear.group && tcfg.policy && input.linear.policy === tcfg.policy) {
    return input;
  }
  const plain = input.linear && input.linear.group ? toObject(input) : input;
  return fromObject(plain.linear || {}, plain.persistent || {}, tcfg.policy);
}

// ─── P1: per-rule minimal-activation match (branch & bound) ─────────

/**
 * Find THE match for a rule: the valid assignment with minimal activation
 * a(m), FIFO-lexicographic tie-break (Matching spec). Candidate cohorts are
 * enumerated in index order (stamp-ascending = oldest first, the `fifo`
 * sampler; `lifo` reverses). Persistent goals are proven and windows
 * evaluated at each complete assignment; guard failure backtracks.
 *
 * Returns { rule, theta, slots, consumed, reserved, activation } or null.
 * consumed/reserved are plain { factHash: take } objects; reserved holds
 * read-arc reservations (never consumed, never re-produced — E7.2).
 *
 * `diag` (optional, #why_not — Phase 4c): a mutable record collecting the
 * BEST FAILED candidate — { deepest, missing, goal, window } where
 * `missing` is the shallowest never-satisfied pattern, `goal` the first
 * failing persistent goal at a complete assignment, `window` a killing
 * before-bound { bound, activation }. Zero cost when absent.
 */
function tryTimedMatch(rule, state, calc, matchOpts, tcfg, diag, baseA) {
  const stamps = state.linear.stamps;        // labelled state (THY_0024)
  const cmp = (a, b) => stamps.cmp(a, b);    // over stamp IDS
  const lifo = tcfg.cohort === 'lifo';
  const linearPats = rule.antecedent.linear || [];
  const persistentList = rule.antecedent.persistent || [];
  const slots = rule.metavarSlots;
  const theta = new Array(rule.metavarCount).fill(undefined);
  const consumed = new Map();                // packed ref -> take
  const reserved = new Map();
  // Which pattern occurrences are read arcs: rule.readOnly lists one entry
  // per read copy; occurrences beyond the budget are ordinary consumes.
  const readBudget = new Map();
  if (rule.readOnly) {
    for (const h of rule.readOnly) readBudget.set(h, (readBudget.get(h) || 0) + 1);
  }

  let best = null;
  const topUndo = undoSave();

  const evalWindow = (w) => {
    let v = w.ground !== undefined ? w.ground : theta[w.slot];
    if (v !== undefined && tcfg.canonStamp) v = tcfg.canonStamp(v);
    if (v === undefined || !tcfg.isStamp(v)) {
      throw new Error(`Rule '${rule.name}': window expression did not resolve to a ground rational stamp`);
    }
    return stamps.internTerm(v);             // window bounds compare as ids
  };

  function leaf(partialA) {
    // Persistent provers write theta slots DIRECTLY (not via the unify
    // journal), so a leaf must snapshot the whole array and restore it —
    // undoRestore alone would leak clause-derived bindings (e.g. window
    // outputs Q$n) into sibling candidates of the backtracking search.
    const savedTheta = theta.slice();
    const saved = undoSave();
    if (diag) diag.leaf = true;               // every linear pattern matched
    let done = false;
    if (persistentList.length > 0) {
      const idx = matchOpts.provePersistent(
        persistentList, 0, theta, slots, state, calc, null, matchOpts);
      if (idx < persistentList.length) {
        done = true;
        if (diag && diag.goal === undefined) diag.goal = persistentList[idx];
      }
    }
    if (!done) {
      let a = partialA;
      let ok = true;
      if (rule.windows) {
        for (const w of rule.windows.after) {
          const v = evalWindow(w);
          if (cmp(v, a) > 0) a = v;           // after: lower bounds join (max)
        }
        for (const w of rule.windows.before) {
          const v = evalWindow(w);
          if (cmp(a, v) >= 0) {               // deadline: a < before
            ok = false;
            if (diag) diag.window = { bound: stamps.term(v), activation: stamps.term(a) };
            break;
          }
        }
      }
      // strict < : the first assignment found at equal activation wins the
      // tie — FIFO by construction (enumeration order is the cohort sampler)
      if (ok && (best === null || cmp(a, best.activation) < 0)) {
        best = {
          rule, slots,
          activation: a,
          theta: theta.slice(),
          consumed: Object.fromEntries(consumed),
          reserved: Object.fromEntries(reserved),
        };
      }
    }
    undoDiscard(saved);
    for (let i = 0; i < theta.length; i++) theta[i] = savedTheta[i];
  }

  function search(i, partialA) {
    // B&B prune: activation is a max — it only grows deeper in the search.
    // >= (not >) keeps the FIRST match found at equal activation (FIFO).
    // INVARIANT PAIR: this `>=` and leaf()'s strict `<` must stay in
    // agreement — each alone suffices for the FIFO tie observable (which
    // is why single-line mutations here survive tests), but together
    // they also guarantee the prune never explores an assignment the
    // leaf would reject. Pinned by the equal-activation tie tests
    // (till-eat leaf shape; till-fifo-pair prune shape, round-15 F6.iii).
    if (best !== null && cmp(partialA, best.activation) >= 0) return;
    if (i === linearPats.length) { leaf(partialA); return; }
    const p = linearPats[i];
    if (diag && i > diag.deepest) { diag.deepest = i; diag.missing = p; }
    const meta = rule.linearMeta[p];
    const isRead = (readBudget.get(p) || 0) > 0;
    if (isRead) readBudget.set(p, readBudget.get(p) - 1);
    const body = meta.body;                    // pattern under a count wrapper
    const bodyIsAt = Store.tag(body) === 'at';
    // Row columns: inner (content addresses), stamp ids, counts. The
    // state is FIXED during matching, so row indexes are stable and
    // availability reads the count column directly (no binary search).
    let ib, sb, cn;
    if (meta.pred) {
      const k = state.groupKeyForPred(meta.pred);
      const fs = state.linear;
      const len = k < 0 ? 0 : fs.lens[k];
      ib = len ? fs.groups[k] : _emptyRows.ib;
      sb = len ? fs.sids[k] : _emptyRows.sb;
      cn = len ? fs.counts[k] : _emptyRows.cn;
      var n = len;
    } else {
      const all = _allLinearRows(state);
      ib = all.ib; sb = all.sb; cn = all.cn; n = all.n;
    }
    const availOf = (gi, ref) => cn[gi]
      - (consumed.get(ref) || 0) - (reserved.get(ref) || 0);

    // Age-agnostic counted patterns (D4 revised, TODO_0011 follow-up): an
    // UNSTAMPED `!_k A` / `!_W A` binds no stamp, so the stamp axis must
    // be unobservable through it — the take SPREADS across cohorts in
    // sampler order (oldest-first under fifo), and `!_W` binds the TOTAL.
    // The stamped forms `!_k A@T` / `!_W A@T` bind ONE stamp and remain
    // cohort-locked (the else-branch below) — binding discipline decides
    // cohort discipline. Activation joins the newest taken stamp, so the
    // FIFO spread is the activation-minimal choice by construction.
    const isCounted = (meta.countTake || 0) > 1 || meta.countVar;
    if (isCounted && !bodyIsAt) {
      for (let gi = 0; gi < n; gi++) {
        const i0 = lifo ? n - 1 - gi : gi;
        const ref0 = packRef(ib[i0], sb[i0]);
        if (availOf(i0, ref0) <= 0) continue;
        const saved = undoSave();
        if (!matchIdx(body, ib[i0], theta, slots)) {
          undoRestore(theta, saved);
          continue;
        }
        const innerB = ib[i0];
        const target = meta.countVar ? Infinity : meta.countTake;
        const takes = [];                       // [packed ref, take] pairs
        let total = 0;
        let maxStamp = sb[i0];
        for (let gj = gi; gj < n && total < target; gj++) {
          const ij = lifo ? n - 1 - gj : gj;
          if (ib[ij] !== innerB) continue;
          const ref = packRef(ib[ij], sb[ij]);
          const av = availOf(ij, ref);
          if (av <= 0) continue;
          const t = meta.countVar ? av : Math.min(av, target - total);
          takes.push([ref, t]);
          total += t;
          if (cmp(sb[ij], maxStamp) > 0) maxStamp = sb[ij];
        }
        let m = !meta.countVar ? total >= meta.countTake : total > 0;
        // Whole-cohort bind (D4): W = total AS OF NOW. Recomputed on every
        // match — never cached — so firing-time reflection is automatic.
        let wroteCount = -1;
        if (m && meta.countVar) {
          const slot = slots[meta.countVar];
          const cv = Store.put1('binlit', BigInt(total));
          if (theta[slot] === undefined) { theta[slot] = cv; wroteCount = slot; }
          else if (theta[slot] !== cv) m = false;
        }
        if (m) {
          const bucket = isRead ? reserved : consumed;
          for (const [h, t] of takes) bucket.set(h, (bucket.get(h) || 0) + t);
          search(i + 1, cmp(maxStamp, partialA) > 0 ? maxStamp : partialA);
          for (const [h, t] of takes) {
            const left = bucket.get(h) - t;
            if (left === 0) bucket.delete(h); else bucket.set(h, left);
          }
        }
        if (wroteCount >= 0) theta[wroteCount] = undefined;
        undoRestore(theta, saved);
        // Later anchors of the SAME inner only shrink the pool and grow the
        // activation; anchors of a DIFFERENT inner are genuine alternatives.
      }
      if (isRead) readBudget.set(p, (readBudget.get(p) || 0) + 1);
      return;
    }

    for (let gi = 0; gi < n; gi++) {
      const ri = lifo ? n - 1 - gi : gi;
      const ref = packRef(ib[ri], sb[ri]);
      const avail = availOf(ri, ref);
      if (avail <= 0) continue;
      const take = meta.countVar ? avail : (meta.countTake || 1);
      if (avail < take) continue;
      const fStamp = sb[ri];
      const saved = undoSave();
      let m;
      if (bodyIsAt) {
        // Stamp-binding pattern A@Q — the reification boundary (THY_0024):
        // only here does a label become a term.
        m = matchIdx(Store.child(body, 0), ib[ri], theta, slots) &&
            matchIdx(Store.child(body, 1), stamps.term(fStamp), theta, slots);
      } else {
        m = matchIdx(body, ib[ri], theta, slots);
      }
      // Whole-cohort bind (D4): W = cohort size AS OF NOW. Recomputed on
      // every match — never cached — so firing-time reflection is automatic.
      let wroteCount = -1;
      if (m && meta.countVar) {
        const slot = slots[meta.countVar];
        const cv = Store.put1('binlit', BigInt(take));
        if (theta[slot] === undefined) { theta[slot] = cv; wroteCount = slot; }
        else if (theta[slot] !== cv) m = false;
      }
      if (m) {
        const bucket = isRead ? reserved : consumed;
        bucket.set(ref, (bucket.get(ref) || 0) + take);
        search(i + 1, cmp(fStamp, partialA) > 0 ? fStamp : partialA);
        const left = bucket.get(ref) - take;
        if (left === 0) bucket.delete(ref); else bucket.set(ref, left);
      }
      if (wroteCount >= 0) theta[wroteCount] = undefined;
      undoRestore(theta, saved);
    }
    if (isRead) readBudget.set(p, (readBudget.get(p) || 0) + 1);
  }

  // Base activation: the unit, or a possessed rule's own stamp (Phase 6c)
  // — entering here (not joined after) keeps before-windows and the B&B
  // prune sound: a rule cannot fire before it exists.
  search(0, baseA !== undefined ? baseA : 0);
  undoDiscard(topUndo);

  if (best && rule.existentialSlots && rule.existentialSlots.length > 0 && matchOpts.resolveEx) {
    matchOpts.resolveEx(best.theta, slots, rule, state, calc, matchOpts);
  }
  return best;
}

const _emptyRows = { ib: new Int32Array(0), sb: new Int32Array(0), cn: new Int32Array(0) };

/** Fallback row view for a wildcard-pred pattern (rare): every linear row
 *  flattened into parallel arrays. */
function _allLinearRows(state) {
  const fs = state.linear;
  const ib = [], sb = [], cn = [];
  for (let t = 0; t < fs.maxTagId; t++) {
    const len = fs.lens[t];
    if (!len) continue;
    const gib = fs.groups[t], gsb = fs.sids[t], gcn = fs.counts[t];
    for (let i = 0; i < len; i++) { ib.push(gib[i]); sb.push(gsb[i]); cn.push(gcn[i]); }
  }
  return { ib, sb, cn, n: ib.length };
}

/** Menus (`with` formulas) currently in the state, both zones — their
 *  alternatives are rules the host can materialize via projection, so the
 *  coalescer must respect what they observe (durable exclusion). */
function _stateWiths(state) {
  const wTag = Store.TAG.with;
  if (wTag === undefined) return null;
  const out = [];
  const pg = state.persistent.group(wTag);
  for (let i = 0; i < pg.length; i++) out.push(pg[i]);
  // Labelled state: group(k) IS the inner column — with-headed rows file
  // under the with tag in both policy-keyed and policy-less label sets
  // (the label boundary decodes at() before insertion, so no at-group
  // fallback scan exists anymore).
  const lg = state.linear.group(wTag);
  for (let i = 0; i < lg.length; i++) out.push(lg[i]);
  return out.length ? out : null;
}

/** Fact keys mentioned by any rule's linear antecedent, plus whether any
 *  pattern has an unknowable head — the instant-feeding tables (round 13/14:
 *  factKeyOf is the SAME key space that keys output heads in _feedsInstant).
 *  Shared by settle's nondet guard and settleExplore's branching test. */
function _antePredSet(ruleList, tcfg) {
  const preds = new Set();
  let wildcard = false;
  for (const r of ruleList) {
    for (const p of (r.antecedent.linear || [])) {
      const pred = factKeyOf(p, tcfg.expTag);
      if (pred) preds.add(pred);
      else wildcard = true;
    }
  }
  return { preds, wildcard };
}


// ─── Firing ─────────────────────────────────────────────────────────

/**
 * Fire a match: consume selected rows at a(m), produce each linear output
 * B as a (B, a(m) ⊗ d) row, counted outputs !_Y B as Y copies (D4).
 * Returns { done (stamp id), delay (term|null), produced (ref -> count),
 * producedPreds } (producedPreds feeds dirty tracking, P3). The graded
 * firing law on labels (THY_0024): no term is interned for a stamp
 * nothing observes.
 *
 * `mult` (TODO_0278 B1, cohort firing): fire the SAME match mult times in
 * one step — consume mult·take per row, produce mult·count per output (one
 * cohort). The caller guarantees the batch equals the sequential
 * mult-prefix (_batchGuard/_batchMult); `produced` stays PER-FIRE so event
 * records RLE-expand to the sequential event multiset (rider 4).
 */
function fire(state, m, tcfg, mult = 1) {
  const rule = m.rule;
  const stamps = state.linear.stamps;
  for (const hStr in m.consumed) {
    const ref = Number(hStr);
    state.linear.remove(Store.tagId(refInner(ref)), ref, null, m.consumed[hStr] * mult);
  }
  // Delay: ground rational or an antecedent-bound term (E7.1); must be a
  // ground canonical stamp after substitution — the compile-time mode check
  // guarantees boundness, this guards groundness/sort.
  let d = null, done = m.activation;
  if (rule.delay) {
    d = rule.delay.ground !== undefined ? rule.delay.ground : m.theta[rule.delay.slot];
    if (d !== undefined && tcfg.canonStamp) d = tcfg.canonStamp(d);
    if (d === undefined || !tcfg.isStamp(d)) {
      throw new Error(`Rule '${rule.name}': delay did not resolve to a ground rational (E7.1 mode check)`);
    }
    const dv = stamps.alg.parse(d);
    // Value fence (TODO_0273 defense-in-depth): isStamp is tag-only; a
    // negative delay is out of the grade fence and must never enter the state.
    if (stamps.alg.cmp(dv, stamps.alg.unit) < 0) {
      throw new Error(`Rule '${rule.name}': delay resolved to a negative grade — out of the delay fence`);
    }
    done = stamps.compose(m.activation, dv);
  }

  const pats = rule.consequent.linear || [];
  const recipes = rule.compiledConseqLinear;
  const producedPreds = [];
  const produced = {};                         // packed ref -> count (E7.3 provenance)
  for (let i = 0; i < pats.length; i++) {
    let h = compiledSub(pats[i], i, m.theta, m.slots, recipes, subApplyIdx);
    let count = 1;
    if (tcfg.expTag && Store.tag(h) === tcfg.expTag) {
      // Counted output !_Y B: Y must have resolved to a ground natural.
      const g = Store.child(h, 0);
      if (Store.tag(g) !== 'binlit') {
        throw new Error(`Rule '${rule.name}': consequent count grade did not resolve to a ground integer`);
      }
      count = Number(Store.child(g, 0));
      h = Store.child(h, 1);
    }
    // Produced lolis are POSSESSED RULES (Phase 6c): stamped like any
    // output — the rule exists from `done` onward (its stamp joins its
    // firing activation as the base).

    if (count === 0) continue;
    const ref = packRef(h, done);
    // I32 fence (B1 rider 6): run-length counts are Int32 — a batched
    // produce that would cross it throws LOUDLY (the sequential unroll
    // would wrap the same total silently; the fence is new honesty).
    if (mult > 1 && count * mult >= 0x40000000) {
      throw new Error(`Rule '${rule.name}': batched produce count ${count * mult} exceeds the Int32 run-length fence`);
    }
    state.linear.insert(Store.tagId(h), ref, null, count * mult);
    produced[ref] = (produced[ref] || 0) + count;
    const pred = factKeyOf(h, tcfg.expTag);
    if (pred && !producedPreds.includes(pred)) producedPreds.push(pred);
  }
  producePers(state.persistent, rule.consequent.persistent || [], m.theta, m.slots, rule, null);
  const producedPersistent = (rule.consequent.persistent || []).length > 0;
  return { done, delay: d, produced, producedPreds, producedPersistent };
}

// ─── P5: content-derived PRF chooser (stateless, D17) ───────────────

function _mix32(x) {
  x = Math.imul(x ^ (x >>> 16), 0x45d9f3b);
  x = Math.imul(x ^ (x >>> 13), 0x45d9f3b);
  return (x ^ (x >>> 16)) >>> 0;
}

function _thetaHash(theta) {
  let h = 0;
  for (let i = 0; i < theta.length; i++) {
    h = _mix32(h ^ (((theta[i] === undefined ? -1 : theta[i]) | 0) + 0x9e3779b9) ^ i);
  }
  return h >>> 0;
}

function _matchKey(m) {
  const cons = Object.entries(m.consumed).map(([k, v]) => k + 'x' + v).sort().join(',');
  return m.rule.name + '|' + cons + '|' + m.theta.join(',');
}

/** FNV-1a over a string (32-bit) — for covariant candidate keys. */
function _strHash(s) {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 0x01000193);
  return h >>> 0;
}

/**
 * Can matching this rule bind an ABSOLUTE time into theta? Only stamp-
 * binding antecedent patterns (A@Q, !_k A@T) open that channel — every
 * other binding (counts, W-totals, clause-derived arithmetic, persistent
 * lookups, existentials) is a function of signature-visible content,
 * which an exact recurrence forces equal. Numeric-tag sniffing on theta
 * VALUES is wrong here: a count is a rational too, but degree 0.
 */
const _bindsStampCache = new WeakMap();
function _bindsStamp(rule, tcfg) {
  let v = _bindsStampCache.get(rule);
  if (v === undefined) {
    v = false;
    for (const p of (rule.antecedent.linear || [])) {
      const meta = rule.linearMeta && rule.linearMeta[p];
      const body = meta ? meta.body : p;
      if (Store.tag(body) === tcfg.stampTag) { v = true; break; }
    }
    _bindsStampCache.set(rule, v);
  }
  return v;
}

/**
 * Translation-covariant canonical identity of a tied match (TODO_0278
 * A3a): rule name + consumed cohorts at FRONTIER-RELATIVE stamps + the
 * stamp-free theta. A cohort that is COALESCE-ELIGIBLE at this frontier
 * (dead stamp under the effective exclusion) encodes as the arrived
 * marker 'A' — its encoding under the canonical coalesced normal form —
 * whether or not a coalesce pass has actually merged it yet. That makes
 * the key blind to dead-stamp identity AND to coalesce CADENCE, so runs
 * that differ only in when they coalesced (plain vs accel checkpoints)
 * stay in draw lockstep, and an exact orbit recurrence forces replays.
 */
function _relCandKey(m, stamps, fParts, alg, isDead) {
  // Aggregate takes per (inner, canonical stamp): a spread take over
  // not-yet-merged dead cohorts must key identically to the same take
  // from the merged cohort (split vs merged is coalesce-cadence noise).
  const agg = new Map();
  for (const k in m.consumed) {
    const ref = Number(k);
    const sid = refStamp(ref);
    const inner = refInner(ref);
    let rel;
    if (sid === 0 || (isDead && isDead(inner, sid))) rel = 'A';
    else { const r = alg.sub(stamps.value(sid), fParts); rel = r[0] + '/' + r[1]; }
    const key = inner + '@' + rel;
    agg.set(key, (agg.get(key) || 0) + m.consumed[k]);
  }
  const parts = [...agg.entries()].map(([k, c]) => k + 'x' + c).sort();
  return m.rule.name + '|' + parts.join(',') + '|' + m.theta.join(',');
}

/**
 * Resolve an equal-activation tie. 'random' = a stateless PRF (D17) —
 * reproducible, horizon-split invariant, no RNG state anywhere.
 *
 * COVARIANT ties (no stamp-bound theta — TODO_0278 A3a): the PRF input is
 * the seed and the tied set's translation-covariant identities, nothing
 * absolute — so an exact orbit recurrence replays the draw verbatim, and
 * tie-poisoned cycles (multi-consumer economies) certify with no loss of
 * exactness. Consequence (documented): a certified idle loop is periodic
 * in its choices — that is what state-identical means; and a tie whose
 * covariant context recurs resolves identically each time (fairness
 * across repeats is not a contract — any resolution is a valid world).
 *
 * Non-covariant ties (stamp-binding thetas) keep the absolute state hash
 * in the input and void the acceleration window (settle's lastNondet).
 * 'deterministic' = first by the canonical key (covariant key when the
 * tie is covariant, for the same replay property). A function is called
 * as chooser(tied, state, seed).
 */
function choose(tied, state, seed, chooser, relKey) {
  if (tied.length === 1) return tied[0];
  if (typeof chooser === 'function') return chooser(tied, state, seed);
  if (relKey) {
    const keyed = tied.map(m => [relKey(m), m])
      .sort((a, b) => (a[0] < b[0] ? -1 : 1));
    if (chooser === 'deterministic') return keyed[0][1];
    let candHash = 0;
    for (const [k, m] of keyed) {
      candHash = (candHash ^ _mix32((m.rule.hash | 0) ^ _strHash(k))) >>> 0;
    }
    const r = _mix32((seed >>> 0) ^ candHash);
    return keyed[r % keyed.length][1];
  }
  const sorted = tied.slice().sort((a, b) => (_matchKey(a) < _matchKey(b) ? -1 : 1));
  if (chooser === 'deterministic') return sorted[0];
  let candHash = 0;
  for (const m of sorted) candHash = (candHash ^ _mix32((m.rule.hash | 0) ^ _thetaHash(m.theta))) >>> 0;
  const r = _mix32((seed >>> 0) ^ state.stateHash ^ candHash);
  return sorted[r % sorted.length];
}

// ─── P3: rule-granular dirty tracking (optional scheduler) ──────────

/**
 * The ONLY planned cache (round 9): per-rule activations, recomputed lazily
 * when the rule is dirty. Bindings are NEVER stored across state changes —
 * matches are recomputed for the activation-minimal rules on every step, so
 * no staleness class exists. Acceptance (D13): trace-identical to rescan.
 *
 * Scaling (TODO_0277): activations live in a lazy-invalidation binary
 * min-heap — a step costs O(#dirty · match + log #rules) instead of an
 * O(#rules) min-scan. Stale heap entries (superseded versions) discard on
 * pop. The scheduler is reusable across settle calls: settle caches it on
 * the raw State keyed by the FactSet mutation counters (see _schedCache).
 */
function _makeDirtySched(ruleList, tcfg, stamps) {
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
        const m = tryTimedMatch(r, state, calc, matchOpts, tcfg);
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
          const m = tryTimedMatch(e[1], state, calc, matchOpts, tcfg);
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

// ─── Phase 6c: possessed rules — loli facts as match sources ────────

/**
 * Enumerate the state's loli facts: [{ fact, inner, stamp }] (fact = the
 * stamped hash as held in the FactSet). O(#lolis) under an inner-tag group
 * policy (till); falls back to filtering the at-group under the default
 * policy. Zero cost when the calculus has no implication tag.
 */
function _stateLolis(state, tcfg) {
  if (!tcfg.implTag) return [];
  const loliTag = Store.TAG[tcfg.implTag];
  if (loliTag === undefined) return [];
  const out = [];
  const fs = state.linear;
  if (loliTag >= fs.maxTagId) return out;
  const len = fs.lens[loliTag];
  if (!len) return out;
  const ib = fs.groups[loliTag], sb = fs.sids[loliTag];
  for (let i = 0; i < len; i++) {
    // rows are distinct (inner, sid) pairs by construction — no dedup
    out.push({ fact: packRef(ib[i], sb[i]), inner: ib[i], stamp: sb[i] });
  }
  return out;
}

/**
 * Match candidates from possessed rules: each loli fact compiles on demand
 * (opts.compileLoli — provided by the loader with the calculus' compile
 * config; compileRule's content-addressed cache makes repeats free) and
 * matches with its own stamp as the base activation. The fact itself joins
 * `consumed` — one-shot by linearity. Loud fence: compileLoli rejects
 * non-ground lolis (v1).
 */
function loliCandidates(state, tcfg, compileLoli, calc, matchOpts, out) {
  const lolis = _stateLolis(state, tcfg);
  for (const e of lolis) {
    const rule = compileLoli(e.inner);
    const m = tryTimedMatch(rule, state, calc, matchOpts, tcfg, undefined, e.stamp);
    if (!m) continue;
    m.consumed[e.fact] = (m.consumed[e.fact] || 0) + 1;
    m.loliFact = e.fact;
    out.push(m);
  }
  return out;
}

// ─── P2: settle ─────────────────────────────────────────────────────

// Scheduler reuse across settle calls (TODO_0277): raw-mode pipelines hand
// the SAME State back each tick; if nothing mutated it since the last
// settle exit (deterministic FactSet mutation counters — no hash trust),
// the dirty scheduler's activation cache is still exact and the O(#rules)
// rebuild is skipped.
const _schedCache = new WeakMap();   // State -> { ruleList, lMut, pMut, sched }

/**
 * Fire, in nondecreasing activation order, every match with activation ≤ T.
 * Composability law: settle(settle(S,T₁),T₂) = settle(S,T₂) for T₁ ≤ T₂.
 *
 * @param {Object} inputState - plain { linear, persistent } or State
 * @param {Array} rules - compiled rules
 * @param {Object} opts - { horizon (stamp hash, REQUIRED), timedConfig
 *   (REQUIRED), calc, matchOpts, maxInstantSteps (Zeno guard: max firings
 *   at ONE instant, default 100000), maxSteps (opt-in TOTAL hard cap, off
 *   by default), events (false: skip the events array — result carries
 *   events: null + eventTotals { rule: count } instead), onEvent (per-
 *   firing record stream, independent of `events`), seed, chooser, cohort,
 *   scheduler: 'rescan'|'dirty', trace, onStep, coalesce (opt-in arrived-
 *   cohort normalization — see coalesce.js; changes cohort identity and
 *   therefore future PRF tie draws, never WHAT is reachable), raw (return
 *   the live FactSet State instead of a plain object — feed it to the next
 *   settle for O(live facts) ticks; ownership transfers to the pipeline),
 *   rebase (requires coalesce: shift the time origin to the earliest live
 *   stamp at exit, capped at the horizon — result.rebase carries the shift
 *   B; the caller owns the accumulated base and passes future horizons in
 *   the rebased frame. Keeps the reachable stamp vocabulary FINITE for
 *   periodic systems, so the content-addressed Store stops growing),
 *   certificate (a saved orbit proof from a prior exit — implies
 *   accelerate; validated at the current frontier, applied as one jump,
 *   any mismatch falls back to re-detection; see result.certificate),
 *   certificateMode ('verify': re-prove one period live instead of
 *   trusting the certificate), batch (default true — cohort firing,
 *   TODO_0278 B1: a unique candidate whose intermediate fires provably
 *   cannot change the instant's candidate landscape fires ONCE at
 *   multiplicity k; state-identical to per-item firing, event records
 *   carry `multiplicity` and RLE-expand to the sequential event
 *   multiset; `batch: false` restores per-item firing) }
 * @returns {{ state, quiescent, steps, events, trace, next }} — `next` is
 *   the earliest pending activation beyond the horizon (stamp hash) or null;
 *   `events` is the completion queue (E7.3): one record per firing. Under
 *   acceleration a horizon exit covered by a proven orbit adds
 *   `certificate` (JSON-safe: { v, fingerprint, sigKey, period, sinkDelta,
 *   cycleEvents }) — save it with the state, feed it back as
 *   opts.certificate to jump the elapsed time on resume.
 */
function settle(inputState, rules, opts = {}) {
  const base = opts.timedConfig;
  if (!base) throw new Error('settle requires opts.timedConfig (buildTimedConfig(cc))');
  const tcfg = (opts.cohort && opts.cohort !== base.cohort)
    ? { ...base, cohort: opts.cohort } : base;
  const horizon = opts.horizon;
  if (horizon === undefined || !tcfg.isStamp(horizon)) {
    throw new Error('settle requires opts.horizon as a ground stamp (use parseStamp)');
  }
  // Zeno guard (D16, redefined — TODO_0278 A2 rider 4): true Zeno is NO
  // TIME PROGRESS — unboundedly many firings at one instant. The guard
  // counts firings since the frontier last advanced (aMin is nondecreasing
  // across firings) and throws past maxInstantSteps, so a dense-but-finite
  // catch-up runs to completion no matter how much elapsed time it crosses.
  // Flat maxSteps survives as an OPT-IN total hard cap — the recourse for
  // untrusted programs whose divergence the instant guard cannot see (a
  // delay-shrinking convergent schedule advances the frontier every step).
  const zenoCap = opts.maxInstantSteps || 100000;
  const hardCap = opts.maxSteps || 0;          // 0 = no flat cap
  const matchOpts = opts.matchOpts || EMPTY_MATCH_OPTS;
  const calc = opts.calc || null;
  const seed = opts.seed !== undefined ? opts.seed : tcfg.seed;
  const chooser = opts.chooser || tcfg.chooser;
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  _rejectMultiAlt(ruleList);
  clearBWCache();                              // same tabling contract as forward.run

  const state = normalizeTimedState(inputState, tcfg);
  // Labelled state (THY_0024): the scheduler's working currency is the
  // STAMP ID — terms exist only at the boundaries (horizon in, events/next
  // out, pattern bindings).
  const stamps = state.linear.stamps;
  const alg = stamps.alg;
  const cmp = (a, b) => stamps.cmp(a, b);
  const horizonId = stamps.internTerm(horizon);
  const horizonParts = stamps.value(horizonId);
  /** Boundary conversion: packed-ref map -> at-encoded map (event records
   *  and hooks keep the public at() format; memoized reify makes repeats
   *  cheap, and suppressed-event runs never pay it). */
  const _refsToAt = (obj) => {
    const out = {};
    for (const k in obj) {
      const ref = Number(k);
      const h = Store.put(tcfg.stampTag, [refInner(ref), stamps.term(refStamp(ref))]);
      out[h] = (out[h] || 0) + obj[k];
    }
    return out;
  };
  // Event suppression (TODO_0278 A2 rider 5): a week-scale catch-up's OOM
  // is the events array as much as the unroll — { events: false } skips the
  // records entirely and returns per-rule totals instead (events: null in
  // the result, loud on accidental .length). opts.onEvent streams the full
  // record per firing either way.
  const keepEvents = opts.events !== false;
  const onEvent = opts.onEvent || null;
  const events = keepEvents ? [] : null;
  const eventTotals = keepEvents ? null : Object.create(null);
  const trace = opts.trace ? [] : null;
  // Dirty tracking is the default (trace-identical to rescan, P3/D13);
  // opts.scheduler = 'rescan' opts out. A cached scheduler revives when
  // the state is untouched since the settle that built it.
  let sched = null;
  if (opts.scheduler !== 'rescan') {
    const c = _schedCache.get(state);
    if (c && c.ruleList === ruleList &&
        c.lMut === state.linear.mut && c.pMut === state.persistent.mut) {
      sched = c.sched;
    } else {
      sched = _makeDirtySched(ruleList, tcfg, stamps);
    }
  }
  // Translation rebase (TODO_0277 B3): sound for the same reason coalescing
  // is — max-plus schedules are translation-invariant, and dead-unit stamps
  // stay fixed points. B = min(earliest live stamp, horizon) so rebased
  // stamps and future rebased horizons stay non-negative.
  const _rebaseNow = () => {
    const ZERO = alg.unit;
    const stateLolis = opts.compileLoli ? _stateLolis(state, tcfg) : null;
    const eff = effectiveExclusion(observers, stateLolis, opts.compileLoli, tcfg, _stateWiths(state));
    // Dynamic covariance guard: possessed rules and menus can carry window
    // bounds the entry check could not see. A window reachable from the
    // state makes the translation unsound (covariance.js) — skip the shift
    // (rebase = 0 is an honest no-op; the caller adds nothing to its base).
    if (eff.hasWindow) return ZERO;
    if (stateLolis && stateLolis.length > 0 && opts.compileLoli) {
      if (firstNonCovariant(stateLolis.map(e => opts.compileLoli(e.inner)), tcfg)) return ZERO;
    }
    const dead = (pred) => !eff.all && !!pred && !eff.preds.has(pred);
    const linear = state.linear;
    const jobs = [];                     // [group, inner, sid, count]
    let minSid = null;
    for (let t = 0; t < linear.maxTagId; t++) {
      const len = linear.lens[t];
      if (!len) continue;
      const ib = linear.groups[t], sb = linear.sids[t], cnt = linear.counts[t];
      for (let i = 0; i < len; i++) {
        const sid = sb[i];
        if (sid === 0 && dead(factKeyOf(ib[i], tcfg.expTag))) continue;
        jobs.push(t, ib[i], sid, cnt[i]);
        if (minSid === null || cmp(sid, minSid) < 0) minSid = sid;
      }
    }
    const bm = minSid === null || cmp(minSid, horizonId) > 0
      ? horizonParts : stamps.value(minSid);
    // Floor to an integer shift: callers tick on a fixed grid (k/N
    // seconds); an integral origin shift maps the grid onto itself, so the
    // reachable stamp VOCABULARY stays finite across epochs.
    const B = [bm[0] / bm[1], 1n];                        // BigInt floor (ℚ≥0)
    if (B[0] === 0n) return ZERO;                         // origin already here
    // Rebuild-swap (THY_0024): shifted rows re-intern into a FRESH table —
    // value collisions merge through interning, dead entries die with the
    // old table (compaction built in), and no Store term is ever minted.
    const nt = new StampTable(alg);
    for (let j = 0; j < jobs.length; j += 4) {
      const t = jobs[j], inner = jobs[j + 1], sid = jobs[j + 2], c = jobs[j + 3];
      linear.remove(t, packRef(inner, sid), null, c);
    }
    // Two passes: all removals first, then insertions — the surviving
    // sid-0 rows keep their ids (unit is id 0 in both tables).
    linear.stamps = nt;
    for (let j = 0; j < jobs.length; j += 4) {
      const t = jobs[j], inner = jobs[j + 1], sid = jobs[j + 2], c = jobs[j + 3];
      const ns = nt.intern(alg.sub(stamps.value(sid), B));
      linear.insert(t, packRef(inner, ns), null, c);
    }
    return B;
  };
  const _exit = (ret, mint) => {
    let rb = null;                       // shift VALUE (alg parts) | null
    if (opts.rebase) {
      rb = _rebaseNow();
      ret.rebase = alg.reify(rb);
      if (rb[0] !== 0n && !opts.raw) ret.state = toObject(state);
    }
    // Certificate mint (TODO_0278 A1) — after the rebase shift, so the
    // signature describes exactly the state being returned/saved.
    if (mint) {
      const cert = mint(rb);
      if (cert) ret.certificate = cert;
    }
    // A nonzero rebase swaps the stamp table — the scheduler's cached
    // activations are old-table ids, so the cache must not survive it.
    if (sched && opts.raw && (rb === null || rb[0] === 0n)) {
      _schedCache.set(state, {
        ruleList, sched,
        lMut: state.linear.mut, pMut: state.persistent.mut,
      });
    }
    return ret;
  };

  // Arrived-cohort coalescing (TODO_0277): derived exclusion set for the
  // static rules; state lolis fold in at each coalesce point. Mid-run the
  // bound is the current frontier aMin (STRICT); at return it is the
  // horizon (every pending activation exceeds it).
  // A certificate implies acceleration: resuming a saved orbit proof only
  // makes sense under the machinery that can validate and extend it.
  const doAccel = !!opts.accelerate || !!opts.certificate;
  const doCoalesce = !!opts.coalesce || doAccel;   // acceleration needs the normal form
  // Cohort firing (TODO_0278 B1): DEFAULT ON — exact and state-identical
  // (the batch equals the sequential k-prefix, riders 1-3), same class as
  // run-length/dirty-sched. `batch: false` opts out (differential pin).
  const doBatch = opts.batch !== false;
  const observers = doCoalesce ? stampObserversCached(ruleList, tcfg) : null;
  if (opts.rebase) {
    // Translation-covariance guard (audit: rebase silently broke ground
    // window bounds — the state shifts, compiled-in absolute bounds do not).
    if (!doCoalesce) throw new Error('settle: rebase requires coalesce (dead stamps are the fixed points of the translation)');
    const nc = firstNonCovariant(ruleList, tcfg);
    if (nc) {
      throw new Error(`settle: rebase refused — rule '${nc.rule.name}' is not translation-invariant (${nc.reason}). Drop rebase or make the bound stamp-relative (Q + c).`);
    }
    if (observers.hasWindow) {
      throw new Error('settle: rebase refused — a consequent-embedded rule or menu carries a window bound (formula-level bounds cannot be shifted)');
    }
  }
  const _coalesceNow = (bound, strict) => coalesce(state, bound, tcfg, observers, {
    strict,
    stateLolis: opts.compileLoli ? _stateLolis(state, tcfg) : null,
    compileLoli: opts.compileLoli,
    stateMenus: _stateWiths(state),
  });
  const accel = doAccel ? makeAccel(ruleList, tcfg, { compileLoli: opts.compileLoli }) : null;
  const accelerated = doAccel ? [] : undefined;
  // Nondeterminism guard for acceleration: only GENUINE conflicts and
  // instant-feeding ties (settleExplore's own branch conditions) are draw-
  // sensitive — independent equal-activation firings commute, so they do
  // not invalidate a periodic-orbit window. Precompute the instant-feeding
  // tables exactly as settleExplore does.
  // Also under plain coalesce: draw-sensitive firings normalize the state
  // first (see the draw-normalization step in the loop), which needs the
  // same instant-feeding tables.
  const _acc = (doAccel || doCoalesce || doBatch) ? _antePredSet(ruleList, tcfg) : null;
  // Effective exclusion for draw-key eligibility (A3a): recomputed when
  // the state mutates — cheap, per-rule/formula contribs are cached.
  let _effDraw = null, _effDrawL = -1, _effDrawP = -1;
  const _effNow = () => {
    if (_effDraw && _effDrawL === state.linear.mut && _effDrawP === state.persistent.mut) return _effDraw;
    const sl = opts.compileLoli ? _stateLolis(state, tcfg) : null;
    _effDraw = effectiveExclusion(observers, sl, opts.compileLoli, tcfg, _stateWiths(state));
    _effDrawL = state.linear.mut;
    _effDrawP = state.persistent.mut;
    return _effDraw;
  };
  let lastNondet = -1;
  let lastCheckStep = -1;

  // ── Orbit certificates (TODO_0278 A1) ──
  // _proven: the latest orbit proof covering the run — set by an in-run
  // certified jump or a validated certificate resume. An exit inside it
  // (no draw since its sighting, no deadline crossed) mints a certificate.
  // _pendingCert: a caller-supplied certificate, attempted once before the
  // first firing (the saved state IS the mint state, so the exit-phase
  // signature revalidates trivially — any mismatch falls back).
  const _parseCert = (c) => {
    try {
      if (!c || c.v !== 1 || typeof c.sigKey !== 'string' ||
          typeof c.fingerprint !== 'string') return null;
      const period = [BigInt(c.period[0]), BigInt(c.period[1])];
      if (period[0] <= 0n || period[1] <= 0n) return null;
      if (!Number.isInteger(c.cycleEvents) || c.cycleEvents < 1) return null;
      const sinkDelta = new Map();
      for (const [h, d] of (c.sinkDelta || [])) {
        if (!Number.isInteger(h) || !Number.isInteger(d) || d < 1) return null;
        sinkDelta.set(h, d);
      }
      return { fingerprint: c.fingerprint, sigKey: c.sigKey, period,
               sinkDelta, cycleEvents: c.cycleEvents };
    } catch { return null; }
  };
  let _pendingCert = doAccel && opts.certificate ? _parseCert(opts.certificate) : null;
  let _proven = null;

  // Coalesce/accelerate checkpoint (TODO_0277): coalesce strictly below the
  // frontier aMin; probe the orbit detector; apply a certified jump. Returns
  // true when the state was rewritten — `cands` hold pre-rewrite hashes and
  // the loop must re-enter (the dirty scheduler's caches survive: activation
  // VALUES are coalesce-invariant).
  // Activation signature: every live rule/loli activation relative
  // to the frontier. Ground (absolute) after-bounds pin activations,
  // which shift relative to a moving frontier — time-inhomogeneous
  // rules can never alias two sightings (before-bounds are handled
  // separately: accel.checkpoint caps jumps below live deadlines).
  const _actKey = (aMin, cands) => {
    const fParts = stamps.value(aMin);
    const rel = (a) => { const r = alg.sub(stamps.value(a), fParts); return `${r[0]}/${r[1]}`; };
    const actParts = [];
    if (sched) {
      for (const [r, a] of sched.activations()) {
        if (a !== null) actParts.push(r.name + '@' + rel(a));
      }
    } else {
      for (const m of cands) if (!m.loliFact) actParts.push(m.rule.name + '@' + rel(m.activation));
    }
    for (const m of cands) if (m.loliFact) actParts.push(m.rule.name + '@' + rel(m.activation));
    actParts.sort();
    return actParts.join(';');
  };

  const _checkpointNow = (aMin, cands) => {
    lastCheckStep = steps;
    const stateLolis = opts.compileLoli ? _stateLolis(state, tcfg) : null;
    const eff = effectiveExclusion(observers, stateLolis, opts.compileLoli, tcfg, _stateWiths(state));
    const rewrote = coalesce(state, aMin, tcfg, observers, { strict: true, effective: eff });
    let jumped = false;
    if (accel && !eff.all) {
      const jump = accel.checkpoint(state, stamps.value(aMin), steps, lastNondet,
        horizonParts, stateLolis, eff, _actKey(aMin, cands));
      if (jump) {
        applyJump(state, jump.cycles, jump.period, jump.sinkDelta, tcfg, jump.cls);
        accelerated.push({
          at: stamps.term(aMin), period: putRat(...jump.period),
          cycles: jump.cycles, skippedEvents: jump.skipped,
        });
        _proven = { period: jump.period, sinkDelta: jump.sinkDelta,
                    cycleEvents: jump.cycleEvents, sightingStep: jump.sightingStep,
                    nextDeadline: jump.nextDeadline };
        if (sched) sched = _makeDirtySched(ruleList, tcfg, stamps);
        jumped = true;
      }
    }
    return rewrote > 0 || jumped;
  };

  // Certificate resume (TODO_0278 A1): one attempt, before the first
  // firing. Fingerprint pins the Store bundle; the accel probe revalidates
  // classification, deadlines, and the exact exit-phase signature at the
  // CURRENT frontier — any mismatch is a silent, safe fallback to in-run
  // re-detection. 'verify' mode plants the certificate as a prior sighting
  // instead of trusting it: the natural checkpoints re-prove one period.
  const _tryCertificate = (cert, aMin, cands) => {
    if (!calc || typeof calc.verifyFingerprint !== 'function' ||
        !calc.verifyFingerprint(cert.fingerprint)) {
      if (process.env.CALC_ACCEL_DEBUG) console.error('[accel] certificate fingerprint rejected');
      return false;
    }
    const stateLolis = opts.compileLoli ? _stateLolis(state, tcfg) : null;
    const eff = effectiveExclusion(observers, stateLolis, opts.compileLoli, tcfg, _stateWiths(state));
    if (eff.all) return false;
    const r = accel.tryResume(state, stamps.value(aMin), horizonParts, stateLolis, eff,
      _actKey(aMin, cands), cert, opts.certificateMode || 'trust');
    if (!r || r.seeded) return false;
    _proven = { period: r.period, sinkDelta: r.sinkDelta, cycleEvents: cert.cycleEvents,
                sightingStep: -1, nextDeadline: r.nextDeadline };
    if (r.cycles < 1) return false;        // revalidated; elapsed < one period
    applyJump(state, r.cycles, r.period, r.sinkDelta, tcfg, r.cls);
    accelerated.push({
      at: stamps.term(aMin), period: putRat(...r.period), cycles: r.cycles,
      skippedEvents: r.skipped, resumed: true,
    });
    if (sched) sched = _makeDirtySched(ruleList, tcfg, stamps);
    return true;
  };

  // Certificate mint at a horizon exit (TODO_0278 A1). Conditions: a
  // proven orbit covers the run's tail (no draw-sensitive nondeterminism
  // since its sighting — phase independence then extends the period to the
  // exit phase) and no ground deadline was crossable within the horizon
  // (a crossing is a regime change; the proven period would be stale).
  // The signature is taken AFTER a rebase shift (the saved state is the
  // shifted one); the activation extraKey is frontier-relative and thus
  // shift-invariant, so pre-rebase values serve.
  // NOTE: called from _exit AFTER a possible rebase table-swap — aMin ids
  // from the loop are stale there, so the frontier VALUE and the (shift-
  // invariant, frontier-relative) extraKey are captured BEFORE the exit.
  const _mintNow = (aMinParts, extraKey, rebase) => {
    if (!accel || !_proven || lastNondet > _proven.sightingStep) return null;
    if (_proven.nextDeadline !== null && alg.cmp(_proven.nextDeadline, horizonParts) <= 0) return null;
    const fp = calc && calc.bundleFingerprint;
    if (!fp) return null;
    const stateLolis = opts.compileLoli ? _stateLolis(state, tcfg) : null;
    const eff = effectiveExclusion(observers, stateLolis, opts.compileLoli, tcfg, _stateWiths(state));
    if (eff.all) return null;
    const f = rebase !== null && rebase[0] !== 0n ? alg.sub(aMinParts, rebase) : aMinParts;
    return accel.mint(state, f, stateLolis, eff, extraKey, _proven, fp);
  };

  let steps = 0;
  let zenoLast = null;                         // frontier at the last firing
  let instSteps = 0;                           // firings at that instant
  for (;;) {
    let cands;
    if (sched) {
      cands = sched.candidates(state, calc, matchOpts, tcfg);
    } else {
      cands = [];
      for (const r of ruleList) {
        const m = tryTimedMatch(r, state, calc, matchOpts, tcfg);
        if (m) cands.push(m);
      }
    }
    // Possessed rules are rescanned every step under BOTH schedulers (few
    // facts, group-indexed) — dirty ≡ rescan holds for them trivially.
    if (opts.compileLoli) {
      loliCandidates(state, tcfg, opts.compileLoli, calc, matchOpts, cands);
    }
    if (cands.length === 0) {
      if (doCoalesce) _coalesceNow(horizonId, false);
      return _exit({ state: opts.raw ? state : toObject(state), quiescent: true, steps, events, trace, next: null, ...(eventTotals ? { eventTotals } : {}), ...(accelerated ? { accelerated } : {}) });
    }
    let aMin = cands[0].activation;
    for (const m of cands) if (cmp(m.activation, aMin) < 0) aMin = m.activation;
    if (cmp(aMin, horizonId) > 0) {
      // Horizon reached: the future stays pending; state is self-describing
      // (no watermark, E5) — a later settle(T') resumes from here.
      if (doCoalesce) _coalesceNow(horizonId, false);
      // Mint inputs captured PRE-exit: a rebase inside _exit swaps the
      // stamp table, invalidating loop-scope ids (see _mintNow).
      const aMinParts = stamps.value(aMin);
      const mintKey = doAccel ? _actKey(aMin, cands) : null;
      return _exit({ state: opts.raw ? state : toObject(state), quiescent: true, steps, events, trace, next: stamps.term(aMin), ...(eventTotals ? { eventTotals } : {}), ...(accelerated ? { accelerated } : {}) },
        (rb) => _mintNow(aMinParts, mintKey, rb));
    }
    // Certificate resume: one shot, before the first firing — the saved
    // state is the mint state, so the exit-phase proof revalidates here.
    if (_pendingCert) {
      const c = _pendingCert;
      _pendingCert = null;
      if (_tryCertificate(c, aMin, cands)) continue;
    }
    // The frontier is aMin (the next event's instant): stamps strictly
    // below it are dead for every pending activation max.
    const _ckEvery = accel ? accel.interval() : 64;
    if (doCoalesce && steps > 0 && steps % _ckEvery === 0 && steps !== lastCheckStep) {
      if (_checkpointNow(aMin, cands)) continue;
    }
    const tied = cands.filter(mm => cmp(mm.activation, aMin) === 0);
    const tieSensitive = tied.length > 1 && _acc &&
      (_conflicts(tied, state) ||
       tied.some(mm => _feedsInstant(mm, tcfg, _acc.preds, _acc.wildcard)));
    // Draw normalization for WEIGHTED firings (TODO_0278 A3a): a woplus
    // draw reads the absolute state hash, which under coalescing must come
    // from the CANONICAL coalesced normal form at this frontier — or the
    // checkpoint CADENCE (accel coalesces more often than a plain run)
    // would leak into the draw. Tie draws need no normalization: their
    // covariant keys already encode coalesce-eligible cohorts canonically.
    // Idempotent: at most one rewrite pass per instant, then 0 → proceed.
    if (doCoalesce &&
        tied.some(mm => mm.rule.weighted && mm.rule.consequentAlts.length > 1)) {
      if (_coalesceNow(aMin, true) > 0) continue;
    }
    // Zeno / hard-cap guards (D16 / A2): tick once per firing, reset when
    // the frontier advances — aMin is nondecreasing across firings. Sits
    // after every continue path: it counts FIRINGS.
    if (zenoLast === null || cmp(aMin, zenoLast) > 0) { zenoLast = aMin; instSteps = 0; }
    if (++instSteps > zenoCap) {
      throw new Error(`settle: ${instSteps} firings at instant ${_stampDbg(stamps, aMin)} — zero-delay rule cycle pinning logical time? (Zeno guard, D16; maxInstantSteps=${zenoCap})`);
    }
    if (hardCap && steps >= hardCap) {
      throw new Error(`settle: maxSteps=${hardCap} exceeded (opt-in hard cap — per-instant divergence is maxInstantSteps's job)`);
    }
    let m;
    if (tied.length > 1) {
      // Covariant ties (TODO_0278 A3a): with a translation-covariant draw
      // input, an exact orbit recurrence FORCES the replay — the draw is
      // no longer window-voiding. Stamp-binding thetas make the tie
      // time-inhomogeneous, and a custom chooser may read absolute state:
      // both fall back to the absolute input + voiding (sound as before).
      const covariant = typeof chooser !== 'function' &&
        !tied.some(mm => _bindsStamp(mm.rule, tcfg));
      if (doAccel && tieSensitive && !covariant) {
        lastNondet = steps;                        // draw-sensitive tie
        if (process.env.CALC_ACCEL_DEBUG) {
          console.error(`[accel] nondet tie @${steps}: ${tied.map(mm => mm.rule.name).join(' | ')}`);
        }
      }
      const fP = stamps.value(aMin);
      // Coalesce-eligibility for the canonical key encoding (mirrors
      // coalesce()'s own predicate at the strict mid-run bound).
      let isDead = null;
      if (doCoalesce) {
        const eff = _effNow();
        if (!eff.all) {
          isDead = (inner, sid) => {
            if (stamps.cmp(sid, aMin) >= 0) return false;
            const it = Store.tag(inner);
            if (it === 'with' || (tcfg.implTag && it === tcfg.implTag)) return false;
            const pred = factKeyOf(inner, tcfg.expTag);
            return !!pred && !eff.preds.has(pred);
          };
        }
      }
      m = choose(tied, state, seed, chooser,
        covariant ? (mm) => _relCandKey(mm, stamps, fP, alg, isDead) : null);
    } else {
      m = tied[0];
    }
    if (m.rule.weighted && m.rule.consequentAlts.length > 1) {
      lastNondet = steps;                          // woplus draw — likewise
      m = _withAlt(m, _sampleAlt(m, state, seed, tcfg));   // woplus: PRF branch draw (4b)
    }
    // Cohort firing (TODO_0278 B1): fire the unique candidate ONCE at
    // multiplicity k when the sequential scheduler would provably fire
    // this exact match k times consecutively — see _batchGuard/_batchMult.
    // The batch is one step for Zeno/steps (a zero-progress loop feeds
    // itself at the instant, so it can never batch past the guard) and
    // one RLE event record (multiplicity field; expansion ≡ sequential).
    let mult = 1;
    if (doBatch && tied.length === 1) {
      mult = _batchMult(m, state);
      if (mult > 1 && !_batchGuard(m, tcfg, _acc)) mult = 1;
    }
    const fired = fire(state, m, tcfg, mult);
    if (accel) accel.noteFire(m.consumed, state);
    if (sched) sched.markFired(m, fired);
    if (eventTotals) eventTotals[m.rule.name] = (eventTotals[m.rule.name] || 0) + mult;
    if (keepEvents || onEvent) {
      // Boundary: event records carry the public at-encoding and term
      // stamps (THY_0024) — minted only when someone is listening.
      // Batched firings carry PER-FIRE consumed/produced + multiplicity:
      // the event list is an RLE of the sequential one (B1 rider 4).
      const ev = {
        rule: m.rule.name, activation: stamps.term(m.activation), delay: fired.delay,
        done: stamps.term(fired.done), theta: m.theta,
        consumed: _refsToAt(m.consumed), reserved: _refsToAt(m.reserved),
        produced: _refsToAt(fired.produced),
        ...(mult > 1 ? { multiplicity: mult } : {}),
        ...(m.altIndex !== undefined ? { alt: m.altIndex } : {}),
      };
      if (keepEvents) events.push(ev);
      if (onEvent) onEvent(ev);
    }
    steps++;
    if (trace) trace.push(`[${steps - 1}] ${m.rule.name}${mult > 1 ? ' x' + mult : ''}`);
    if (opts.onStep) {
      opts.onStep({
        step: steps, rule: m.rule, consumed: _refsToAt(m.consumed),
        theta: m.theta.slice(), slots: m.slots,
        activation: stamps.term(m.activation), delay: fired.delay, state,
        ...(mult > 1 ? { multiplicity: mult } : {}),
      });
    }
  }
}

/** Peek at the smallest pending activation without firing (or null). */
function nextActivation(inputState, rules, opts = {}) {
  const tcfg = opts.timedConfig;
  if (!tcfg) throw new Error('nextActivation requires opts.timedConfig');
  const matchOpts = opts.matchOpts || EMPTY_MATCH_OPTS;
  const state = normalizeTimedState(inputState, tcfg);
  const stamps = state.linear.stamps;
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  let aMin = null;
  const cands = [];
  for (const r of ruleList) {
    const m = tryTimedMatch(r, state, opts.calc || null, matchOpts, tcfg);
    if (m) cands.push(m);
  }
  if (opts.compileLoli) {
    loliCandidates(state, tcfg, opts.compileLoli, opts.calc || null, matchOpts, cands);
  }
  for (const m of cands) {
    if (aMin === null || stamps.cmp(m.activation, aMin) < 0) aMin = m.activation;
  }
  return aMin === null ? null : stamps.term(aMin);
}

// ─── settleChunked: bounded catch-up slices (TODO_0278 A2) ──────────

/**
 * Catch up to a far horizon in bounded slices — settleChunked(S, rules,
 * { ...settle opts, chunk, onChunk }) fires exactly the events of one
 * settle(S, T). Soundness is E5 composability: settle(settle(S,T₁),T₂) =
 * settle(S,T₂), and the PRF chooser is horizon-split invariant, so even
 * weighted draws replay identically (exact mode; under coalesce the usual
 * cohort-identity contract applies to any split). Each slice covers
 * (prev horizon, next-activation + chunk] — anchored at the pending
 * schedule, so an idle span costs one slice, not elapsed/chunk of them —
 * and control returns between slices: onChunk({ chunks, settledTo, steps,
 * next }, caller-frame stamps) is the UI progress hook.
 *
 * Drop-in result contract: `next` and `rebase` are reported in the
 * CALLER's frame (rebase = the accumulated shift across slices);
 * `certificate` is the final slice's mint. Certificates THREAD: an input
 * opts.certificate seeds the first slice and each slice's mint feeds the
 * next, so a proven idle orbit costs one validated jump per slice.
 * opts.maxSteps is a TOTAL budget across slices.
 *
 * @param {Object} opts - settle opts plus { chunk (stamp hash, REQUIRED,
 *   > 0: the slice width beyond the next pending activation),
 *   onChunk (optional progress callback) }
 */
function settleChunked(inputState, rules, opts = {}) {
  const tcfg = opts.timedConfig;
  if (!tcfg) throw new Error('settleChunked requires opts.timedConfig (buildTimedConfig(cc))');
  const horizon = opts.horizon;
  if (horizon === undefined || !tcfg.isStamp(horizon)) {
    throw new Error('settleChunked requires opts.horizon as a ground stamp (use parseStamp)');
  }
  const cmp = tcfg.availability.cmp;
  const chunk = opts.chunk;
  if (chunk === undefined || !tcfg.isStamp(chunk) || cmp(chunk, tcfg.effect.unit()) <= 0) {
    throw new Error('settleChunked requires opts.chunk as a positive ground stamp (the slice width)');
  }
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  let state = normalizeTimedState(inputState, tcfg);
  const keepEvents = opts.events !== false;
  const events = keepEvents ? [] : null;
  const eventTotals = keepEvents ? null : Object.create(null);
  const trace = opts.trace ? [] : null;
  let accelerated;
  let cert = opts.certificate;
  let steps = 0, chunks = 0;
  let acc = [0n, 1n];                    // accumulated rebase: caller → state frame
  const toCaller = (h) => (acc[0] === 0n ? h : putRat(..._wAdd(ratParts(h), acc)));
  let next = nextActivation(state, ruleList, opts);   // state-frame stamp or null
  let last;
  for (;;) {
    const tEff = acc[0] === 0n ? horizon : putRat(..._wSub(ratParts(horizon), acc));
    let h = tEff, final = true;
    if (next !== null && cmp(next, tEff) <= 0) {
      const stretch = tcfg.effect.compose(next, chunk);
      if (cmp(stretch, tEff) < 0) { h = stretch; final = false; }
    }
    if (opts.maxSteps && opts.maxSteps - steps <= 0) {
      throw new Error(`settleChunked: maxSteps=${opts.maxSteps} exceeded (total budget across slices)`);
    }
    const r = settle(state, ruleList, {
      ...opts, horizon: h, raw: true, certificate: cert,
      chunk: undefined, onChunk: undefined,
      ...(opts.maxSteps ? { maxSteps: opts.maxSteps - steps } : {}),
    });
    chunks++;
    steps += r.steps;
    state = r.state;
    last = r;
    if (keepEvents) { for (const e of r.events) events.push(e); }
    else if (r.eventTotals) {
      for (const k in r.eventTotals) eventTotals[k] = (eventTotals[k] || 0) + r.eventTotals[k];
    }
    if (trace && r.trace) { for (const t of r.trace) trace.push(t); }
    if (r.accelerated) (accelerated || (accelerated = [])).push(...r.accelerated);
    if (r.certificate) cert = r.certificate;
    // A slice's exit rebase shifts the state frame; its `next` is reported
    // pre-shift (in the frame ITS horizon was posed) — bring it along.
    const rb = r.rebase !== undefined ? ratParts(r.rebase) : null;
    const settledTo = toCaller(h);       // h was posed in the pre-shift frame
    if (rb && rb[0] !== 0n) {
      acc = _wAdd(acc, rb);
      next = r.next === null ? null : putRat(..._wSub(ratParts(r.next), rb));
    } else {
      next = r.next;
    }
    if (opts.onChunk) {
      opts.onChunk({ chunks, settledTo, steps,
        next: next === null ? null : toCaller(next) });
    }
    if (final) break;
  }
  const out = {
    state: opts.raw ? state : toObject(state),
    quiescent: last.quiescent,
    steps, chunks, events, trace,
    next: next === null ? null : toCaller(next),
  };
  if (eventTotals) out.eventTotals = eventTotals;
  if (accelerated) out.accelerated = accelerated;
  if (opts.rebase) out.rebase = acc[0] === 0n ? tcfg.effect.unit() : putRat(...acc);
  if (last.certificate) out.certificate = last.certificate;
  return out;
}

// Scope guard: UNWEIGHTED additive-choice consequents have no timed story —
// use `woplus Q A B` (Phase 4b), whose alternatives carry a distribution.
// Validated lists are remembered — per-tick settles skip the O(#rules) walk.
const _multiAltOk = new WeakSet();
function _rejectMultiAlt(ruleList) {
  if (typeof ruleList === 'object' && _multiAltOk.has(ruleList)) return;
  for (const r of ruleList) {
    if (r.consequentAlts && r.consequentAlts.length > 1 && !r.weighted) {
      throw new Error(`Rule '${r.name}': unweighted additive-choice consequents under the timed scheduler — use woplus Q A B (weighted internal choice)`);
    }
  }
  if (typeof ruleList === 'object') _multiAltOk.add(ruleList);
}

// ─── Phase 4b: weighted internal choice (woplus) ────────────────────

/**
 * Resolve an alternative's weight to an exact [n,d] pair. Ground weights
 * pass through; symbolic weights ({ g, syms } — fire-time woplus, Phase 6)
 * multiply in each θ-resolved factor (comp: the 1−Q complement). Every
 * factor must resolve to a ground rational in [0,1] — canonStamp folds
 * clause-derived forms (rat(N,D) terms, i/o/e chains) first, mirroring the
 * delay/window paths. Loud failure: an ill-sorted or out-of-range weight
 * is a program bug, not a non-match (the tokens are already committed).
 */
function _altWeight(alt, m, tcfg) {
  const w = alt.weight;
  if (Array.isArray(w)) return w;
  let out = w.g;
  for (const s of w.syms) {
    let q = m.theta[s.slot];
    if (q !== undefined && tcfg.canonStamp) q = tcfg.canonStamp(q);
    let nd = q === undefined ? null : ratParts(q);
    if (!nd) {
      throw new Error(`Rule '${m.rule.name}': woplus weight did not resolve to a ground rational at fire time (got '${q === undefined ? 'unbound' : Store.tag(q)}')`);
    }
    if (nd[0] < 0n || nd[0] > nd[1]) {
      throw new Error(`Rule '${m.rule.name}': woplus weight resolved to ${nd[0]}/${nd[1]} — outside [0, 1]`);
    }
    if (s.comp) nd = _wSub([1n, 1n], nd);
    out = _wMul(out, nd);
  }
  return out;
}

/**
 * Sample a weighted alternative via the same stateless PRF family as the
 * conflict chooser (D17): u = mix(seed, state hash, match identity)/2³²
 * falls into the cumulative-weight interval of exactly one alternative
 * (weights are exact rationals summing to 1 — compile validates ground
 * distributions; fire-time weights sum to 1 by the Q/1−Q construction).
 * Reproducible and horizon-split invariant by construction.
 */
function _sampleAlt(m, state, seed, tcfg) {
  const alts = m.rule.consequentAlts;
  const r = _mix32((seed >>> 0) ^ state.stateHash ^ _mix32((m.rule.hash | 0) ^ _thetaHash(m.theta)));
  const u = [BigInt(r >>> 0), 4294967296n];
  let cum = [0n, 1n];
  for (let i = 0; i < alts.length; i++) {
    cum = _wAdd(cum, _altWeight(alts[i], m, tcfg));
    if (_wCmp(u, cum) < 0) return i;
  }
  return alts.length - 1;   // u = 1 - ε edge
}

/** Commit a match to one consequent alternative (clone with nulled
 *  compiled-substitution caches — they are indexed for alternative 0). */
function _withAlt(m, i) {
  return {
    ...m,
    altIndex: i,
    rule: {
      ...m.rule, consequent: m.rule.consequentAlts[i],
      compiledConseqLinear: null, compiledConseqPersistent: null,
    },
  };
}

// ─── Timed explore: branch only on genuine conflicts ────────────────

/**
 * Exhaustive exploration of a timed state up to the horizon: the set of
 * outcomes reachable under ANY conflict-chooser resolution. Firing order is
 * FIXED by activation (D12), so interleavings of independent events are
 * never branched — confluence prunes them by construction. A branch point
 * is a GENUINE conflict only: two equal-activation matches drawing on the
 * same cohort (who gets the token is the chooser's call — either answer is
 * a distinct world), consumers starving a read of its last copies, or —
 * round 13 — a tied match that can PRODUCE at the current instant into a
 * predicate some rule consumes (instant-feeding): a zero-delay firing can
 * enable a new competitor (or grow a !_W cohort) for another tied match,
 * so committing one order is no longer exhaustive (ample-set condition).
 * Concurrent reads alone never conflict (E7.2).
 *
 * Candidates are per-rule minimal-activation matches (same as exec) —
 * within-rule alternative assignments at equal activation are FIFO-broken
 * by the Matching spec, identically in every branch, so the enumeration
 * covers exactly exec's reachable set. (A broader assignment-level
 * branching criterion is THY-A territory — open question 2.)
 *
 * Returns { tree, leaves } — leaves are plain final states (settled at T).
 */
function settleExplore(inputState, rules, opts = {}) {
  const tcfg = opts.timedConfig;
  if (!tcfg) throw new Error('settleExplore requires opts.timedConfig');
  const horizon = opts.horizon;
  if (horizon === undefined || !tcfg.isStamp(horizon)) {
    throw new Error('settleExplore requires opts.horizon as a ground stamp');
  }
  // maxSteps bounds TOTAL fired events across the whole tree (the Zeno
  // guard, D16, and the memory guard: every node holds match/state data, so
  // a depth-only bound would let a branchy tree do unbounded work). The
  // separate DEPTH_CAP keeps the recursive DFS inside the JS stack budget —
  // schedules deeper than it belong to settle() (iterative explore rides
  // with the Phase-7 subtree-memo rewrite).
  const maxSteps = opts.maxSteps || 10000;
  const DEPTH_CAP = 1000;
  let fired = 0;
  const matchOpts = opts.matchOpts || EMPTY_MATCH_OPTS;
  const calc = opts.calc || null;
  const ruleList = Array.isArray(rules) ? rules : (rules.rules || rules);
  _rejectMultiAlt(ruleList);
  clearBWCache();

  const root = normalizeTimedState(inputState, tcfg);
  const stamps = root.linear.stamps;      // shared across branch snapshots
  const cmp = (a, b) => stamps.cmp(a, b);
  const horizonId = stamps.internTerm(horizon);

  const leaves = [];

  // Instant-feeding precomputation (round 13): the fact keys any rule's
  // linear antecedent mentions (factKeyOf — the SAME function that keys
  // output heads in _feedsInstant, round-14), plus whether any pattern
  // has a variable head (matches everything — then ALL instant
  // production feeds). Lax keys also cover literal-fact patterns, which
  // the strict triggerPreds space reported as wildcards.
  const { preds: antePreds, wildcard: wildcardPattern } = _antePredSet(ruleList, tcfg);

  // pathWeight: exact [num, den] product of woplus branch weights along the
  // path (conflict branches don't divide weight — they are adversarial
  // chooser worlds, each carrying its full conditional distribution).
  function step(state, depth, pathWeight) {
    if (depth > DEPTH_CAP) {
      throw new Error(`settleExplore: recursion depth ${depth} exceeded the DFS stack cap (${DEPTH_CAP}) — schedules this deep belong to settle()`);
    }
    const cands = [];
    for (const r of ruleList) {
      const m = tryTimedMatch(r, state, calc, matchOpts, tcfg);
      if (m) cands.push(m);
    }
    if (opts.compileLoli) {
      loliCandidates(state, tcfg, opts.compileLoli, calc, matchOpts, cands);
    }
    let aMin = null;
    if (cands.length > 0) {
      aMin = cands[0].activation;
      for (const m of cands) if (cmp(m.activation, aMin) < 0) aMin = m.activation;
    }
    if (aMin === null || cmp(aMin, horizonId) > 0) {
      const leaf = { type: 'leaf', state: toObject(state), weight: pathWeight };
      if (aMin !== null) leaf.next = stamps.term(aMin);
      leaves.push(leaf);
      return leaf;
    }
    const tied = cands.filter(mm => cmp(mm.activation, aMin) === 0);
    if (tied.length === 1 ||
        !(_conflicts(tied, state) ||
          tied.some(m => _feedsInstant(m, tcfg, antePreds, wildcardPattern)))) {
      // Independent (or singleton) tied set: any order reaches the same
      // state — commit without branching (partial-order reduction). Sound
      // because disjoint consumed cohorts + no read starvation + no
      // instant-feeding ⇒ tied firings commute (each per-rule best match
      // recomputes identically after any other fires).
      const m = tied.slice().sort((a, b) => (_matchKey(a) < _matchKey(b) ? -1 : 1))[0];
      return _fireOrFork(state, m, depth, pathWeight);
    }
    // Genuine conflict: branch on each tied candidate firing first.
    const sorted = tied.slice().sort((a, b) => (_matchKey(a) < _matchKey(b) ? -1 : 1));
    const children = [];
    for (const m of sorted) {
      const branch = state.snapshot();
      children.push({
        choice: { rule: m.rule.name, consumed: _consumedToAt(m.consumed) },
        tree: _fireOrFork(branch, m, depth, pathWeight),
      });
    }
    return { type: 'conflict', activation: stamps.term(aMin), children };
  }

  /** Boundary: public tree nodes carry the at-encoding (THY_0024). */
  function _consumedToAt(obj) {
    const out = {};
    for (const k in obj) {
      const ref = Number(k);
      const h = Store.put(tcfg.stampTag, [refInner(ref), stamps.term(refStamp(ref))]);
      out[h] = (out[h] || 0) + obj[k];
    }
    return out;
  }

  // Fire a match; a weighted rule (woplus, 4b) forks into one child per
  // consequent alternative, the edge carrying its exact weight — the tree
  // IS the outcome distribution (weights sum to 1 per fork).
  function _fireOrFork(state, m, depth, pathWeight) {
    if (m.rule.weighted && m.rule.consequentAlts.length > 1) {
      const children = [];
      for (let i = 0; i < m.rule.consequentAlts.length; i++) {
        const w = _altWeight(m.rule.consequentAlts[i], m, tcfg);
        const branch = state.snapshot();
        _countFired();
        fire(branch, _withAlt(m, i), tcfg);
        children.push({ weight: w, tree: step(branch, depth + 1, _wMul(pathWeight, w)) });
      }
      return { type: 'choice', rule: m.rule.name, activation: stamps.term(m.activation), children };
    }
    _countFired();
    fire(state, m, tcfg);
    return step(state, depth + 1, pathWeight);
  }

  function _countFired() {
    if (++fired > maxSteps) {
      throw new Error(`settleExplore: ${fired} total fired events exceeded maxSteps=${maxSteps} — zero-delay cycle or combinatorial branching? (Zeno guard, D16)`);
    }
  }

  const tree = step(root, 0, [1n, 1n]);
  return { tree, leaves };
}

/**
 * Instant-feeding test (round 13): can this tied match's firing add tokens
 * at the CURRENT instant (delay = unit, so outputs land at stamp a(m)) or
 * persistent facts (timeless — instantly visible) that some rule's
 * antecedent mentions? If so, firing it may enable a new same-instant
 * competitor for another tied match (or grow a !_W cohort), and committing
 * one order stops being exhaustive — the ample-set condition. Conservative:
 * unresolvable delays and unknown-headed outputs count as feeding.
 */
function _feedsInstant(m, tcfg, antePreds, wildcardPattern) {
  const rule = m.rule;
  if (rule.delay) {
    let d = rule.delay.ground !== undefined ? rule.delay.ground : m.theta[rule.delay.slot];
    if (d !== undefined && tcfg.canonStamp) d = tcfg.canonStamp(d);
    if (d !== undefined && tcfg.isStamp(d) &&
        tcfg.availability.cmp(d, tcfg.effect.unit()) !== 0) {
      return false;                 // strictly-future outputs can't join this instant
    }
  }
  const alts = rule.weighted && rule.consequentAlts ? rule.consequentAlts : [rule.consequent];
  for (const alt of alts) {
    if ((alt.persistent || []).length > 0) return true;
    for (const pat of (alt.linear || [])) {
      // Producing a POSSESSED RULE at this instant may enable a competitor
      // no static analysis foresaw — conservatively instant-feeding
      // (Phase 6c; the earlier delay check already excludes strictly-future
      // rule births, so menus produced with a delay keep the pruning).
      if (tcfg.implTag && Store.tag(pat) === tcfg.implTag) return true;
      const pred = factKeyOf(pat, tcfg.expTag);
      if (!pred) return true;                                      // unknown head
      if (wildcardPattern || antePreds.has(pred)) return true;
    }
  }
  return false;
}

// ─── Cohort firing (TODO_0278 B1) ───────────────────────────────────

/**
 * May this match fire at multiplicity > 1? Sound iff the sequential
 * scheduler would fire this exact match k times consecutively — the
 * caller has already checked uniqueness (tied.length === 1); this guard
 * rules out every channel through which an intermediate fire could
 * change the candidate landscape at the instant (riders 1b-1f):
 *  - same-instant enablement (_feedsInstant: zero-delay outputs feeding
 *    a rule/loli antecedent, or a wildcard pattern in scope);
 *  - persistent production at ANY delay — persistent facts are timeless,
 *    visible at the instant even under a delayed monad (stricter than
 *    _feedsInstant's early delay-return);
 *  - weighted consequents (each fire draws its own alt from a state-
 *    dependent PRF; a multinomial batch is A3b's world-valid mode);
 *  - existential outputs (resolveEx runs per fire);
 *  - possessed lolis (v1 conservative).
 * Every failure falls back to per-item firing — batching is
 * optimization, per-item is semantics (the FFI doctrine).
 */
function _batchGuard(m, tcfg, acc) {
  const rule = m.rule;
  if (m.loliFact) return false;
  if (rule.weighted && rule.consequentAlts && rule.consequentAlts.length > 1) return false;
  if (rule.existentialSlots && rule.existentialSlots.length > 0) return false;
  if ((rule.consequent.persistent || []).length > 0) return false;
  return !_feedsInstant(m, tcfg, acc.preds, acc.wildcard);
}

/**
 * Batch multiplicity: min over consumed refs of floor((count − reserved)
 * / take) — the largest k for which k identical fires of THIS match are
 * resource-covered from the SAME cohorts (rider 2). The formula subsumes
 * the coarse guards: `!_W` takes the whole pool (floor = 1); an
 * age-agnostic spread take fully exhausts every cohort but its last
 * (floor = 1 there); a preserved machine has count = #machines, so k
 * same-stamp machines batch k-parallel while the reproduced copies land
 * at a⊗d and serialize the next round. Reads subtract (each fire re-
 * reads the pool: k·take + reserve ≤ count).
 */
function _batchMult(m, state) {
  let mult = Infinity;
  for (const hStr in m.consumed) {
    const ref = Number(hStr);
    const have = state.linear.count(Store.tagId(refInner(ref)), ref);
    const res = m.reserved[hStr] || 0;
    const k = Math.floor((have - res) / m.consumed[hStr]);
    if (k < mult) mult = k;
    if (mult <= 1) return 1;
  }
  return mult === Infinity ? 1 : mult;   // no linear consumption: never batch
}

/** Conflict test over an equal-activation tied set: do two matches draw on
 *  the same cohort (token assignment is a genuine choice), or would the
 *  consumers starve a read of its needed copies (order-dependent, E7.2)? */
function _conflicts(tied, state) {
  const consumers = new Map();   // cohort -> # of tied matches consuming it
  const consumedNeed = new Map();
  const readNeed = new Map();
  for (const m of tied) {
    for (const hStr in m.consumed) {
      const h = Number(hStr);
      consumers.set(h, (consumers.get(h) || 0) + 1);
      consumedNeed.set(h, (consumedNeed.get(h) || 0) + m.consumed[hStr]);
    }
    for (const hStr in m.reserved) {
      const h = Number(hStr);
      const take = m.reserved[hStr];
      if (take > (readNeed.get(h) || 0)) readNeed.set(h, take);
    }
  }
  for (const [h, need] of consumedNeed) {
    if (consumers.get(h) > 1) return true;   // shared cohort ⇒ chooser's call
    const have = state.linear.count(Store.tagId(refInner(h)), h);
    if (need > have - (readNeed.get(h) || 0)) return true;   // read starvation
  }
  return false;
}

export {
  buildTimedConfig, normalizeTimedState, tryTimedMatch, fire,
  settle, settleChunked, nextActivation, settleExplore,
  isAt, innerOf, stampOf, loliCandidates,
};
export default {
  buildTimedConfig, normalizeTimedState, tryTimedMatch, fire,
  settle, settleChunked, nextActivation, settleExplore,
  isAt, innerOf, stampOf, loliCandidates,
};

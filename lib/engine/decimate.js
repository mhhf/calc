/**
 * Decimation driver — collapse of superposed existentials (TODO_0297
 * P2/P3; design 0292 L3/M1/M4/M8/M9, theory THY_0026).
 *
 * The timed engine leaves an unresolved existential consequent in the
 * state as a SUSPENDED fact — `at(superpose(s, exists(body)), t)` for the
 * ∃_ρ surface `exists X: s @w. A`, or `at(exists(body), t)` for a plain
 * binder. The superpose-fact IS THY_0026's wave: the un-fired ∃_ρ-R,
 * carrying its domain sort. Plain settle never touches either (D4);
 * under the driver, ∃_ρ superposes and plain ∃ SKOLEMIZES (M1 — a fresh
 * evar that is never collapsed, reported in `skolems`). The loop:
 *
 *   settle → OPEN each suspended fact (fresh evar into the binder,
 *   conjuncts split at the original stamp; superpose registers a wave
 *   evar → sort, plain registers a skolem) → re-settle (bias rules bind
 *   the evar; knowledge accumulates monotonically) → posteriors:
 *   prior(c) · Π distinct bias facts (M8) → min-entropy wave first (M5)
 *   → draw a member (PRF, exact rational weights) → substituteEvar
 *   (targeted re-hash) → … until no waves remain.
 *
 * RECURSION (P3): a classifier may have CONSTRUCTOR members
 * (`cons: (a: lst) -> lst @w Q.` — rung 2). Drawing one instantiates the
 * head only: the witness is `cons(e')` with fresh arg evars registered
 * as NEW waves of the argument sorts — lazy fixpoint collapse, i.e.
 * ancestral PCFG sampling (THY_0026 §3). Almost-sure termination iff
 * the prior is subcritical (Chi–Geman, T2) — the load lint advises,
 * and M7 hard-errors here on a supercritical prior without an explicit
 * maxCollapses. 'exact'/'solve' over a sort with constructor members
 * REQUIRE maxCollapses (the collapse tree is infinite); branches past
 * the bound are DROPPED and the result is marked `truncated` — the
 * depth-bounded total is a monotone lower fixpoint approximant of the
 * true mass (D2(iii)).
 *
 * Wave identity for PRF inputs is VALUE-derived (THY_0024): the facts
 * containing the evar with the evar replaced by a hole marker — never
 * the evar id. A wave consumed un-observed (a rule ate the fact holding
 * it before any draw) is dropped: no choice was made, no mass factor.
 *
 * Realizations (M4/D3 — evaluation strategies of ONE weighted forest):
 *   'sample' — settle-shaped run; contradiction (a wave with zero
 *              posterior mass) restarts from the initial snapshot with
 *              the attempt counter in every PRF input (M9). Returns the
 *              ground state + exact importance accounting (T3): mass =
 *              Π drawn wave weights · Π woplus branch weights (the
 *              settle-side ⊕ draws are part of the sampled path —
 *              cross-mode consistency with 'exact'); importance =
 *              Π posterior totals only (woplus factors cancel in the
 *              estimator, so E[importance] = total mass INCLUDING
 *              woplus branching). E[importance] holds PER ATTEMPT
 *              (failures count as zero) — the returned first-success
 *              value is conditioned on success; use `attempts` to
 *              Horvitz–Thompson correct when contradictions occur
 *              (THY_0026 §8 T3 caveat).
 *   'exact'  — enumerate the collapse tree; outcomes carry exact
 *              unnormalized masses (normalization is META, D2), deduped
 *              by final state. woplus forks inside settle are enumerated
 *              too (settleExplore composition — both are ⊕ realizations,
 *              weights sum to 1 per fork so totals are woplus-invariant);
 *              genuine conflicts are adversarial, not ⊕, and error
 *              loudly (settleBranching: 'seed' restores the
 *              chooser-resolved reading).
 *   'solve'  — DFS with first-solution cutoff (decision queries, D7):
 *              deterministically complete up to the depth bound,
 *              distribution-distorting by design.
 *
 * Bias scope: posteriors read persistent `bias(wave, ctor, q)` facts
 * from the STATE (forward-derived monotone conditioning) plus ALL
 * clause-derived biases per (wave, member) via the all-solutions
 * backward query (calc.proveAll; distinct values multiply, duplicate
 * derivations of one value dedup — set semantics either way).
 * Datasort domains (regular-tree-language conditioning, inside-mass
 * renormalization) are TODO_0011 rung 2 — not smuggled in here.
 */

'use strict';

import Store from '../kernel/store.js';
import { freshEvar } from '../kernel/fresh.js';
import { debruijnSubst, apply } from '../kernel/substitute.js';
import { mul as ratMul, cmp as ratCmp, add as ratAdd, div as ratDiv } from '../rat.js';
import { mix32, strHash, sampleIndex } from './prf.js';
import { ratParts } from './theories/ratlit-theory.js';
import { _parseSignature } from './type-check.js';

const BIAS_PRED = 'bias';        // the M8 machinery predicate (like SORT_PREDS)
const WITHIN_PRED = 'within';    // dynamic datasort conditioning (fence B)
const ONE = [1n, 1n];
const ZERO = [0n, 1n];

// ─── term walks ─────────────────────────────────────────────────────

function _forEachEvar(h, fn) {
  if (Store.tag(h) === 'evar') { fn(h); return; }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) _forEachEvar(c, fn);
  }
}

function _containsEvar(h, e) {
  if (h === e) return true;
  if (Store.tag(h) === 'evar') return false;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && _containsEvar(c, e)) return true;
  }
  return false;
}

/** Rebuild h with every occurrence of evar e replaced by val. */
function _substEvar(h, e, val) {
  if (h === e) return val;
  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const r = _substEvar(c, e, val);
      if (r !== c) changed = true;
      nc.push(r);
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(Store.tag(h), nc) : h;
}

// ─── boundary-state helpers (plain {linear, persistent} objects) ────

const _clone = (s) => ({ linear: { ...s.linear }, persistent: { ...(s.persistent || {}) } });
const _bump = (zone, h, n) => { zone[h] = (zone[h] || 0) + n; if (zone[h] === 0) delete zone[h]; };

function _stripStamp(h, stampTag) {
  return Store.tag(h) === stampTag
    ? { inner: Store.child(h, 0), stamp: Store.child(h, 1) }
    : { inner: h, stamp: null };
}
const _restamp = (inner, stamp, stampTag) =>
  stamp === null ? inner : Store.put(stampTag, [inner, stamp]);

/** Canonical value key of a whole state (dedup for 'exact'). */
function _stateKey(s) {
  const part = (z) => Object.entries(z || {}).map(([h, c]) => `${h}x${c}`).sort().join(',');
  return part(s.linear) + '|' + part(s.persistent);
}

/**
 * Substitute an evar across a boundary state — the targeted re-hash.
 * Counts merge when substitution collides distinct facts.
 */
function substituteEvar(state, e, val) {
  const out = { linear: {}, persistent: {} };
  for (const zone of ['linear', 'persistent']) {
    for (const [k, n] of Object.entries(state[zone] || {})) {
      const h = Number(k);
      _bump(out[zone], _containsEvar(h, e) ? _substEvar(h, e, val) : h, n);
    }
  }
  return out;
}

// ─── opening suspended facts ────────────────────────────────────────

/** Split an opened ∃-body into linear/persistent conjunct insertions.
 *  Shared with the @draw checker (lib/prover/draw-check.js) — one
 *  definition of what a collapse inserts. */
function splitBody(h, roles) {
  const prod = roles.product || 'tensor';
  const unit = roles.unit || 'one';
  const bang = roles.exponential || 'bang';
  const linear = [];
  const persistent = [];
  (function go(x) {
    const t = Store.tag(x);
    if (t === prod) { go(Store.child(x, 0)); go(Store.child(x, 1)); return; }
    if (t === unit) return;
    if (t === bang) { persistent.push(Store.child(x, Store.arity(x) - 1)); return; }
    linear.push(x);
  })(h);
  return { linear, persistent };
}

/**
 * Open every suspended fact: `superpose(s, exists(body))` → wave evar of
 * declared sort s; plain `exists(body)` → skolem evar (M1/D4). Body
 * conjuncts split at the original stamp; each COUNT is its own opening.
 * Nested binders inside a body stay suspended for the next round.
 * Returns { state, opened, waves: [[evar, sort]], skolems: [evar],
 * opens: [{ fact, evar, sort|null }] } — opens records one entry per
 * opening (fact = the suspended fact hash incl. its stamp wrapper), the
 * raw material of run certification (elaborate-collapse.js).
 */
function openSuspended(state, { stampTag, roles, sorts }) {
  let opened = 0;
  const waves = [];
  const skolems = [];
  const opens = [];
  const out = { linear: {}, persistent: { ...(state.persistent || {}) } };
  for (const [k, n] of Object.entries(state.linear || {})) {
    const h = Number(k);
    const { inner, stamp } = _stripStamp(h, stampTag);
    const t = Store.tag(inner);
    let sortName = null;
    let ex = null;
    if (t === 'superpose') {
      const sAtom = Store.child(inner, 0);
      ex = Store.child(inner, 1);
      sortName = Store.tag(sAtom) === 'atom' ? Store.child(sAtom, 0) : null;
      if (sortName === null || Store.tag(ex) !== 'exists') {
        throw new Error('decimate: malformed superpose fact — expected superpose(<sort>, exists(body))');
      }
      if (!sorts || !(sorts.isClassifier(sortName) ||
          (sorts.isDatasort && sorts.isDatasort(sortName)))) {
        throw new Error(`decimate: superposed sort '${sortName}' is not a classifier or datasort`);
      }
    } else if (t === 'exists') {
      ex = inner;
    } else {
      _bump(out.linear, h, n);
      continue;
    }
    for (let i = 0; i < n; i++) {
      const e = freshEvar();
      if (sortName !== null) waves.push([e, sortName]);
      else skolems.push(e);
      opens.push({ fact: h, evar: e, sort: sortName });
      const body = debruijnSubst(Store.child(ex, 0), 0n, e);
      const { linear, persistent } = splitBody(body, roles);
      for (const f of linear) _bump(out.linear, _restamp(f, stamp, stampTag), 1);
      for (const f of persistent) _bump(out.persistent, f, 1);
      opened++;
    }
  }
  return { state: out, opened, waves, skolems, opens };
}

/** Does evar e occur anywhere in the state? */
function _occurs(state, e) {
  for (const zone of ['linear', 'persistent']) {
    for (const k of Object.keys(state[zone] || {})) {
      if (_containsEvar(Number(k), e)) return true;
    }
  }
  return false;
}

/** Value-derived wave key (THY_0024): the facts containing the evar,
 *  target → hole, other evars → a generic mark; never the evar id. */
const _HOLE = () => Store.put('atom', ['_wave_hole']);
const _MARK = () => Store.put('atom', ['_wave_other']);
function _waveKey(state, e) {
  const hole = _HOLE(); const mark = _MARK();
  const parts = [];
  for (const zone of ['linear', 'persistent']) {
    for (const [k, n] of Object.entries(state[zone] || {})) {
      const h = Number(k);
      if (!_containsEvar(h, e)) continue;
      let holed = _substEvar(h, e, hole);
      // Other evars → a generic mark (their ids must not leak either)
      let prev;
      do { prev = holed; let other = null;
        _forEachEvar(holed, (x) => { if (other === null) other = x; });
        if (other !== null) holed = _substEvar(holed, other, mark);
      } while (holed !== prev);
      parts.push(`${zone[0]}${holed}x${n}`);
    }
  }
  return parts.sort().join(',');
}

// ─── posteriors (M8) ────────────────────────────────────────────────

/**
 * Posterior weights over a wave's domain: prior(c) · Π distinct bias
 * facts bias(e, c, q). State-resident persistent facts are enumerated
 * exactly (content-addressed dedup is free set semantics); clause-derived
 * bias is enumerated ALL-SOLUTIONS per (wave, member) via calc.proveAll
 * (resolve-all SLD) — independent clause-derived biases each condition
 * the posterior, and derivations of the SAME value dedup to one factor
 * (the fact-set semantics, identical to state-resident facts). A
 * committed-choice calc.prove probe remains the fallback for calculi
 * without proveAll.
 */
function _posterior(calc, state, e, sort) {
  // Domain: classifier members, or a datasort's admitted heads over its
  // base (static conditioning — restriction, masses unchanged, B4).
  // Recursive datasorts (trans nonempty) add child-state tracking and a
  // mass-proportional DRAW distribution (the exact conditioned sampler:
  // drawWeights(c) = massFactor(c) · Π m(child states) — B6's telescope
  // makes importance ≡ m(state) on bias-free programs). Dynamic
  // `within(e, S)` facts intersect further below (finite domains only —
  // recursive intersection is product states, fence B slice 3).
  // The registered sort may itself be a product key (a child wave of an
  // entangled conditioned draw) — resolve through stateInfo.
  const regInfo = calc.sorts.stateInfo ? calc.sorts.stateInfo(sort) : null;
  const isDs = regInfo !== null;
  const base = isDs ? regInfo.base : sort;
  // Dynamic `within(e, S)` facts join the wave's registered sort into a
  // canonical PRODUCT state (slice 3, Q2: anonymous intersections —
  // membership is just both goals; this is only the mass/draw index).
  const stateNames = isDs ? sort.split('&') : [];
  for (const k of Object.keys(state.persistent || {})) {
    const h = Number(k);
    if (Store.tag(h) !== WITHIN_PRED || Store.arity(h) < 2) continue;
    if (Store.child(h, 0) !== e) continue;
    const sAtom = Store.child(h, 1);
    const sName = Store.tag(sAtom) === 'atom' ? Store.child(sAtom, 0) : null;
    const info = sName !== null && calc.sorts.isDatasort && calc.sorts.isDatasort(sName)
      ? calc.sorts.datasortInfo(sName) : null;
    if (!info) {
      throw new Error(`decimate: within(_, '${sName}') — '${sName}' is not a declared datasort`);
    }
    if (info.base !== base && !calc.sorts.subsort(base, info.base)) {
      throw new Error(`decimate: within(_, '${sName}') conditions a wave over '${base}' but '${sName}' refines '${info.base}'`);
    }
    stateNames.push(sName);
  }
  let members;
  let childStates = null;
  let emptyProduct = false;
  let stateKey = null;   // effective conditioning state, when ≠ the registered sort
  if (stateNames.length === 0) {
    members = [...calc.sorts.membersOf(sort)].sort();
    if (members.length === 0) throw new Error(`decimate: classifier '${sort}' has no members`);
    // When the program has inside masses (recursive datasorts declared),
    // ⊤ structured waves ALSO draw mass-proportionally — exact ancestral
    // sampling, and the B6 telescope needs it (a ρ-proportional ⊤ child
    // under a conditioned root would break the per-seed constancy).
    // Programs without datasorts keep the ρ-proportional + importance
    // discipline unchanged (presence-gated: calc.masses is null there).
    if (calc.masses && _isStructured(calc, sort)) {
      childStates = new Map();
      for (const m of members) {
        const sigHash = calc.definitions.get(m);
        const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
        if (sig && sig.argSorts.length > 0) childStates.set(m, sig.argSorts);
      }
    }
  } else {
    const key = calc.sorts.stateInfo.canon(stateNames);
    const info = calc.sorts.stateInfo(key);
    if (key !== sort) stateKey = key;
    members = [...info.members, ...info.trans.keys()].sort();
    if (info.trans.size > 0) childStates = new Map(info.trans);
    if (members.length === 0) {
      // over-constrained product: the conditioned event is empty —
      // contradiction (M9 restart / dead branch), not an error
      if (stateNames.length === 1) throw new Error(`decimate: datasort '${sort}' has no members`);
      emptyProduct = true;
    }
  }
  if (emptyProduct) {
    return { members: [], weights: [], total: ZERO,
      drawWeights: [], drawTotal: ZERO, childStates: null, stateKey };
  }
  const prior = (m) => (calc.priors && calc.priors.get(m)) || ONE;
  const seen = new Set();
  const biasByMember = new Map(members.map((m) => [m, ONE]));
  const applyBias = (factHash) => {
    if (Store.tag(factHash) !== BIAS_PRED || Store.arity(factHash) < 3) return;
    if (Store.child(factHash, 0) !== e) return;
    const c = Store.child(factHash, 1);
    if (Store.tag(c) !== 'atom') return;
    const name = Store.child(c, 0);
    if (!biasByMember.has(name) || seen.has(factHash)) return;
    const q = ratParts(Store.child(factHash, 2));
    if (!q || q[0] < 0n) {
      throw new Error(`decimate: bias weight for '${name}' is not a nonnegative rational`);
    }
    seen.add(factHash);
    biasByMember.set(name, ratMul(biasByMember.get(name), q));
  };
  for (const k of Object.keys(state.persistent || {})) applyBias(Number(k));
  // Clause-derived bias: all-solutions per (wave, member) — dedup by
  // fact hash makes derivation multiplicity irrelevant (set semantics).
  if (typeof calc.proveAll === 'function') {
    const MAX = 256;
    for (const m of members) {
      const qv = Store.put('metavar', ['_Q']);
      const goal = Store.put(BIAS_PRED, [e, Store.put('atom', [m]), qv]);
      let sols = [];
      try { sols = calc.proveAll([goal], { maxSolutions: MAX }); } catch { /* no bias clauses — fine */ }
      if (sols.length > MAX) {
        throw new Error(`decimate: more than ${MAX} clause-derived bias solutions for '${m}' — unbounded bias enumeration (make the bias clause deterministic or derive bias facts forward)`);
      }
      for (const theta of sols) {
        const val = apply(qv, theta);
        if (val !== qv) applyBias(Store.put(BIAS_PRED, [e, Store.put('atom', [m]), val]));
      }
    }
  } else if (typeof calc.prove === 'function') {
    // committed-choice fallback (calculi without proveAll)
    for (const m of members) {
      const qv = Store.put('metavar', ['_Q']);
      const goal = Store.put(BIAS_PRED, [e, Store.put('atom', [m]), qv]);
      let res = null;
      try { res = calc.prove(goal); } catch { /* no bias clauses — fine */ }
      if (res && res.success && res.theta) {
        const val = apply(qv, res.theta);
        if (val !== qv) applyBias(Store.put(BIAS_PRED, [e, Store.put('atom', [m]), val]));
      }
    }
  }
  const weights = members.map((m) => ratMul(prior(m), biasByMember.get(m)));
  let total = ZERO;
  for (const w of weights) total = ratAdd(total, w);
  // Conditioned-structured waves draw ∝ massFactor·Π m(child states) —
  // the exact sampler over the restricted language; the recorded MASS
  // factor stays the prior·bias product (restriction semantics, B4).
  let drawWeights = weights;
  let drawTotal = total;
  if (childStates !== null) {
    drawWeights = members.map((m, i) => {
      const cs = childStates.get(m);
      if (!cs) return weights[i];
      let w = weights[i];
      for (const s of cs) {
        // the calculus-bound solver covers lazily-arising product states
        // (slice 3) and classifier ⊤ states alike; load-time states are
        // cache hits
        if (!calc._datasortMass) {
          throw new Error(`decimate: conditioned draws need an inside-mass solver — this calculus binds none (cc.datasortMasses)`);
        }
        const ms = calc._datasortMass.ensureMass(calc, s);
        if (!ms) throw new Error(`decimate: no inside mass for state '${s}'`);
        w = ratMul(w, ms);
      }
      return w;
    });
    drawTotal = ZERO;
    for (const w of drawWeights) drawTotal = ratAdd(drawTotal, w);
  }
  return { members, weights, total, drawWeights, drawTotal, childStates, stateKey };
}

function _entropy({ weights, total }) {
  if (total[0] === 0n) return 0;
  const T = Number(total[0]) / Number(total[1]);
  let h = 0;
  for (const [n, d] of weights) {
    if (n === 0n) continue;
    const p = (Number(n) / Number(d)) / T;
    h -= p * Math.log(p);
  }
  return h;
}

// ─── witnesses (lazy head-constructor collapse, P3) ─────────────────

/**
 * Build the witness for member m: an atom for a nullary member, or
 * `m(e1..ek)` with fresh arg-evar WAVES for a constructor member (lazy
 * fixpoint collapse — one head per draw, THY_0026 §3).
 */
function _witness(calc, m, childStates = null) {
  const sigHash = calc.definitions.get(m);
  const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
  if (!sig || sig.argSorts.length === 0) {
    return { hash: Store.put('atom', [m]), argWaves: [] };
  }
  const argWaves = [];
  const args = sig.argSorts.map((s, i) => {
    // Conditioned draws register arg waves at the automaton's CHILD
    // STATES (datasort names or product keys) instead of the ⊤ arg sorts.
    const st = childStates ? childStates[i] : s;
    if (!(calc.sorts.isClassifier(st) ||
        (calc.sorts.stateInfo && calc.sorts.stateInfo(st) !== null))) {
      throw new Error(`decimate: constructor member '${m}' has a non-classifier argument sort '${st}' — its argument cannot superpose`);
    }
    const e2 = freshEvar();
    argWaves.push([e2, st]);
    return e2;
  });
  return { hash: Store.put(m, args), argWaves };
}

/** Does the sort have constructor members (⟹ possibly infinite tree)? */
function _isStructured(calc, sort) {
  const info = calc.sorts.stateInfo ? calc.sorts.stateInfo(sort) : null;
  if (info) return info.trans.size > 0;
  for (const m of calc.sorts.membersOf(sort)) {
    const sigHash = calc.definitions.get(m);
    const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
    if (sig && sig.argSorts.length > 0) return true;
  }
  return false;
}

// ─── the driver ─────────────────────────────────────────────────────

/**
 * Settle to quiescence, opening suspended facts between rounds until
 * none remain; waveMap/skolemSet accumulate the openings. A wave whose
 * evar no longer occurs (consumed un-observed) is dropped.
 */
/** Π woplus branch weights over a settle segment's weighted firings —
 *  the settle-side ⊕ draws of a sampled path (cross-mode consistency
 *  with 'exact', which enumerates them via settleExplore). */
function _woplusFactor(events, ruleByName) {
  let f = ONE;
  for (const ev of events || []) {
    if (ev.alt === undefined) continue;
    const r = ruleByName && ruleByName.get(ev.rule);
    if (!r || !r.weighted || !r.consequentAlts) {
      throw new Error(`decimate: weighted firing by rule '${ev.rule}' outside the program's rule table — mass accounting incomplete`);
    }
    const w = r.consequentAlts[ev.alt].weight;
    const mult = ev.multiplicity || 1;
    for (let i = 0; i < mult; i++) f = ratMul(f, w);
  }
  return f;
}

function _settleOpen(calc, state, horizon, sOpts, env, waveMap, skolemSet, trace = null, acc = null) {
  for (;;) {
    const res = calc.settle(state, horizon, sOpts);
    if (!res.quiescent) {
      throw new Error('decimate: settle did not quiesce (raise settle maxSteps)');
    }
    if (trace) trace.push({ settle: res.events || [] });
    if (acc) acc.w = ratMul(acc.w, _woplusFactor(res.events, env.ruleByName));
    const { state: opened, opened: n, waves, skolems, opens } = openSuspended(res.state, env);
    state = opened;
    for (const [e, s] of waves) waveMap.set(e, s);
    for (const e of skolems) skolemSet.add(e);
    if (trace) for (const o of opens) trace.push({ open: o });
    if (n === 0) break;
  }
  for (const e of [...waveMap.keys()]) {
    if (!_occurs(state, e)) waveMap.delete(e);
  }
  return state;
}

/** Current waves as [{ e, sort, key }], key-sorted (deterministic). */
function _waves(state, waveMap) {
  return [...waveMap.entries()]
    .map(([e, sort]) => ({ e, sort, key: _waveKey(state, e) }))
    .sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0));
}

function _checkM7(calc, opts) {
  if (!opts.maxCollapses && calc.priorLint &&
      calc.priorLint.some((a) => a.kind === 'supercritical-prior')) {
    throw new Error('decimate: supercritical priors (Chi–Geman m > 1) — collapse diverges with positive probability; pass an explicit maxCollapses depth bound (M7)');
  }
}

function collapse(calc, initialState, opts = {}) {
  if (!calc.sorts) throw new Error('decimate: calculus/program without a sort system — waves need classifier sorts');
  const mode = opts.mode || 'sample';
  const seed = (opts.seed || 0) >>> 0;
  const horizon = opts.horizon !== undefined ? opts.horizon : '0';
  const maxCollapses = opts.maxCollapses || (mode === 'sample' ? 10000 : 0);
  const maxAttempts = opts.maxAttempts || 64;
  const env = { stampTag: opts.stampTag || 'at', roles: calc.roles || {}, sorts: calc.sorts };
  _checkM7(calc, opts);
  if (opts.trace && mode !== 'sample') {
    throw new Error("decimate: trace recording is a run-shaped notion — only mode 'sample' records one (exact/solve enumerate a tree)");
  }

  if (mode === 'sample') {
    // woplus draws inside settle are part of the sampled path: their
    // branch weights multiply into MASS (cross-mode consistency with
    // 'exact'). Importance is untouched — a woplus branch is sampled
    // with exactly its weight, so the factors cancel in the estimator
    // and E[importance] = total mass INCLUDING woplus branching (T3).
    const ruleByName = new Map((calc.forwardRules || []).map((r) => [r.name, r]));
    const envS = { ...env, ruleByName };
    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      const aSeed = mix32(seed ^ mix32(attempt >>> 0));
      // events forced ON: the woplus mass accounting reads the records
      const sOpts = { maxSteps: 10000, ...(opts.settle || {}), seed: aSeed, events: true };
      let state = _clone(initialState);
      const waveMap = new Map();
      const skolemSet = new Set();
      let mass = ONE;              // Π drawn weights (unnormalized true mass)
      let importance = ONE;        // Π posterior totals (T3 estimator weight)
      const collapses = [];
      const trace = opts.trace ? [] : null;   // per-attempt (restarts reset it)
      const acc = { w: ONE };                 // Π woplus branch weights
      let dead = false;
      for (let step = 0; step < maxCollapses; step++) {
        state = _settleOpen(calc, state, horizon, sOpts, envS, waveMap, skolemSet, trace, acc);
        const waves = _waves(state, waveMap);
        if (waves.length === 0) {
          return { state, ground: true, skolems: skolemSet.size, attempts: attempt,
            mass: ratMul(mass, acc.w), importance, collapses,
            ...(trace ? { trace } : {}) };
        }
        const posts = waves.map((w) => ({ w, p: _posterior(calc, state, w.e, w.sort) }));
        if (posts.some(({ p }) => p.drawTotal[0] === 0n)) { dead = true; break; }   // contradiction → restart (M9)
        let best = null; let bestH = Infinity;
        for (const c of posts) {
          const h = _entropy({ weights: c.p.drawWeights, total: c.p.drawTotal });
          if (h < bestH - 1e-12) { best = c; bestH = h; }
          else if (h < bestH + 1e-12 && best) {
            // PRF value-derived tie-break (never an id)
            const r = (k) => mix32(aSeed ^ mix32(strHash(k)) ^ mix32(step >>> 0));
            if (r(c.w.key) < r(best.w.key)) best = c;
          }
        }
        const { members, weights, total, drawWeights, drawTotal, childStates } = best.p;
        const u = mix32(aSeed ^ mix32(strHash(best.w.key)) ^ mix32(step >>> 0) ^ 0x9e3779b9);
        const idx = sampleIndex(u, members.length, (i) => drawWeights[i], drawTotal);
        mass = ratMul(mass, weights[idx]);
        // importance = mass/P(run): per draw, massFactor·drawTotal/drawWeight
        // — Σ(ρ·bias) for the prior-proportional sampler (unchanged), the
        // telescoping m(state)/Πm(children) for the conditioned one (B6)
        importance = ratMul(importance,
          ratDiv(ratMul(weights[idx], drawTotal), drawWeights[idx]));
        const sk = best.p.stateKey;
        collapses.push({ sort: best.w.sort, member: members[idx], weight: weights[idx], total,
          ...(sk ? { state: sk } : {}) });
        const wit = _witness(calc, members[idx],
          childStates ? childStates.get(members[idx]) || null : null);
        if (trace) {
          trace.push({ draw: { evar: best.w.e, sort: best.w.sort, member: members[idx],
            witness: wit.hash, ...(sk ? { state: sk } : {}) } });
        }
        waveMap.delete(best.w.e);
        for (const [e2, s2] of wit.argWaves) waveMap.set(e2, s2);
        state = substituteEvar(state, best.w.e, wit.hash);
      }
      if (!dead) throw new Error(`decimate: maxCollapses=${maxCollapses} exceeded — subcritical priors terminate a.s.; raise the bound or rebalance @w`);
    }
    throw new Error(`decimate: contradiction persisted through ${maxAttempts} restarts`);
  }

  if (mode === 'exact' || mode === 'solve') {
    const sOpts = { maxSteps: 10000, ...(opts.settle || {}), seed };
    const byKey = new Map();      // stateKey → { state, mass }
    let found = null;
    let truncated = false;

    // exact × woplus (TODO_0298): woplus forks inside settle are ⊕
    // branches of the SAME measure the waves realize — enumerate them
    // with settleExplore, multiplying exact leaf path-weights into the
    // branch mass (weights sum to 1 per fork, so T1 totals are
    // unchanged by woplus). A GENUINE conflict node is chooser
    // nondeterminism (adversarial worlds, not ⊕) with no mass
    // semantics — a loud error: make the contention confluent
    // (certifyContention) or pass settleBranching: 'seed' for the
    // chooser-resolved reading.
    const branching = opts.settleBranching ||
      (typeof calc.settleExplore === 'function' ? 'explore' : 'seed');
    const _hasConflict = (t) => {
      if (!t || typeof t !== 'object') return false;
      if (t.type === 'conflict') return true;
      for (const c of t.children || []) if (_hasConflict(c.tree)) return true;
      return false;
    };
    /** Settle-world enumeration: settle (all ⊕ branches) → open, to a
     *  fixpoint per world — the branching analogue of _settleOpen.
     *  Returns [{ state, waveMap, skolemSet, w }]; zero-weight worlds
     *  are dropped (like zero-weight members). */
    const settleWorlds = (state0, waveMap0, skolemSet0) => {
      const out = [];
      const go2 = (st, wm, sk, w) => {
        const res = calc.settleExplore(st, horizon, sOpts);
        if (_hasConflict(res.tree)) {
          throw new Error("decimate: settleExplore hit a genuine conflict — chooser nondeterminism is adversarial, not ⊕, and has no mass semantics; make the contention confluent or pass settleBranching: 'seed'");
        }
        for (const leaf of res.leaves) {
          const w2 = ratMul(w, leaf.weight || ONE);
          if (w2[0] === 0n) continue;
          const { state: opened, opened: n, waves, skolems } = openSuspended(leaf.state, env);
          const wm2 = new Map(wm);
          const sk2 = new Set(sk);
          for (const [e, s] of waves) wm2.set(e, s);
          for (const e of skolems) sk2.add(e);
          if (n === 0) {
            for (const e of [...wm2.keys()]) if (!_occurs(opened, e)) wm2.delete(e);
            out.push({ state: opened, waveMap: wm2, skolemSet: sk2, w: w2 });
          } else {
            go2(opened, wm2, sk2, w2);
          }
        }
      };
      go2(state0, waveMap0, skolemSet0, ONE);
      return out;
    };

    const go = (state0, waveMap0, skolemSet0, mass0, depth) => {
      if (found) return;
      if (branching !== 'explore') {
        const st = _settleOpen(calc, state0, horizon, sOpts, env, waveMap0, skolemSet0);
        goWaves(st, waveMap0, skolemSet0, mass0, depth);
        return;
      }
      for (const world of settleWorlds(state0, waveMap0, skolemSet0)) {
        if (found) return;
        goWaves(world.state, world.waveMap, world.skolemSet, ratMul(mass0, world.w), depth);
      }
    };

    const goWaves = (state, waveMap, skolemSet, mass, depth) => {
      if (found) return;
      const waves = _waves(state, waveMap);
      if (waves.length === 0) {
        if (mode === 'solve') { found = { state, skolems: skolemSet.size }; return; }
        const key = _stateKey(state);
        const prev = byKey.get(key);
        if (prev) prev.mass = ratAdd(prev.mass, mass);
        else byKey.set(key, { state, mass });
        return;
      }
      // Structured (possibly infinite) sorts need an explicit bound —
      // truncated branches are DROPPED (depth-bounded mass is a monotone
      // lower approximant of the true fixpoint, D2(iii)).
      if (!maxCollapses && waves.some((w) => _isStructured(calc, w.sort))) {
        throw new Error(`decimate: '${mode}' over a structured sort enumerates an infinite collapse tree — pass an explicit maxCollapses depth bound`);
      }
      if (maxCollapses && depth >= maxCollapses) { truncated = true; return; }
      // deterministic wave pick: min entropy, tie → lexicographic key
      let best = null; let bestH = Infinity;
      for (const w of waves) {
        const p = _posterior(calc, state, w.e, w.sort);
        const h = _entropy({ weights: p.drawWeights, total: p.drawTotal });
        if (h < bestH - 1e-12 || (h < bestH + 1e-12 && (!best || w.key < best.w.key))) {
          best = { w, p }; bestH = h;
        }
      }
      const { members, weights, childStates } = best.p;
      const order = members.map((m, i) => [m, weights[i]])
        .filter(([, w]) => w[0] > 0n);
      if (mode === 'solve') order.sort((a, b) => -ratCmp(a[1], b[1]) || (a[0] < b[0] ? -1 : 1));
      for (const [m, w] of order) {
        const wit = _witness(calc, m, childStates ? childStates.get(m) || null : null);
        const wm = new Map(waveMap);
        wm.delete(best.w.e);
        for (const [e2, s2] of wit.argWaves) wm.set(e2, s2);
        go(substituteEvar(state, best.w.e, wit.hash), wm, new Set(skolemSet), ratMul(mass, w), depth + 1);
        if (found) return;
      }
    };
    go(_clone(initialState), new Map(), new Set(), ONE, 0);
    if (mode === 'solve') {
      return found
        ? { state: found.state, ground: true, skolems: found.skolems, truncated }
        : { state: null, exhausted: true, truncated };
    }
    const outcomes = [...byKey.values()];
    let total = ZERO;
    for (const o of outcomes) total = ratAdd(total, o.mass);
    return { outcomes, total, truncated };
  }

  throw new Error(`decimate: unknown mode '${mode}' (sample | exact | solve)`);
}

// ─── interactive stepping (the shell's collapse mode, TODO_0298) ────

/**
 * One settle+open round to quiescence, then the wave menu: entropy-
 * sorted [{ e, sort, key, posterior, entropy }]. The caller threads
 * `session` = { state, waveMap, skolemSet } across calls (mutated in
 * place); the driver's own loop is `collapse` — this is its per-frame
 * face (each draw a frame).
 */
function collapseView(calc, session, opts = {}) {
  if (!calc.sorts) throw new Error('decimate: calculus/program without a sort system — waves need classifier sorts');
  const env = { stampTag: opts.stampTag || 'at', roles: calc.roles || {}, sorts: calc.sorts };
  const sOpts = { maxSteps: 10000, ...(opts.settle || {}), seed: (opts.seed || 0) >>> 0 };
  const horizon = opts.horizon !== undefined ? opts.horizon : '0';
  session.state = _settleOpen(calc, session.state, horizon, sOpts, env,
    session.waveMap, session.skolemSet);
  const waves = _waves(session.state, session.waveMap).map((w) => {
    const posterior = _posterior(calc, session.state, w.e, w.sort);
    return { ...w, posterior,
      entropy: _entropy({ weights: posterior.drawWeights, total: posterior.drawTotal }) };
  });
  waves.sort((a, b) => a.entropy - b.entropy || (a.key < b.key ? -1 : a.key > b.key ? 1 : 0));
  return waves;
}

/**
 * Draw one wave from a collapseView menu: PRF-sampled over its posterior
 * (value-derived inputs — seed/step/wave key, never evar ids), or forced
 * with opts.member. Substitutes the witness; constructor arg waves join
 * the session (rung 2). Returns the collapse record { sort, member,
 * weight, total }, or { contradiction: true } on zero posterior mass,
 * or { refused: member } for a forced member of zero weight.
 */
function collapseDraw(calc, session, wave, opts = {}) {
  const { members, weights, total, drawWeights, drawTotal, childStates } = wave.posterior;
  if (drawTotal[0] === 0n) return { contradiction: true };
  let idx;
  if (opts.member !== undefined) {
    idx = members.indexOf(opts.member);
    if (idx < 0) throw new Error(`decimate: '${opts.member}' is not a member of '${wave.sort}'`);
    if (drawWeights[idx][0] === 0n) return { refused: opts.member };
  } else {
    const seed = (opts.seed || 0) >>> 0;
    const step = (opts.step || 0) >>> 0;
    const u = mix32(seed ^ mix32(strHash(wave.key)) ^ mix32(step) ^ 0x9e3779b9);
    idx = sampleIndex(u, members.length, (i) => drawWeights[i], drawTotal);
  }
  const wit = _witness(calc, members[idx],
    childStates ? childStates.get(members[idx]) || null : null);
  session.waveMap.delete(wave.e);
  for (const [e2, s2] of wit.argWaves) session.waveMap.set(e2, s2);
  session.state = substituteEvar(session.state, wave.e, wit.hash);
  return { sort: wave.sort, member: members[idx], weight: weights[idx], total };
}

export {
  collapse, substituteEvar, openSuspended, splitBody,
  collapseView, collapseDraw,
  _substEvar as substEvarInTerm,
};
export default { collapse, substituteEvar, openSuspended, splitBody, collapseView, collapseDraw };

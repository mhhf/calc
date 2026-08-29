/**
 * Decimation driver — collapse of superposed existentials (TODO_0297 P2;
 * design 0292 L3/M4/M8/M9, theory THY_0026).
 *
 * The timed engine leaves an unresolved existential consequent in the
 * state as a SUSPENDED ∃-fact — `at(exists(body), t)` — which is exactly
 * THY_0026's wave: the un-fired ∃-R. Plain settle never touches it (D4
 * opt-in: running this driver is the observation). The driver's loop:
 *
 *   settle → OPEN each suspended ∃-fact (fresh evar into the binder,
 *   split the body's conjuncts at the same stamp) → re-settle (bias
 *   rules bind the evar, knowledge accumulates monotonically) → compute
 *   per-wave posteriors: prior(c) · Π distinct bias facts (M8) → pick
 *   the min-entropy wave (M5) → draw a member (PRF, exact rational
 *   weights) → substituteEvar (targeted re-hash) → re-settle … until
 *   the state is ground.
 *
 * Wave identity for PRF inputs is VALUE-derived (THY_0024): the facts
 * containing the evar, with the evar replaced by a hole marker — never
 * the evar id (ids are history-dependent). A wave's SORT is read off the
 * signature positions the evar occupies (closed world: every predicate
 * and constructor is declared); its domain is the classifier's members,
 * its prior weights come from calc.priors (@w — unannotated member = 1).
 *
 * Realizations (M4/D3 — evaluation strategies of ONE weighted forest):
 *   'sample' — settle-shaped run; contradiction (a wave with zero
 *              posterior mass) restarts from the initial snapshot with
 *              the attempt counter fed into every PRF input (M9).
 *              Returns the ground state + exact importance accounting
 *              (T3): mass = Π drawn weights, importance = Π posterior
 *              totals (E[importance] = total surviving mass).
 *   'exact'  — enumerate the full collapse tree; returns outcomes with
 *              exact unnormalized masses (normalization is META, D2)
 *              deduped by final state. woplus draws inside settle stay
 *              seed-resolved (composing with settleExplore is future
 *              work — documented, not hidden).
 *   'solve'  — DFS with first-solution cutoff (decision queries, D7):
 *              deterministically complete, distribution-distorting by
 *              design.
 *
 * M7: supercritical priors (calc.priorLint) hard-error here unless the
 * caller passes an explicit maxCollapses depth bound.
 *
 * Bias scope (P2): posteriors read persistent `bias(wave, ctor, q)`
 * facts from the STATE (forward-derived knowledge — the monotone
 * conditioning channel) plus at most one clause-derived bias per
 * (wave, member) via the calc's backward prover. Multiple independent
 * clause-derived biases per pair ride P3.
 */

'use strict';

import Store from '../kernel/store.js';
import { freshEvar } from '../kernel/fresh.js';
import { debruijnSubst, apply } from '../kernel/substitute.js';
import { mul as ratMul, cmp as ratCmp, add as ratAdd } from '../rat.js';
import { mix32, strHash, sampleIndex } from './prf.js';
import { ratParts } from './theories/ratlit-theory.js';
import { _parseSignature } from './type-check.js';

const BIAS_PRED = 'bias';        // the M8 machinery predicate (like SORT_PREDS)
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

// ─── wave discovery ─────────────────────────────────────────────────

/** Split an opened ∃-body into linear/persistent conjunct insertions. */
function _splitBody(h, roles) {
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
 * Open every suspended ∃-fact: replace `exists(body)` with body[0 := fresh
 * evar], conjuncts split at the original stamp. Each COUNT is its own
 * wave (k copies → k distinct evars). Nested binders stay suspended for
 * the next round. Returns { state, opened }.
 */
function openSuspended(state, { stampTag, roles }) {
  let opened = 0;
  const out = { linear: {}, persistent: { ...(state.persistent || {}) } };
  for (const [k, n] of Object.entries(state.linear || {})) {
    const h = Number(k);
    const { inner, stamp } = _stripStamp(h, stampTag);
    if (Store.tag(inner) !== 'exists') { _bump(out.linear, h, n); continue; }
    for (let i = 0; i < n; i++) {
      const body = debruijnSubst(Store.child(inner, 0), 0n, freshEvar());
      const { linear, persistent } = _splitBody(body, roles);
      for (const f of linear) _bump(out.linear, _restamp(f, stamp, stampTag), 1);
      for (const f of persistent) _bump(out.persistent, f, 1);
      opened++;
    }
  }
  return { state: out, opened };
}

/** All evars present in a boundary state (Set of hashes). */
function _stateEvars(state) {
  const evars = new Set();
  for (const zone of ['linear', 'persistent']) {
    for (const k of Object.keys(state[zone] || {})) _forEachEvar(Number(k), (e) => evars.add(e));
  }
  return evars;
}

/**
 * Resolve an evar's sort from the signature positions it occupies.
 * Returns the least classifier sort, or throws (an unsupported wave is
 * an error, never a silent skolem).
 */
function _waveSort(calc, state, e) {
  const sortSys = calc.sorts;
  const found = new Set();
  const visit = (h) => {
    const tag = Store.tag(h);
    const sigHash = calc.definitions.get(tag);
    const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
    const a = Store.arity(h);
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (!Store.isTermChild(c)) continue;
      if (c === e) {
        if (sig && sig.argSorts[i]) found.add(sig.argSorts[i]);
      } else if (_containsEvar(c, e)) {
        visit(c);
      }
    }
  };
  for (const zone of ['linear', 'persistent']) {
    for (const k of Object.keys(state[zone] || {})) {
      const h = Number(k);
      if (_containsEvar(h, e)) visit(h);
    }
  }
  let least = null;
  for (const s of found) {
    if (!sortSys.isClassifier(s)) continue;
    if (least === null || sortSys.subsort(s, least)) least = s;
    else if (!sortSys.subsort(least, s)) {
      throw new Error(`decimate: wave occupies incomparable classifier sorts ('${least}' vs '${s}')`);
    }
  }
  if (least === null) {
    throw new Error(`decimate: wave sort unresolved — the existential occupies no classifier-sorted position (sorts seen: ${[...found].join(', ') || 'none'})`);
  }
  return least;
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
 * exactly (content-addressed dedup is free set semantics); the backward
 * prover contributes at most one clause-derived bias per (wave, member).
 */
function _posterior(calc, state, e, sort) {
  const members = [...calc.sorts.membersOf(sort)].sort();
  if (members.length === 0) throw new Error(`decimate: classifier '${sort}' has no members`);
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
  // Clause-derived bias: one committed-choice probe per (wave, member).
  if (typeof calc.prove === 'function') {
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
  return { members, weights, total };
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

// ─── the driver ─────────────────────────────────────────────────────

/**
 * Settle to quiescence, opening suspended ∃-facts between rounds until
 * none remain. Returns the quiescent boundary state.
 */
function _settleOpen(calc, state, horizon, sOpts, env) {
  for (;;) {
    const res = calc.settle(state, horizon, sOpts);
    if (!res.quiescent) {
      throw new Error('decimate: settle did not quiesce (raise settle maxSteps)');
    }
    const { state: opened, opened: n } = openSuspended(res.state, env);
    state = opened;
    if (n === 0) return state;
  }
}

/** Enumerate the current waves: [{ e, sort, key }] sorted by key. */
function _waves(calc, state) {
  return [..._stateEvars(state)]
    .map((e) => ({ e, sort: _waveSort(calc, state, e), key: _waveKey(state, e) }))
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
  const maxCollapses = opts.maxCollapses || 10000;
  const maxAttempts = opts.maxAttempts || 64;
  const env = { stampTag: opts.stampTag || 'at', roles: calc.roles || {} };
  _checkM7(calc, opts);

  if (mode === 'sample') {
    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      const aSeed = mix32(seed ^ mix32(attempt >>> 0));
      const sOpts = { maxSteps: 10000, ...(opts.settle || {}), seed: aSeed };
      let state = _clone(initialState);
      let mass = ONE;              // Π drawn weights (unnormalized true mass)
      let importance = ONE;        // Π posterior totals (T3 estimator weight)
      const collapses = [];
      let dead = false;
      for (let step = 0; step < maxCollapses; step++) {
        state = _settleOpen(calc, state, horizon, sOpts, env);
        const waves = _waves(calc, state);
        if (waves.length === 0) {
          return { state, ground: true, attempts: attempt, mass, importance, collapses };
        }
        const posts = waves.map((w) => ({ w, p: _posterior(calc, state, w.e, w.sort) }));
        if (posts.some(({ p }) => p.total[0] === 0n)) { dead = true; break; }   // contradiction → restart (M9)
        let best = null; let bestH = Infinity;
        for (const c of posts) {
          const h = _entropy(c.p);
          if (h < bestH - 1e-12) { best = c; bestH = h; }
          else if (h < bestH + 1e-12 && best) {
            // PRF value-derived tie-break (never an id)
            const r = (k) => mix32(aSeed ^ mix32(strHash(k)) ^ mix32(step >>> 0));
            if (r(c.w.key) < r(best.w.key)) best = c;
          }
        }
        const { members, weights, total } = best.p;
        const u = mix32(aSeed ^ mix32(strHash(best.w.key)) ^ mix32(step >>> 0) ^ 0x9e3779b9);
        const idx = sampleIndex(u, members.length, (i) => weights[i], total);
        mass = ratMul(mass, weights[idx]);
        importance = ratMul(importance, total);
        collapses.push({ sort: best.w.sort, member: members[idx], weight: weights[idx], total });
        state = substituteEvar(state, best.w.e, Store.put('atom', [members[idx]]));
      }
      if (!dead) throw new Error(`decimate: maxCollapses=${maxCollapses} exceeded`);
    }
    throw new Error(`decimate: contradiction persisted through ${maxAttempts} restarts`);
  }

  if (mode === 'exact' || mode === 'solve') {
    const sOpts = { maxSteps: 10000, ...(opts.settle || {}), seed };
    const byKey = new Map();      // stateKey → { state, mass }
    let found = null;
    const go = (state, mass, depth) => {
      if (found) return;
      if (depth > maxCollapses) throw new Error(`decimate: maxCollapses=${maxCollapses} exceeded`);
      state = _settleOpen(calc, state, horizon, sOpts, env);
      const waves = _waves(calc, state);
      if (waves.length === 0) {
        if (mode === 'solve') { found = { state, mass }; return; }
        const key = _stateKey(state);
        const prev = byKey.get(key);
        if (prev) prev.mass = ratAdd(prev.mass, mass);
        else byKey.set(key, { state, mass });
        return;
      }
      // deterministic wave pick: min entropy, tie → lexicographic key
      let best = null; let bestH = Infinity;
      for (const w of waves) {
        const p = _posterior(calc, state, w.e, w.sort);
        const h = _entropy(p);
        if (h < bestH - 1e-12 || (h < bestH + 1e-12 && (!best || w.key < best.w.key))) {
          best = { w, p }; bestH = h;
        }
      }
      const { members, weights } = best.p;
      const order = members.map((m, i) => [m, weights[i]])
        .filter(([, w]) => w[0] > 0n);
      if (mode === 'solve') order.sort((a, b) => -ratCmp(a[1], b[1]) || (a[0] < b[0] ? -1 : 1));
      for (const [m, w] of order) {
        go(substituteEvar(state, best.w.e, Store.put('atom', [m])), ratMul(mass, w), depth + 1);
        if (found) return;
      }
    };
    go(_clone(initialState), ONE, 0);
    if (mode === 'solve') {
      return found ? { state: found.state, ground: true } : { state: null, exhausted: true };
    }
    const outcomes = [...byKey.values()];
    let total = ZERO;
    for (const o of outcomes) total = ratAdd(total, o.mass);
    return { outcomes, total };
  }

  throw new Error(`decimate: unknown mode '${mode}' (sample | exact | solve)`);
}

export { collapse, substituteEvar, openSuspended };
export default { collapse, substituteEvar, openSuspended };
